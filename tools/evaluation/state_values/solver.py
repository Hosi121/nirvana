"""SMT comparison of return/state values, with concrete countermodel replay."""
from dataclasses import dataclass, field
import math
import re
import subprocess


@dataclass
class Proof:
    status: str
    query: str
    responses: list = field(default_factory=list)
    reason: str | None = None
    witness: dict | None = None


def compare(graph, source, generated, executable, seconds=2):
    if not math.isfinite(seconds) or not 0 < seconds <= 30:
        raise ValueError('invalid state value solver budget')
    if len(source.outputs) != 5 or len(generated.outputs) != 5:
        raise ValueError('state value output denominator')
    if any(graph.type(i).bits != 64 or graph.type(i).signed for i in [*source.outputs, *generated.outputs]):
        raise ValueError('state value output type')
    difference = ' '.join(f'(distinct v{a} v{b})' for a, b in zip(source.outputs, generated.outputs))
    query = (f'(set-option :timeout {max(1, int(seconds * 1000))})\n'
             '(set-option :produce-models true)\n(set-option :pp.bv-literals true)\n'
             + graph.smt() + f'(assert (or {difference}))\n')
    proof = Proof('unknown', query)
    def run(model=False):
        script = query + '(check-sat)\n' + ('(get-value (word0 word1 word2 word3))\n' if model else '')
        result = subprocess.run([str(executable), '-in', '-smt2'], input=script,
                                capture_output=True, text=True, timeout=seconds + 0.25)
        proof.responses.append({'returncode': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr})
        if result.returncode or result.stderr or len(result.stdout) > 65536:
            raise ValueError('solver failure or excessive output')
        return result.stdout.strip()
    try:
        status = run()
        if status == 'unsat': proof.status = 'equivalent_under_model'
        elif status == 'unknown': proof.reason = 'solver_unknown'
        elif status == 'sat':
            response = run(True)
            value = r'\(word[0-3]\s+#x[0-9a-fA-F]{16}\)\s*'
            if not re.fullmatch(r'sat\s*\(\s*(?:' + value + r'){4}\)\s*', response):
                raise ValueError('solver model response')
            words = {int(i): int(n, 16) for i, n in re.findall(r'\(word([0-3])\s+#x([0-9a-fA-F]{16})\)', response)}
            if set(words) != set(range(4)): raise ValueError('solver input word denominator')
            inputs = [words[i] for i in range(4)]
            a, b = [graph.evaluate(m.outputs, inputs) for m in [source, generated]]
            if a == b: raise ValueError('solver countermodel did not replay')
            proof.status = 'counterexample_under_model'
            proof.witness = {'input_words': inputs, 'source': a, 'generated': b}
        else: raise ValueError('solver response')
    except FileNotFoundError:
        proof.reason = 'solver_unavailable'
    except subprocess.TimeoutExpired:
        proof.reason = 'solver_timeout'
    except (OSError, ValueError) as error:
        proof.reason = str(error)
    return proof
