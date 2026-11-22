"""SMT comparison of return/state values, with concrete countermodel replay."""
from dataclasses import dataclass, field
import math
import re
import subprocess
import time


@dataclass
class Proof:
    status: str
    query: str
    responses: list = field(default_factory=list)
    reason: str | None = None
    witness: dict | None = None


def compare(graph, source, generated, executable, seconds=2, *, recorded=None, failure_reason=None):
    if type(seconds) not in [int, float] or not math.isfinite(seconds) or not 0 < seconds <= 30:
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
    retained = None if recorded is None else list(recorded)
    def run(model=False):
        script = query + '(check-sat)\n' + ('(get-value (word0 word1 word2 word3))\n' if model else '')
        if retained is None:
            started = time.monotonic()
            result = subprocess.run([str(executable), '-in', '-smt2'], input=script,
                                    capture_output=True, text=True, timeout=seconds + 0.25)
            response = {'returncode': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr,
                        'wall_seconds': time.monotonic() - started}
        else:
            if not retained:
                if failure_reason == 'solver_unavailable': raise FileNotFoundError()
                if failure_reason == 'solver_timeout': raise subprocess.TimeoutExpired('retained-solver', seconds)
                raise ValueError(failure_reason or 'missing solver response')
            response = retained.pop(0)
            if (not isinstance(response, dict) or set(response) != {'returncode', 'stdout', 'stderr', 'wall_seconds'}
                    or type(response['returncode']) is not int
                    or type(response['wall_seconds']) not in [int, float]
                    or not math.isfinite(response['wall_seconds']) or response['wall_seconds'] < 0
                    or not all(isinstance(response[k], str) for k in ['stdout', 'stderr'])):
                raise ValueError('solver record shape')
        proof.responses.append(response)
        if response['returncode'] or response['stderr'] or len(response['stdout']) > 65536:
            raise ValueError('solver failure or excessive output')
        return response['stdout'].strip()
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
        if retained: raise ValueError('unused solver responses')
    except FileNotFoundError:
        proof.reason = 'solver_unavailable'
    except subprocess.TimeoutExpired:
        proof.reason = 'solver_timeout'
    except (OSError, ValueError) as error:
        proof.status, proof.witness = 'unknown', None
        proof.reason = str(error)
    return proof
