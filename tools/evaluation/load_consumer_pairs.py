"""Replay the checked load-consumer pair under its explicit private-value projection.

Rust validates the rewrite and source/display correspondence. This reader
validates retained boundaries, coverage, input binding and raw observations.
"""

import re
from . import semantic_pairs
from .semantics import sha

MODEL = "checked-strict-load-consumer-v1"
PAIR_MODEL = "load-consumer-state-pairs-v1"
PAIR_FILE = "load-consumer-states.jsonl"
CHECKER = "load_consumer::validate+readable::loop_recovery::source"
STABLE_MODEL = "checked-stable-load-consumer-v2"
STABLE_CHECKER = (
    "load_consumer::validate_with_stable_inputs+readable::loop_recovery::source"
)
MEMORY_MODEL = "checked-memory-value-consumer-v3"
MEMORY_CHECKER = (
    "load_consumer::validate_memory_values+readable::loop_recovery::source"
)
MAX_CONTEXT_INPUTS = 64
MAX_IR = 16 * 1024 * 1024
ARTIFACTS = {
    "input_ir": "load-consumer-input.ir.txt",
    "lowered_ir": "load-consumer-lowered.ir.txt",
}
require = semantic_pairs.require


def register_list(value, registers, *, nonempty=False):
    require(
        isinstance(value, list)
        and (bool(value) or not nonempty)
        and len(value) <= registers
        and all(type(n) is int and 0 <= n < registers for n in value)
        and len(set(value)) == len(value),
        "load-consumer register set",
    )
    return value


def validate(
    entry, budgets, requested, directory, machine_registers, *, retained=False
):
    e = entry["transition"]
    require(
        isinstance(e, dict)
        and set(e) - {k + "_sha256" for k in ARTIFACTS}
        == {
            "model",
            "checker",
            "registers",
            "entry",
            "parameters",
            "private_registers",
            "folds",
            *ARTIFACTS,
            "state_pairs",
        },
        "load-consumer transition fields",
    )
    require(
        type(e["model"]) is str
        and e["model"] in [MODEL, STABLE_MODEL, MEMORY_MODEL]
        and e["checker"]
        == {MODEL: CHECKER, STABLE_MODEL: STABLE_CHECKER, MEMORY_MODEL: MEMORY_CHECKER}[
            e["model"]
        ]
        and type(e["registers"]) is int
        and machine_registers <= e["registers"] <= 65536
        and semantic_pairs.u64(e["entry"]),
        "load-consumer transition boundary",
    )
    registers = e["registers"]
    params = register_list(e["parameters"], registers)
    private = register_list(e["private_registers"], registers, nonempty=True)
    require(
        private == sorted(private) and not set(params).intersection(private),
        "load-consumer private parameter exclusion",
    )
    folds = e["folds"]
    require(
        isinstance(folds, list) and 1 <= len(folds) <= 64, "load-consumer fold count"
    )
    temps = []
    loads = set()
    consumers = set()
    stable = e["model"] in [STABLE_MODEL, MEMORY_MODEL]
    memory = e["model"] == MEMORY_MODEL
    contextual = False
    memory_expression = False
    for fold in folds:
        require(
            isinstance(fold, dict)
            and set(fold)
            == {
                "load_pc",
                "load_assignment",
                "consumer_pc",
                "consumer_assignment",
                "temporary",
                "destination",
            }
            | ({"inputs"} if stable else set())
            | ({"producer_kind"} if memory else set())
            and all(semantic_pairs.u64(fold[k]) for k in ["load_pc", "consumer_pc"])
            and all(
                type(fold[k]) is int and 0 <= fold[k] < 32768
                for k in ["load_assignment", "consumer_assignment"]
            )
            and all(
                type(fold[k]) is int and 0 <= fold[k] < registers
                for k in ["temporary", "destination"]
            )
            and fold["temporary"] != fold["destination"],
            "load-consumer fold shape",
        )
        load = (fold["load_pc"], fold["load_assignment"])
        consumer = (fold["consumer_pc"], fold["consumer_assignment"])
        require(
            load != consumer and load not in loads and consumer not in consumers,
            "load-consumer distinct paired points",
        )
        loads.add(load)
        consumers.add(consumer)
        temps.append(fold["temporary"])
        if memory:
            require(
                type(fold["producer_kind"]) is str
                and fold["producer_kind"] in ["root_load", "memory_expression"],
                "load-consumer exact producer kind",
            )
            memory_expression |= fold["producer_kind"] == "memory_expression"
        if stable:
            inputs = register_list(fold["inputs"], registers)
            require(
                len(inputs) <= MAX_CONTEXT_INPUTS
                and inputs == sorted(inputs)
                and not set(inputs).intersection(private),
                "load-consumer stable context inputs",
            )
            contextual |= bool(inputs)
    require(
        len(set(temps)) == len(temps)
        and sorted(temps) == private
        and not loads.intersection(consumers),
        "load-consumer exact private fold projection",
    )
    require(
        not stable or memory or contextual,
        "load-consumer stable model needs context inputs",
    )
    require(
        not memory or memory_expression,
        "load-consumer memory model needs a memory expression",
    )
    for key, name in ARTIFACTS.items():
        require(e[key] == name, "load-consumer IR artifact name")
        path = directory / name
        require(path.stat().st_size <= MAX_IR, "load-consumer IR artifact quota")
        digest = sha(path)
        require(
            (not retained or key + "_sha256" in e)
            and e.get(key + "_sha256", digest) == digest,
            "load-consumer IR artifact hash",
        )
        with path.open() as stream:
            header = re.fullmatch(
                r"entry=(\d+) registers=(\d+)\n", stream.readline(1024)
            )
        require(
            header is not None
            and [int(header[1]), int(header[2])] == [e["entry"], registers],
            "load-consumer exact input/lowered namespace",
        )
        e[key + "_sha256"] = digest
    adapted = dict(e, source_registers=registers)
    e["state_pairs"] = semantic_pairs.validate_projected(
        e["state_pairs"],
        entry,
        adapted,
        budgets,
        requested,
        directory,
        machine_registers,
        model=PAIR_MODEL,
        filename=PAIR_FILE,
        private=tuple(private),
        retained=retained,
    )
    return e
