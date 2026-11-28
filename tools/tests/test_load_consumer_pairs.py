"""Private-value projection remains narrow and raw snapshots remain replayable."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation import load_consumer_pairs as folds, stages, reports, semantic_pairs
from evaluation.semantics import ProtocolError
import test_semantic_pairs as pair_fixtures
from test_selected_signed_storage import bound_report
from report_fixture import save


def fixture(root):
    evidence, budgets, rows = pair_fixtures.StatePairTests().fixture(root)
    (root / "input.ir").rename(root / folds.ARTIFACTS["input_ir"])
    save(root, folds.ARTIFACTS["lowered_ir"], "entry=16 registers=34\npaired IR\n")
    for row in rows:
        if row["budget"]:
            row["actual"]["registers"][32] ^= 123
    transition = dict(
        model=folds.MODEL,
        checker=folds.CHECKER,
        registers=34,
        entry=16,
        parameters=[4, 7],
        private_registers=[32],
        folds=[
            dict(
                load_pc=16,
                load_assignment=0,
                consumer_pc=32,
                consumer_assignment=0,
                temporary=32,
                destination=33,
            )
        ],
        **folds.ARTIFACTS,
        state_pairs=dict(model=folds.PAIR_MODEL, file=folds.PAIR_FILE),
    )
    entry = dict(
        name="selected_load_consumer",
        status="passed",
        observations=len(rows),
        comparisons=["lowered_zero", "lowered_ones"],
        witness=None,
        transition=transition,
    )
    return entry, budgets, rows


def replay(root, entry, budgets, rows, *, retained=False):
    save(root, folds.PAIR_FILE, "".join(json.dumps(row) + "\n" for row in rows))
    folds.validate(entry, budgets, 3, root, 32, retained=retained)
    return entry["transition"]["state_pairs"]


class LoadConsumerPairs(unittest.TestCase):
    def test_private_values_are_preserved_raw_and_only_the_checked_projection_is_compared(
        self,
    ):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            entry, budgets, rows = fixture(root)
            result = replay(root, entry, budgets, rows)
            self.assertEqual(
                (
                    result["rows"],
                    result["mismatches"],
                    result["private_difference_rows"],
                ),
                (18, 0, 12),
            )
            self.assertEqual(result["input_binding"], "native-vectors")
            self.assertEqual(replay(root, entry, budgets, rows, retained=True), result)
            raw = json.loads((root / folds.PAIR_FILE).read_text().splitlines()[-1])
            self.assertNotEqual(
                raw["expected"]["registers"][32], raw["actual"]["registers"][32]
            )

    def test_public_state_and_initial_state_mutations_are_counterexamples(self):
        for field in [
            "register",
            "ram",
            "fault",
            "pc",
            "trace",
            "input",
            "initial-private",
            "coverage",
            "truncated",
        ]:
            with tempfile.TemporaryDirectory() as temporary, self.subTest(field=field):
                root = Path(temporary)
                entry, budgets, rows = fixture(root)
                if field == "register":
                    rows[-1]["actual"]["registers"][33] ^= 1
                elif field == "ram":
                    rows[-1]["actual"]["memory"][0] ^= 1
                elif field == "fault":
                    rows[-1]["actual"]["status"] = [1, 0, 1, 8]
                elif field == "pc":
                    rows[-1]["actual"]["instruction"] = 99
                elif field == "trace":
                    rows[-1]["actual"]["trace"] = [99]
                elif field == "input":
                    rows[-1]["input"][7] ^= 1
                elif field == "initial-private":
                    rows[0]["actual"]["registers"][32] ^= 1
                elif field == "coverage":
                    rows[0], rows[1] = rows[1], rows[0]
                else:
                    rows.pop()
                    entry["observations"] -= 1
                with self.assertRaises(ProtocolError):
                    replay(root, entry, budgets, rows)

    def test_fold_projection_parameters_shapes_and_bindings_cannot_be_relaxed(self):
        mutations = [
            lambda e: e.update(private_registers=[32, 33]),
            lambda e: e.update(private_registers=[33]),
            lambda e: e.update(private_registers=[32, 32]),
            lambda e: e.update(private_registers=[True]),
            lambda e: e.update(private_registers=[[]]),
            lambda e: e.update(parameters=[4, 7, 32]),
            lambda e: e.update(registers=True),
            lambda e: e.update(entry=32),
            lambda e: e.update(checker="unchecked"),
            lambda e: e["folds"].append(copy.deepcopy(e["folds"][0])),
            lambda e: e["folds"][0].update(destination=32),
            lambda e: e["folds"][0].update(load_assignment=True),
            lambda e: e["folds"][0].update(consumer_pc=16),
            lambda e: e.update(input_ir="elsewhere.ir"),
            lambda e: e.update(lowered_ir_sha256="0" * 64),
        ]
        for n, mutate in enumerate(mutations):
            with tempfile.TemporaryDirectory() as temporary, self.subTest(mutation=n):
                root = Path(temporary)
                entry, budgets, rows = fixture(root)
                mutate(entry["transition"])
                with self.assertRaises(ProtocolError):
                    replay(root, entry, budgets, rows)

    def test_partial_records_and_replayed_public_counterexamples_remain_distinct(self):
        for status in ["budget_exhausted", "counterexample"]:
            with (
                tempfile.TemporaryDirectory() as temporary,
                self.subTest(status=status),
            ):
                root = Path(temporary)
                entry, budgets, rows = fixture(root)
                entry["status"] = status
                if status == "counterexample":
                    rows[-1]["actual"]["registers"][33] ^= 1
                else:
                    rows.pop()
                    entry["observations"] -= 1
                result = replay(root, entry, budgets, rows)
                self.assertEqual(result["mismatches"], int(status == "counterexample"))

    def test_v9_requires_the_new_stage_and_summary_and_replays_legacy_v8(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            report = bound_report(root)
            row = report["rows"][0]
            directory = root / row["artifacts"] / "semantics"
            entry, budgets, rows = fixture(directory)
            replay(directory, entry, budgets, rows)
            value = row["stage_checks"]
            self.assertEqual(value["schema"], "nirvana-evaluation-stages-v8")
            stages.validate(value, 4, directory, 3, 32, retained=True)
            value.update(
                schema="nirvana-evaluation-stages-v9",
                contract="nirvana-stage-input-state-v9",
            )
            value["selected_c"]["parameter_registers"] = [4, 7]
            value["execution"].append(entry)
            stages.validate(value, 4, directory, 3, 32)
            report["summary"]["architecture_execution"] = stages.execution_summary(
                report["rows"]
            )
            reports.index(report)
            report["summary"]["architecture_execution"].pop("selected_load_consumer")
            with self.assertRaisesRegex(ValueError, "execution denominator"):
                reports.index(report)
            value["execution"].pop()
            with self.assertRaisesRegex(ProtocolError, "execution names"):
                stages.validate(value, 4, directory, 3, 32)

    def test_new_counterexample_is_a_regression_even_when_baseline_was_inconclusive(
        self,
    ):
        with tempfile.TemporaryDirectory() as temporary:
            roots = [Path(temporary) / side for side in ["before", "after"]]
            for n, root in enumerate(roots):
                report = bound_report(root)
                row = report["rows"][0]
                directory = root / row["artifacts"] / "semantics"
                entry, budgets, rows = fixture(directory)
                if n:
                    entry.update(
                        status="counterexample",
                        witness="selected_load_consumer.witness.txt",
                    )
                    rows[-1]["actual"]["registers"][33] ^= 1
                    save(directory, entry["witness"], "public register corruption\n")
                else:
                    entry.update(status="budget_exhausted", observations=0)
                    rows = []
                replay(directory, entry, budgets, rows)
                value = row["stage_checks"]
                value.update(
                    schema="nirvana-evaluation-stages-v9",
                    contract="nirvana-stage-input-state-v9",
                    status="counterexample" if n else "inconclusive",
                )
                value["selected_c"]["parameter_registers"] = [4, 7]
                value["execution"].append(entry)
                stages.validate(value, 4, directory, 3, 32)
                row["semantics"]["prepare_stdout_sha256"] = save(
                    directory.parent,
                    "semantic_prepare.stdout.txt",
                    json.dumps({**row["semantics"]["profile"], "stage_checks": value}),
                )
                report["summary"]["architecture_execution"] = stages.execution_summary(
                    report["rows"]
                )
                save(root, "report.json", json.dumps(report))
            comparison = reports.compare(*(root / "report.json" for root in roots))
            self.assertEqual(comparison["architecture_regressions"], 1)
            self.assertEqual(comparison["rows"][0]["architecture_checks_lost"], [])

    def test_downgrading_to_v8_keeps_the_new_observer_in_the_comparison_denominator(
        self,
    ):
        with tempfile.TemporaryDirectory() as temporary:
            roots = [Path(temporary) / side for side in ["before", "after"]]
            for n, root in enumerate(roots):
                report = bound_report(root)
                row = report["rows"][0]
                directory = root / row["artifacts"] / "semantics"
                if n == 0:
                    entry, budgets, rows = fixture(directory)
                    replay(directory, entry, budgets, rows)
                    value = row["stage_checks"]
                    value.update(
                        schema="nirvana-evaluation-stages-v9",
                        contract="nirvana-stage-input-state-v9",
                    )
                    value["selected_c"]["parameter_registers"] = [4, 7]
                    value["execution"].append(entry)
                    stages.validate(value, 4, directory, 3, 32)
                    row["semantics"]["prepare_stdout_sha256"] = save(
                        directory.parent,
                        "semantic_prepare.stdout.txt",
                        json.dumps(
                            {**row["semantics"]["profile"], "stage_checks": value}
                        ),
                    )
                    report["summary"]["architecture_execution"] = (
                        stages.execution_summary(report["rows"])
                    )
                save(root, "report.json", json.dumps(report))
            comparison = reports.compare(*(root / "report.json" for root in roots))
            self.assertEqual(comparison["architecture_regressions"], 1)
            self.assertEqual(
                comparison["candidate_execution"]["selected_load_consumer"],
                {"not_run": 1},
            )


if __name__ == "__main__":
    unittest.main()
