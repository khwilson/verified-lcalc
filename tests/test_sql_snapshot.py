import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.benchmark_conductors import MODULARITY, audit_messages
from scripts.conductor_validation import ARITHMETIC, binding_source
from scripts.download_lmfdb_sql import validate_rows


class SnapshotChecks(unittest.TestCase):
    def test_numeric_array_and_unknown_reference(self) -> None:
        inputs, refs = validate_rows([("37.a1", 37, "[0.0,0,1,-1,0]", None)], [], 1)
        self.assertEqual(inputs[0]["ainvs"], [0, 0, 1, -1, 0])
        self.assertNotIn("analytic_rank", inputs[0])
        self.assertIsNone(refs[0]["analytic_rank"])

    def test_duplicate_exclusion_and_order(self) -> None:
        row = ("37.a1", 37, [0, 0, 1, -1, 0], 1)
        for rows, excluded, count in [
            ([row], ["37.a1"], 1),
            ([row, row], [], 2),
            ([row], [], 2),
            ([("43.a1", 43, [0, 1, 1, 0, 0], 1), row], [], 2),
        ]:
            with (
                self.subTest(rows=rows, excluded=excluded),
                self.assertRaises(ValueError),
            ):
                validate_rows(rows, excluded, count)

    def test_reject_fractional_equation(self) -> None:
        with self.assertRaises(ValueError):
            validate_rows([("37.a1", 37, "[0,0,1,-1.5,0]", 1)], [], 1)

    def test_analytic_assumption_cannot_leak_into_arithmetic(self) -> None:
        with self.assertRaises(ValueError):
            audit_messages(
                f"'X.payload_correct' depends on axioms: [{MODULARITY}]",
                ["X.payload_correct"],
            )
        self.assertEqual(
            audit_messages(
                f"'X.analytic_rank' depends on axioms: [{MODULARITY}]",
                ["X.analytic_rank"],
            ),
            {"X.analytic_rank": [MODULARITY]},
        )

    def test_missing_component_audit_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            audit_messages("", ["X.coefficients_correct"])

    def test_no_axioms_message(self) -> None:
        self.assertEqual(
            audit_messages(
                "'X.nonsingular' does not depend on any axioms", ["X.nonsingular"]
            ),
            {"X.nonsingular": []},
        )

    def test_rank_claim_requires_all_components(self) -> None:
        row = dict(
            label="37.a1",
            conductor=37,
            namespace="X.C37_a1",
            components=["nonsingular"],
            proposed_rank=1,
            lower_bound=None,
            status="proposed-exact-rank-one",
        )
        with self.assertRaises(ValueError):
            binding_source(
                "X",
                37,
                [row],
                [dict(label="37.a1", conductor=37, ainvs=[0, 0, 1, -1, 0])],
            )

    def test_binding_covers_rank_and_numerical_settings(self) -> None:
        row = dict(
            label="37.a1",
            conductor=37,
            namespace="X.C37_a1",
            components=sorted(ARITHMETIC | {"payload_correct", "analytic_rank"}),
            proposed_rank=1,
            lower_bound=None,
            status="proposed-exact-rank-one",
            bits=53,
            terms=12,
            steps=1,
            cutoff=8,
        )
        source, _ = binding_source(
            "X", 37, [row], [dict(label="37.a1", conductor=37, ainvs=[0, 0, 1, -1, 0])]
        )
        self.assertIn("= 1 := X.C37_a1.analytic_rank", source)
        self.assertIn("precisionBits = 53", source)
        self.assertIn("stepsPerUnit = 1", source)
        row["bits"] = "53"
        with self.assertRaises(ValueError):
            binding_source(
                "X",
                37,
                [row],
                [dict(label="37.a1", conductor=37, ainvs=[0, 0, 1, -1, 0])],
            )


if __name__ == "__main__":
    unittest.main()
