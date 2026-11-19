import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
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


if __name__ == "__main__":
    unittest.main()
