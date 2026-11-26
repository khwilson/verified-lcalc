"""Exercise the single-curve producer without running Lean in the Python suite."""

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.produce_ec_witness import build_input

ROOT = Path(__file__).resolve().parents[1]
JOINED = ROOT / "tests/fixtures/lmfdb/112.a2-joined.json"
PRODUCER = ROOT / "scripts/produce_ec_witness.py"
LEAN = ["lake", "-f", "lakefile.certificates.lean", "env", "lean"]


def joined() -> dict[str, Any]:
    return json.loads(JOINED.read_text())


def rows(data: dict[str, Any], table: str) -> list[dict[str, Any]]:
    return data["data"][data["tables"].index(table)]


def produce(
    data: dict[str, Any], directory: Path, timeout: int
) -> tuple[subprocess.CompletedProcess[str], dict[str, Any], Path]:
    source = directory / "joined.json"
    source.write_text(json.dumps(data))
    output = directory / "witness.json"
    result = subprocess.run(
        [sys.executable, str(PRODUCER), str(source), "--output", str(output)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )
    if not result.stdout:
        raise AssertionError(result.stderr)
    return result, json.loads(result.stdout), output


class JoinChecks(unittest.TestCase):
    def test_accept_native_curve_and_class_labels(self) -> None:
        witness, _, sources = build_input(joined())
        self.assertEqual(witness["ainvs"], [0, 1, 0, 0, 4])
        self.assertEqual(witness["conductor"], 112)
        self.assertEqual([row["prime"] for row in witness["local_invariants"]], [2, 7])
        self.assertEqual(
            {
                source
                for source in sources["conductor"]
                if source.startswith("ec_galrep")
            },
            {"ec_galrep[0].conductor", "ec_galrep[2].conductor"},
        )

    def test_reject_mismatched_subject_rows_and_duplicate_prime(self) -> None:
        for corruption in (
            "isogeny class",
            "local conductor",
            "Galois conductor",
            "duplicate prime",
        ):
            with (
                self.subTest(corruption=corruption),
                tempfile.TemporaryDirectory() as d,
            ):
                directory = Path(d)
                data = joined()
                local = rows(data, "ec_localdata")
                previous = (
                    b"previous witness\n" if corruption == "isogeny class" else None
                )
                if previous is not None:
                    (directory / "witness.json").write_bytes(previous)
                if corruption == "isogeny class":
                    rows(data, "ec_classdata")[0]["lmfdb_iso"] = "112.b"
                elif corruption == "local conductor":
                    local[1]["conductor"] = 113
                elif corruption == "Galois conductor":
                    rows(data, "ec_galrep")[1]["conductor"] = 113
                else:
                    local.append({**local[0], "id": 715})
                result, report, output = produce(data, directory, timeout=30)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(report["status"], "rejected")
                if previous is not None:
                    self.assertEqual(output.read_bytes(), previous)
                else:
                    self.assertFalse(output.exists())


@unittest.skipUnless(
    os.environ.get("VERIFIED_LCALC_PRODUCER_LEAN") == "1", "Lean CI only"
)
class KernelReplay(unittest.TestCase):
    def test_partial_aplist_checks_retained_prime(self) -> None:
        for coefficient in (-3, -2):
            with (
                self.subTest(coefficient=coefficient),
                tempfile.TemporaryDirectory() as d,
            ):
                data = {"ainvs": [0, 0, 8, -16, 0], "aplist": [0, coefficient]}
                result, report, output = produce(data, Path(d), timeout=600)
                if coefficient == -3:
                    self.assertEqual(result.returncode, 0, (report, result.stderr))
                    self.assertEqual(report["status"], "checked")
                    self.assertEqual(report["fields"]["aplist"]["status"], "partial")
                    self.assertIn(
                        "aplist_minimality_inconclusive", report["obligations"]
                    )
                    witness = json.loads(output.read_text())
                    self.assertNotIn("aplist", witness)
                    self.assertEqual(witness["ap"], [["3", "-3"]])
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(report["status"], "rejected")
                    self.assertIn("prime_coefficients_valid", report["error"])
                    self.assertFalse(output.exists())

    def test_native_join_and_importable_typed_facts(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            directory = Path(d)
            data = joined()
            # A deliberately implausible reference rank must not affect arithmetic proof search.
            rows(data, "ec_curvedata")[0].update(analytic_rank=99, rank=99)
            rows(data, "ec_mwbsd")[0]["rank_bounds"] = [99, 99]
            result, report, output = produce(data, directory, timeout=600)
            self.assertEqual(result.returncode, 0, (report, result.stderr))
            self.assertEqual(report["status"], "checked")
            self.assertEqual(report["input_provenance"], data["provenance"])
            self.assertEqual(
                set(report["fields"]["conductor"]["sources"]),
                {
                    "ec_curvedata.conductor",
                    "ec_classdata.conductor",
                    "ec_mwbsd.conductor",
                    "ec_localdata[2].conductor",
                    "ec_localdata[7].conductor",
                    "ec_galrep[0].conductor",
                    "ec_galrep[2].conductor",
                },
            )
            for field in [
                "ainvs",
                "jinv",
                "signD",
                "absD",
                "conductor",
                "bad_primes",
                "num_bad_primes",
                "potential_good_reduction",
                "semistable",
                "aplist",
                "anlist",
                "local_invariants.7.kodaira_symbol",
                "local_invariants.7.tamagawa_number",
                *(
                    f"local_invariants.{prime}.{field}"
                    for prime in (2, 7)
                    for field in (
                        "prime",
                        "conductor_valuation",
                        "discriminant_valuation",
                        "j_denominator_valuation",
                        "reduction_type",
                        "root_number",
                    )
                ),
            ]:
                with self.subTest(field=field):
                    self.assertEqual(report["fields"][field]["status"], "checked")
            for field in (
                "gens",
                "ngens",
                "torsion_generators",
                "xcoord_integral_points",
            ):
                self.assertEqual(report["fields"][field]["status"], "partial")
            for field in ("analytic_rank", "rank", "rank_bounds"):
                self.assertEqual(report["fields"][field]["status"], "unsupported")
            for field in ("torsion", "torsion_primes", "torsion_structure"):
                self.assertEqual(report["fields"][field]["status"], "unsupported")
            for prime in (2, 7):
                self.assertEqual(
                    report["fields"][f"local_invariants.{prime}.kodaira_symbol"][
                        "sources"
                    ],
                    [f"ec_localdata[{prime}].kodaira_symbol"],
                )
            self.assertEqual(
                report["fields"]["local_invariants.2.kodaira_symbol"]["status"],
                "partial",
            )
            self.assertEqual(
                report["fields"]["local_invariants.2.tamagawa_number"]["status"],
                "unsupported",
            )
            self.assertTrue(output.is_file())

            # Use the produced file at the public command. Check the theorem
            # types and the scope of the aggregate independently of the report.
            replay = directory / "Replay.lean"
            replay.write_text(
                """import VerifiedLcalc.Tactic.CertifyEC
open VerifiedLcalc
certify_ec Produced from_json "witness.json"

example : Produced.curve.Δ = -7168 := by decide +kernel
example : Produced.curve.Δ.natAbs = 7168 := Produced.minimal_discriminant_abs.2
example : Produced.curve.Δ.sign = -1 := Produced.discriminant_sign
example : (Produced.curve.baseChange ℚ).j = -4 / 7 := Produced.j_invariant
example : (Produced.curve.baseChange ℚ).toAffine.Equation 0 2 :=
  Produced.generators.points_on_curve 0 2 (by decide +kernel)
example : (Produced.certificate.arithmetic.tamagawa.map fun f => ((f.prime : ℕ), f.value)) =
    [(7, 1)] := by decide +kernel
example : Produced.certificate.analytic.rank.isNone = true := rfl
example : Produced.certificate.algebraic.rank.isNone = true := rfl
"""
            )
            verification = subprocess.run(
                [*LEAN, str(replay)],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=600,
                check=False,
            )
            self.assertEqual(
                verification.returncode, 0, verification.stdout + verification.stderr
            )

    def test_corrupt_supported_claims_have_no_output(self) -> None:
        for corruption in ("j-invariant", "prime 7 discriminant valuation"):
            with (
                self.subTest(corruption=corruption),
                tempfile.TemporaryDirectory() as d,
            ):
                data = joined()
                if corruption == "j-invariant":
                    rows(data, "ec_curvedata")[0]["jinv"] = [-5, 7]
                else:
                    rows(data, "ec_localdata")[1]["discriminant_valuation"] = 2
                result, report, output = produce(data, Path(d), timeout=600)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(report["status"], "rejected")
                expected_check = (
                    "j_invariant" if corruption == "j-invariant" else "local_invariants"
                )
                self.assertIn(expected_check, report["error"])
                self.assertFalse(output.exists())
                self.assertEqual(
                    {path.name for path in Path(d).iterdir()}, {"joined.json"}
                )


if __name__ == "__main__":
    unittest.main()
