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
from scripts.produce_ec_witness import build_input, report_fields

ROOT = Path(__file__).resolve().parents[1]
JOINED = ROOT / "tests/fixtures/lmfdb/112.a2-joined.json"
PRODUCER = ROOT / "scripts/produce_ec_witness.py"
CAPTURE = ROOT / "scripts/capture_lmfdb_fixture.py"
NATIVE = ROOT / "tests/fixtures/lmfdb/112.a2-native.json"
NATIVE_MANIFEST = NATIVE.with_suffix(".provenance.json")
TAMAGAWA_17A2 = ROOT / "tests/fixtures/lmfdb/17.a2-tamagawa-joined.json"
TAMAGAWA_TYPE_III_49A4 = ROOT / "tests/fixtures/lmfdb/49.a4-tamagawa-joined.json"
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
    def test_integral_count_status_requires_exact_or_checked_lower_bound(self) -> None:
        witness = {"num_int_pts": 1, "integral_points": [[0, 0]]}
        fields: dict[str, dict[str, Any]] = {}
        report_fields(
            witness,
            fields,
            {"WitnessCheck.listed_integral_count_lower_bound": True},
            {},
            [],
        )
        self.assertEqual(fields["num_int_pts"]["status"], "partial")

        fields = {}
        report_fields(
            witness,
            fields,
            {
                "WitnessCheck.listed_integral_count_lower_bound": True,
                "WitnessCheck.num_int_pts": True,
            },
            {},
            [],
        )
        self.assertEqual(fields["num_int_pts"]["status"], "checked")

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
    def test_native_i2_tamagawa_projection_and_corruption(self) -> None:
        data = json.loads(TAMAGAWA_17A2.read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory() as d:
            directory = Path(d)
            result, report, output = produce(data, directory, timeout=600)
            self.assertEqual(result.returncode, 0, (report, result.stderr))
            self.assertEqual(report["status"], "checked")
            field = report["fields"]["local_invariants.17.tamagawa_number"]
            self.assertEqual(field["status"], "checked")
            self.assertEqual(field["sources"], ["ec_localdata[17].tamagawa_number"])
            witness = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(witness["local_invariants"][0]["tamagawa_number"], 2)

            previous = output.read_bytes()
            rows(data, "ec_localdata")[0]["tamagawa_number"] = 1
            result, report, output = produce(data, directory, timeout=600)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(report["status"], "rejected")
            self.assertIn("tamagawa_values_valid", report["error"])
            self.assertEqual(output.read_bytes(), previous)

    def test_tame_type_iii_tamagawa_projection_and_corruption(self) -> None:
        data = json.loads(TAMAGAWA_TYPE_III_49A4.read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory() as d:
            directory = Path(d)
            result, report, output = produce(data, directory, timeout=600)
            self.assertEqual(result.returncode, 0, (report, result.stderr))
            self.assertEqual(report["status"], "checked")
            field = report["fields"]["local_invariants.7.tamagawa_number"]
            self.assertEqual(field["status"], "checked")
            self.assertEqual(field["sources"], ["ec_localdata[7].tamagawa_number"])
            witness = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(witness["local_invariants"][0]["tamagawa_number"], 2)

            previous = output.read_bytes()
            rows(data, "ec_localdata")[0]["tamagawa_number"] = 1
            result, report, output = produce(data, directory, timeout=600)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(report["status"], "rejected")
            self.assertIn("tamagawa_values_valid", report["error"])
            self.assertEqual(output.read_bytes(), previous)

    def test_mod_two_obstruction_checks_empty_integral_count(self) -> None:
        # LMFDB 179.a1 has no points modulo two and no integral x-coordinates.
        with tempfile.TemporaryDirectory() as d:
            data = {
                "ainvs": [0, 0, 1, -1, -1],
                "xcoord_integral_points": [],
                "num_int_pts": 0,
            }
            result, report, output = produce(data, Path(d), timeout=600)
            self.assertEqual(result.returncode, 0, (report, result.stderr))
            self.assertEqual(report["fields"]["num_int_pts"]["status"], "checked")
            witness = json.loads(output.read_text())
            self.assertEqual(witness["num_int_pts"], 0)

            previous = output.read_bytes()
            data["num_int_pts"] = 1
            result, report, output = produce(data, Path(d), timeout=600)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(report["status"], "rejected")
            self.assertEqual(output.read_bytes(), previous)

        # 37.a1 has affine points modulo two, so an empty x-coordinate claim
        # cannot trigger exact completeness; the ordinary fallback stays partial.
        with tempfile.TemporaryDirectory() as d:
            data = {
                "ainvs": [0, 0, 1, -1, 0],
                "xcoord_integral_points": [],
                "num_int_pts": 1,
            }
            result, report, _ = produce(data, Path(d), timeout=600)
            self.assertEqual(result.returncode, 0, (report, result.stderr))
            self.assertEqual(report["status"], "checked")
            self.assertEqual(report["fields"]["num_int_pts"]["status"], "unsupported")

    def test_torsion_structure_and_trivial_intrinsic_torsion(self) -> None:
        fixture = ROOT / "tests/fixtures/torsion/120.b4.json"
        data = json.loads(fixture.read_text())
        data.pop("torsion_bound", None)
        data.pop("torsion_generator_orders", None)
        with tempfile.TemporaryDirectory() as d:
            result, report, _ = produce(data, Path(d), timeout=600)
        self.assertEqual(result.returncode, 0, (report, result.stderr))
        self.assertEqual(report["fields"]["torsion"]["status"], "checked")
        self.assertEqual(report["fields"]["torsion_structure"]["status"], "checked")

        native = {"ainvs": [0, 0, 1, -1, 0], "intrinsic_torsion": 1}
        with tempfile.TemporaryDirectory() as d:
            result, report, _ = produce(native, Path(d), timeout=600)
        self.assertEqual(result.returncode, 0, (report, result.stderr))
        self.assertEqual(report["fields"]["intrinsic_torsion"]["status"], "checked")

    def test_corrupted_torsion_claim_is_rejected_without_output(self) -> None:
        fixture = ROOT / "tests/fixtures/torsion/120.b4.json"
        data = json.loads(fixture.read_text())
        data.pop("torsion_bound", None)
        data.pop("torsion_generator_orders", None)
        data["torsion_structure"] = [1, 8]
        with tempfile.TemporaryDirectory() as d:
            result, report, output = produce(data, Path(d), timeout=600)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(report["status"], "rejected")
        self.assertFalse(output.exists())

    def test_partial_aplist_checks_retained_prime(self) -> None:
        for coefficient in (-3, -2):
            with (
                self.subTest(coefficient=coefficient),
                tempfile.TemporaryDirectory() as d,
            ):
                data = {
                    "ainvs": [0, 0, 8, -16, 0],
                    "aplist": [0, coefficient],
                    "integral_points": [[0, 0]],
                }
                result, report, output = produce(data, Path(d), timeout=600)
                if coefficient == -3:
                    self.assertEqual(result.returncode, 0, (report, result.stderr))
                    self.assertEqual(report["status"], "checked")
                    self.assertEqual(report["fields"]["aplist"]["status"], "partial")
                    integral = report["fields"]["integral_points"]
                    self.assertEqual(integral["status"], "partial")
                    self.assertIn(
                        "All supplied integral pairs lie on the curve",
                        integral["reason"],
                    )
                    self.assertIn("completeness needs evidence", integral["reason"])
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

    def test_native_analytic_rank_and_special_value(self) -> None:
        # Relevant fields from the joined LMFDB 37.a1 row.
        data = {
            "tables": ["ec_curvedata", "ec_mwbsd"],
            "label_cols": ["lmfdb_label", "lmfdb_label"],
            "labels": ["37.a1", "37.a1"],
            "data": [
                [
                    {
                        "lmfdb_label": "37.a1",
                        "lmfdb_iso": "37.a",
                        "ainvs": [0, 0, 1, -1, 0],
                        "conductor": 37,
                        "analytic_rank": 1,
                        "serre_invariants": [[37, 38, 1]],
                    }
                ],
                [
                    {
                        "lmfdb_label": "37.a1",
                        "conductor": 37,
                        "tamagawa_product": 1,
                        "special_value": {
                            "__RealLiteral__": 0,
                            "data": "0.30599977383405230182048368332169132525",
                            "prec": 127,
                        },
                    }
                ],
            ],
        }
        with tempfile.TemporaryDirectory() as d:
            directory = Path(d)
            result, report, output = produce(data, directory, timeout=600)
            self.assertEqual(result.returncode, 0, (report, result.stderr))
            self.assertEqual(report["fields"]["analytic_rank"]["status"], "checked")
            self.assertEqual(report["fields"]["tamagawa_product"]["status"], "checked")
            self.assertEqual(report["fields"]["serre_invariants"]["status"], "partial")
            self.assertEqual(report["fields"]["special_value"]["status"], "partial")
            self.assertIn("special_value_precision_inconclusive", report["obligations"])
            previous = output.read_bytes()
            witness = json.loads(previous)
            self.assertEqual(witness["analytic_witness"]["rank"], "1")
            self.assertEqual(
                witness["special_value"], rows(data, "ec_mwbsd")[0]["special_value"]
            )

            rows(data, "ec_curvedata")[0]["analytic_rank"] = 0
            result, report, output = produce(data, directory, timeout=600)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(report["status"], "rejected")
            self.assertIn("catalogue_rank_value_eq", report["error"])
            self.assertEqual(output.read_bytes(), previous)

            rows(data, "ec_curvedata")[0]["analytic_rank"] = 1
            rows(data, "ec_mwbsd")[0]["special_value"]["data"] = "20.0000"
            result, report, output = produce(data, directory, timeout=600)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(
                "special_value_disagrees_with_enclosure", report["obligations"]
            )
            self.assertIn("special_value_valid", report["error"])
            self.assertEqual(output.read_bytes(), previous)

    def test_native_join_and_importable_typed_facts(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            directory = Path(d)
            projection = directory / "projection.json"
            replay = subprocess.run(
                [
                    sys.executable,
                    str(CAPTURE),
                    "replay",
                    str(NATIVE),
                    "--manifest",
                    str(NATIVE_MANIFEST),
                    "--output",
                    str(projection),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
            )
            self.assertEqual(replay.returncode, 0, replay.stdout + replay.stderr)
            data = json.loads(projection.read_text(encoding="utf-8"), parse_float=str)
            # The separate algebraic rank report supplies no input to the analytic proof.
            rows(data, "ec_curvedata")[0]["rank"] = 99
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
                "abc_quality",
                "analytic_rank",
                "torsion",
                "torsion_primes",
                "torsion_structure",
                "torsion_generators",
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
                "xcoord_integral_points",
            ):
                self.assertEqual(report["fields"][field]["status"], "partial")
            for field in ("rank", "rank_bounds"):
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
example :
    |(Produced.curve.baseChange ℚ).abcQuality Produced.abc_quality_defined -
      (10348177494302118 / 10000000000000000 : ℝ)| ≤ 1 / 1000000000000 := by
  convert Produced.abc_quality using 1 <;> norm_num [Produced.claimed_abc_quality]
example : (Produced.curve.baseChange ℚ).toAffine.Equation 0 2 :=
  Produced.generators.points_on_curve 0 2 (by decide +kernel)
example : (Produced.certificate.arithmetic.tamagawa.map fun f => ((f.prime : ℕ), f.value)) =
    [(7, 1)] := by decide +kernel
example : (Produced.certificate.analytic.rank.map (·.val)) = some 1 := rfl
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
        for corruption in (
            "j-invariant",
            "abc quality",
            "prime 7 discriminant valuation",
        ):
            with (
                self.subTest(corruption=corruption),
                tempfile.TemporaryDirectory() as d,
            ):
                data = joined()
                if corruption == "j-invariant":
                    rows(data, "ec_curvedata")[0]["jinv"] = [-5, 7]
                elif corruption == "abc quality":
                    rows(data, "ec_curvedata")[0]["abc_quality"] = 2
                else:
                    rows(data, "ec_localdata")[1]["discriminant_valuation"] = 2
                result, report, output = produce(data, Path(d), timeout=600)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(report["status"], "rejected")
                expected_check = {
                    "j-invariant": "j_invariant",
                    "abc quality": "abc_quality",
                    "prime 7 discriminant valuation": "local_invariants",
                }[corruption]
                self.assertIn(expected_check, report["error"])
                self.assertFalse(output.exists())
                self.assertEqual(
                    {path.name for path in Path(d).iterdir()}, {"joined.json"}
                )


if __name__ == "__main__":
    unittest.main()
