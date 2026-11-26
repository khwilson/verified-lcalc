"""Tests for the table-qualified LMFDB milestone ledger."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from collections.abc import Generator
from contextlib import contextmanager
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.capture_lmfdb_fixture import replay_capture_bytes  # noqa: E402
from scripts.report_lmfdb_field_ledger import (  # noqa: E402
    DEFAULT_COVERAGE,
    build_ledger,
    consumer_statuses,
)

NATIVE = ROOT / "tests/fixtures/lmfdb/112.a2-native.json"
MANIFEST = ROOT / "tests/fixtures/lmfdb/112.a2-native.provenance.json"
COVERAGE = ROOT / "web/certificates/fixture-field-coverage.json"
NEXT_STEPS = ROOT / "docs/roadmaps/lmfdb-producer-next-steps.json"
TABLE_FIELD_KEYS = {
    (entry["table"], entry["field"])
    for entry in json.loads(COVERAGE.read_text())["fields"]
}


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def producer_receipt_provenance(manifest: dict[str, Any]) -> dict[str, Any]:
    return {
        "source": manifest["provenance"]["source"],
        "source_sha256": manifest["provenance"]["sha256"],
        "table_capture_manifest": [
            {
                "name": row["name"],
                "join_key": row["join_key"],
                "join_value": row["join_value"],
                "status": row["status"],
                "row_keys": row["row_keys"],
            }
            for row in manifest["tables"]
        ],
    }


def replay_input_sha256(native_path: Path, manifest: dict[str, Any]) -> str:
    replayed = replay_capture_bytes(native_path.read_bytes(), manifest)
    return hashlib.sha256(replayed).hexdigest()


def natural_key_parts(row: dict[str, Any]) -> tuple[str, ...]:
    names = row["row_key_name"]
    if isinstance(names, str):
        return tuple(names.strip("[]").replace("+", ",").split(","))
    return tuple(names)


def ledger(**kwargs: Path) -> dict[str, Any]:
    return build_ledger(
        kwargs.get("native_path", NATIVE),
        kwargs.get("manifest_path", MANIFEST),
        kwargs.get("coverage_path", COVERAGE),
        kwargs.get("next_steps_path", NEXT_STEPS),
        producer_path=kwargs.get("producer_path"),
    )


class FieldLedgerContracts(unittest.TestCase):
    def test_catalogue_denominator_and_table_qualified_recommendations(self) -> None:
        report = ledger()
        entries = report["fields"]
        keys = [(entry["table"], entry["field"]) for entry in entries]
        self.assertEqual(report["denominator"]["table_qualified_fields"], 101)
        self.assertEqual(report["denominator"]["distinct_names"], 85)
        self.assertEqual(len(keys), 101)
        self.assertEqual(len(set(keys)), 101)
        self.assertEqual(set(keys), TABLE_FIELD_KEYS)
        recommendations = read_json(NEXT_STEPS)
        self.assertEqual(
            set(recommendations), {f"{table}.{field}" for table, field in keys}
        )
        for entry in entries:
            self.assertEqual(
                entry["next_step"],
                recommendations[f"{entry['table']}.{entry['field']}"],
            )

    def test_milestones_remain_independent_and_consumer_does_not_imply_publication(
        self,
    ) -> None:
        report = ledger()
        entries = {
            (entry["table"], entry["field"]): entry for entry in report["fields"]
        }
        rank = entries[("ec_curvedata", "analytic_rank")]
        self.assertEqual(rank["native"]["table_status"], "present")
        self.assertEqual(rank["native"]["field_status"], "value")
        self.assertEqual(rank["producer"]["status"], "not_run")
        self.assertTrue(rank["consumer"]["evidence"])
        self.assertEqual(rank["publication"]["status"], "not_supplied")
        self.assertEqual(rank["blocker"]["layer"], "producer")

        evidence = next(
            evidence
            for evidence in rank["consumer"]["evidence"]
            if evidence["curve"] == "112.a2"
        )
        self.assertEqual(evidence["status"], "assumption_backed")
        self.assertEqual(evidence["binding"], "same_curve_label")
        self.assertFalse(evidence["capture_hash_bound"])
        self.assertEqual(
            evidence["project_axioms"],
            ["VerifiedLcalc.Assumptions.ellipticModularity"],
        )
        self.assertEqual(evidence["extent"], "complete_for_sample")

    def test_rank_consumer_distinguishes_realization_from_modularity_axiom(
        self,
    ) -> None:
        audited = read_json(DEFAULT_COVERAGE)
        rank = next(
            field
            for field in audited["fields"]
            if (field["table"], field["field"]) == ("ec_curvedata", "analytic_rank")
        )
        proofs = {item["curve"]: item for item in rank["evidence"]}
        conditional = proofs["37.a1"]
        assumption_backed = proofs["112.a2"]
        self.assertEqual(conditional["project_axioms"], [])
        self.assertIn("ArithmeticModularRealization", conditional["statement"])
        self.assertEqual(consumer_statuses([conditional]), {"conditional_fixture": 1})
        self.assertEqual(
            assumption_backed["project_axioms"],
            ["VerifiedLcalc.Assumptions.ellipticModularity"],
        )
        self.assertEqual(
            consumer_statuses([assumption_backed]), {"assumption_backed": 1}
        )
        self.assertEqual(
            consumer_statuses([conditional, assumption_backed]),
            {"conditional_fixture": 1, "assumption_backed": 1},
        )

    def test_partial_consumer_evidence_remains_partial(self) -> None:
        report = ledger()
        entry = next(
            field
            for field in report["fields"]
            if (field["table"], field["field"])
            == ("ec_mwbsd", "xcoord_integral_points")
        )
        evidence = next(
            item for item in entry["consumer"]["evidence"] if item["curve"] == "112.a2"
        )
        self.assertEqual(evidence["extent"], "partial")
        self.assertEqual(evidence["status"], "unconditional")

    def test_blocker_is_field_specific_and_points_to_its_contract_scope(self) -> None:
        report = ledger()
        entries = {
            (entry["table"], entry["field"]): entry for entry in report["fields"]
        }
        prime = entries[("ec_galrep", "prime")]
        self.assertEqual(prime["dispatch"]["status"], "galrep_field_not_dispatched")
        self.assertEqual(prime["blocker"]["layer"], "producer_dispatch")
        self.assertEqual(prime["blocker"]["detail"], prime["next_step"])
        self.assertIn("zero", prime["next_step"].lower())

        growth_field = entries[("ec_torsion_growth", "field")]
        self.assertIn("irreducible", growth_field["next_step"].lower())
        self.assertEqual(growth_field["blocker"]["detail"], growth_field["next_step"])

    def test_natural_row_keys_keep_prime_zero_class_and_extension_identity(
        self,
    ) -> None:
        report = ledger()
        entries = {
            (entry["table"], entry["field"]): entry for entry in report["fields"]
        }

        galrep = entries[("ec_galrep", "prime")]["native"]
        self.assertEqual([row["row_key"] for row in galrep["rows"]], [0, 2])
        self.assertEqual({row["row_key_name"] for row in galrep["rows"]}, {"prime"})

        local = entries[("ec_localdata", "conductor_valuation")]["native"]
        self.assertEqual([row["row_key"] for row in local["rows"]], [2, 7])
        self.assertEqual({row["row_key_name"] for row in local["rows"]}, {"prime"})

        class_row = entries[("ec_classdata", "anlist")]["native"]["rows"]
        class_native = entries[("ec_classdata", "anlist")]["native"]
        self.assertEqual(class_native["join_key"], "lmfdb_iso")
        self.assertEqual(class_native["join_value"], "112.a")
        self.assertEqual(class_row[0]["row_key"], "112.a")

        growth = entries[("ec_torsion_growth", "field")]["native"]
        self.assertEqual(len(growth["rows"]), 7)
        self.assertEqual(
            {natural_key_parts(row) for row in growth["rows"]},
            {("degree", "field")},
        )
        self.assertTrue(all(len(row["row_key"]) == 2 for row in growth["rows"]))
        self.assertEqual(len({json.dumps(row["row_key"]) for row in growth["rows"]}), 7)

        padic = entries[("ec_padic", "p")]["native"]
        self.assertEqual(padic["join_key"], "lmfdb_iso")
        self.assertEqual(padic["join_value"], "112.a")
        self.assertEqual({row["row_key_name"] for row in padic["rows"]}, {"p"})
        self.assertEqual(len({row["row_key"] for row in padic["rows"]}), 19)

    def test_empty_array_null_absent_field_and_absent_table_are_distinct(self) -> None:
        # Existing 112.a2 source contains a present empty list value.
        report = ledger()
        sha_primes = next(
            entry
            for entry in report["fields"]
            if (entry["table"], entry["field"]) == ("ec_curvedata", "sha_primes")
        )
        row = sha_primes["native"]["rows"][0]
        self.assertEqual(row["state"], "empty_array")
        self.assertEqual(row["value_json"], "[]")

        # Build a hash-consistent synthetic capture with a JSON null, a missing
        # field, and an absent table row; preserve each as a separate state.
        with self._synthetic_capture() as (source, manifest):
            synthetic_report = ledger(
                native_path=source,
                manifest_path=manifest,
            )
            fields = {
                (entry["table"], entry["field"]): entry
                for entry in synthetic_report["fields"]
            }
            self.assertEqual(
                fields[("ec_curvedata", "abc_quality")]["native"]["rows"][0]["state"],
                "json_null",
            )
            self.assertEqual(
                fields[("ec_curvedata", "absD")]["native"]["rows"][0]["state"],
                "field_absent",
            )
            self.assertEqual(
                fields[("ec_iwasawa", "iwdata")]["native"]["table_status"],
                "no_rows",
            )

    def test_mismatching_producer_receipt_is_rejected(self) -> None:
        manifest = read_json(MANIFEST)
        receipt = {
            "status": "checked",
            "input_provenance": producer_receipt_provenance(manifest),
            "input_sha256": "0" * 64,
            "fields": {},
        }
        with tempfile.TemporaryDirectory() as directory:
            producer = Path(directory) / "producer.json"
            producer.write_text(json.dumps(receipt))
            with self.assertRaises(ValueError):
                ledger(producer_path=producer)
            output = Path(directory) / "ledger.json"
            output.write_text("preserve rejected output")
            result = subprocess.run(
                [
                    sys.executable,
                    str(ROOT / "scripts/report_lmfdb_field_ledger.py"),
                    "--producer",
                    str(producer),
                    "--output",
                    str(output),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_text(), "preserve rejected output")

    def test_matching_source_provenance_cannot_substitute_for_replay_input_hash(
        self,
    ) -> None:
        manifest = read_json(MANIFEST)
        receipt = {
            "status": "checked",
            "input_provenance": producer_receipt_provenance(manifest),
            "input_sha256": "0" * 64,
            "fields": {},
        }
        self.assertEqual(
            receipt["input_provenance"]["source_sha256"],
            manifest["provenance"]["sha256"],
        )
        self.assertNotEqual(
            receipt["input_sha256"], replay_input_sha256(NATIVE, manifest)
        )
        with tempfile.TemporaryDirectory() as directory:
            producer = Path(directory) / "producer.json"
            producer.write_text(json.dumps(receipt))
            with self.assertRaises(ValueError):
                ledger(producer_path=producer)

    def test_valid_producer_status_does_not_overwrite_other_milestones(self) -> None:
        manifest = read_json(MANIFEST)
        receipt = {
            "status": "checked",
            "input_provenance": producer_receipt_provenance(manifest),
            "input_sha256": replay_input_sha256(NATIVE, manifest),
            "fields": {
                "local_invariants.2.conductor_valuation": {
                    "status": "partial",
                    "reason": "fixture test bound",
                    "sources": ["ec_localdata[2].conductor_valuation"],
                }
            },
        }
        with tempfile.TemporaryDirectory() as directory:
            producer = Path(directory) / "producer.json"
            producer.write_text(json.dumps(receipt))
            report = ledger(producer_path=producer)
        entry = next(
            field
            for field in report["fields"]
            if (field["table"], field["field"])
            == ("ec_localdata", "conductor_valuation")
        )
        self.assertEqual(entry["producer"]["status"], "partial_coverage")
        self.assertEqual(entry["producer"]["observations"][0]["row_key"], 2)
        self.assertEqual(entry["producer"]["observations"][0]["status"], "partial")
        self.assertEqual(entry["producer"]["observations"][1]["row_key"], 7)
        self.assertEqual(entry["producer"]["observations"][1]["status"], "not_reported")
        self.assertNotEqual(entry["consumer"]["status"], "partial")
        self.assertEqual(entry["publication"]["status"], "not_supplied")

    @contextmanager
    def _synthetic_capture(self) -> Generator[tuple[Path, Path], None, None]:
        script = ROOT / "scripts/capture_lmfdb_fixture.py"
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            source = read_json(NATIVE)
            curve_index = source["tables"].index("ec_curvedata")
            curve = source["data"][curve_index][0]
            curve["abc_quality"] = None
            curve.pop("absD")
            iwasawa_index = source["tables"].index("ec_iwasawa")
            source["data"][iwasawa_index] = []
            source["totals"][iwasawa_index] = 0
            raw_input = base / "raw.json"
            raw_input.write_text(json.dumps(source))
            raw = base / "native.json"
            manifest = base / "manifest.json"
            result = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "capture",
                    str(raw_input),
                    "--output",
                    str(raw),
                    "--manifest-output",
                    str(manifest),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            yield raw, manifest


if __name__ == "__main__":
    unittest.main()
