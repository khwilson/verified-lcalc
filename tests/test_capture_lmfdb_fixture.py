"""Offline contract tests for native LMFDB capture projection."""

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.capture_lmfdb_fixture as capture_module  # noqa: E402
from scripts.capture_lmfdb_fixture import replay_capture
from scripts.produce_ec_witness import build_input

ROOT = Path(__file__).resolve().parents[1]
NATIVE = ROOT / "tests/fixtures/lmfdb/112.a2-native.json"
MANIFEST = ROOT / "tests/fixtures/lmfdb/112.a2-native.provenance.json"
JOINED = ROOT / "tests/fixtures/lmfdb/112.a2-joined.json"
TABLES = {
    "ec_curvedata",
    "ec_classdata",
    "ec_localdata",
    "ec_mwbsd",
    "ec_galrep",
    "ec_torsion_growth",
    "ec_iwasawa",
    "ec_padic",
}


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


class NativeCaptureReplay(unittest.TestCase):
    def test_112a2_projection_matches_existing_joined_witness(self) -> None:
        projected = replay_capture(read_json(NATIVE), read_json(MANIFEST))
        actual, _, actual_sources = build_input(projected)
        expected, _, expected_sources = build_input(read_json(JOINED))
        for field, value in expected.items():
            self.assertEqual(actual[field], value, field)
            if field in expected_sources:
                self.assertEqual(actual_sources[field], expected_sources[field], field)
        self.assertEqual(
            projected["provenance"]["source_sha256"],
            read_json(MANIFEST)["provenance"]["sha256"],
        )

    def test_capture_has_provenance_and_explicit_eight_table_status(self) -> None:
        capture = read_json(NATIVE)
        manifest = read_json(MANIFEST)
        self.assertEqual(manifest["format"], "verified-lcalc-lmfdb-native-v1")
        self.assertEqual(manifest["label"], "112.a2")
        provenance = manifest["provenance"]
        self.assertRegex(provenance["sha256"], r"^[0-9a-f]{64}$")
        self.assertEqual(
            hashlib.sha256(NATIVE.read_bytes()).hexdigest(), provenance["sha256"]
        )
        self.assertEqual(provenance["license"], "CC BY-SA")
        self.assertTrue(provenance.get("source"))
        self.assertTrue(
            provenance.get("captured_at") or provenance.get("source_revision")
        )

        tables = manifest["tables"]
        self.assertEqual({table["name"] for table in tables}, TABLES)
        self.assertEqual(len(tables), len(TABLES))
        for table in tables:
            self.assertIn(table["status"], {"present", "absent", "not_captured"})
            self.assertTrue(table["join_key"])
            self.assertIsInstance(table["row_keys"], list)
            self.assertEqual(table["status"] == "present", bool(table["row_keys"]))
        for _name, label, key, rows in zip(
            capture["tables"],
            capture["labels"],
            capture["label_cols"],
            capture["data"],
            strict=True,
        ):
            for row in rows:
                self.assertEqual(row[key], label)

    def test_projection_preserves_native_json_encodings(self) -> None:
        capture = read_json(NATIVE)
        projected = replay_capture(capture, read_json(MANIFEST))
        original = read_json(NATIVE)
        original_rows = {
            name: rows
            for name, rows in zip(original["tables"], original["data"], strict=True)
        }
        projected_rows = {
            name: rows
            for name, rows in zip(projected["tables"], projected["data"], strict=True)
        }
        # Compare serialized JSON so integer/decimal and nested encodings stay exact.
        for table, rows in original_rows.items():
            self.assertEqual(
                json.dumps(
                    projected_rows[table], sort_keys=True, separators=(",", ":")
                ),
                json.dumps(rows, sort_keys=True, separators=(",", ":")),
            )
        # Exercise representative exact encodings without parsing them numerically.
        curve = original_rows["ec_curvedata"][0]
        self.assertEqual(curve["jinv"], [-4, 7])
        mw = original_rows["ec_mwbsd"][0]
        self.assertEqual(projected_rows["ec_mwbsd"][0]["gens"], mw["gens"])
        self.assertEqual(
            projected_rows["ec_mwbsd"][0]["torsion_generators"],
            mw["torsion_generators"],
        )

    def test_absent_and_present_empty_are_distinct_in_projection(self) -> None:
        capture = copy.deepcopy(read_json(NATIVE))
        manifest = copy.deepcopy(read_json(MANIFEST))
        # `sha_primes` is present as an empty list on a captured curve row.
        curve = capture["data"][capture["tables"].index("ec_curvedata")][0]
        self.assertEqual(curve["sha_primes"], [])

        # A captured table with no rows is explicitly absent; it differs from a
        # present row whose list-valued field is empty.
        absent = next(
            table for table in manifest["tables"] if table["name"] == "ec_iwasawa"
        )
        index = capture["tables"].index("ec_iwasawa")
        capture["data"][index] = []
        capture["totals"][index] = 0
        absent.update(status="absent", row_keys=[])
        projected = replay_capture(capture, manifest)
        statuses = {
            table["name"]: table["status"]
            for table in projected["provenance"]["table_capture_manifest"]
        }
        self.assertEqual(statuses["ec_curvedata"], "present")
        self.assertEqual(statuses["ec_iwasawa"], "absent")
        projected_curve = projected["data"][projected["tables"].index("ec_curvedata")][
            0
        ]
        self.assertEqual(projected_curve["sha_primes"], [])

    def test_offline_replay_cli_checks_digest_before_writing(self) -> None:
        script = ROOT / "scripts/capture_lmfdb_fixture.py"
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "projection.json"
            command = [
                sys.executable,
                str(script),
                "replay",
                str(NATIVE),
                "--manifest",
                str(MANIFEST),
                "--output",
                str(output),
            ]
            result = subprocess.run(
                command, cwd=ROOT, capture_output=True, text=True, check=False
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            replayed = json.loads(output.read_text())
            source = read_json(NATIVE)
            for key in ("tables", "labels", "label_cols", "totals", "data"):
                self.assertEqual(replayed[key], source[key], key)
            self.assertEqual(
                replayed["provenance"]["source_sha256"],
                read_json(MANIFEST)["provenance"]["sha256"],
            )

            bad_manifest = Path(directory) / "bad-manifest.json"
            bad = read_json(MANIFEST)
            bad["provenance"]["sha256"] = "0" * 64
            bad_manifest.write_text(json.dumps(bad))
            output.write_text("preserve on rejection")
            rejected = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "replay",
                    str(NATIVE),
                    "--manifest",
                    str(bad_manifest),
                    "--output",
                    str(output),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(output.read_text(), "preserve on rejection")

            exact_decimal = b"1.23456789012345678901234567890123456789"
            altered_raw = Path(directory) / "exact-decimal-source.json"
            original_bytes = NATIVE.read_bytes()
            altered_bytes = original_bytes.replace(
                b"1.0348177494302118", exact_decimal, 1
            )
            self.assertNotEqual(altered_bytes, original_bytes)
            altered_raw.write_bytes(altered_bytes)
            captured_raw = Path(directory) / "exact-decimal-capture.json"
            captured_manifest = Path(directory) / "exact-decimal-manifest.json"
            capture = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "capture",
                    str(altered_raw),
                    "--output",
                    str(captured_raw),
                    "--manifest-output",
                    str(captured_manifest),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(capture.returncode, 0, capture.stderr)
            decimal_output = Path(directory) / "exact-decimal-projection.json"
            replay = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "replay",
                    str(captured_raw),
                    "--manifest",
                    str(captured_manifest),
                    "--output",
                    str(decimal_output),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(replay.returncode, 0, replay.stderr)
            self.assertIn(exact_decimal, decimal_output.read_bytes())

    def test_capture_does_not_clobber_existing_pair_and_pair_remains_replayable(
        self,
    ) -> None:
        script = ROOT / "scripts/capture_lmfdb_fixture.py"
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            raw_output = base / "captured.json"
            manifest_output = base / "captured.provenance.json"
            raw_output.write_bytes(NATIVE.read_bytes())
            manifest_output.write_bytes(MANIFEST.read_bytes())
            before_raw = raw_output.read_bytes()
            before_manifest = manifest_output.read_bytes()

            capture = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "capture",
                    str(NATIVE),
                    "--output",
                    str(raw_output),
                    "--manifest-output",
                    str(manifest_output),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertNotEqual(capture.returncode, 0)
            self.assertEqual(raw_output.read_bytes(), before_raw)
            self.assertEqual(manifest_output.read_bytes(), before_manifest)

            replay_output = base / "replayed.json"
            replay = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "replay",
                    str(raw_output),
                    "--manifest",
                    str(manifest_output),
                    "--output",
                    str(replay_output),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(replay.returncode, 0, replay.stderr)
            self.assertTrue(replay_output.is_file())

    def test_second_capture_destination_failure_leaves_no_partial_pair(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            raw_output = base / "new-capture.json"
            manifest_output = base / "new-manifest.json"
            real_link = capture_module.os.link
            link_count = 0

            def fail_second_link(source: Path, destination: Path) -> None:
                nonlocal link_count
                link_count += 1
                if link_count == 2:
                    raise OSError("simulated second destination failure")
                real_link(source, destination)

            with patch.object(capture_module.os, "link", side_effect=fail_second_link):
                with self.assertRaisesRegex(OSError, "second destination"):
                    capture_module._install_pair_no_clobber(
                        (
                            (raw_output, NATIVE.read_bytes()),
                            (manifest_output, MANIFEST.read_bytes()),
                        )
                    )
            self.assertEqual(link_count, 2)
            self.assertFalse(raw_output.exists())
            self.assertFalse(manifest_output.exists())
            self.assertEqual(list(base.glob(".*.stage")), [])

            replay_output = base / "source-remains-usable.json"
            script = ROOT / "scripts/capture_lmfdb_fixture.py"
            replay = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "replay",
                    str(NATIVE),
                    "--manifest",
                    str(MANIFEST),
                    "--output",
                    str(replay_output),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(replay.returncode, 0, replay.stderr)
            self.assertTrue(replay_output.is_file())

    def test_replay_replace_failure_preserves_existing_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "existing-replay.json"
            output.write_bytes(b"keep previous replay")
            original = output.read_bytes()

            def fail_replace(source: Path, destination: Path) -> None:
                raise OSError("simulated replay replace failure")

            with patch.object(capture_module.os, "replace", side_effect=fail_replace):
                with self.assertRaisesRegex(OSError, "replay replace"):
                    capture_module._atomic_replace(output, b"new replay")
            self.assertEqual(output.read_bytes(), original)
            self.assertEqual(list(Path(directory).glob(".*.stage")), [])

    def test_replay_output_write_failure_preserves_source_pair(self) -> None:
        script = ROOT / "scripts/capture_lmfdb_fixture.py"
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            blocked_parent = base / "output-parent"
            blocked_parent.write_text("not a directory")
            output = blocked_parent / "replay.json"
            before_raw = NATIVE.read_bytes()
            before_manifest = MANIFEST.read_bytes()
            replay = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "replay",
                    str(NATIVE),
                    "--manifest",
                    str(MANIFEST),
                    "--output",
                    str(output),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertNotEqual(replay.returncode, 0)
            self.assertEqual(NATIVE.read_bytes(), before_raw)
            self.assertEqual(MANIFEST.read_bytes(), before_manifest)

            usable_output = base / "usable-replay.json"
            retry = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "replay",
                    str(NATIVE),
                    "--manifest",
                    str(MANIFEST),
                    "--output",
                    str(usable_output),
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(retry.returncode, 0, retry.stderr)
            self.assertTrue(usable_output.is_file())

    def test_rejects_wrong_label_and_conflicting_duplicate_rows(self) -> None:
        capture = read_json(NATIVE)
        manifest = read_json(MANIFEST)
        for table_name in ("ec_curvedata", "ec_localdata"):
            with self.subTest(table=table_name):
                corrupted = copy.deepcopy(capture)
                bad_manifest = copy.deepcopy(manifest)
                rows = corrupted["data"][corrupted["tables"].index(table_name)]
                if table_name == "ec_curvedata":
                    rows[0]["lmfdb_label"] = "112.a1"
                else:
                    rows[1]["prime"] = 2
                    local_index = next(
                        i
                        for i, entry in enumerate(bad_manifest["tables"])
                        if entry["name"] == "ec_localdata"
                    )
                    bad_manifest["tables"][local_index]["row_keys"] = [2, 2]
                with self.assertRaises((ValueError, KeyError)):
                    replay_capture(corrupted, bad_manifest)


if __name__ == "__main__":
    unittest.main()
