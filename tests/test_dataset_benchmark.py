import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.benchmark_ec_dataset import (
    adopt_generation,
    numerical_batches,
    reference_ranks,
    selected_inputs,
)


@pytest.mark.parametrize("source_entry", ["../math lib", ".lake/packages/mathlib"])
def test_mathlib_provenance_uses_resolved_checkout(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    source_entry: str,
) -> None:
    import scripts.benchmark_certify_ec as benchmark

    root = tmp_path / "project"
    root.mkdir()
    checkout = (root / source_entry).resolve()
    checkout.mkdir(parents=True)
    (checkout / "Mathlib.lean").touch()
    monkeypatch.setattr(benchmark, "ROOT", root)

    def capture(args: list[str]) -> str:
        if args == [*benchmark.LAKE, "env", "printenv", "LEAN_SRC_PATH"]:
            return os.pathsep.join(["examples", source_entry, source_entry])
        assert args == [
            "git",
            "-C",
            str(checkout),
            "rev-parse",
            "--show-toplevel",
            "HEAD",
        ]
        return f"{checkout}\n{'a' * 40}"

    monkeypatch.setattr(benchmark, "captured", capture)
    assert benchmark.mathlib_revision() == "a" * 40


def test_sql_and_legacy_inputs_do_not_expose_reference_ranks(tmp_path: Path) -> None:
    row = {"label": "37.a1", "ainvs": [0, 0, 1, -1, 0], "conductor": 37}
    for key in ["inputs", "cases"]:
        source = tmp_path / f"{key}.json"
        second = {**row, "label": "37.b1"}
        source.write_text(
            json.dumps(
                {key: [{**row, "analytic_rank": 999}, {**second, "analytic_rank": 0}]}
            )
        )
        assert selected_inputs(source, 1) == [row]
        assert selected_inputs(source, 1, offset=1) == [second]
        with pytest.raises(ValueError):
            selected_inputs(source, 2, offset=1)
        with pytest.raises(ValueError):
            selected_inputs(source, 1, offset=-1)
    duplicate = tmp_path / "duplicates.json"
    duplicate.write_text(json.dumps({"inputs": [row, row]}))
    with pytest.raises(ValueError):
        selected_inputs(duplicate, 2)


def test_separate_references_match_labels_not_positions(tmp_path: Path) -> None:
    source = tmp_path / "inputs.json"
    source.write_text('{"inputs": []}')
    references = tmp_path / "references.json"
    rows = [
        {"label": "43.a1", "analytic_rank": 1},
        {"label": "37.a1", "analytic_rank": 0},
        {"label": "389.a1", "analytic_rank": None},
    ]
    references.write_text(json.dumps({"references": rows}))
    assert reference_ranks(source, references) == {
        "37.a1": 0,
        "43.a1": 1,
        "389.a1": None,
    }
    references.write_text(json.dumps({"references": rows + rows}))
    with pytest.raises(ValueError):
        reference_ranks(source, references)


def test_work_bounded_batches_keep_every_candidate_in_order() -> None:
    def row(index: int, terms: int, steps: int, cutoff: int) -> dict[str, Any]:
        return {
            "index": index,
            "reference_rank": 999,
            "parameters": {
                "terms": str(terms),
                "steps_per_unit": str(steps),
                "cutoff": str(cutoff),
            },
        }

    rows = [row(0, 4, 0, 0), row(1, 4, 0, 0), row(2, 128, 8, 32), row(3, 4, 0, 0)]
    batches = numerical_batches(rows, 20, 4000)
    assert [[r["index"] for r in batch] for batch in batches] == [[0, 1], [2], [3]]
    assert [r for batch in batches for r in batch] == rows
    assert [len(b) for b in numerical_batches(rows, 2, 0)] == [2, 2]


def test_generation_reuse_checks_subjects_and_discards_old_proof_status(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import copy
    import hashlib

    import scripts.benchmark_ec_dataset as benchmark

    monkeypatch.setattr(benchmark, "ROOT", tmp_path)
    old = tmp_path / ".lake" / "old"
    (old / "witnesses").mkdir(parents=True)
    work = tmp_path / ".lake" / "new"
    work.mkdir()
    identity: dict[str, Any] = {
        key: "same"
        for key in [
            "source_sha256",
            "references_sha256",
            "mathlib_revision",
            "actual_lean_version",
            "count",
            "producer_sha256",
            "toolchain",
            "production_sha256",
        ]
    }
    identity["production_sha256"] = {
        "VerifiedLcalc/Numerics/Core.lean": "same",
        "VerifiedLcalc/Tactic/CertifyEC.lean": "before",
    }
    subject = {"ainvs": ["0", "0", "1", "-1", "0"], "conductor": "37"}
    parameters = {"terms": "24", "steps_per_unit": "1", "cutoff": "8"}
    witness = {"subject": subject, "rank": "1", "parameters": parameters}
    file = old / "witnesses" / "0.json"
    file.write_text(json.dumps(witness))
    row: dict[str, Any] = {
        "index": 0,
        "label": "37.a1",
        "conductor": 37,
        "status": "checked",
        "file": "0.json",
        "rank": "1",
        "parameters": parameters,
        "witness_sha256": hashlib.sha256(file.read_bytes()).hexdigest(),
        "validation_seconds": 999,
        "module": "OldBatch",
    }
    previous: dict[str, Any] = {
        "identity": identity,
        "generation_complete": True,
        "curves": [row],
        "work_directory": ".lake/old",
    }
    inputs = [{"label": "37.a1", "ainvs": [0, 0, 1, -1, 0], "conductor": 37}]
    result = adopt_generation(previous, identity, inputs, work)
    assert result[0]["status"] == "proposed"
    assert "validation_seconds" not in result[0] and "module" not in result[0]
    assert (work / "witnesses" / "0.json").read_bytes() == file.read_bytes()
    for mutate in ["subject", "rank", "environment", "offset", "incomplete"]:
        bad = copy.deepcopy(previous)
        if mutate == "subject":
            bad_inputs = [{**inputs[0], "conductor": 43}]
        else:
            bad_inputs = inputs
        if mutate == "rank":
            bad["curves"][0]["rank"] = "0"
        elif mutate == "environment":
            bad["identity"]["producer_sha256"] = "different"
        elif mutate == "offset":
            bad["identity"]["offset"] = 1
        elif mutate == "incomplete":
            bad["generation_complete"] = False
        with pytest.raises(ValueError):
            adopt_generation(bad, identity, bad_inputs, work)


@pytest.mark.parametrize(
    ("failure", "expected_outcomes"),
    [
        (None, {"checked": 1, "inconclusive": 1}),
        ("build", {}),
        ("generation", {"inconclusive": 1}),
        ("timeout", {"timeout": 1, "inconclusive": 1}),
        ("missing", {"batch_failed": 1, "inconclusive": 1}),
        ("mismatch", {"checked": 1, "inconclusive": 1}),
    ],
)
def test_dataset_report_checkpoints_and_exit_status(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    failure: str | None,
    expected_outcomes: dict[str, int],
) -> None:
    import scripts.benchmark_ec_dataset as benchmark

    monkeypatch.setattr(benchmark, "ROOT", tmp_path)
    monkeypatch.setattr(benchmark, "mathlib_revision", lambda: "mathlib")
    monkeypatch.setattr(benchmark.platform, "platform", lambda: "test")
    monkeypatch.setattr(benchmark, "captured", lambda _args: "version")
    (tmp_path / "lean-toolchain").touch()
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "benchmarks/ProduceECWitnesses.lean").touch()
    (tmp_path / "benchmarks/ValidateEC.lean").touch()
    source = tmp_path / "curves.json"
    curves = [
        {
            "label": label,
            "conductor": 37,
            "ainvs": [0, 0, 1, -1, 0],
            "analytic_rank": 0 if failure == "mismatch" else 1,
        }
        for label in ["37.a1", "37.a2", "37.a3"]
    ]
    source.write_text(json.dumps({"cases": curves}))
    out = tmp_path / "report.json"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "benchmark",
            "--source",
            str(source),
            "--output",
            str(out),
            "--count",
            "2",
            "--offset",
            "1",
        ],
    )

    def prebuild(_args: list[str], **_kwargs: Any) -> None:
        if failure == "build":
            raise subprocess.CalledProcessError(1, "lake")

    def timed(
        _args: list[str], _cwd: Path, _env: dict[str, str], log: Path, _timeout: int
    ) -> dict[str, Any]:
        status = "finished"
        returncode: int | None = 0
        if log.name == "generation.jsonl":
            inputs = json.loads((log.parent / "inputs.json").read_text())["inputs"]
            assert inputs == [
                {key: row[key] for key in ["label", "conductor", "ainvs"]}
                for row in curves[1:]
            ]
            rows: list[dict[str, Any]] = [
                {"index": 0, "label": "37.a2", "status": "inconclusive"},
            ]
            if failure == "generation":
                status, returncode = "timeout", None
            else:
                (log.parent / "witnesses").mkdir()
                (log.parent / "witnesses/1.json").write_text(
                    json.dumps(
                        {
                            "schema": "lcalc.ec-rank.v1",
                            "rank": "1",
                            "subject": {"conductor": "37"},
                            "arithmetic": {"minimality": ["37"]},
                            "coefficients": ["1", "-2"],
                        }
                    )
                )
                rows.append(
                    {
                        "index": 1,
                        "label": "37.a3",
                        "status": "proposed",
                        "rank": "1",
                        "file": "1.json",
                        "parameters": {
                            "terms": "24",
                            "steps_per_unit": "1",
                            "cutoff": "8",
                        },
                    }
                )
            log.write_text(
                "".join(
                    json.dumps({"result": row, "generation_ns": 1}) + "\n"
                    for row in rows
                )
            )
        elif log.name == "Batch0000.log":
            if failure == "timeout":
                status, returncode = "timeout", None
            event = {
                "label": "37.a3",
                "status": "checked",
                "validation_ns": 1,
                "error": "",
            }
            log.write_text(
                "" if failure == "missing" else "EC_BENCH " + json.dumps(event) + "\n"
            )
            log.with_suffix(".olean").touch()
        return {
            "status": status,
            "returncode": returncode,
            "wall_seconds": 1,
            "cpu_seconds": 1,
        }

    monkeypatch.setattr(benchmark.subprocess, "run", prebuild)
    monkeypatch.setattr(benchmark, "timed", timed)
    if failure is None:
        benchmark.main()
    else:
        with pytest.raises((subprocess.CalledProcessError, RuntimeError)):
            benchmark.main()
    report = json.loads(out.read_text())
    assert report["complete"] is (failure is None)
    assert ("error" in report) is (failure is not None)
    assert report["identity"]["offset"] == report["offset"] == 1
    assert report["wall_seconds"] > 0
    assert report["invocation_count"] == 1
    assert [row["label"] for row in report["curves"]] == {
        "build": [],
        "generation": ["37.a2"],
    }.get(failure or "", ["37.a2", "37.a3"])
    if "summary" in report:
        assert report["summary"]["outcomes"] == expected_outcomes
        assert report["summary"]["reference_agreements"] == int(failure is None)
        assert report["summary"]["reference_mismatches"] == int(failure == "mismatch")
    if failure is None:
        monkeypatch.setattr(sys, "argv", [*sys.argv[:-1], "0", "--resume"])
        with pytest.raises(SystemExit, match="2"):
            benchmark.main()
        assert json.loads(out.read_text()) == report
