import json
import os
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
        source.write_text(json.dumps({key: [{**row, "analytic_rank": 999}]}))
        assert selected_inputs(source, 1) == [row]
        with pytest.raises(ValueError):
            selected_inputs(source, 2)
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
    for mutate in ["subject", "rank", "environment", "incomplete"]:
        bad = copy.deepcopy(previous)
        if mutate == "subject":
            bad_inputs = [{**inputs[0], "conductor": 43}]
        else:
            bad_inputs = inputs
        if mutate == "rank":
            bad["curves"][0]["rank"] = "0"
        elif mutate == "environment":
            bad["identity"]["producer_sha256"] = "different"
        elif mutate == "incomplete":
            bad["generation_complete"] = False
        with pytest.raises(ValueError):
            adopt_generation(bad, identity, bad_inputs, work)
