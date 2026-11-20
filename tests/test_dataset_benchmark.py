import json
import sys
from pathlib import Path
from typing import Any

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.benchmark_ec_dataset import (
    numerical_batches,
    reference_ranks,
    selected_inputs,
)


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
