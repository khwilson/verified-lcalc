"""Check the slice plan used by the hosted certificate benchmark."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.plan_ec_batch_chain import next_batch_offset


def test_inclusive_limit_and_single_dispatch() -> None:
    assert next_batch_offset(77, 3, 0) is None
    assert next_batch_offset(1000, 0, 10) == 1000
    assert next_batch_offset(1000, 8000, 10) == 9000
    assert next_batch_offset(1000, 9000, 10) is None
    assert next_batch_offset(1000, 3000, 4) is None


@pytest.mark.parametrize(
    ("count", "offset", "through_batch"),
    [
        (999, 0, 10),
        (1000, 1, 10),
        (1000, -1000, 10),
        (1000, 10000, 10),
        (1000, 9000, 9),
        (1000, 0, 11),
        (1000, 0, -1),
    ],
)
def test_reject_invalid_chain(count: int, offset: int, through_batch: int) -> None:
    with pytest.raises(ValueError):
        next_batch_offset(count, offset, through_batch)
