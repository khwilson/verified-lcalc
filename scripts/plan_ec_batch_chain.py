"""Validate the Actions inputs for a chain over the tracked 10,000-curve snapshot."""

import os
import re

BATCH_SIZE = 1000
BATCH_COUNT = 10


def next_batch_offset(count: int, offset: int, through_batch: int) -> int | None:
    """Return the next offset for an inclusive, one-based batch limit."""
    if through_batch == 0:
        return None
    if count != BATCH_SIZE or offset % BATCH_SIZE:
        raise ValueError("A chain requires count 1000 and an offset divisible by 1000.")
    current_batch = offset // BATCH_SIZE + 1
    if not 1 <= current_batch <= through_batch <= BATCH_COUNT:
        raise ValueError("A chain requires 1 <= current batch <= through_batch <= 10.")
    return offset + BATCH_SIZE if current_batch < through_batch else None


def main() -> None:
    if (
        os.environ["GITHUB_REPOSITORY"] != "khwilson/verified-lcalc"
        or os.environ["GITHUB_REF"] != "refs/heads/main"
    ):
        raise SystemExit("Batch chains must run on khwilson/verified-lcalc main.")
    try:
        through_batch = int(os.environ["THROUGH_BATCH"])
        parent_run = os.environ["PARENT_RUN"]
        if parent_run and (
            through_batch == 0
            or not re.fullmatch(r"[1-9][0-9]*/attempts/[1-9][0-9]*", parent_run)
        ):
            raise ValueError(
                "A parent run must identify the preceding chain run and attempt."
            )
        next_offset = next_batch_offset(
            int(os.environ["COUNT"]), int(os.environ["OFFSET"]), through_batch
        )
    except ValueError as error:
        raise SystemExit(str(error)) from error

    if parent_run:
        server = os.environ["GITHUB_SERVER_URL"]
        repo = os.environ["GITHUB_REPOSITORY"]
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as summary:
            summary.write(
                f"Continued from [run {parent_run}]({server}/{repo}/actions/runs/{parent_run}).\n"
            )
    if next_offset is not None:
        with open(os.environ["GITHUB_OUTPUT"], "a") as output:
            output.write(f"next-offset={next_offset}\n")


if __name__ == "__main__":
    main()
