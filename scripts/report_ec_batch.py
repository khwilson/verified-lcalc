"""Render a dataset benchmark JSON report as Markdown."""

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any


def timing_row(label: str, rows: list[dict[str, Any]]) -> str:
    durations = sorted(
        row["validation_seconds"] for row in rows if "validation_seconds" in row
    )
    if not durations:
        return f"| {label} | 0 / {len(rows)} | — | — | — |"
    last = len(durations) - 1
    p50 = durations[round(last * 0.50)]
    p95 = durations[round(last * 0.95)]
    return (
        f"| {label} | {len(durations)} / {len(rows)} | {p50:.3f} s | "
        f"{p95:.3f} s | {durations[-1]:.3f} s |"
    )


def render(report: dict[str, Any]) -> str:
    identity = report["identity"]
    selected = identity["count"]
    offset = identity.get("offset", 0)
    rows = report["curves"]
    complete = report.get("complete", False)
    checked = [row for row in rows if row["status"] == "checked"]
    counts = Counter(row["status"] for row in rows)
    inconclusive = counts["inconclusive"]
    pending = selected - len(rows) + counts["proposed"]
    failures = selected - len(checked) - inconclusive - pending
    decided = selected - pending
    lines = [
        "# Elliptic curve certificate batch",
        "",
        f"Run {'complete' if complete else 'in progress or interrupted'}. "
        f"Selected {selected} input rows at offset {offset} (zero-based).",
        "",
        "| Outcome | Curves / selected |",
        "| --- | ---: |",
        f"| Passed kernel validation | {len(checked)} / {selected} |",
        f"| Inconclusive | {inconclusive} / {selected} |",
        f"| Failed | {failures} / {selected} |",
        f"| Pending | {pending} / {selected} |",
    ]
    if error := report.get("error"):
        detail = " ".join(str(error).split())
        if len(detail) > 300:
            detail = detail[:297] + "..."
        lines.extend(["", "Runner error", "", f"    {detail}"])
    if failures:
        details = ", ".join(
            f"`{status}` {count}"
            for status, count in sorted(counts.items())
            if status not in {"checked", "inconclusive", "proposed"}
        )
        lines.extend(["", f"Failure breakdown — {details}."])
    references = Counter(row.get("reference_matches") for row in checked)
    compared = references[True] + references[False]
    lines.extend(
        [
            "",
            f"Reference ranks compared for {compared} / {len(checked)} checked curves. "
            f"Disagreements — {references[False]} / {compared} compared.",
        ]
    )
    groups = report.get("compiled_reuse_groups", [])
    audited = sum(group["curves"] for group in groups if group["returncode"] == 0)
    audit = report.get("compiled_reuse")
    if audit is not None:
        audited = audit["curves"] if audit["returncode"] == 0 else audited
    if any(group["returncode"] != 0 for group in groups) or (
        audit is not None and audit["returncode"] != 0
    ):
        audit_status = "failed"
    elif audit is not None and audited == len(checked) and audited:
        audit_status = "passed"
    elif audited:
        audit_status = "partial"
    else:
        audit_status = "no recorded imports"
    lines.extend(
        [
            f"Compiled proof import audit — {audit_status}. "
            f"{audited} / {len(checked)} checked curves imported successfully.",
            "",
            "## Timing",
            "",
        ]
    )
    wall = report.get("wall_seconds")
    checkpoint = "" if complete else " through last checkpoint"
    if wall is None:
        lines.append("Runner wall time and throughput are unavailable in this report.")
    elif report.get("invocation_count", 1) > 1:
        lines.extend(
            [
                f"Latest runner invocation wall time{checkpoint} — {wall:.3f} s.",
                "Throughput is unavailable because the outcome counts span multiple invocations.",
            ]
        )
    else:
        lines.append(f"Runner wall time (all phases){checkpoint} — {wall:.3f} s.")
        if wall > 0:
            lines.extend(
                [
                    f"Throughput — {decided / wall:.3f} curves with a recorded outcome/s "
                    f"({decided} / {selected} selected).",
                    f"Checked throughput — {len(checked) / wall:.3f} curves/s "
                    f"({len(checked)} / {selected} selected).",
                ]
            )
    generation = report.get("generation", {}).get("wall_seconds")
    if generation is not None:
        reused = " (prior invocation)" if report.get("generation_reuse") else ""
        lines.append(f"Witness generation wall time{reused} — {generation:.3f} s.")
    phase_times = [
        phase["wall_seconds"]
        for phase in report.get("validation_phases", [])
        if "wall_seconds" in phase
    ]
    validation = (
        sum(phase_times)
        if phase_times
        else report.get("summary", {}).get("validation_phase_wall_seconds")
    )
    if validation is not None:
        lines.append(f"Validation phase wall time — {validation:.3f} s.")
    import_wall = audit.get("wall_seconds") if audit is not None else None
    if import_wall is None:
        group_times = [
            group["wall_seconds"] for group in groups if "wall_seconds" in group
        ]
        import_wall = sum(group_times) if group_times else None
    if import_wall is not None:
        lines.append(f"Post-validation import wall time — {import_wall:.3f} s.")
    lines.extend(
        [
            "",
            "| Lean certificate command | Timed / checked | p50 | p95 | Max |",
            "| --- | ---: | ---: | ---: | ---: |",
            timing_row("All checked curves", checked),
        ]
    )
    for rank in (0, 1):
        rank_rows = [row for row in checked if row.get("rank") in (rank, str(rank))]
        lines.append(timing_row(f"Checked rank {rank}", rank_rows))
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report_path", type=Path)
    args = parser.parse_args()
    try:
        report = json.loads(args.report_path.read_text(encoding="utf-8"))
        output = render(report)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(
            f"{args.report_path}: cannot summarize benchmark report: {error}",
            file=sys.stderr,
        )
        return 1
    print(output, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
