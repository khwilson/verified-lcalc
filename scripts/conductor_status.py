#!/usr/bin/env python3
"""Read-only status and aggregate timings for a conductor benchmark."""

import argparse
import csv
import io
import json
import statistics
from collections import Counter
from pathlib import Path
from typing import Any

JsonObject = dict[str, Any]


def summarize(report: JsonObject) -> JsonObject:
    done = [c for c in report["conductors"] if c["status"] == "checked"]
    cases = [r for c in done for r in c["cases"]]
    cold = [c["kernel_build_seconds"] for c in done if not c["prior_artifact_exists"]]
    return dict(
        complete=report["complete"],
        selected_conductors=len(report["selected_conductors"]),
        selected_curves=report["selected_curve_count"],
        checked_conductors=len(done),
        checked_curves=len(cases),
        certified_ranks=dict(
            Counter(
                str(c["certified_rank"])
                for c in cases
                if c["certified_rank"] is not None
            )
        ),
        verified_count=sum(c["certified_rank"] is not None for c in cases),
        inconclusive_count=sum(c["certified_rank"] is None for c in cases),
        inconclusive_reasons=dict(
            Counter(c["status"] for c in cases if c["certified_rank"] is None)
        ),
        reference_mismatches=sum(c["reference_mismatches"] for c in done),
        audited_components=sum(c["audited_component_count"] for c in done),
        pending_revalidation=len(report.get("pending_checked_conductors", [])),
        active=[
            {k: c[k] for k in ["conductor", "status", "error"] if k in c}
            for c in report["conductors"]
            if c["status"] != "checked"
        ],
        kernel_build_seconds=sum(c["kernel_build_seconds"] for c in done),
        producer_seconds=sum(c["producer_seconds"] for c in done),
        warm_validation_seconds=sum(c.get("warm_validation_seconds", 0) for c in done),
        resume_validation_seconds=sum(
            sum(c.get("resume_validation_seconds", [])) for c in done
        ),
        cold_kernel_median_seconds=statistics.median(cold) if cold else None,
        cold_kernel_max_seconds=max(cold) if cold else None,
        latest_session_elapsed_seconds=report.get("session_elapsed_seconds"),
        conditional_axiom=report["conditional_axiom"],
    )


def write_summary(path: Path, report: JsonObject) -> None:
    summary = summarize(report)
    path.with_name("summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    state = "Complete" if summary["complete"] else "In progress"
    text = f"""# SQL conductor benchmark: {state}

Checked {summary["checked_curves"]} of {summary["selected_curves"]} curves in
{summary["checked_conductors"]} of {summary["selected_conductors"]} conductors.

- Conditional exact-rank certificates: {summary["verified_count"]}
- Inconclusive curves processed: {summary["inconclusive_count"]}
- Reference mismatches: {summary["reference_mismatches"]}
- Named concrete components audited: {summary["audited_components"]}
- Sum of recorded kernel build times: {summary["kernel_build_seconds"]:.3f} seconds
- Sum of candidate production times: {summary["producer_seconds"]:.3f} seconds
- Sum of warm validation times: {summary["warm_validation_seconds"]:.3f} seconds
- Sum of resume validation times: {summary["resume_validation_seconds"]:.3f} seconds

Every analytic rank claim is conditional on `{summary["conditional_axiom"]}`.
An inconclusive result is not an exact-rank certificate. Warm validation reuses
checked artifacts; it is not a fresh kernel replay. These stage sums describe
completed conductors and are not the full campaign wall time. `report.json`
records the current session wall time and per-conductor data.
"""
    if summary["active"]:
        text += "\nActive/failure status: `" + json.dumps(summary["active"]) + "`\n"
    path.with_name("TIMINGS.md").write_text(text)
    fields = [
        "conductor",
        "status",
        "certificate_validation_version",
        "prior_artifact_exists",
        "verified_count",
        "inconclusive_count",
        "audited_component_count",
        "reference_mismatches",
        "producer_seconds",
        "kernel_build_seconds",
        "warm_validation_seconds",
        "elapsed_seconds",
    ]
    output = io.StringIO()
    writer = csv.DictWriter(output, fieldnames=fields, extrasaction="ignore")
    writer.writeheader()
    for c in report["conductors"]:
        writer.writerow(c)
    path.with_name("timings.csv").write_text(output.getvalue())


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("report", type=Path)
    args = p.parse_args()
    print(
        json.dumps(
            summarize(json.loads(args.report.read_text())), indent=2, sort_keys=True
        )
    )


if __name__ == "__main__":
    main()
