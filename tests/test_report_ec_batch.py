import json
import subprocess
import sys
from pathlib import Path
from typing import Any

SCRIPT = Path(__file__).resolve().parents[1] / "scripts/report_ec_batch.py"


def run_report(
    path: Path, report: dict[str, Any] | None = None
) -> subprocess.CompletedProcess[str]:
    if report is not None:
        path.write_text(json.dumps(report), encoding="utf-8")
    return subprocess.run(
        [sys.executable, str(SCRIPT), str(path)],
        capture_output=True,
        text=True,
        check=False,
    )


def test_complete_report_uses_runner_wall_and_checked_command_timings(
    tmp_path: Path,
) -> None:
    result = run_report(
        tmp_path / "report.json",
        {
            "complete": True,
            "identity": {"count": 5, "offset": 10},
            "wall_seconds": 20,
            "generation": {"wall_seconds": 5},
            "summary": {"validation_phase_wall_seconds": 9},
            "curves": [
                {
                    "status": "checked",
                    "rank": "0",
                    "validation_seconds": 1,
                    "reference_matches": True,
                },
                {
                    "status": "checked",
                    "rank": "1",
                    "validation_seconds": 4,
                    "reference_matches": False,
                },
                {"status": "checked", "rank": "1", "validation_seconds": 8},
                {"status": "inconclusive"},
                {"status": "rejected", "validation_seconds": 100},
            ],
            "compiled_reuse": {"returncode": 0, "curves": 3, "wall_seconds": 2},
        },
    )
    assert result.returncode == 0, result.stderr
    assert "Selected 5 input rows at offset 10" in result.stdout
    assert "| Passed kernel validation | 3 / 5 |" in result.stdout
    assert "| Inconclusive | 1 / 5 |" in result.stdout
    assert "| Failed | 1 / 5 |" in result.stdout
    assert "Disagreements — 1 / 2 compared." in result.stdout
    assert "3 / 3 checked curves imported successfully" in result.stdout
    assert "Runner wall time (all phases) — 20.000 s." in result.stdout
    assert "Witness generation wall time — 5.000 s." in result.stdout
    assert "Validation phase wall time — 9.000 s." in result.stdout
    assert "Post-validation import wall time — 2.000 s." in result.stdout
    assert "0.250 curves with a recorded outcome/s" in result.stdout
    assert "Checked throughput — 0.150 curves/s" in result.stdout
    assert (
        "| All checked curves | 3 / 3 | 4.000 s | 8.000 s | 8.000 s |" in result.stdout
    )
    assert "| Checked rank 0 | 1 / 1 | 1.000 s | 1.000 s | 1.000 s |" in result.stdout
    assert "| Checked rank 1 | 2 / 2 | 4.000 s | 8.000 s | 8.000 s |" in result.stdout


def test_partial_report_retains_pending_and_failed_audit(tmp_path: Path) -> None:
    result = run_report(
        tmp_path / "report.json",
        {
            "identity": {"count": 4},
            "error": "consumer failed\n<script>alert(1)</script>",
            "validation_phases": [{"wall_seconds": 8}, {"wall_seconds": 4}],
            "curves": [
                {"status": "checked"},
                {"status": "checked"},
                {"status": "proposed"},
            ],
            "compiled_reuse_groups": [
                {"curves": 1, "returncode": 0, "wall_seconds": 2},
                {"curves": 1, "returncode": 1, "wall_seconds": 3},
            ],
        },
    )
    assert result.returncode == 0, result.stderr
    assert "| Pending | 2 / 4 |" in result.stdout
    assert "| Failed | 0 / 4 |" in result.stdout
    assert "0 / 2 checked curves" in result.stdout
    assert "audit — failed. 1 / 2 checked curves" in result.stdout
    assert "Runner wall time and throughput are unavailable" in result.stdout
    assert "Validation phase wall time — 12.000 s." in result.stdout
    assert "Post-validation import wall time — 5.000 s." in result.stdout
    assert "\n    consumer failed <script>alert(1)</script>\n" in result.stdout


def test_missing_report_has_path_and_fails(tmp_path: Path) -> None:
    path = tmp_path / "missing.json"
    result = run_report(path)
    assert result.returncode == 1
    assert str(path) in result.stderr
    assert "cannot summarize benchmark report" in result.stderr


def test_resumed_report_avoids_combining_counts_and_latest_wall_time(
    tmp_path: Path,
) -> None:
    result = run_report(
        tmp_path / "report.json",
        {
            "identity": {"count": 2},
            "invocation_count": 2,
            "wall_seconds": 3,
            "curves": [{"status": "checked"}, {"status": "checked"}],
        },
    )
    assert result.returncode == 0, result.stderr
    assert (
        "Latest runner invocation wall time through last checkpoint — 3.000 s."
        in result.stdout
    )
    assert "the outcome counts span multiple invocations" in result.stdout
    assert "curves/s" not in result.stdout
