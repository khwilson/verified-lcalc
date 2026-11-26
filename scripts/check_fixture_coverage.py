"""Compare the companion's fixture report with the audited Lean declarations."""

import argparse
import json
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOF = "tests/consumers/FixtureFieldCoverage.lean"
REPORT = ROOT / "web/certificates/fixture-field-coverage.json"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write", action="store_true", help="Update the published JSON"
    )
    args = parser.parse_args()
    result = subprocess.run(
        ["lake", "-f", "lakefile.certificates.lean", "env", "lean", PROOF],
        cwd=ROOT,
        env={**os.environ, "VERIFIED_LCALC_FIXTURE_COVERAGE": "1"},
        check=False,
        stdout=subprocess.PIPE,
        text=True,
    )
    if result.returncode:
        raise SystemExit(result.stdout or result.returncode)
    report = json.loads(result.stdout)
    if report["proof_source"] != PROOF:
        raise SystemExit("Fixture report proof source changed")
    lines = (ROOT / PROOF).read_text(encoding="utf-8").splitlines()
    for field in report["fields"]:
        for proof in field["evidence"]:
            name = proof["theorem"].rsplit(".", 1)[-1]
            line = proof["proof_line"]
            if not 1 <= line <= len(lines) or not lines[line - 1].startswith(
                f"theorem {name}"
            ):
                raise SystemExit(f"Stale theorem source location for {name}: {line}")
            if not (ROOT / proof["source"]).is_file():
                raise SystemExit(f"Fixture input no longer exists: {proof['source']}")
    rendered = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.write:
        REPORT.write_text(rendered, encoding="utf-8")
    elif not REPORT.is_file() or REPORT.read_text(encoding="utf-8") != rendered:
        raise SystemExit(
            "Update the fixture report with scripts/check_fixture_coverage.py --write"
        )


if __name__ == "__main__":
    main()
