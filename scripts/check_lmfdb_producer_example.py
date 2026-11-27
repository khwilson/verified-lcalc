"""Reproduce the single-curve native producer evidence used in the roadmap."""

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "tests/fixtures/lmfdb/112.a2-native.json"
SNAPSHOT = ROOT / "docs/roadmaps/lmfdb-112-a2-producer-example.json"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Regenerate the snapshot")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="lmfdb-roadmap-example-") as directory:
        projection = Path(directory) / "projection.json"
        witness = Path(directory) / "witness.json"
        subprocess.run(
            [
                sys.executable,
                "scripts/capture_lmfdb_fixture.py",
                "replay",
                str(CAPTURE),
                "--output",
                str(projection),
            ],
            cwd=ROOT,
            check=True,
        )
        result = subprocess.run(
            [
                sys.executable,
                "scripts/produce_ec_witness.py",
                str(projection),
                "--output",
                str(witness),
            ],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            text=True,
            check=False,
        )
        if result.returncode:
            raise SystemExit(result.stdout or result.returncode)
    report = json.loads(result.stdout)
    if report.get("status") != "checked":
        raise SystemExit("Expected a checked producer run for native 112.a2")
    rendered = json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    if args.write:
        SNAPSHOT.write_text(rendered, encoding="utf-8")
    elif not SNAPSHOT.is_file() or SNAPSHOT.read_text(encoding="utf-8") != rendered:
        raise SystemExit(
            "Regenerate with scripts/check_lmfdb_producer_example.py --write"
        )


if __name__ == "__main__":
    main()
