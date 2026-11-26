"""Verify the companion's Lean field contract locations against the compiler."""

import argparse
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPORTER = "scripts/export_lmfdb_dependency_contracts.lean"
SNAPSHOT = ROOT / "docs/roadmaps/lmfdb-field-contracts.json"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Regenerate the snapshot")
    args = parser.parse_args()
    compiled = subprocess.run(
        ["lake", "-f", "lakefile.certificates.lean", "env", "lean", EXPORTER],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        check=False,
    )
    if compiled.returncode:
        raise SystemExit(compiled.stdout or compiled.returncode)
    routes = json.loads(compiled.stdout)
    rows = (json.dumps(row, ensure_ascii=False, sort_keys=True) for row in routes)
    rendered = "[\n" + ",\n".join("  " + row for row in rows) + "\n]\n"
    if args.write:
        SNAPSHOT.write_text(rendered, encoding="utf-8")
    elif not SNAPSHOT.is_file() or SNAPSHOT.read_text(encoding="utf-8") != rendered:
        raise SystemExit(
            "Regenerate with scripts/check_lmfdb_dependency_contracts.py --write"
        )


if __name__ == "__main__":
    main()
