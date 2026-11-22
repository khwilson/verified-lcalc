"""Print Mathlib cache roots used by tracked Lean sources and their TauCeti imports."""

import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(
    r"^(?:(?:public|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?"
    r"((?:Mathlib|TauCeti)(?:\.[\w']+)*)(?=[ \t\r\n]|$)",
    re.MULTILINE,
)


def main() -> None:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    tauceti = ROOT / manifest["packagesDir"] / "TauCeti"
    tracked = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "*.lean"], cwd=ROOT
    ).decode()
    sources = (ROOT / path for path in tracked.split("\0") if path)
    pending = [path for path in sources if path.is_file()]
    mathlib: set[str] = set()
    visited: set[str] = set()
    while pending:
        for module in IMPORT.findall(pending.pop().read_text()):
            if module == "Mathlib" or module.startswith("Mathlib."):
                mathlib.add(module)
            elif module not in visited:
                visited.add(module)
                pending.append(
                    tauceti.joinpath(*module.split(".")).with_suffix(".lean")
                )
    for module in sorted(mathlib):
        print(module)


if __name__ == "__main__":
    main()
