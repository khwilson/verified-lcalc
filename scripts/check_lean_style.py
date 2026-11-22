"""Run the Mathlib style and declaration documentation checks on a Git range."""

import argparse
import subprocess
from pathlib import Path
from tempfile import NamedTemporaryFile

CERTIFICATE_LAKE = ["lake", "-f", "lakefile.certificates.lean"]
MATRIX_SOURCES = [
    "tests/VerifiedLcalcTests/Fixtures/LmfdbCI.lean",
    "tests/consumers/LmfdbCI.lean",
]
DOC_SCAN = """
open Lean in
run_meta do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let candidates := env.constants.fold (init := #[]) fun acc declName _ =>
    match (env.getModuleIdxFor? declName).bind (fun idx => modules[idx.toNat]?) with
    | some mod => if targets.contains mod then acc.push declName else acc
    | none => acc
  for declName in candidates do
    if let some problem ← Batteries.Tactic.Lint.docBlame.test declName then
      logError m!"{declName}: {problem}"
"""


def header_options(file: str) -> list[str]:
    """Recognize the project header while keeping the default for other notices."""
    lines = Path(file).read_text().splitlines()
    if lines[:1] == ["/-"] and lines[2:3] == ["Part of verified-lcalc."]:
        return ["-Dweak.linter.style.header.license=Part of verified-lcalc."]
    return []


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "base", help="compare the current checkout to this Git revision"
    )
    base = parser.parse_args().base
    changed = subprocess.check_output(
        [
            "git",
            "diff",
            "--name-only",
            "--diff-filter=ACMR",
            "-z",
            base,
            "HEAD",
            "--",
            "*.lean",
        ]
    ).decode()
    # Lake DSL files are elaborated by Lake itself when loading the configuration.
    sources = {
        file
        for file in changed.split("\0")
        if file and not file.startswith("lakefile.")
    }
    files = sorted(sources.union(MATRIX_SOURCES))
    for file in files:
        # The alternate Lake configuration provides the compiled certificate examples.
        subprocess.run(
            [
                *CERTIFICATE_LAKE,
                "env",
                "lean",
                "-Dweak.linter.mathlibStandardSet=true",
                "-Dweak.linter.style.longFile=1500",
                "-Dweak.linter.style.longFileDefValue=1500",
                "-DwarningAsError=true",
                *header_options(file),
                file,
            ],
            check=True,
        )
    subprocess.run(
        [
            *CERTIFICATE_LAKE,
            "env",
            "lean",
            "--run",
            "scripts/LeanTextStyle.lean",
            *files,
        ],
        check=True,
    )

    # Legacy imports expose the declaration kinds and docs that module imports hide.
    modules = [
        ".".join(Path(file).with_suffix("").parts)
        for file in files
        if file == "VerifiedLcalc.lean" or file.startswith("VerifiedLcalc/")
    ]
    if modules:
        subprocess.run(["lake", "build", *modules], check=True)
        imports = "\n".join(f"import {module}" for module in modules)
        targets = ", ".join(f"`{module}" for module in modules)
        with NamedTemporaryFile(mode="w", suffix=".lean", dir=".lake") as driver:
            driver.write(
                f"import Mathlib.Tactic.Linter.Lint\n{imports}\n\n"
                f"private def targets : Array Lean.Name := #[{targets}]\n{DOC_SCAN}"
            )
            driver.flush()
            subprocess.run([*CERTIFICATE_LAKE, "env", "lean", driver.name], check=True)


if __name__ == "__main__":
    main()
