"""Rebuild a published batch's exact JSON certificates in its pinned Lean checkout."""

import argparse
import gzip
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import zlib
from collections.abc import Iterator
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.benchmark_ec_dataset import LAKE, catalog_import_examples, selected_inputs
from scripts.export_ec_catalog import (
    ASSUMPTIONS,
    MAX_WITNESS_LINE,
    ROOT,
    SOURCE,
    WITNESS_ARCHIVE,
    batch_identity,
    read_json,
    require,
    sha256,
    witness_rank,
)

LEAN_HEADER = """module
public import VerifiedLcalc.Tactic.CertifyEC

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

@[expose] public section
"""


def checked_rows(catalog: dict[str, Any], root: Path) -> dict[str, dict[str, Any]]:
    require(
        type(catalog["schema"]) is int and catalog["schema"] == 1,
        "Unknown catalog schema",
    )
    require("witness_archive" in catalog, "Catalog has no replayable witness archive")
    archive_url = catalog["witness_archive"]["url"]
    require(
        isinstance(archive_url, str) and archive_url.endswith(f"/{WITNESS_ARCHIVE}"),
        "Unexpected witness archive URL",
    )
    prefix = catalog["module_prefix"]
    require(
        catalog["batch"] == batch_identity(archive_url.rsplit("/", 1)[0], prefix),
        "Batch identity differs from release tag",
    )
    source = root / SOURCE
    require(catalog["source_sha256"] == sha256(source), "Input snapshot hash differs")
    offset, count = (catalog["selection"][key] for key in ("offset", "count"))
    require(type(offset) is int and type(count) is int, "Invalid catalog selection")
    subjects = selected_inputs(source, count, offset)
    rows = {}
    for index, (row, subject) in enumerate(
        zip(catalog["curves"], subjects, strict=True)
    ):
        label = subject["label"]
        require(
            row["label"] == label
            and type(row["conductor"]) is int
            and row["conductor"] == subject["conductor"]
            and len(row["ainvs"]) == 5
            and all(type(value) is int for value in row["ainvs"])
            and row["ainvs"] == subject["ainvs"],
            f"Catalog subject differs for {label}",
        )
        status = row["status"]
        if status == "inconclusive":
            require(
                row["facts"] == [] and "witness_sha256" not in row,
                f"Inconclusive curve {label} has certificate evidence",
            )
            continue
        require(status == "checked", f"Unknown status for {label}")
        declaration = f"{prefix}Curve{index:04d}"
        facts = {fact["field"]: fact for fact in row["facts"]}
        require(
            facts.keys() == ASSUMPTIONS.keys() and len(row["facts"]) == len(facts),
            f"Catalog facts differ for {label}",
        )
        rank = facts["analytic_rank"]["value"]
        require(type(rank) is int and rank in (0, 1), f"Invalid rank for {label}")
        for field, assumptions in ASSUMPTIONS.items():
            fact = facts[field]
            require(
                fact["theorem"] == f"{declaration}.{field}"
                and fact["assumptions"] == assumptions
                and (field == "analytic_rank" or fact["value"] is True),
                f"Invalid {field} fact for {label}",
            )
        rows[label] = {
            **row,
            "index": index,
            "declaration_prefix": declaration,
            "rank": rank,
        }

    return rows


def checked_groups(
    catalog: dict[str, Any], rows: dict[str, dict[str, Any]]
) -> dict[str, list[str]]:
    prefix = catalog["module_prefix"]
    modules: dict[str, list[str]] = {}
    remaining = set(rows)
    for batch in catalog["validation_batches"]:
        module, labels = batch["module"], batch["labels"]
        require(
            re.fullmatch(rf"{prefix}Batch[0-9]{{4,}}", module)
            and module not in modules
            and isinstance(labels, list)
            and labels,
            "Invalid validation batch",
        )
        for label in labels:
            require(label in remaining, f"Unexpected or duplicate batch curve {label}")
            require(
                all(fact["module"] == module for fact in rows[label]["facts"]),
                f"Fact module differs from validation batch for {label}",
            )
            remaining.remove(label)
        modules[module] = labels
    require(not remaining, "Validation batches omit checked curves")
    imports = [module for group in catalog["import_groups"] for module in group]
    require(
        len(imports) == len(modules)
        and set(imports) == modules.keys()
        and all(
            isinstance(group, list) and group for group in catalog["import_groups"]
        ),
        "Import groups differ from validation batches",
    )
    return modules


def archive_rows(archive_path: Path) -> Iterator[dict[str, Any]]:
    with gzip.open(archive_path, "rb") as archive:
        while line := archive.readline(MAX_WITNESS_LINE + 1):
            require(
                len(line) <= MAX_WITNESS_LINE and line.endswith(b"\n"),
                "Invalid witness archive line",
            )
            yield json.loads(line)


def extract_witnesses(
    catalog: dict[str, Any],
    archive_path: Path,
    rows: dict[str, dict[str, Any]],
    selected: set[str],
    work: Path,
) -> None:
    require(
        sha256(archive_path) == catalog["witness_archive"]["sha256"],
        "Witness archive hash differs",
    )
    remaining = set(rows)
    for entry in archive_rows(archive_path):
        label = entry["label"]
        require(
            set(entry) == {"label", "witness_json"} and label in remaining,
            f"Unexpected or duplicate archived witness for {label}",
        )
        remaining.remove(label)
        raw = entry["witness_json"].encode("utf-8")
        row = rows[label]
        require(
            hashlib.sha256(raw).hexdigest() == row["witness_sha256"],
            f"Witness hash differs for {label}",
        )
        require(
            int(witness_rank(json.loads(raw), row)) == row["rank"],
            f"Witness rank differs from catalog for {label}",
        )
        if label in selected:
            (work / f"{row['index']}.json").write_bytes(raw)
    require(not remaining, "Archive omits checked witnesses")


def capture(args: list[str], cwd: Path, env: dict[str, str] | None = None) -> str:
    return subprocess.check_output(args, cwd=cwd, env=env, text=True).strip()


def lean_release(version: str) -> str:
    """Drop the build target while retaining the Lean version, commit and build mode."""
    return re.sub(r"(version [^,]+), [^,]+, (commit )", r"\1, \2", version)


def prepare_lean(catalog: dict[str, Any], root: Path) -> tuple[Path, dict[str, str]]:
    require(
        capture(["git", "rev-parse", "HEAD"], root) == catalog["git_revision"]
        and not capture(["git", "status", "--porcelain", "--untracked-files=no"], root),
        "Replay requires a clean checkout at the catalog's Git revision",
    )
    require(
        (root / "lean-toolchain").read_text().strip() == catalog["toolchain"],
        "Lean toolchain differs from the catalog",
    )
    manifest = read_json(root / "lake-manifest.json")
    packages = {p["name"]: p["rev"] for p in manifest["packages"]}
    require(
        packages["mathlib"] == catalog["mathlib_revision"]
        and packages["TauCeti"] == catalog["tauceti_revision"],
        "Dependency revisions differ from the catalog",
    )
    env = {
        name: value
        for name, value in os.environ.items()
        if not name.startswith("LEAN_")
    }
    lean = Path(capture(["lean", "--print-prefix"], root, env)) / "bin" / "lean"
    require(
        lean_release(capture([str(lean), "--version"], root, env))
        == lean_release(catalog["lean_version"]),
        "Lean version differs from the catalog",
    )
    src_paths = {
        (root / path).resolve()
        for path in capture(
            [*LAKE, "env", "printenv", "LEAN_SRC_PATH"], root, env
        ).split(os.pathsep)
    }
    for name, revision in packages.items():
        package = (root / manifest["packagesDir"] / name).resolve()
        require(
            package in src_paths
            and capture(["git", "rev-parse", "HEAD"], package) == revision
            and not capture(
                ["git", "status", "--porcelain", "--untracked-files=no"], package
            ),
            f"Lake package {name} does not use the clean pinned revision",
        )
    subprocess.run(
        [*LAKE, "build", "VerifiedLcalc.Tactic.CertifyEC"],
        cwd=root,
        env=env,
        check=True,
    )
    env["LEAN_PATH"] = capture([*LAKE, "env", "printenv", "LEAN_PATH"], root, env)
    return lean, env


def verify(
    catalog: dict[str, Any],
    modules: dict[str, list[str]],
    rows: dict[str, dict[str, Any]],
    selected: set[str],
    work: Path,
    lean: Path,
    env: dict[str, str],
) -> None:
    # Use fresh module files and rename no catalog-supplied paths.
    env = {**env, "LEAN_PATH": str(work) + os.pathsep + env["LEAN_PATH"]}
    for module, labels in modules.items():
        source = LEAN_HEADER + "".join(
            f'certify_ec {rows[label]["declaration_prefix"]} from_json "{rows[label]["index"]}.json"\n'
            for label in labels
            if label in selected
        )
        if source == LEAN_HEADER:
            continue
        filename = f"{module}.lean"
        (work / filename).write_text(source, encoding="utf-8")
        subprocess.run(
            [str(lean), "-DwarningAsError=true", "-o", f"{module}.olean", filename],
            cwd=work,
            env=env,
            check=True,
        )
    for index, group in enumerate(catalog["import_groups"]):
        available = [
            module for module in group if selected.intersection(modules[module])
        ]
        if not available:
            continue
        consumer = (
            "module\n"
            + "".join(f"import {module}\n" for module in available)
            + "\n"
            + "".join(
                catalog_import_examples(rows[label], rows[label])
                for module in available
                for label in modules[module]
                if label in selected
            )
        )
        filename = f"ReplayConsumer{index:04d}.lean"
        (work / filename).write_text(consumer, encoding="utf-8")
        subprocess.run(
            [str(lean), "-DwarningAsError=true", filename],
            cwd=work,
            env=env,
            check=True,
        )


def replay(
    catalog_path: Path, archive_path: Path, curve: str | None, root: Path = ROOT
) -> int:
    catalog = read_json(catalog_path)
    rows = checked_rows(catalog, root)
    modules = checked_groups(catalog, rows)
    require(curve is None or curve in rows, f"No checked witness for {curve}")
    selected = {curve} if curve is not None else set(rows)
    with tempfile.TemporaryDirectory(prefix="ec-replay-") as temporary:
        work = Path(temporary)
        extract_witnesses(catalog, archive_path, rows, selected, work)
        if selected:
            lean, env = prepare_lean(catalog, root)
            verify(catalog, modules, rows, selected, work, lean, env)
    return len(selected)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalog", type=Path)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--curve", help="Replay one checked curve from the batch")
    args = parser.parse_args()
    try:
        count = replay(args.catalog, args.archive, args.curve)
    except (
        EOFError,
        KeyError,
        OSError,
        TypeError,
        ValueError,
        subprocess.CalledProcessError,
        zlib.error,
    ) as error:
        parser.exit(1, f"Certificate replay failed: {error}\n")
    print(f"Replayed and checked {count} certificate(s) in Lean.")


if __name__ == "__main__":
    main()
