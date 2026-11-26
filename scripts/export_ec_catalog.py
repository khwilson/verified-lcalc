"""Package the imported facts from a successful hosted certificate benchmark."""

import argparse
import gzip
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any
from zipfile import ZIP_DEFLATED, ZipFile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.benchmark_ec_dataset import CATALOG_FACT_FIELDS, arithmetic_catalog_values

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path("data/lmfdb/sql-10000/inputs.json")
ASSUMPTIONS = {
    "analytic_rank": ["VerifiedLcalc.Assumptions.ellipticModularity"],
    "nonsingular": [],
    "global_minimal": [],
    "arithmetic_conductor": [],
    "arithmetic_root_number": [],
    "l_function_coefficients": [],
    "discriminant_prime_factorization": [],
}
THEOREMS = {
    "arithmetic_conductor": "conductor_valid",
    "arithmetic_root_number": "root_number_valid",
    "discriminant_prime_factorization": "minimality_valid",
}
SIDECARS = (".olean.private", ".olean.server", ".ir", ".ir.sig", ".ilean")
WITNESS_ARCHIVE = "witnesses.jsonl.gz"
MAX_WITNESS_LINE = 1024 * 1024


def read_json(path: Path) -> Any:
    return json.loads(path.read_text())


def sha256(path: Path) -> str:
    with path.open("rb") as file:
        return hashlib.file_digest(file, "sha256").hexdigest()


def require(condition: object, message: str) -> None:
    if not condition:
        raise ValueError(message)


def batch_identity(release_url: str, prefix: str) -> dict[str, Any]:
    match = re.fullmatch(
        r"https://github\.com/[\w.-]+/[\w.-]+/releases/download/"
        r"(ec-certificates-([1-9][0-9]*)-([1-9][0-9]*))",
        release_url,
        re.ASCII,
    )
    if match is None:
        raise ValueError(
            "Expected a GitHub release URL with an ec-certificates run tag"
        )
    tag, run, attempt = match.groups()
    require(
        prefix == f"Run{run}Attempt{attempt}", "Batch prefix differs from release tag"
    )
    return {"release_tag": tag, "run_id": int(run), "run_attempt": int(attempt)}


def witness_rank(witness: dict[str, Any], row: dict[str, Any]) -> str:
    require(
        witness["schema"] == "lcalc.ec-rank.v1"
        and witness["subject"]
        == {"conductor": str(row["conductor"]), "ainvs": list(map(str, row["ainvs"]))}
        and witness["rank"] in ("0", "1"),
        f"Witness does not bind the exported rank to {row['label']}",
    )
    return witness["rank"]


def succeeded(measurement: dict[str, Any]) -> bool:
    return type(measurement["returncode"]) is int and measurement["returncode"] == 0


def selection(report: dict[str, Any], root: Path) -> tuple[Path, list[dict[str, Any]]]:
    require(
        report["schema"] == "verified-lcalc.dataset-benchmark.v2"
        and report["complete"] is True
        and report.get("generation_complete") is True
        and succeeded(report["generation"])
        and not report.get("error"),
        "Expected a completed successful dataset benchmark",
    )
    fields = report["catalog_fact_fields"]
    require(
        len(fields) == len(CATALOG_FACT_FIELDS)
        and set(fields) == set(CATALOG_FACT_FIELDS),
        "Benchmark did not import and check the supported catalogue facts",
    )
    identity = report["identity"]
    offset, count = identity["offset"], identity["count"]
    require(
        type(offset) is int and offset >= 0 and type(count) is int and count > 0,
        "Invalid benchmark selection",
    )
    require(
        identity["runner_sha256"] == sha256(root / "scripts/benchmark_ec_dataset.py")
        and identity["validator_sha256"] == sha256(root / "benchmarks/ValidateEC.lean")
        and identity["production_sha256"]
        == {
            str(path.relative_to(root)): sha256(path)
            for path in (root / "VerifiedLcalc").rglob("*.lean")
        },
        "Benchmark source fingerprints differ from this checkout",
    )
    key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()[:16]
    expected_work = f".lake/ec-dataset-{key}"
    require(
        report["work_directory"] == expected_work, "Unexpected benchmark work directory"
    )
    work = root / expected_work
    require(
        work.resolve() == work and work.is_dir(),
        "Expected local benchmark artifacts under .lake",
    )
    source = root / SOURCE
    require(identity["source_sha256"] == sha256(source), "Input snapshot hash differs")
    inputs = read_json(source)["inputs"][offset : offset + count]
    require(
        len(inputs) == count and len({row["label"] for row in inputs}) == count,
        "Input snapshot has incomplete or repeated labels in the selection",
    )
    require(read_json(work / "inputs.json") == {"inputs": inputs}, "Lean inputs differ")
    require(len(report["curves"]) == count, "Report does not cover the selection")
    return work, inputs


def checked_modules(report: dict[str, Any], checked: dict[str, str]) -> dict[str, str]:
    """Require each checked label to appear in a good batch and its import group."""
    prefix = report["identity"]["module_prefix"]
    require(
        not prefix or re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", prefix),
        "Invalid module prefix",
    )
    labels_seen: set[str] = set()
    module_counts: Counter[str] = Counter()
    for batch in report["batches"]:
        index = batch["batch_index"]
        require(type(index) is int and index >= 0, "Invalid batch index")
        module, labels = batch["module"], batch["labels"]
        require(
            module == f"{prefix}Batch{index:04d}"
            and module not in module_counts
            and succeeded(batch)
            and batch["status"] == "finished"
            and labels,
            f"Unsuccessful or unexpected validation batch {module}",
        )
        for label in labels:
            require(
                label not in labels_seen and checked.get(label) == module,
                f"Unexpected batch assignment for {label}",
            )
            labels_seen.add(label)
        module_counts[module] = len(labels)
    require(
        labels_seen == checked.keys(), "Some checked curves have no validation batch"
    )
    imported: dict[str, str] = {}
    groups = report.get("compiled_reuse_groups", [])
    for group in groups:
        modules = group["modules"]
        require(
            succeeded(group)
            and group["status"] == "finished"
            and modules
            and len(set(modules)) == len(modules)
            and not (imported.keys() & set(modules))
            and set(modules) <= module_counts.keys()
            and group["curves"] == sum(module_counts[module] for module in modules),
            "Invalid or unsuccessful compiled proof import group",
        )
        digests = group.get("module_sha256")
        if not isinstance(digests, dict):
            raise ValueError("Compiled proof import group has missing module hashes")
        require(
            digests.keys() == set(modules)
            and all(
                isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest)
                for digest in digests.values()
            ),
            "Compiled proof import group has missing or invalid module hashes",
        )
        imported.update(digests)
    reuse = report["compiled_reuse"]
    require(
        imported.keys() == module_counts.keys()
        and succeeded(reuse)
        and reuse["curves"] == len(checked)
        and reuse["groups"] == len(groups),
        "Compiled proof import does not cover every checked curve",
    )
    return imported


def catalog_rows(
    report: dict[str, Any], inputs: list[dict[str, Any]], work: Path
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    rows: list[dict[str, Any]] = []
    checked: dict[str, str] = {}
    for index, (row, subject) in enumerate(zip(report["curves"], inputs, strict=True)):
        label, conductor, ainvs = (
            subject["label"],
            subject["conductor"],
            subject["ainvs"],
        )
        require(
            row["index"] == index
            and row["label"] == label
            and row["conductor"] == conductor,
            f"Report subject differs at input {index}",
        )
        status = row["status"]
        entry: dict[str, Any] = {
            "label": label,
            "conductor": conductor,
            "ainvs": ainvs,
            "status": status,
            "facts": [],
        }
        if status == "checked":
            prefix = f"{report['identity']['module_prefix']}Curve{index:04d}"
            require(
                row["declaration_prefix"] == prefix,
                f"Unexpected declaration for {label}",
            )
            require(
                row["file"] == f"{index}.json",
                f"Unexpected witness filename for {label}",
            )
            witness_file = work / "witnesses" / row["file"]
            require(
                sha256(witness_file) == row["witness_sha256"],
                f"Witness hash differs for {label}",
            )
            witness = read_json(witness_file)
            require(
                row["rank"] == witness_rank(witness, entry)
                and row["parameters"] == witness["parameters"],
                f"Witness does not bind the exported rank to {label}",
            )
            entry["witness_sha256"] = row["witness_sha256"]
            module = row["module"]
            checked[label] = module
            arithmetic = arithmetic_catalog_values(witness)
            require(
                row["arithmetic_catalog"] == arithmetic,
                f"Witness does not bind the imported arithmetic facts to {label}",
            )
            values = {
                "analytic_rank": int(witness["rank"]),
                "nonsingular": True,
                "global_minimal": True,
                **arithmetic,
            }
            entry["facts"] = [
                {
                    "field": field,
                    "value": value,
                    "theorem": f"{prefix}.{THEOREMS.get(field, field)}",
                    "module": module,
                    "assumptions": ASSUMPTIONS[field],
                }
                for field, value in values.items()
            ]
        else:
            require(
                status == "inconclusive" and "file" not in row,
                f"Cannot export benchmark outcome {status} for {label}",
            )
            if "reason" in row:
                entry["reason"] = row["reason"]
        rows.append(entry)
    return rows, checked


def package_witnesses(work: Path, rows: list[dict[str, Any]], output: Path) -> str:
    with (
        output.open("wb") as file,
        gzip.GzipFile(filename="", mode="wb", fileobj=file, mtime=0) as archive,
    ):
        for index, row in enumerate(rows):
            if row["status"] == "checked":
                raw = (work / "witnesses" / f"{index}.json").read_bytes()
                require(
                    hashlib.sha256(raw).hexdigest() == row["witness_sha256"],
                    f"Witness bytes changed for {row['label']}",
                )
                entry = {"label": row["label"], "witness_json": raw.decode("utf-8")}
                line = json.dumps(entry, ensure_ascii=False).encode("utf-8") + b"\n"
                require(
                    len(line) <= MAX_WITNESS_LINE,
                    f"Witness is too large for {row['label']}",
                )
                archive.write(line)
    return sha256(output)


def checksums(hashes: dict[str, str]) -> str:
    return "".join(f"{value}  {name}\n" for name, value in sorted(hashes.items()))


def package_module(
    work: Path, module: str, output: Path, expected_sha256: str, witness_only: bool
) -> dict[str, str]:
    olean = work / f"{module}.olean"
    require(
        olean.is_file() and olean.stat().st_size > 0,
        f"Missing compiled module {module}",
    )
    if not witness_only:
        shutil.copyfile(olean, output / olean.name)
    olean_digest = sha256(olean if witness_only else output / olean.name)
    require(
        olean_digest == expected_sha256,
        f"Compiled module differs from imported bytes: {module}",
    )
    if witness_only:
        return {}
    hashes = {olean.name: olean_digest}
    bundle = output / f"{module}.zip"
    with ZipFile(bundle, "w", compression=ZIP_DEFLATED) as archive:
        archive.write(output / olean.name, olean.name)
        for suffix in SIDECARS:
            sidecar = work / f"{module}{suffix}"
            if sidecar.is_file():
                hashes[sidecar.name] = sha256(sidecar)
                archive.write(sidecar, sidecar.name)
        archive.writestr("SHA256SUMS.txt", checksums(hashes))
    return {olean.name: hashes[olean.name], bundle.name: sha256(bundle)}


def export_catalog(
    report_path: Path,
    output: Path,
    release_url: str,
    root: Path = ROOT,
    *,
    witness_only: bool = False,
) -> None:
    release_url = release_url.rstrip("/")
    report = read_json(report_path)
    work, inputs = selection(report, root)
    rows, checked = catalog_rows(report, inputs, work)
    modules = checked_modules(report, checked)

    git_revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()
    identity = report["identity"]
    batch = batch_identity(release_url, identity["module_prefix"])
    toolchain = (root / "lean-toolchain").read_text().strip()
    packages = {
        p["name"]: p["rev"] for p in read_json(root / "lake-manifest.json")["packages"]
    }
    require(
        git_revision == report["git_revision"]
        and not subprocess.check_output(
            ["git", "status", "--porcelain", "--untracked-files=no"],
            cwd=root,
            text=True,
        ).strip()
        and toolchain == identity["toolchain"]
        and packages["mathlib"]
        == report["mathlib_revision"]
        == identity["mathlib_revision"],
        "Benchmark provenance differs from the pinned checkout",
    )

    output = output.resolve()
    require(
        not output.exists() or (output.is_dir() and not any(output.iterdir())),
        "Output must be a new or empty directory",
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=output.parent) as temporary:
        assets = Path(temporary) / "assets"
        assets.mkdir()
        hashes = {
            name: digest
            for module, expected_hash in sorted(modules.items())
            for name, digest in package_module(
                work, module, assets, expected_hash, witness_only
            ).items()
        }
        hashes[WITNESS_ARCHIVE] = package_witnesses(
            work, rows, assets / WITNESS_ARCHIVE
        )
        if not witness_only:
            for fact in (fact for row in rows for fact in row["facts"]):
                olean = f"{fact['module']}.olean"
                bundle = f"{fact['module']}.zip"
                fact.update(
                    olean_url=f"{release_url}/{olean}",
                    sha256=hashes[olean],
                    bundle_url=f"{release_url}/{bundle}",
                    bundle_sha256=hashes[bundle],
                )
        catalog = {
            "schema": 2,
            "batch": batch,
            "module_prefix": identity["module_prefix"],
            "witness_archive": {
                "url": f"{release_url}/{WITNESS_ARCHIVE}",
                "sha256": hashes[WITNESS_ARCHIVE],
            },
            "validation_batches": [
                {key: batch[key] for key in ("module", "labels")}
                for batch in report["batches"]
            ],
            "import_groups": [
                group["modules"] for group in report.get("compiled_reuse_groups", [])
            ],
            "git_revision": git_revision,
            "toolchain": toolchain,
            "mathlib_revision": packages["mathlib"],
            "tauceti_revision": packages["TauCeti"],
            "lean_version": identity["actual_lean_version"],
            "platform": report["platform"],
            "source_sha256": identity["source_sha256"],
            "attribution": "Curve data by The LMFDB Collaboration (CC-BY-SA).",
            "provenance_url": (
                f"https://github.com/khwilson/verified-lcalc/tree/{git_revision}/data/lmfdb/sql-10000"
            ),
            "benchmark_report_sha256": sha256(report_path),
            "selection": {"offset": identity["offset"], "count": identity["count"]},
            "curves": rows,
        }
        catalog_path = assets / "catalog.json"
        catalog_path.write_text(
            json.dumps(catalog, indent=2, ensure_ascii=False) + "\n"
        )
        hashes[catalog_path.name] = sha256(catalog_path)
        (assets / "SHA256SUMS.txt").write_text(checksums(hashes))
        assets.replace(output)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--release-url", required=True)
    parser.add_argument(
        "--witness-only", action="store_true", help="Omit compiled modules"
    )
    args = parser.parse_args()
    try:
        export_catalog(
            args.report, args.output, args.release_url, witness_only=args.witness_only
        )
    except (
        KeyError,
        OSError,
        ValueError,
        TypeError,
        subprocess.CalledProcessError,
    ) as error:
        parser.exit(1, f"Certificate catalog export failed: {error}\n")


if __name__ == "__main__":
    main()
