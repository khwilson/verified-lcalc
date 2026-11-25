import gzip
import hashlib
import json
import sys
from pathlib import Path
from typing import Any
from zipfile import ZipFile

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts import export_ec_catalog as exporter
from scripts import replay_ec_batch as replay

RELEASE = "https://github.com/owner/repo/releases/download/ec-certificates-123-2"
MODULE = "Run123Attempt2Batch0000"
SUBJECT = {"label": "285.c1", "conductor": 285, "ainvs": [1, 1, 0, -6007, -181724]}
OTHER = {**SUBJECT, "label": "285.c2", "ainvs": [1, 1, 0, -1237, 13054]}


def write_json(path: Path, data: Any) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data))
    return path


@pytest.fixture
def benchmark(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> tuple[Path, Path, dict[str, Any]]:
    root = tmp_path.resolve()
    rev, mathlib, tauceti = "a" * 40, "b" * 40, "c" * 40
    monkeypatch.setattr(
        exporter.subprocess,
        "check_output",
        lambda args, **kw: rev + "\n" if args[1] == "rev-parse" else "",
    )
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.37.0-rc1\n")
    write_json(
        root / "lake-manifest.json",
        {
            "packages": [
                {"name": "mathlib", "rev": mathlib},
                {"name": "TauCeti", "rev": tauceti},
            ]
        },
    )
    source = write_json(root / exporter.SOURCE, {"inputs": [OTHER, SUBJECT]})
    runner = write_json(root / "scripts/benchmark_ec_dataset.py", "")
    validator = write_json(root / "benchmarks/ValidateEC.lean", "")
    production = write_json(root / "VerifiedLcalc/Stub.lean", "")
    identity = {
        "count": 1,
        "offset": 1,
        "source_sha256": exporter.sha256(source),
        "runner_sha256": exporter.sha256(runner),
        "validator_sha256": exporter.sha256(validator),
        "production_sha256": {"VerifiedLcalc/Stub.lean": exporter.sha256(production)},
        "module_prefix": "Run123Attempt2",
        "toolchain": "leanprover/lean4:v4.37.0-rc1",
        "actual_lean_version": "Lean test version",
        "mathlib_revision": mathlib,
    }
    key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()[:16]
    work = root / ".lake" / f"ec-dataset-{key}"
    write_json(work / "inputs.json", {"inputs": [SUBJECT]})
    parameters = {
        "precision_bits": "96",
        "terms": "24",
        "steps_per_unit": "1",
        "cutoff": "8",
    }
    witness = {
        "schema": "lcalc.ec-rank.v1",
        "subject": {"ainvs": ["1", "1", "0", "-6007", "-181724"], "conductor": "285"},
        "rank": "0",
        "parameters": parameters,
    }
    witness_path = write_json(work / "witnesses/0.json", witness)
    witness_path.write_bytes(b" \r\n" + witness_path.read_bytes() + b"\r\n")
    for suffix in (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig"):
        (work / f"{MODULE}{suffix}").write_text(suffix)
    success = {"returncode": 0, "status": "finished"}
    report = {
        "schema": "verified-lcalc.dataset-benchmark.v2",
        "complete": True,
        "generation_complete": True,
        "generation": success.copy(),
        "catalog_fact_fields": list(exporter.ASSUMPTIONS),
        "identity": identity,
        "git_revision": rev,
        "mathlib_revision": mathlib,
        "platform": "Linux",
        "work_directory": str(work.relative_to(root)),
        "curves": [
            {
                "index": 0,
                "label": SUBJECT["label"],
                "conductor": 285,
                "status": "checked",
                "module": MODULE,
                "declaration_prefix": "Run123Attempt2Curve0000",
                "file": "0.json",
                "rank": "0",
                "parameters": parameters,
                "witness_sha256": exporter.sha256(witness_path),
            }
        ],
        "batches": [
            {
                **success,
                "batch_index": 0,
                "module": MODULE,
                "labels": [SUBJECT["label"]],
            },
        ],
        "compiled_reuse": {"curves": 1, "groups": 1, "returncode": 0},
        "compiled_reuse_groups": [
            {
                **success,
                "curves": 1,
                "modules": [MODULE],
                "module_sha256": {MODULE: exporter.sha256(work / f"{MODULE}.olean")},
            }
        ],
    }
    return root, work, report


def test_exports_verified_facts_and_complete_module_bundle(
    benchmark: tuple[Path, Path, dict[str, Any]],
) -> None:
    root, work, report = benchmark
    path = write_json(root / "report.json", report)
    output = root / "release"
    output.mkdir()
    exporter.export_catalog(path, output, RELEASE, root)
    catalog = exporter.read_json(output / "catalog.json")
    assert catalog["schema"] == 1
    assert catalog["selection"] == {"count": 1, "offset": 1}
    assert catalog["tauceti_revision"] == "c" * 40
    assert catalog["batch"] == {
        "run_id": 123,
        "run_attempt": 2,
        "release_tag": "ec-certificates-123-2",
    }
    archive = output / exporter.WITNESS_ARCHIVE
    assert catalog["witness_archive"] == {
        "url": f"{RELEASE}/{archive.name}",
        "sha256": exporter.sha256(archive),
    }
    assert catalog["validation_batches"] == [
        {"module": MODULE, "labels": [SUBJECT["label"]]}
    ]
    assert catalog["import_groups"] == [[MODULE]]
    witness_path = work / "witnesses/0.json"
    [entry] = list(replay.archive_rows(archive))
    assert entry["label"] == SUBJECT["label"]
    assert entry["witness_json"].encode("utf-8") == witness_path.read_bytes()
    second = root / "second"
    exporter.export_catalog(path, second, RELEASE, root, witness_only=True)
    assert archive.read_bytes() == (second / archive.name).read_bytes()
    assert {p.name for p in second.iterdir()} == {
        archive.name,
        "catalog.json",
        "SHA256SUMS.txt",
    }
    for fact in exporter.read_json(second / "catalog.json")["curves"][0]["facts"]:
        assert "olean_url" not in fact and "bundle_url" not in fact

    row = catalog["curves"][0]
    assert {key: row[key] for key in SUBJECT} == SUBJECT
    assert row["witness_sha256"] == exporter.sha256(witness_path)
    facts = {fact["field"]: fact for fact in row["facts"]}
    assert set(facts) == {"analytic_rank", "nonsingular", "global_minimal"}
    assert (
        type(facts["analytic_rank"]["value"]) is int
        and facts["analytic_rank"]["value"] == 0
    )
    assert facts["analytic_rank"]["assumptions"] == [
        "VerifiedLcalc.Assumptions.ellipticModularity"
    ]
    for field, fact in facts.items():
        assert fact["theorem"] == f"Run123Attempt2Curve0000.{field}"
        assert fact["module"] == MODULE
        assert fact["olean_url"] == f"{RELEASE}/{MODULE}.olean"
        assert fact["bundle_url"] == f"{RELEASE}/{MODULE}.zip"
        assert fact["sha256"] == exporter.sha256(output / f"{MODULE}.olean")
        assert fact["bundle_sha256"] == exporter.sha256(output / f"{MODULE}.zip")
        if field != "analytic_rank":
            assert fact["value"] is True and fact["assumptions"] == []
    assert (output / "SHA256SUMS.txt").read_text().splitlines() == [
        f"{exporter.sha256(output / name)}  {name}"
        for name in (f"{MODULE}.olean", f"{MODULE}.zip", "catalog.json", archive.name)
    ]
    with ZipFile(output / f"{MODULE}.zip") as archive:
        files = {p.name: p for p in work.glob(MODULE + ".*")}
        assert set(archive.namelist()) == {*files, "SHA256SUMS.txt"}
        for name, artifact in files.items():
            assert archive.read(name) == artifact.read_bytes()
            assert (
                f"{exporter.sha256(artifact)}  {name}\n"
                in archive.read("SHA256SUMS.txt").decode()
            )


@pytest.mark.parametrize(
    "error",
    [
        "incomplete",
        "marker",
        "batch",
        "batch_labels",
        "import",
        "import_count",
        "no_groups",
        "bad_module_hashes",
        "replaced_module",
        "rank",
        "witness",
        "subject",
        "lean_inputs",
        "module",
    ],
)
def test_refuses_to_export_incomplete_or_unbound_facts(
    benchmark: tuple[Path, Path, dict[str, Any]], error: str
) -> None:
    root, work, report = benchmark
    if error == "incomplete":
        report["complete"] = False
    elif error == "marker":
        report["catalog_fact_fields"] = ["analytic_rank"]
    elif error == "batch":
        report["batches"][0]["returncode"] = 1
    elif error == "batch_labels":
        report["batches"][0]["labels"] = [OTHER["label"]]
    elif error == "import":
        report["compiled_reuse_groups"][0]["returncode"] = 1
    elif error == "import_count":
        report["compiled_reuse_groups"][0]["curves"] = 2
    elif error == "no_groups":
        del report["compiled_reuse_groups"]
    elif error == "bad_module_hashes":
        report["compiled_reuse_groups"][0]["module_sha256"] = {
            "UnrelatedBatch0000": "a" * 64
        }
    elif error == "replaced_module":
        (work / f"{MODULE}.olean").write_text("replacement")
    elif error == "rank":
        report["curves"][0]["rank"] = "1"
    elif error in {"witness", "subject"}:
        witness_path = work / "witnesses/0.json"
        witness = exporter.read_json(witness_path)
        witness["subject"]["ainvs"][0] = "2"
        write_json(witness_path, witness)
        if error == "subject":
            report["curves"][0]["witness_sha256"] = exporter.sha256(witness_path)
    elif error == "lean_inputs":
        write_json(work / "inputs.json", {"inputs": [OTHER]})
    elif error == "module":
        (work / f"{MODULE}.olean").unlink()
    path = write_json(root / "report.json", report)
    output = root / "release"
    with pytest.raises(ValueError):
        exporter.export_catalog(path, output, RELEASE, root)
    assert not output.exists()


def test_exports_inconclusive_without_facts(
    benchmark: tuple[Path, Path, dict[str, Any]],
) -> None:
    root, _, report = benchmark
    report["curves"] = [
        {
            "index": 0,
            "label": SUBJECT["label"],
            "conductor": 285,
            "status": "inconclusive",
            "reason": "derivative_enclosure_inconclusive",
        },
    ]
    report["compiled_reuse"].update(curves=0, groups=0)
    del report["compiled_reuse_groups"]
    report["batches"] = []
    output = root / "release"
    exporter.export_catalog(
        write_json(root / "report.json", report), output, RELEASE, root
    )
    [entry] = exporter.read_json(output / "catalog.json")["curves"]
    assert entry["facts"] == [] and entry["status"] == "inconclusive"
    assert entry["reason"] == "derivative_enclosure_inconclusive"
    assert {path.name for path in output.iterdir()} == {
        "catalog.json",
        "SHA256SUMS.txt",
        exporter.WITNESS_ARCHIVE,
    }

    archive = output / exporter.WITNESS_ARCHIVE
    assert gzip.decompress(archive.read_bytes()) == b""
    assert replay.replay(output / "catalog.json", archive, None, root) == 0
    with pytest.raises(ValueError, match="No checked witness"):
        replay.replay(output / "catalog.json", archive, str(SUBJECT["label"]), root)


@pytest.mark.parametrize(
    ("change", "error"),
    [
        ("compressed", "Witness archive hash differs"),
        ("witness", "Witness hash differs"),
        ("missing", "Archive omits checked witnesses"),
        ("duplicate", "Unexpected or duplicate archived witness"),
        ("rank", "Witness rank differs from catalog"),
        ("theorem", "Invalid analytic_rank fact"),
        ("import", "Import groups differ from validation batches"),
    ],
)
def test_replay_rejects_catalog_or_archive_tampering(
    benchmark: tuple[Path, Path, dict[str, Any]], change: str, error: str
) -> None:
    root, _, report = benchmark
    output = root / "release"
    exporter.export_catalog(
        write_json(root / "report.json", report), output, RELEASE, root
    )
    catalog_path, archive = output / "catalog.json", output / exporter.WITNESS_ARCHIVE
    catalog = exporter.read_json(catalog_path)
    if change == "compressed":
        archive.write_bytes(archive.read_bytes() + b"x")
    elif change in {"witness", "missing", "duplicate"}:
        raw = gzip.decompress(archive.read_bytes())
        if change == "witness":
            entry = json.loads(raw)
            entry["witness_json"] += " "
            raw = json.dumps(entry).encode() + b"\n"
        elif change == "duplicate":
            raw += raw
        else:
            raw = b""
        archive.write_bytes(gzip.compress(raw, mtime=0))
        catalog["witness_archive"]["sha256"] = exporter.sha256(archive)
    elif change == "rank":
        catalog["curves"][0]["facts"][0]["value"] = 1
    elif change == "theorem":
        catalog["curves"][0]["facts"][0]["theorem"] += "\naxiom injected"
    else:
        catalog["import_groups"].append(["Injected"])
    write_json(catalog_path, catalog)
    with pytest.raises(ValueError, match=error):
        replay.replay(catalog_path, archive, None, root)


def test_replay_calls_lean_on_exact_source_and_consumer(
    benchmark: tuple[Path, Path, dict[str, Any]], monkeypatch: pytest.MonkeyPatch
) -> None:
    root, work, report = benchmark
    output = root / "release"
    exporter.export_catalog(
        write_json(root / "report.json", report),
        output,
        RELEASE,
        root,
        witness_only=True,
    )
    monkeypatch.setattr(
        replay, "prepare_lean", lambda *a: (Path("lean"), {"LEAN_PATH": "lib"})
    )
    sources = []

    def run(args: list[str], cwd: Path, **kwargs: Any) -> None:
        assert args[0] == "lean" and kwargs["check"]
        assert (cwd / "0.json").read_bytes() == (work / "witnesses/0.json").read_bytes()
        sources.append((cwd / args[-1]).read_text())

    monkeypatch.setattr(replay.subprocess, "run", run)
    assert (
        replay.replay(
            output / "catalog.json",
            output / exporter.WITNESS_ARCHIVE,
            str(SUBJECT["label"]),
            root,
        )
        == 1
    )
    batch, consumer = sources
    assert 'certify_ec Run123Attempt2Curve0000 from_json "0.json"' in batch
    assert f"import {MODULE}" in consumer
    for field in exporter.ASSUMPTIONS:
        assert f":= Run123Attempt2Curve0000.{field}" in consumer
    assert "⟨1, 1, 0, -6007, -181724⟩" in consumer
    assert ".result.conductor = 285" in consumer


def test_witness_only_checks_compiled_import_hash(
    benchmark: tuple[Path, Path, dict[str, Any]],
) -> None:
    root, work, report = benchmark
    (work / f"{MODULE}.olean").write_text("replacement")
    with pytest.raises(ValueError, match="Compiled module differs from imported bytes"):
        exporter.export_catalog(
            write_json(root / "report.json", report),
            root / "release",
            RELEASE,
            root,
            witness_only=True,
        )


def test_replay_requires_pinned_checkout(
    benchmark: tuple[Path, Path, dict[str, Any]],
) -> None:
    root, _, report = benchmark
    output = root / "release"
    exporter.export_catalog(
        write_json(root / "report.json", report), output, RELEASE, root
    )
    catalog_path = output / "catalog.json"
    catalog = exporter.read_json(catalog_path)
    catalog["git_revision"] = "d" * 40
    write_json(catalog_path, catalog)
    with pytest.raises(
        ValueError, match="clean checkout at the catalog's Git revision"
    ):
        replay.replay(catalog_path, output / exporter.WITNESS_ARCHIVE, None, root)
