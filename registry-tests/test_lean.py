import os
import subprocess
from pathlib import Path

import pytest
from fastapi.testclient import TestClient
from support import RegistryFixture
from test_registry import ROWS

from lcalc_registry.api import create_app
from lcalc_registry.backend import NativeBackend
from lcalc_registry.bundles import check_bundle
from lcalc_registry.cache import RegistryCache
from lcalc_registry.models import CampaignReport, Candidate
from lcalc_registry.worker import Worker

pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(
        os.getenv("REGISTRY_LEAN_TESTS") != "1",
        reason="Set REGISTRY_LEAN_TESTS=1 to run the actual Lean kernel",
    ),
]


def test_real_candidate_bundle_kernel_campaign_and_cache_only_consumer(
    setup: RegistryFixture, tmp_path: Path
) -> None:
    settings, reg = setup
    backend = NativeBackend(settings)
    profile = reg.register_environment(backend.manifest, backend.implementation)
    src = reg.import_source(
        "real kernel smoke",
        ROWS,
        {"test": "actual Lean; reference rank is deliberately wrong and ignored"},
    )
    curve = reg.curves(src.id)[0]
    reg.enqueue_generation([curve["id"]], profile.id)
    worker = Worker(reg, backend, settings)
    assert worker.once()
    versions = reg.versions()
    assert len(versions) == 1
    assert reg.checks() == []
    assert versions[0]["status"] == "candidate"
    v = versions[0]
    assert reg.get(Candidate, v["candidate_id"]).statement["analytic_rank"] == "1"
    bundle = tmp_path / "selected.zip"
    bundle.write_bytes(reg.proof_bundle([v["id"]]))
    # Real local checking of the exported source, independent of service registration.
    report = check_bundle(
        bundle,
        tmp_path / "local-check",
        settings.data_dir / "signing-public.pem",
        settings,
    )
    assert len(report["checks"]) == 1
    assert (tmp_path / "local-check/Usage.olean").exists()
    reuse = tmp_path / "Reuse.lean"
    reuse.write_text(
        "import Usage\nopen VerifiedLcalc.Assumptions\n"
        "open ImportedCertificates.Curve1\n"
        "theorem rank_reused : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := analytic_rank\n"
    )
    reused = subprocess.run(
        [str(backend.environment.lean), str(reuse)],
        env={**os.environ, "LEAN_PATH": report["lean_path"], "LEAN_NUM_THREADS": "1"},
        capture_output=True,
        text=True,
        timeout=60,
    )
    assert reused.returncode == 0, reused.stdout + reused.stderr
    assert reg.checks() == []
    campaign = reg.create_campaign("actual Lean check", [v["id"]])
    assert worker.once()
    event = reg.checks()[0]
    assert event.outcome == "accepted", event.error
    assert reg.get(CampaignReport, campaign.id).envelope["manifest"]["accepted"] == 1
    with TestClient(create_app(settings, reg)) as client:

        def get(path: str) -> bytes:
            response = client.get(path)
            assert response.status_code == 200, response.text
            return response.content

        cache = RegistryCache(
            "http://localhost:8788",
            settings.data_dir / "signing-public.pem",
            tmp_path / "cache",
            backend.manifest,
            get=get,
        )
        fetched = cache.fetch(v["candidate_id"])
    consumer = tmp_path / "Consumer.lean"
    m = fetched["module"]
    consumer.write_text(
        f"import {m}\nopen VerifiedLcalc.Assumptions\nset_option pp.fullNames true\ntheorem reused_rank : analyticOrderAt (modularWitness {m}.curve {m}.curve_nonsingular).formL (1 : ℂ) = 1 := {m}.curve_analytic_rank\n#check {m}.subject_eq\n#check {m}.submitted_analytic_rank\n#eval {m}.certifiedRank.val\n"
    )
    result = subprocess.run(
        [str(backend.environment.lean), str(consumer)],
        env={
            **os.environ,
            "LEAN_PATH": fetched["lean_path"] + ":" + backend.environment.lean_path,
            "LEAN_NUM_THREADS": "1",
        },
        capture_output=True,
        text=True,
        timeout=180,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip().endswith("1")


def test_real_submitted_witness_without_search_and_kernel_rejection(
    setup: RegistryFixture,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import copy

    from lcalc_registry.checker.protocol import certificate
    from lcalc_registry.models import Task

    settings, reg = setup
    backend = NativeBackend(settings)
    env = reg.register_environment(backend.manifest, backend.implementation)
    src = reg.import_source(
        "submitted smoke",
        [
            {
                "label": "11.a1",
                "ainvs": [0, -1, 1, -10, -20],
                "conductor": 11,
            }
        ],
        {},
    )
    curve = reg.curves(src.id)[0]
    original = backend.generate(curve["subject"]).witness
    # A mathematically equal, differently spelled rational must not be rejected
    # because it differs from the generator's preferred serialization.
    payload = copy.deepcopy(original)
    n, d = payload["evaluator"]["alpha"][0].split("/")
    payload["evaluator"]["alpha"][0] = f"{2 * int(n)}/{2 * int(d)}"

    def forbidden_search(subject: object) -> None:
        raise AssertionError("Submitted witness must not trigger numerical search")

    monkeypatch.setattr(backend, "generate", forbidden_search)
    task = reg.request_proof(src.id, "11.a1", env.id, payload)
    worker = Worker(reg, backend, settings)
    assert worker.once()
    completed = reg.get(Task, task.id)
    assert completed.status == "succeeded", completed.error
    version = completed.result["proof_version_id"]
    assert reg.checks() == []
    reg.create_campaign("check submitted rational", [version])
    assert worker.once()
    assert reg.checks(version)[0].outcome == "accepted", reg.checks(version)[0].error

    bad = copy.deepcopy(payload)
    bad["coefficients"][0] = "999"
    task = reg.request_proof(src.id, "11.a1", env.id, certificate(bad))
    assert worker.once()
    completed = reg.get(Task, task.id)
    assert completed.status == "succeeded", completed.error  # source is unchecked
    version = completed.result["proof_version_id"]
    reg.create_campaign("reject bad submitted coefficient", [version])
    assert worker.once()
    assert reg.checks(version)[0].outcome == "rejected"


def test_native_wild_tate_witness_render_matches_existing_template(
    setup: RegistryFixture,
    tmp_path: Path,
) -> None:
    from lcalc_registry.checker.protocol import command_line

    settings, _ = setup
    backend = NativeBackend(settings)
    generated = backend.generate(
        {"ainvs": ["0", "1", "0", "0", "4"], "conductor": "112"}
    )
    payload = generated.witness
    assert payload["arithmetic"]["at_two"] is not None
    old_source = tmp_path / "fixed.lean"
    # The old command reconstructs this fixed witness. Its source must agree
    # exactly with decoding and rendering the supplied arithmetic/numerical data.
    subprocess.run(
        [
            str(backend.environment.worker),
            "prove",
            command_line(payload["subject"], payload["parameters"]),
            generated.module,
            str(old_source),
        ],
        check=True,
        capture_output=True,
        text=True,
        timeout=60,
    )
    from lcalc_registry.checker.kernel import bindings

    assert generated.source == old_source.read_text() + bindings(
        generated.module, payload
    )
