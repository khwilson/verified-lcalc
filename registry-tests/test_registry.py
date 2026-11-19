import base64
import hashlib
import io
import json
import zipfile
from pathlib import Path
from typing import cast

import pytest
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
from fastapi.testclient import TestClient
from sqlalchemy import text
from sqlalchemy.exc import DatabaseError
from support import RegistryFixture

from lcalc_registry.api import create_app
from lcalc_registry.backend import Generated, Inconclusive
from lcalc_registry.checker.contracts import (
    ArtifactMetadata,
    CacheManifest,
    CentralCertificate,
    Certificate,
    CurveSubject,
    EnvironmentManifest,
    JsonObject,
)
from lcalc_registry.checker.protocol import Invalid, canonical, digest, statement
from lcalc_registry.models import (
    CampaignReport,
    Candidate,
    Environment,
    ProofVersion,
    Source,
    Task,
)
from lcalc_registry.service import Missing, Registry
from lcalc_registry.worker import Worker

ROWS = [
    {"label": "37.a1", "ainvs": [0, 0, 1, -1, 0], "conductor": 37, "analytic_rank": 999}
]


def base(registry: Registry) -> tuple[Environment, Source, JsonObject]:
    env = registry.register_environment(
        {
            "schema": "lcalc.environment.v1",
            "lean": "Lean (version 4.36.0-rc2, test)",
            "mathlib": "test-only",
            "tau_ceti": None,
            "platform": {},
            "checker_sources": {},
            "modularity_statement_sha256": "test-only",
        },
        {"test_only": "true"},
    )
    src = registry.import_source("test snapshot", ROWS, {"origin": "unit-test"})
    curve = registry.curves(src.id)[0]
    return env, src, curve


def witness(subject: CurveSubject) -> CentralCertificate:
    # A shape-valid test fixture, never a mathematically checked certificate.
    return {
        "schema": "lcalc.ec-rank.v1",
        "subject": subject,
        "parameters": {
            "precision_bits": "53",
            "terms": "1",
            "steps_per_unit": "0",
            "cutoff": "0",
        },
        "rank": "0",
        "coefficients": ["1"],
        "arithmetic": {"minimality": [], "at_two": None, "at_three": None},
        "enclosure": {"real": ["1/1", "2/1"], "imag": ["0/1", "0/1"]},
        "evaluator": {"alpha": ["1/1", "2/1"], "tail": "1/1", "geometric_upper": "1/2"},
    }


class FakeBackend:
    def __init__(self, env: Environment) -> None:
        self.id = env.id
        self.manifest = cast(EnvironmentManifest, env.manifest)
        self.implementation = env.implementation
        self.verify_calls = 0
        self.reject = False
        self.inconclusive = False

    def generate(self, subject: CurveSubject) -> Generated:
        if self.inconclusive:
            raise Inconclusive("unsupported test curve")
        p = witness(subject)
        module = f"LcalcCertificates.C{digest(p)}_E{self.id}"
        return Generated(p, "-- deliberately non-executable unit-test source\n", module)

    def render(self, payload: Certificate) -> Generated:
        module = f"LcalcCertificates.C{digest(payload)}_E{self.id}"
        return Generated(
            payload, "-- deliberately non-executable unit-test source\n", module
        )

    def verify(
        self, version: ProofVersion, payload: Certificate
    ) -> tuple[CacheManifest, dict[str, bytes]]:
        self.verify_calls += 1
        if self.reject:
            raise Invalid("unit-test rejection")
        source = b"-- deliberately non-executable unit-test source\n"
        binary = b"unit-test object, not a Lean proof"
        artifacts: list[ArtifactMetadata] = [
            {
                "path": version.module.replace(".", "/") + ext,
                "sha256": hashlib.sha256(raw).hexdigest(),
                "size": len(raw),
            }
            for ext, raw in [(".lean", source), (".olean", binary)]
        ]
        return {
            "schema": "lcalc.cache-manifest.v1",
            "certificate_id": version.candidate_id,
            "environment_id": self.id,
            "environment": self.manifest,
            "module": version.module,
            "artifacts": artifacts,
            "statement_id": digest(statement(payload)),
            "statement": statement(payload),
            "axioms": {},
            "validated_at": 0.0,
            "validation_seconds": 0.0,
            "trust": "Unit-test fake, not a mathematical proof",
            "validation_implementation": self.implementation,
        }, {hashlib.sha256(raw).hexdigest(): raw for raw in [source, binary]}


def generate(
    setup: RegistryFixture,
) -> tuple[JsonObject, Environment, Source, JsonObject, FakeBackend, Worker]:
    settings, reg = setup
    env, src, curve = base(reg)
    backend = FakeBackend(env)
    worker = Worker(reg, backend, settings)
    reg.enqueue_generation([curve["id"]], env.id)
    assert worker.once()
    return reg.versions()[0], env, src, curve, backend, worker


def test_candidate_generation_never_implies_checked(setup: RegistryFixture) -> None:
    settings, reg = setup
    version, env, src, curve, backend, worker = generate(setup)
    assert version["status"] == "candidate"
    assert reg.checks() == []
    assert backend.verify_calls == 0
    assert reg.stats()["verification"] == 0
    assert reg.get(Candidate, version["candidate_id"]).statement["analytic_rank"] == "0"
    assert (
        "999"
        not in canonical(reg.get(Candidate, version["candidate_id"]).witness).decode()
    )
    with pytest.raises(Missing):
        reg.cached_certificate(version["candidate_id"], env.id)


def test_snapshot_identity_and_labels_are_versioned(setup: RegistryFixture) -> None:
    _, reg = setup
    env, src, curve = base(reg)
    assert (
        reg.import_source("test snapshot", ROWS, {"origin": "unit-test"}).id == src.id
    )
    revised = reg.import_source(
        "test snapshot", [{**ROWS[0], "ainvs": [0, 1, 1, -1, 0]}], {"origin": "revised"}
    )
    assert revised.id != src.id
    assert (
        reg.curves(src.id, label="37.a1")[0]["subject"]
        != reg.curves(revised.id, label="37.a1")[0]["subject"]
    )
    with pytest.raises(Invalid):
        reg.import_source("duplicate", [ROWS[0], ROWS[0]], {})


def test_check_campaign_is_explicit_immutable_and_repeatable(
    setup: RegistryFixture,
) -> None:
    _, reg = setup
    version, env, src, curve, backend, worker = generate(setup)
    campaign = reg.create_campaign("first check", [version["id"]])
    assert reg.checks() == []
    assert worker.once()
    assert backend.verify_calls == 1
    first = reg.checks()[0]
    assert first.outcome == "accepted"
    assert reg.versions()[0]["status"] == "checked"
    report = reg.get(CampaignReport, campaign.id)
    assert report.envelope["manifest"]["accepted"] == 1
    assert report.envelope["manifest"]["selection_sha256"] == digest([version["id"]])
    reg.create_campaign("second check", [version["id"]])
    backend.reject = True
    assert worker.once()
    assert len(reg.checks()) == 2
    assert reg.checks()[0].outcome == "rejected"
    assert reg.versions()[0]["status"] == "checked"  # historical success is not erased
    assert reg.cached_certificate(version["candidate_id"], env.id) == first.envelope
    key = serialization.load_pem_public_key(reg.signer.public_key())
    assert isinstance(key, Ed25519PublicKey)
    key.verify(
        base64.b64decode(first.envelope["signature"]),
        canonical(first.envelope["manifest"]),
    )


def test_append_only_evidence_enforced_in_database(setup: RegistryFixture) -> None:
    _, reg = setup
    version, *_ = generate(setup)
    for table, column, value in [
        ("registry_candidate", "id", version["candidate_id"]),
        ("registry_proof_version", "id", version["id"]),
    ]:
        with pytest.raises(DatabaseError):
            with reg.engine.begin() as c:
                c.execute(
                    text(f"DELETE FROM {table} WHERE {column}=:key"), {"key": value}
                )
    assert reg.get(Candidate, version["candidate_id"])


def test_lease_reclaim_rejects_stale_worker(setup: RegistryFixture) -> None:
    settings, reg = setup
    env, src, curve = base(reg)
    reg.enqueue_generation([curve["id"]], env.id)
    first = reg.claim(env.id, -1)
    second = reg.claim(env.id, 120)
    assert first is not None and second is not None
    assert first.id == second.id and first.lease_token != second.lease_token
    assert first.lease_token is not None and second.lease_token is not None
    with pytest.raises(Invalid):
        reg.fail_task(first.id, first.lease_token, "stale")
    reg.fail_task(second.id, second.lease_token, "current")


def test_periodic_campaign_freezes_existing_selection(setup: RegistryFixture) -> None:
    _, reg = setup
    v, env, src, curve, backend, worker = generate(setup)
    reg.create_schedule("daily", src.id, env.id, 86400, 100)
    campaign = reg.tick()
    assert campaign is not None
    assert reg.tick() is None
    assert reg.campaign_status(campaign.id)["members"][0]["proof_version_id"] == v["id"]
    assert worker.once()
    assert reg.get(CampaignReport, campaign.id)


def test_inconclusive_generation_is_not_a_rank_result(setup: RegistryFixture) -> None:
    settings, reg = setup
    env, src, curve = base(reg)
    backend = FakeBackend(env)
    backend.inconclusive = True
    task = reg.enqueue_generation([curve["id"]], env.id)[0]
    Worker(reg, backend, settings).once()
    assert reg.get(Task, task.id).status == "inconclusive"
    assert reg.versions() == []
    assert reg.checks() == []


def test_bundle_contains_source_and_exact_inputs_but_no_success_claim(
    setup: RegistryFixture,
) -> None:
    _, reg = setup
    v, env, *_ = generate(setup)
    with zipfile.ZipFile(io.BytesIO(reg.proof_bundle([v["id"]]))) as z:
        m = json.loads(z.read("manifest.json"))
        envelope = json.loads(z.read("bundle-attestation.json"))
        assert m["status"] == "unchecked-candidates"
        assert m["environment_id"] == env.id
        assert envelope["manifest"] == m
        assert all(not name.endswith(".olean") for name in z.namelist())
        assert (
            hashlib.sha256(z.read(v["module"].replace(".", "/") + ".lean")).hexdigest()
            == v["source_sha256"]
        )
        assert (
            digest(json.loads(z.read("witnesses/" + v["candidate_id"] + ".json")))
            == v["candidate_id"]
        )


def test_http_dashboard_read_only_provenance_and_authorization(
    setup: RegistryFixture,
) -> None:
    settings, reg = setup
    v, env, src, curve, backend, worker = generate(setup)
    with TestClient(create_app(settings, reg)) as client:
        assert client.get("/").status_code == 200
        assert client.get("/v1/proof-versions").json()[0]["status"] == "candidate"
        body = {"name": "requested", "proof_version_ids": [v["id"]]}
        assert client.post("/v1/campaigns", json=body).status_code == 401
        assert settings.api_token is not None
        auth = {"Authorization": "Bearer " + settings.api_token}
        response = client.post("/v1/campaigns", json=body, headers=auth)
        assert response.status_code == 202
        assert reg.checks() == []
        assert (
            client.patch(
                "/v1/proof-versions/" + v["id"],
                json={"status": "checked"},
                headers=auth,
            ).status_code
            == 405
        )
        assert (
            client.post(
                "/v1/verifications", json={"outcome": "accepted"}, headers=auth
            ).status_code
            == 405
        )
        assert (
            client.get(
                "/v1/tasks/"
                + reg.campaign_status(response.json()["id"])["members"][0]["task_id"]
            )
            .json()
            .get("lease_token")
            is None
        )
        assert (
            client.get(
                "/v1/certificates/" + v["candidate_id"], params={"environment": env.id}
            ).status_code
            == 404
        )
        assert client.post("/mcp/", json={}, headers={}).status_code == 401
        assert (
            client.post(
                "/v1/sources", content=b"x" * (2 * 1024 * 1024 + 1), headers=auth
            ).status_code
            == 413
        )


def test_profile_mismatch_and_frozen_source_mismatch_fail(
    setup: RegistryFixture,
) -> None:
    _, reg = setup
    v, env, src, curve, backend, worker = generate(setup)
    reg.create_campaign("tamper", [v["id"]])
    task = reg.claim(env.id, 120)
    assert task is not None and task.lease_token is not None
    version = reg.get(ProofVersion, v["id"])
    payload = reg.get(Candidate, v["candidate_id"]).witness
    manifest, objects = backend.verify(version, payload)
    manifest["environment_id"] = "wrong"
    with pytest.raises(Invalid):
        reg.record_check(task.id, task.lease_token, "accepted", manifest, objects)
    assert reg.checks() == []


def test_new_installation_does_not_overwrite_profile_or_steal_old_tasks(
    setup: RegistryFixture,
) -> None:
    from lcalc_registry.models import Installation
    from lcalc_registry.service import installation_id

    settings, reg = setup
    v, env, src, curve, old, old_worker = generate(setup)
    reg.create_campaign("old installation check", [v["id"]])
    newer = {**env.implementation, "revision": "new"}
    reg.register_environment(env.manifest, newer)
    changed = FakeBackend(env)
    changed.implementation = newer
    new_worker = Worker(reg, changed, settings)
    assert (
        not new_worker.once()
    )  # old proof remains assigned to its original installation
    assert old_worker.once()
    reg.enqueue_generation([curve["id"]], env.id)
    assert new_worker.once()
    assert len(reg.versions()) == 2
    with pytest.raises(Invalid):
        reg.proof_bundle([x["id"] for x in reg.versions()])
    assert reg.get(Installation, installation_id(env.id, newer)).implementation == newer


def test_python_cache_verifier_and_corrupt_signature(
    setup: RegistryFixture, tmp_path: Path
) -> None:
    from lcalc_registry.cache import RegistryCache

    settings, reg = setup
    v, env, src, curve, backend, worker = generate(setup)
    reg.create_campaign("test signing", [v["id"]])
    worker.once()
    with TestClient(create_app(settings, reg)) as client:

        def get(path: str) -> bytes:
            response = client.get(path)
            assert response.status_code == 200
            return response.content

        result = RegistryCache(
            "http://localhost:8788",
            settings.data_dir / "signing-public.pem",
            tmp_path / "cache",
            env.manifest,
            get=get,
        ).fetch(v["candidate_id"])
        assert result["environment_id"] == env.id

        def tamper(path: str) -> bytes:
            raw = get(path)
            if "/certificates/" in path:
                payload = json.loads(raw)
                payload["manifest"]["trust"] = "changed"
                return canonical(payload)
            return raw

        with pytest.raises(Invalid):
            RegistryCache(
                "http://localhost:8788",
                settings.data_dir / "signing-public.pem",
                tmp_path / "bad",
                env.manifest,
                get=tamper,
            ).fetch(v["candidate_id"])


def test_reference_answers_are_only_compared_after_kernel_verification(
    setup: RegistryFixture,
) -> None:
    _, reg = setup
    v, env, src, curve, backend, worker = generate(setup)
    assert curve["reference_claim"] == {"analytic_rank": "999"}
    campaign = reg.create_campaign("source comparison", [v["id"]], source_id=src.id)
    assert reg.campaign_status(campaign.id)["members"][0]["reference_comparisons"] == []
    worker.once()
    status = reg.campaign_status(campaign.id)
    assert status["members"][0]["outcome"] == "accepted"
    assert status["members"][0]["reference_comparisons"][0]["matches"] is False
    assert (
        reg.get(CampaignReport, campaign.id).envelope["manifest"][
            "reference_mismatches"
        ]
        == 1
    )
    revised = reg.import_source(
        "test snapshot", [{**ROWS[0], "analytic_rank": 0}], {"origin": "unit-test"}
    )
    assert revised.id != src.id  # changing just the reference claim is a new snapshot


def test_schedule_can_be_paused_without_changing_existing_campaign(
    setup: RegistryFixture,
) -> None:
    _, reg = setup
    v, env, src, curve, backend, worker = generate(setup)
    schedule = reg.create_schedule("pause test", src.id, env.id, 3600)
    reg.set_schedule_enabled(schedule.id, False)
    assert reg.tick() is None
    reg.set_schedule_enabled(schedule.id, True)
    campaign = reg.tick()
    assert campaign
    reg.set_schedule_enabled(schedule.id, False)
    assert worker.once()
    assert reg.campaign_status(campaign.id)["complete"]


def test_verification_status_tracks_queue_claim_completion_and_recheck(
    setup: RegistryFixture,
) -> None:
    settings, reg = setup
    version, env, src, _, _, worker = generate(setup)
    with TestClient(create_app(settings, reg)) as client:
        path = f"/v1/proof-versions?source_id={src.id}&environment_id={env.id}"
        headers = {"Authorization": "Bearer test-operator-token"}
        response = client.post(
            "/v1/campaigns",
            json={
                "name": "queued status",
                "proof_version_ids": [version["id"]],
                "source_id": src.id,
            },
            headers=headers,
        )
        assert response.status_code == 202
        queued = client.get(path).json()[0]
        assert queued["status"] == "queued"
        assert queued["verification_status"] == "queued"
        assert queued["last_accepted_check"] is None
        assert "lease_token" not in queued["verification_task"]
        task = reg.claim(env.id, 120)
        assert task is not None and task.lease_token is not None
        running = client.get(path).json()[0]
        assert running["status"] == "running"
        assert running["verification_status"] == "running"
        reg.record_check(task.id, task.lease_token, "rejected", error="Test rejection")
        rejected = client.get(path).json()[0]
        assert rejected["status"] == "candidate"
        assert rejected["verification_status"] == "rejected"
        assert rejected["verification_task"] is None
        assert rejected["last_check"]["error"] == "Test rejection"
        reg.create_campaign("retry accepted", [version["id"]])
        assert worker.once()
        accepted = client.get(path).json()[0]
        assert accepted["status"] == "checked"
        assert accepted["verification_status"] == "accepted"
        assert accepted["last_accepted_check"] is not None
        reg.create_campaign("rechecking checked proof", [version["id"]])
        requeued = client.get(path).json()[0]
        assert requeued["status"] == "queued"
        assert requeued["verification_status"] == "queued"
        assert requeued["last_accepted_check"] == accepted["last_accepted_check"]


def test_running_verification_takes_priority_over_another_queued_check(
    setup: RegistryFixture,
) -> None:
    _, reg = setup
    version, env, _, _, _, _ = generate(setup)
    reg.create_campaign("one", [version["id"]])
    task = reg.claim(env.id, 120)
    assert task is not None
    reg.create_campaign("two", [version["id"]])
    assert reg.versions()[0]["status"] == "running"
    assert reg.versions()[0]["verification_task"]["id"] == task.id
