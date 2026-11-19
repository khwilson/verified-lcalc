import copy
import io
import zipfile
from dataclasses import replace
from typing import cast

from fastapi.testclient import TestClient
from sqlmodel import Session, select
from support import RegistryFixture
from test_registry import FakeBackend, base, witness

from lcalc_registry.api import create_app
from lcalc_registry.checker.contracts import CurveSubject
from lcalc_registry.models import Candidate, Task
from lcalc_registry.worker import Worker


def test_witness_submission_freezes_data_without_search_or_checks(
    setup: RegistryFixture,
) -> None:
    settings, registry = setup
    env, src, curve = base(registry)
    payload = witness(cast(CurveSubject, curve["subject"]))
    # Deliberately invalid mathematics is still a valid unchecked candidate.
    payload["coefficients"] = ["999"]
    backend = FakeBackend(env)
    backend.inconclusive = True  # generate() would fail: submitted data must bypass it.
    body = {
        "source_id": src.id,
        "label": "37.a1",
        "environment_id": env.id,
        "witness": payload,
    }
    with TestClient(create_app(settings, registry)) as client:
        assert client.post("/v1/witnesses", json=body).status_code == 401
        response = client.post(
            "/v1/witnesses",
            json=body,
            headers={"Authorization": "Bearer test-operator-token"},
        )
        assert response.status_code == 202, response.text
        task_id = response.json()["id"]
        # The artifact survives mutation of the caller's original dictionary.
        payload["coefficients"] = ["1"]
        assert Worker(registry, backend, settings).once()
        response = client.get(f"/v1/proof-requests/{task_id}")
        assert response.json()["verification"] == "unchecked"
        assert response.json()["status"] == "succeeded"
        cid = registry.get(Task, task_id).result["candidate_id"]
        assert registry.get(Candidate, cid).witness["coefficients"] == ["999"]
        bundle = client.get(response.json()["bundle_url"])
        assert bundle.status_code == 200
        with zipfile.ZipFile(io.BytesIO(bundle.content)) as archive:
            assert any(name.endswith(".lean") for name in archive.namelist())
        assert registry.checks() == []
        assert backend.verify_calls == 0


def test_public_button_flow_is_opt_in_bounded_and_idempotent(
    setup: RegistryFixture,
) -> None:
    settings, registry = setup
    env, src, curve = base(registry)
    body = {"source_id": src.id, "label": "37.a1", "environment_id": env.id}
    with TestClient(create_app(settings, registry)) as client:
        assert client.post("/v1/proof-requests", json=body).status_code == 403
    settings = replace(settings, public_proof_requests=True, public_max_pending=1)
    with TestClient(create_app(settings, registry)) as client:
        origin = {"Origin": "https://www.lmfdb.org"}
        first = client.post("/v1/proof-requests", json=body, headers=origin)
        assert first.status_code == 202, first.text
        assert first.headers["access-control-allow-origin"] == origin["Origin"]
        repeated = client.post("/v1/proof-requests", json=body)
        assert repeated.json()["id"] == first.json()["id"]
        assert (
            client.get(f"/v1/proof-requests/{first.json()['id']}/bundle").status_code
            == 409
        )
        submitted = {**body, "witness": witness(cast(CurveSubject, curve["subject"]))}
        assert client.post("/v1/proof-requests", json=submitted).status_code == 429
        assert Worker(registry, FakeBackend(env), settings).once()
        assert (
            client.post("/v1/proof-requests", json=body).json()["id"]
            == first.json()["id"]
        )
        assert client.post("/v1/proof-requests", json=submitted).status_code == 202
        assert registry.checks() == []
        # Public endpoint cannot request kernel verification or submit Lean source.
        assert (
            client.post("/v1/proof-requests", json={**body, "verify": True}).status_code
            == 422
        )
        assert (
            client.post(
                "/v1/proof-requests", json={**body, "source": "axiom false : False"}
            ).status_code
            == 422
        )
        assert (
            client.post(
                "/v1/campaigns", json={"name": "no", "proof_version_ids": ["no"]}
            ).status_code
            == 401
        )


def test_witness_schema_and_curve_binding(setup: RegistryFixture) -> None:
    settings, registry = setup
    env, src, curve = base(registry)
    settings = replace(settings, public_proof_requests=True)
    payload = witness(cast(CurveSubject, curve["subject"]))
    body = {
        "source_id": src.id,
        "label": "37.a1",
        "environment_id": env.id,
        "witness": payload,
    }
    with TestClient(create_app(settings, registry)) as client:
        assert (
            client.post(
                "/v1/proof-requests", json={**body, "label": "11.a1"}
            ).status_code
            == 404
        )
        wrong = copy.deepcopy(payload)
        wrong["subject"]["conductor"] = "11"
        assert (
            client.post(
                "/v1/proof-requests", json={**body, "witness": wrong}
            ).status_code
            == 400
        )
        assert (
            client.post(
                "/v1/proof-requests",
                json={**body, "witness": {**payload, "lean": "sorry"}},
            ).status_code
            == 400
        )
        wrong["coefficients"] = ["1\tunsafe"]
        assert (
            client.post(
                "/v1/proof-requests", json={**body, "witness": wrong}
            ).status_code
            == 400
        )
        with Session(registry.engine) as session:
            assert session.exec(select(Task)).all() == []


def test_dashboard_lists_generation_progress_without_lease_credentials(
    setup: RegistryFixture,
) -> None:
    settings, registry = setup
    env, src, curve = base(registry)
    tasks = registry.enqueue_generation([curve["id"]], env.id)
    backend = FakeBackend(env)
    with TestClient(create_app(settings, registry)) as client:
        path = f"/v1/tasks?source_id={src.id}&environment_id={env.id}"
        pending = client.get(path)
        assert pending.status_code == 200
        assert pending.json()[0]["id"] == tasks[0].id
        assert pending.json()[0]["status"] == "pending"
        assert "lease_token" not in pending.json()[0]
        assert client.get(path + "&limit=0").status_code == 422
        assert Worker(registry, backend, settings).once()
        assert client.get(path).json()[0]["status"] == "succeeded"
        # Errors must be visible too, rather than silently leaving an empty list.
        backend.inconclusive = True
        registry.enqueue_generation([curve["id"]], env.id)
        assert Worker(registry, backend, settings).once()
        outcomes = client.get(path).json()
        inconclusive = next(t for t in outcomes if t["status"] == "inconclusive")
        assert inconclusive["error"] == "unsupported test curve"
        assert (
            client.get(f"/v1/tasks?environment_id={env.id}&source_id=other").json()
            == []
        )
