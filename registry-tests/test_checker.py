"""Retained checker/cache regression tests from the retired volunteer service."""

import copy
import hashlib
import json
import subprocess
from pathlib import Path

import pytest

from lcalc_registry.cache import RegistryCache
from lcalc_registry.checker.contracts import Certificate, CurveSubject
from lcalc_registry.checker.kernel import MODULARITY, audit
from lcalc_registry.checker.protocol import (
    Invalid,
    canonical,
    certificate,
    command_line,
    digest,
)
from lcalc_registry.config import ROOT
from lcalc_registry.signing import Signer


def native_witness() -> Certificate:
    worker = ROOT / "worker/build/certificate-worker"
    if not worker.exists():
        pytest.skip("Build the minimal Lean numerical worker first")
    curve: CurveSubject = {"ainvs": ["0", "0", "1", "-1", "0"], "conductor": "37"}
    raw = subprocess.check_output(
        [str(worker), "compute", command_line(curve)], timeout=60
    )
    return certificate(json.loads(raw))


def test_witness_protocol_rejects_extra_fields_and_inexact_numbers() -> None:
    value = native_witness()
    for field, replacement in [("schema", "unknown"), ("rank", "99")]:
        changed = {**value, field: replacement}
        with pytest.raises(Invalid):
            certificate(changed)
    with pytest.raises(Invalid):
        certificate({**value, "source": "axiom forged : False"})
    changed = copy.deepcopy(value)
    changed["subject"]["ainvs"][0] = "01"
    with pytest.raises(Invalid):
        certificate(changed)
    changed = copy.deepcopy(value)
    changed["evaluator"]["tail"] = "1/0"
    with pytest.raises(Invalid):
        certificate(changed)


def test_axiom_audit_rejects_unapproved_axioms_and_missing_components() -> None:
    labels = [
        "payload_correct",
        "minimality_valid",
        "local_data_valid",
        "analytic_rank",
    ]
    text = "\n".join(f"'M.{name}' depends on axioms: [propext]" for name in labels)
    assert audit(text, "M")["analytic_rank"] == ["propext"]
    for invalid in [
        "",
        text.replace("propext", "sorryAx"),
        text.replace("propext", MODULARITY),
    ]:
        with pytest.raises(Invalid):
            audit(invalid, "M")


@pytest.mark.parametrize(
    "path", ["../../stolen.olean", "/tmp/stolen.olean", "unexpected.py"]
)
def test_signed_cache_rejects_path_traversal(tmp_path: Path, path: str) -> None:
    signer = Signer(tmp_path)
    signer.initialize()
    environment = {"schema": "test-profile"}
    eid = digest(environment)
    cid = "a" * 64
    manifest = {
        "schema": "lcalc.cache-manifest.v1",
        "certificate_id": cid,
        "environment_id": eid,
        "environment": environment,
        "module": f"LcalcCertificates.C{cid}_E{eid}",
        "artifacts": [
            {"path": path, "sha256": hashlib.sha256(b"").hexdigest(), "size": 0}
        ],
    }
    envelope = canonical(signer.envelope(manifest))
    with pytest.raises(Invalid):
        RegistryCache(
            "http://localhost:8788",
            tmp_path / "signing-public.pem",
            tmp_path / "cache",
            environment,
            get=lambda _: envelope,
        ).fetch(cid)
