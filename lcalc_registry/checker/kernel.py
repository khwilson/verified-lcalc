"""Reconstruct untrusted data using the Lean worker; kernel-check trusted source."""

import os
import re
import subprocess
import time
from collections.abc import Sequence
from pathlib import Path

from .contracts import (
    ArtifactMetadata,
    AxiomAudit,
    CacheManifest,
    Certificate,
    TateWitness,
)
from .environment import Environment, file_hash
from .protocol import Invalid, canonical, certificate, digest, statement
from .witness import render_source

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
MODULARITY = "VerifiedLcalc.Assumptions.ellipticModularity"


def lean_rat(value: str) -> str:
    a, b = value.split("/")
    return f"(({a} : Rat) / {b})"


def lean_list(values: Sequence[str]) -> str:
    return "[" + ",".join(values) + "]"


def lean_tate(w: TateWitness | None) -> str:
    if w is None:
        return "none"
    fields = ("r", "s", "t", "starT", "cubicRoot", "quadraticRoot", "kodaira")
    return (
        "(some { "
        + ", ".join(f"{k} := {w[k]}" for k in fields)
        + ", chain := "
        + lean_list(w["chain"])
        + " })"
    )


def bindings(name: str, payload: Certificate) -> str:
    p = payload["parameters"]
    s = payload["subject"]
    a = s["ainvs"]
    N = s["conductor"]
    rank = payload["rank"]
    eq = (
        "{ "
        + ", ".join(
            f"{k} := {x}"
            for k, x in zip(["a1", "a2", "a3", "a4", "a6"], a, strict=True)
        )
        + " }"
    )
    lines = [
        f"namespace {name}",
        "open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions",
        f"theorem subject_eq :\n    result.equation = ({eq} : Artifacts.CurveEquation) ∧ result.conductor = {N} := by\n  decide +kernel",
        f"theorem submitted_analytic_rank :\n    analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = {rank} :=\n  analytic_rank",
        f"theorem precision_eq :\n    result.policy.precisionBits = {p['precision_bits']} ∧ result.termLimit = {p['terms']} := by\n  decide +kernel",
        f"theorem coefficients_eq :\n    result.coefficients = ({lean_list(payload['coefficients'])} : List Int) := by\n  decide +kernel",
        f"theorem minimality_primes_eq :\n    minimality.primes = ({lean_list(payload['arithmetic']['minimality'])} : List Nat) := by\n  decide +kernel",
        "theorem local_data_eq :\n    localData = ({ atTwo := "
        + lean_tate(payload["arithmetic"]["at_two"])
        + ", atThree := "
        + lean_tate(payload["arithmetic"]["at_three"])
        + " } : WildData) := by\n  decide +kernel",
    ]
    for field, value in [
        ("alphaLo", payload["evaluator"]["alpha"][0]),
        ("alphaHi", payload["evaluator"]["alpha"][1]),
        ("tail", payload["evaluator"]["tail"]),
    ]:
        lines.append(
            f"theorem {field}_eq :\n    result.{field} = {lean_rat(value)} := by\n  decide +kernel"
        )
    for field, value in zip(
        ["reLo", "reHi", "imLo", "imHi"],
        payload["enclosure"]["real"] + payload["enclosure"]["imag"],
        strict=True,
    ):
        lines.append(
            f"theorem box_{field}_eq :\n    result.box.{field} = {lean_rat(value)} := by\n  decide +kernel"
        )
    if payload["rank"] == "1":
        lines.append(
            f"theorem integration_grid_eq :\n    result.stepsPerUnit = {p['steps_per_unit']} ∧ result.cutoff = {p['cutoff']} := by\n  decide +kernel"
        )
        pair = payload["evaluator"]["finite"]
        lines.append(
            f"theorem finite_eq :\n    result.finite = ({lean_rat(pair[0])},{lean_rat(pair[1])}) := by\n  decide +kernel"
        )
    else:
        lines.append(
            f"theorem geometric_upper_eq :\n    result.geometricUpper = {lean_rat(payload['evaluator']['geometric_upper'])} := by\n  decide +kernel"
        )
    return (
        "\n/-! Named equalities binding the theorem to the submitted witness. -/\n\n"
        + "\n\n".join(lines)
        + f"\n\nend {name}\n"
    )


def audit(text: str, module: str) -> AxiomAudit:
    found = {}
    for name, body in re.findall(
        r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S
    ):
        found[name] = {x.strip() for x in body.split(",") if x.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        found[name] = set()
    result = {}
    for label in [
        "payload_correct",
        "minimality_valid",
        "local_data_valid",
        "analytic_rank",
    ]:
        name = module + "." + label
        if name not in found:
            raise Invalid("Missing axiom audit: " + label)
        allowed = STANDARD | ({MODULARITY} if label == "analytic_rank" else set())
        if not found[name] <= allowed:
            raise Invalid("Unexpected axiom in " + label)
        result[label] = sorted(found[name])
    return result


class KernelChecker:
    def __init__(
        self, environment: Environment, data: Path, timeout: int = 600
    ) -> None:
        self.environment = environment
        self.data = data
        self.timeout = timeout

    def check_payload(self, payload: object) -> CacheManifest:
        """Kernel-check a witness and return an unsigned manifest; no database writes."""
        start = time.monotonic()
        env = self.environment
        env.check_immutable()
        payload = certificate(payload)
        cid = digest(payload)
        module = "LcalcCertificates.C" + cid + "_E" + env.id
        work = self.data / "work" / env.id
        prefix = work / Path(module.replace(".", "/"))
        prefix.parent.mkdir(parents=True, exist_ok=True)
        source = prefix.with_suffix(".lean")
        source.write_text(
            render_source(env, payload, module, source, self.timeout)
            + bindings(module, payload)
        )
        process_env = {
            **os.environ,
            "LEAN_PATH": env.lean_path,
            "LEAN_NUM_THREADS": "1",
        }
        args = [
            str(env.lean),
            "-o",
            str(prefix.with_suffix(".olean")),
            "-i",
            str(prefix.with_suffix(".ilean")),
            "-c",
            str(prefix.with_suffix(".c")),
            str(source.relative_to(work)),
        ]
        with prefix.with_suffix(".validation.log").open("w") as log:
            proc = subprocess.Popen(
                args,
                cwd=work,
                env=process_env,
                stdout=log,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            try:
                code = proc.wait(timeout=self.timeout)
            except BaseException:
                import signal

                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                raise
        text = prefix.with_suffix(".validation.log").read_text()
        if code != 0:
            raise Invalid("Lean kernel rejected certificate; validation log retained")
        axioms = audit(text, module)
        env.check_immutable()
        artifacts: list[ArtifactMetadata] = []
        for extension in [
            ".lean",
            ".olean",
            ".olean.private",
            ".olean.server",
            ".ir",
            ".ir.sig",
            ".ilean",
        ]:
            file = prefix.with_suffix(extension)
            if not file.exists():
                continue
            h = file_hash(file)
            target = self.data / "objects" / h[:2] / h
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists() or file_hash(target) != h:
                import shutil

                temporary = target.with_suffix(".tmp")
                shutil.copyfile(file, temporary)
                if file_hash(temporary) != h:
                    raise Invalid("Artifact changed while publishing")
                temporary.replace(target)
            artifacts.append(
                {
                    "path": str(file.relative_to(work)),
                    "sha256": h,
                    "size": file.stat().st_size,
                }
            )
        if not any(a["path"].endswith(".olean") for a in artifacts):
            raise Invalid("Compiler produced no cached theorem")
        manifest: CacheManifest = {
            "schema": "lcalc.cache-manifest.v1",
            "certificate_id": cid,
            "statement_id": digest(statement(payload)),
            "statement": statement(payload),
            "environment_id": env.id,
            "environment": env.public,
            "module": module,
            "axioms": axioms,
            "artifacts": artifacts,
            "validation_implementation": env.implementation,
            "validated_at": time.time(),
            "validation_seconds": time.monotonic() - start,
            "trust": "kernel-checked with explicit ellipticModularity; compiled cache imports trust this signed build provenance",
        }
        manifest_path = prefix.with_suffix(".manifest.json")
        manifest_path.write_bytes(canonical(manifest))
        return manifest
