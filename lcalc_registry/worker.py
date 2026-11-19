import logging
import subprocess
import threading
from collections.abc import Generator
from contextlib import contextmanager

from .backend import Inconclusive
from .config import Settings
from .contracts import CheckingBackend
from .models import (
    Candidate,
    Curve,
    Environment,
    Installation,
    ProofVersion,
    Task,
)
from .service import Registry, installation_id

logger = logging.getLogger(__name__)


@contextmanager
def heartbeat(registry: Registry, task: Task, seconds: int) -> Generator[None]:
    token = task.lease_token
    if token is None:
        raise ValueError("Worker task has no lease token")
    stop = threading.Event()

    def loop() -> None:
        while not stop.wait(max(1, min(30, seconds / 3))):
            try:
                registry.renew_task(task.id, token, seconds)
            except Exception:
                return  # Final publication still checks ownership and expiration.

    thread = threading.Thread(target=loop, daemon=True)
    thread.start()
    try:
        yield
    finally:
        stop.set()
        thread.join()


class Worker:
    def __init__(
        self, registry: Registry, backend: CheckingBackend, settings: Settings
    ) -> None:
        self.registry = registry
        self.backend = backend
        self.settings = settings
        self.installation_id = installation_id(backend.id, backend.implementation)
        registered = registry.get(Environment, backend.id)
        installation = registry.get(Installation, self.installation_id)
        if (
            registered.manifest != backend.manifest
            or installation.implementation != backend.implementation
        ):
            raise ValueError("Worker differs from registered environment/installation")

    def once(self) -> bool:
        self.registry.seal_ready_campaigns()
        task = self.registry.claim(
            self.backend.id, self.settings.task_lease_seconds, self.installation_id
        )
        if task is None:
            return False
        token = task.lease_token
        if token is None:
            raise ValueError("Claimed task has no lease token")
        logger.info("Starting %s task %s (curve %s)", task.kind, task.id, task.curve_id)
        with heartbeat(self.registry, task, self.settings.task_lease_seconds):
            try:
                if task.kind == "generate":
                    if task.curve_id is None:
                        raise ValueError("Generation task has no curve")
                    curve = self.registry.get(Curve, task.curve_id)
                    submitted = self.registry.submitted_witness(task)
                    result = (
                        self.backend.render(submitted)
                        if submitted is not None
                        else self.backend.generate(curve.subject)
                    )
                    self.registry.register_candidate(
                        task.id,
                        token,
                        result.witness,
                        result.source,
                        result.module,
                    )
                else:
                    if task.proof_version_id is None:
                        raise ValueError("Verification task has no proof version")
                    version = self.registry.get(ProofVersion, task.proof_version_id)
                    candidate = self.registry.get(Candidate, version.candidate_id)
                    manifest, objects = self.backend.verify(version, candidate.witness)
                    self.registry.record_check(
                        task.id, token, "accepted", manifest, objects
                    )
            except Exception as error:
                message = str(error)[:2000]
                if task.kind == "verify":
                    self.registry.record_check(
                        task.id,
                        token,
                        "timeout"
                        if isinstance(error, subprocess.TimeoutExpired)
                        else "rejected",
                        error=message,
                    )
                else:
                    self.registry.fail_task(
                        task.id,
                        token,
                        message,
                        isinstance(error, Inconclusive),
                    )
        finished = self.registry.get(Task, task.id)
        logger.info(
            "Task %s: %s%s",
            task.id,
            finished.status,
            " — " + finished.error if finished.error else "",
        )
        if task.campaign_id:
            self.registry.seal_campaign(task.campaign_id)
        return True
