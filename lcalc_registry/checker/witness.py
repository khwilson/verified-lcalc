"""Bounded data transport to Lean's source renderer; no numerical search."""

import subprocess
from pathlib import Path

from .contracts import Certificate, TateWitness
from .environment import Environment
from .protocol import Invalid, certificate


def tate_wire(value: TateWitness | None) -> str:
    if value is None:
        return "none"
    fields = ("r", "s", "t", "starT", "cubicRoot", "quadraticRoot", "kodaira")
    return ",".join(value[k] for k in fields) + ";" + ",".join(value["chain"])


def witness_wire(payload: Certificate) -> str:
    p = certificate(payload)  # Reject separators, arbitrary source and oversized data.
    params = p["parameters"]
    arithmetic = p["arithmetic"]
    extra = (
        [p["evaluator"]["geometric_upper"], "0/1", "0/1"]
        if p["rank"] == "0"
        else ["0/1", *p["evaluator"]["finite"]]
    )
    return "\t".join(
        [
            p["rank"],
            *p["subject"]["ainvs"],
            p["subject"]["conductor"],
            params["precision_bits"],
            params["terms"],
            params["steps_per_unit"],
            params["cutoff"],
            ",".join(p["coefficients"]),
            ",".join(arithmetic["minimality"]),
            tate_wire(arithmetic["at_two"]),
            tate_wire(arithmetic["at_three"]),
            *p["evaluator"]["alpha"],
            p["evaluator"]["tail"],
            *p["enclosure"]["real"],
            *p["enclosure"]["imag"],
            *extra,
        ]
    )


def render_source(
    environment: Environment,
    payload: Certificate,
    module: str,
    path: Path,
    timeout: int,
) -> str:
    result = subprocess.run(
        [str(environment.worker), "render", witness_wire(payload), module, str(path)],
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    if result.returncode:
        raise Invalid("Installed Lean renderer could not decode the witness")
    return path.read_text()
