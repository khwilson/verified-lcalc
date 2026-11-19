"""Bounded, canonical certificate wire format. No mathematical computation."""

import hashlib
import json
import re
from collections.abc import Iterable
from typing import cast

from .contracts import Certificate, CurveSubject, JsonObject, Parameters, RankStatement

SCHEMA = "lcalc.ec-rank.v1"


class Invalid(ValueError):
    pass


def canonical(value: object) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode()


def digest(value: object) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()


def exact_keys(value: object, keys: Iterable[str]) -> JsonObject:
    if not isinstance(value, dict) or set(value) != set(keys):
        raise Invalid("Unexpected or missing fields")
    return value


def integer(value: object, signed: bool = True) -> str:
    if (
        not isinstance(value, str)
        or len(value) > 512
        or not re.fullmatch(
            r"(?:0|-[1-9][0-9]*|[1-9][0-9]*)" if signed else r"(?:0|[1-9][0-9]*)", value
        )
    ):
        raise Invalid("Expected a canonical decimal string")
    return value


def subject(value: object) -> CurveSubject:
    value = exact_keys(value, ["ainvs", "conductor"])
    if not isinstance(value["ainvs"], list) or len(value["ainvs"]) != 5:
        raise Invalid("Expected five coefficients")
    for a in value["ainvs"]:
        integer(a)
    n = int(integer(value["conductor"], False))
    if not 0 < n <= 10000:
        raise Invalid("Conductor exceeds this worker profile")
    return cast(CurveSubject, value)


def parameters(value: object, rank: str) -> Parameters:
    value = exact_keys(value, ["precision_bits", "terms", "steps_per_unit", "cutoff"])
    p = {k: int(integer(v, False)) for k, v in value.items()}
    if p["precision_bits"] not in [53, 80, 106] or not 1 <= p["terms"] <= 128:
        raise Invalid("Unsupported numerical settings")
    if rank == "0":
        if p["steps_per_unit"] or p["cutoff"]:
            raise Invalid("Central certificates have no derivative grid")
    elif not 1 <= p["steps_per_unit"] <= 16 or not 2 <= p["cutoff"] <= 64:
        raise Invalid("Unsupported derivative grid")
    return cast(Parameters, value)


def rational(value: object) -> None:
    if not isinstance(value, str) or len(value) > 1024:
        raise Invalid("Invalid rational")
    try:
        a, b = value.split("/")
    except ValueError as error:
        raise Invalid("Invalid rational") from error
    integer(a)
    integer(b, False)
    if b == "0":
        raise Invalid("Zero denominator")


def pair(value: object) -> None:
    if not isinstance(value, list) or len(value) != 2:
        raise Invalid("Expected interval endpoints")
    for x in value:
        rational(x)


def tate(value: object) -> None:
    if value is None:
        return
    value = exact_keys(
        value,
        ["r", "s", "t", "starT", "cubicRoot", "quadraticRoot", "chain", "kodaira"],
    )
    for k, v in value.items():
        if k != "chain":
            integer(v)
    if not isinstance(value["chain"], list) or len(value["chain"]) > 64:
        raise Invalid("Oversized Tate chain")
    for x in value["chain"]:
        integer(x)


def certificate(value: object) -> Certificate:
    value = exact_keys(
        value,
        [
            "schema",
            "subject",
            "parameters",
            "rank",
            "coefficients",
            "arithmetic",
            "enclosure",
            "evaluator",
        ],
    )
    if value["schema"] != SCHEMA or value["rank"] not in ["0", "1"]:
        raise Invalid("Unsupported certificate schema or rank")
    subject(value["subject"])
    parameters(value["parameters"], value["rank"])
    if not isinstance(value["coefficients"], list) or len(value["coefficients"]) != int(
        value["parameters"]["terms"]
    ):
        raise Invalid("Invalid coefficient prefix")
    for x in value["coefficients"]:
        integer(x)
    exact_keys(value["arithmetic"], ["minimality", "at_two", "at_three"])
    ps = value["arithmetic"]["minimality"]
    if not isinstance(ps, list) or len(ps) > 256:
        raise Invalid("Oversized factorization")
    for x in ps:
        integer(x, False)
    tate(value["arithmetic"]["at_two"])
    tate(value["arithmetic"]["at_three"])
    exact_keys(value["enclosure"], ["real", "imag"])
    pair(value["enclosure"]["real"])
    pair(value["enclosure"]["imag"])
    exact_keys(
        value["evaluator"],
        ["alpha", "tail", "geometric_upper"]
        if value["rank"] == "0"
        else ["alpha", "tail", "finite"],
    )
    pair(value["evaluator"]["alpha"])
    rational(value["evaluator"]["tail"])
    if value["rank"] == "0":
        rational(value["evaluator"]["geometric_upper"])
    else:
        pair(value["evaluator"]["finite"])
    return cast(Certificate, value)


def command_line(s: CurveSubject, p: Parameters | None = None) -> str:
    subject(s)
    if p is None:
        p = {
            "precision_bits": "53",
            "terms": "0",
            "steps_per_unit": "1",
            "cutoff": "16",
        }
    return "\t".join(
        s["ainvs"]
        + [
            s["conductor"],
            p["precision_bits"],
            p["terms"],
            p["steps_per_unit"] if p["steps_per_unit"] != "0" else "1",
            p["cutoff"] if p["cutoff"] != "0" else "16",
        ]
    )


def statement(value: Certificate) -> RankStatement:
    return {
        "schema": "lcalc.ec-rank-statement.v1",
        "subject": value["subject"],
        "normalization": "elliptic-hasse-weil-L",
        "center": "1",
        "analytic_rank": value["rank"],
    }
