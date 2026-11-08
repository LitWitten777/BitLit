"""Dynamical models, simulation runs and agent models (migration 016).

*Given* means not ``NULL``/``None``.  Blank text is text of only space, tab,
LF, CR, FF, VT (the empty text included).
"""

from __future__ import annotations

import math
from datetime import datetime
from typing import Any, List, Optional

from qbx.empirical.values import Problem, exact, is_blank, is_name, is_name_list, is_number, repeats

MODEL_TYPES = ("ODE", "SDE", "PDE", "discrete")


def dynamical_model_problems(name: Optional[str], model_type: Optional[str],
                             spec: Optional[str], solver_config: Any,
                             metadata: Any) -> List[Problem]:
    """``model_typing`` with error, in order: name (blank), model_type (not
    ODE / SDE / PDE / discrete), spec (blank), solver_config (not an object) —
    else tolerance (present but not a number > 0) —, metadata (not an
    object)."""
    out: List[Problem] = []
    if is_blank(name):
        out.append(("model_typing", {"error": "name"}))
    if model_type not in MODEL_TYPES:
        out.append(("model_typing", {"error": "model_type"}))
    if is_blank(spec):
        out.append(("model_typing", {"error": "spec"}))
    if not isinstance(solver_config, dict):
        out.append(("model_typing", {"error": "solver_config"}))
    elif "tolerance" in solver_config and not (is_number(solver_config["tolerance"])
                                               and exact(solver_config["tolerance"]) > 0):
        out.append(("model_typing", {"error": "tolerance"}))
    if not isinstance(metadata, dict):
        out.append(("model_typing", {"error": "metadata"}))
    return out


def simulation_problems(model_exists: bool, initial_conditions: Any,
                        solver: Optional[str], tolerance: Optional[float],
                        result_uri: Optional[str], result_summary: Any,
                        started_at: Optional[datetime],
                        finished_at: Optional[datetime]) -> List[Problem]:
    """``simulation_typing`` with error, in order: model (none, or not found),
    initial_conditions (not an object), solver (given but blank), tolerance
    (given but not a finite number > 0), result_uri (given but blank),
    result_summary (given but not an object), started_at (none), window
    (finished before it started)."""
    out: List[Problem] = []

    def err(e: str) -> None:
        out.append(("simulation_typing", {"error": e}))

    if not model_exists:
        err("model")
    if not isinstance(initial_conditions, dict):
        err("initial_conditions")
    if solver is not None and is_blank(solver):
        err("solver")
    if tolerance is not None and not (math.isfinite(tolerance) and tolerance > 0):
        err("tolerance")
    if result_uri is not None and is_blank(result_uri):
        err("result_uri")
    if result_summary is not None and not isinstance(result_summary, dict):
        err("result_summary")
    if started_at is None:
        err("started_at")
    elif finished_at is not None and finished_at < started_at:
        err("window")
    return out


def _bound_ok(c: dict) -> bool:
    lo, hi = c.get("min"), c.get("max")
    if ("min" in c and not is_number(lo)) or ("max" in c and not is_number(hi)):
        return False
    return not (is_number(lo) and is_number(hi) and exact(lo) > exact(hi))


def agent_problems(name: Optional[str], body_spec: Any, sensors: Any, actuators: Any,
                   learning_module: Any, safety_constraints: Any,
                   metadata: Any) -> List[Problem]:
    """``agent_typing`` with error, in order: name (blank), body_spec (given
    but not an object), sensors (given but not an array of non-blank strings)
    — else duplicate_sensor {name} for each repeat —, actuators (likewise,
    duplicate_actuator {name}), learning_module (given but not an object),
    safety (given but not an array) — else safety_constraint {index} for each
    constraint that is not an object naming a declared ``actuator`` with
    ``min``/``max`` (when present) numbers and ``min ≤ max`` —, metadata (not
    an object)."""
    out: List[Problem] = []

    def err(e: str, **kw: Any) -> None:
        out.append(("agent_typing", {"error": e, **kw}))

    if is_blank(name):
        err("name")
    if body_spec is not None and not isinstance(body_spec, dict):
        err("body_spec")
    for field, dup, value in (("sensors", "duplicate_sensor", sensors),
                              ("actuators", "duplicate_actuator", actuators)):
        if value is None:
            continue
        if not is_name_list(value):
            err(field)
        else:
            for s in repeats(value):
                err(dup, name=s)
    if learning_module is not None and not isinstance(learning_module, dict):
        err("learning_module")
    if safety_constraints is not None:
        if not isinstance(safety_constraints, list):
            err("safety")
        else:
            declared = set(actuators) if is_name_list(actuators) else set()
            for i, c in enumerate(safety_constraints):
                if not (isinstance(c, dict) and isinstance(c.get("actuator"), str)
                        and c["actuator"] in declared and _bound_ok(c)):
                    err("safety_constraint", index=i)
    if not isinstance(metadata, dict):
        err("metadata")
    return out
