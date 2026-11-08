"""Finite direct mechanisms and their incentive claims (migration 016).

A ``mechanism_spec`` describes a direct mechanism for one agent:

* ``types`` — the agent's possible types (a non-empty array of distinct
  non-blank strings); ``outcomes`` likewise;
* ``allocation`` — an object mapping every type to an outcome (what the
  mechanism does when that type is reported);
* ``payment`` — an object mapping every type to a number (what the agent pays
  when it is reported);
* ``valuation`` — an object mapping every type to an object mapping every
  outcome to a number (what that type values the outcome at).

The utility of type ``t`` reporting ``r`` is
``valuation[t][allocation[r]] − payment[r]``.  ``incentive_constraints`` may
claim ``"ic": true`` (incentive compatibility: no type gains by misreporting)
and ``"ir": true`` (individual rationality: truthful utility ≥ 0).  Every claim
is checked; an unclaimed property is not.  ``Formal/Empirical.lean`` shows the
checks are exactly IC and IR (``icFailures_eq_nil_iff``,
``irFailures_eq_nil_iff``) and that an IC mechanism is weakly monotone and
its payment differences are pinned between valuation differences
(``ic_weak_monotone``, ``ic_payment_bounds``, ``ic_single_parameter_monotone``).
"""

from __future__ import annotations

from fractions import Fraction
from typing import Any, List, Optional

from qbx.empirical.values import Problem, as_json_number, exact, is_blank, is_name_list, is_number


def _names(x: Any) -> bool:
    return is_name_list(x) and len(x) > 0 and len(set(x)) == len(x)


def _keyed(x: Any, keys: List[str]) -> bool:
    return isinstance(x, dict) and set(x) == set(keys)


def spec_problems(spec: Any) -> List[Problem]:
    """``mechanism_typing`` for the spec: spec (not an object) — else types,
    outcomes (not non-empty arrays of distinct non-blank strings) and, when
    both are fine, allocation (not every type to an outcome), payment (not
    every type to a number), valuation (not every type to an object of every
    outcome to a number)."""
    if not isinstance(spec, dict):
        return [("mechanism_typing", {"error": "spec"})]
    out: List[Problem] = []
    types, outcomes = spec.get("types"), spec.get("outcomes")
    if not _names(types):
        out.append(("mechanism_typing", {"error": "types"}))
    if not _names(outcomes):
        out.append(("mechanism_typing", {"error": "outcomes"}))
    if out:
        return out
    alloc, pay, val = spec.get("allocation"), spec.get("payment"), spec.get("valuation")
    if not (_keyed(alloc, types) and all(isinstance(alloc[t], str) and alloc[t] in outcomes
                                         for t in types)):
        out.append(("mechanism_typing", {"error": "allocation"}))
    if not (_keyed(pay, types) and all(is_number(pay[t]) for t in types)):
        out.append(("mechanism_typing", {"error": "payment"}))
    if not (_keyed(val, types) and all(_keyed(val[t], outcomes)
                                       and all(is_number(val[t][o]) for o in outcomes)
                                       for t in types)):
        out.append(("mechanism_typing", {"error": "valuation"}))
    return out


def utility(spec: dict, t: str, r: str) -> Fraction:
    """Utility of type ``t`` reporting ``r``."""
    return exact(spec["valuation"][t][spec["allocation"][r]]) - exact(spec["payment"][r])


def ic_failures(spec: dict) -> List[Problem]:
    """``mechanism_ic`` {type, report, gain} for every type and misreport (in
    types order) that gains (``gain`` = utility of the misreport − truthful
    utility > 0)."""
    out: List[Problem] = []
    for t in spec["types"]:
        truthful = utility(spec, t, t)
        for r in spec["types"]:
            gain = utility(spec, t, r) - truthful
            if r != t and gain > 0:
                out.append(("mechanism_ic", {"type": t, "report": r, "gain": as_json_number(gain)}))
    return out


def ir_failures(spec: dict) -> List[Problem]:
    """``mechanism_ir`` {type, utility} for every type whose truthful utility
    is negative."""
    out: List[Problem] = []
    for t in spec["types"]:
        u = utility(spec, t, t)
        if u < 0:
            out.append(("mechanism_ir", {"type": t, "utility": as_json_number(u)}))
    return out


def mechanism_problems(name: Optional[str], spec: Any, constraints: Any,
                       metadata: Any) -> List[Problem]:
    """``empirical_mechanism_problems``: ``mechanism_typing`` with error, in
    order, name (blank), the spec errors (:func:`spec_problems`), constraints
    (given but not an object, or ``ic``/``ir`` present but not booleans),
    metadata (not an object); when there is no typing problem, the IC failures
    if ``ic`` is claimed, then the IR failures if ``ir`` is claimed."""
    out: List[Problem] = []
    if is_blank(name):
        out.append(("mechanism_typing", {"error": "name"}))
    out += spec_problems(spec)
    if constraints is not None and not (
            isinstance(constraints, dict)
            and all(k not in constraints or isinstance(constraints[k], bool) for k in ("ic", "ir"))):
        out.append(("mechanism_typing", {"error": "constraints"}))
    if not isinstance(metadata, dict):
        out.append(("mechanism_typing", {"error": "metadata"}))
    if out:
        return out
    claims = constraints or {}
    if claims.get("ic") is True:
        out += ic_failures(spec)
    if claims.get("ir") is True:
        out += ir_failures(spec)
    return out
