"""Measurement contracts, bundles, uncertainty types and validations
(migration 016).

**Uncertainty types** (``uncertainty_type``).  A descriptor is a JSON object
whose ``kind`` says how an observation's ``uncertainty`` ``u`` is read:

* ``interval`` — ``u`` is the half-width of an interval that contains the true
  value;
* ``uniform`` — ``u`` is the half-width of the support of a uniform
  distribution;
* ``gaussian`` — ``u`` is a standard uncertainty; the descriptor's
  ``coverage_factor`` ``k > 0`` gives the half-width ``k·u`` of the coverage
  interval.

So every type has a *half-width factor* (1, 1 or ``k``); a contract without an
uncertainty type uses 1.

**Contracts** (``measurement_contract``).  ``body`` may bound the observable
(``min``, ``max``, numbers, ``min ≤ max``) and fix its ``unit`` (non-blank);
``expected_precision`` may give ``absolute`` and ``relative`` (numbers ≥ 0);
``validation_tests`` is a JSON array of distinct test names:

* ``range_check`` — the coverage interval ``[v − h, v + h]`` (``h`` = factor ×
  ``u``) lies within the bounds.  For ``h ≥ 0`` this holds exactly when every
  value the measurement allows is within the bounds (``Formal/Empirical.lean``:
  ``rangeOk_iff``);
* ``precision_check`` — ``u ≤ absolute + relative·|v|`` (missing parts are 0);
* ``unit_check`` — the observation's ``unit`` is the contract's.

**Bundles** (``measurement_bundle``).  ``observations`` is a non-empty JSON
array of objects with a number ``value``, optionally an ``uncertainty`` (a
number ≥ 0; 0 when missing) and a ``unit`` (non-blank).

**Validations** (``measurement_validation``, append-only).  A validation of a
bundle against a contract records ``ok`` and ``report``: the failures
``{"test", "index"}`` in the contract's test order, then by observation index;
``ok`` is true exactly when the report is empty (``ok_iff_all_pass``).  A
bundle's ``validated`` / ``validation_report`` must be those of its latest
validation (``false`` / ``NULL`` when it has none).
"""

from __future__ import annotations

from fractions import Fraction
from typing import Any, Dict, List, Optional, Sequence, Tuple

from qbx.empirical.values import (
    Problem,
    exact,
    is_blank,
    is_name,
    is_number,
    is_semver,
)

TESTS = ("range_check", "precision_check", "unit_check")
UNCERTAINTY_KINDS = ("interval", "uniform", "gaussian")


# ---------------------------------------------------------------------------
# Uncertainty types
# ---------------------------------------------------------------------------
def uncertainty_problems(name: Optional[str], descriptor: Any) -> List[Problem]:
    """``uncertainty_typing`` with error, in order: name (blank), descriptor
    (not an object), kind (not one of the three), coverage_factor (gaussian
    without a number > 0)."""
    out: List[Problem] = []
    if is_blank(name):
        out.append(("uncertainty_typing", {"error": "name"}))
    if not isinstance(descriptor, dict):
        out.append(("uncertainty_typing", {"error": "descriptor"}))
        return out
    kind = descriptor.get("kind")
    if not isinstance(kind, str) or kind not in UNCERTAINTY_KINDS:
        out.append(("uncertainty_typing", {"error": "kind"}))
    elif kind == "gaussian":
        k = descriptor.get("coverage_factor")
        if not is_number(k) or exact(k) <= 0:
            out.append(("uncertainty_typing", {"error": "coverage_factor"}))
    return out


def half_width_factor(descriptor: Optional[dict]) -> Fraction:
    """1 without a type or for interval / uniform; the coverage factor for
    gaussian.  (Only for descriptors without problems.)"""
    if descriptor is None or descriptor.get("kind") != "gaussian":
        return Fraction(1)
    return exact(descriptor["coverage_factor"])


# ---------------------------------------------------------------------------
# Contracts
# ---------------------------------------------------------------------------
def _has_unit(body: Any) -> bool:
    return isinstance(body, dict) and is_name(body.get("unit"))


def contract_problems(name: Optional[str], observable: Optional[str],
                      version: Optional[str], body: Any, precision: Any,
                      tests: Any) -> List[Problem]:
    """``contract_typing`` with error, in order: name, observable (blank),
    version (not ``MAJOR.MINOR.PATCH``), body (not an object) — else bounds
    (``min``/``max`` present but not numbers, or ``min > max``) and unit
    (present but not a non-blank string) —, precision (not an object, or
    ``absolute``/``relative`` present but not numbers ≥ 0), tests (not an array
    of strings) — else, for each test in order, test {test} (unknown) or
    duplicate_test {test} (repeated) —, unit_check (tested without a unit),
    precision_check (tested without ``absolute`` or ``relative``)."""
    out: List[Problem] = []
    if is_blank(name):
        out.append(("contract_typing", {"error": "name"}))
    if is_blank(observable):
        out.append(("contract_typing", {"error": "observable"}))
    if not is_semver(version):
        out.append(("contract_typing", {"error": "version"}))
    if not isinstance(body, dict):
        out.append(("contract_typing", {"error": "body"}))
    else:
        lo, hi = body.get("min"), body.get("max")
        bad = (("min" in body and not is_number(lo)) or ("max" in body and not is_number(hi))
               or (is_number(lo) and is_number(hi) and exact(lo) > exact(hi)))
        if bad:
            out.append(("contract_typing", {"error": "bounds"}))
        if "unit" in body and not is_name(body["unit"]):
            out.append(("contract_typing", {"error": "unit"}))
    precision_ok = isinstance(precision, dict) and all(
        k not in precision or (is_number(precision[k]) and exact(precision[k]) >= 0)
        for k in ("absolute", "relative"))
    if not precision_ok:
        out.append(("contract_typing", {"error": "precision"}))
    if not (isinstance(tests, list) and all(isinstance(t, str) for t in tests)):
        out.append(("contract_typing", {"error": "tests"}))
        tests = []
    seen = set()
    for t in tests:
        if t not in TESTS:
            out.append(("contract_typing", {"error": "test", "test": t}))
        elif t in seen:
            out.append(("contract_typing", {"error": "duplicate_test", "test": t}))
        seen.add(t)
    if "unit_check" in tests and not _has_unit(body):
        out.append(("contract_typing", {"error": "unit_check"}))
    if "precision_check" in tests and not (
            isinstance(precision, dict) and ("absolute" in precision or "relative" in precision)):
        out.append(("contract_typing", {"error": "precision_check"}))
    return out


# ---------------------------------------------------------------------------
# Bundles
# ---------------------------------------------------------------------------
def bundle_problems(observations: Any, context: Any, provenance: Any) -> List[Problem]:
    """``bundle_typing`` with error, in order: observations (not a non-empty
    array) — else, for each observation in order, observation {index, field}
    with field object (not an object), else value (not a number), uncertainty
    (present but not a number ≥ 0), unit (present but not a non-blank string)
    —, context, provenance (not objects)."""
    out: List[Problem] = []
    if not isinstance(observations, list) or not observations:
        out.append(("bundle_typing", {"error": "observations"}))
    else:
        for i, o in enumerate(observations):
            def bad(field: str) -> None:
                out.append(("bundle_typing", {"error": "observation", "index": i, "field": field}))
            if not isinstance(o, dict):
                bad("object")
                continue
            if not is_number(o.get("value")):
                bad("value")
            if "uncertainty" in o and not (is_number(o["uncertainty"])
                                           and exact(o["uncertainty"]) >= 0):
                bad("uncertainty")
            if "unit" in o and not is_name(o["unit"]):
                bad("unit")
    if not isinstance(context, dict):
        out.append(("bundle_typing", {"error": "context"}))
    if not isinstance(provenance, dict):
        out.append(("bundle_typing", {"error": "provenance"}))
    return out


# ---------------------------------------------------------------------------
# Validation
# ---------------------------------------------------------------------------
def range_ok(lo: Optional[Fraction], hi: Optional[Fraction], h: Fraction, v: Fraction) -> bool:
    """``[v − h, v + h]`` lies within the (optional) bounds (``rangeOk``)."""
    return (lo is None or lo <= v - h) and (hi is None or v + h <= hi)


def precision_ok(absolute: Fraction, relative: Fraction, u: Fraction, v: Fraction) -> bool:
    return u <= absolute + relative * abs(v)


def validation_report(body: dict, precision: dict, tests: Sequence[str],
                      factor: Fraction, observations: Sequence[dict]) -> List[Dict[str, Any]]:
    """The failures of a bundle against a contract (both without problems)."""
    lo = exact(body["min"]) if "min" in body else None
    hi = exact(body["max"]) if "max" in body else None
    absolute = exact(precision.get("absolute", 0))
    relative = exact(precision.get("relative", 0))
    report: List[Dict[str, Any]] = []
    for t in tests:
        for i, o in enumerate(observations):
            v = exact(o["value"])
            u = exact(o.get("uncertainty", 0))
            if t == "range_check":
                passed = range_ok(lo, hi, factor * u, v)
            elif t == "precision_check":
                passed = precision_ok(absolute, relative, u, v)
            else:
                passed = o.get("unit") == body.get("unit")
            if not passed:
                report.append({"test": t, "index": i})
    return report


def validate(contract: dict, bundle: dict,
             uncertainty: Optional[dict] = None) -> Tuple[bool, List[Dict[str, Any]]]:
    """``(ok, report)`` of a bundle (keys observations) against a contract
    (keys body, expected_precision, validation_tests) whose uncertainty type
    has descriptor ``uncertainty`` (``None``: no type)."""
    report = validation_report(contract["body"], contract["expected_precision"],
                               contract["validation_tests"], half_width_factor(uncertainty),
                               bundle["observations"])
    return (not report, report)


def contract_fields_problems(contract: dict) -> List[Problem]:
    return contract_problems(contract.get("name"), contract.get("observable_id"),
                             contract.get("version"), contract.get("body"),
                             contract.get("expected_precision"),
                             contract.get("validation_tests"))


def bundle_fields_problems(bundle: dict) -> List[Problem]:
    return bundle_problems(bundle.get("observations"), bundle.get("context"),
                           bundle.get("provenance"))


def validation_problems(recorded_ok: Any, recorded_report: Any,
                        bundle: Optional[dict], contract: Optional[dict],
                        uncertainty: Optional[Tuple[Optional[str], Any]] = None) -> List[Problem]:
    """``empirical_validation_problems``.

    ``bundle``/``contract``: the rows (``None``: missing); ``uncertainty``:
    ``(name, descriptor)`` of the contract's uncertainty type, ``None`` when it
    has none.  Problems, in order: validation_typing {error ∈ bundle, contract
    (missing), ok (NULL), report (not an array)}; validation_input {error ∈
    bundle, contract, uncertainty} (that row has problems); and, when there is
    none of these, validation_result {recorded, computed} when the recorded ok
    or report is not the computed one.
    """
    out: List[Problem] = []
    if bundle is None:
        out.append(("validation_typing", {"error": "bundle"}))
    if contract is None:
        out.append(("validation_typing", {"error": "contract"}))
    if recorded_ok is None:
        out.append(("validation_typing", {"error": "ok"}))
    if not isinstance(recorded_report, list):
        out.append(("validation_typing", {"error": "report"}))
    if bundle is not None and bundle_fields_problems(bundle):
        out.append(("validation_input", {"error": "bundle"}))
    if contract is not None and contract_fields_problems(contract):
        out.append(("validation_input", {"error": "contract"}))
    if uncertainty is not None and uncertainty_problems(*uncertainty):
        out.append(("validation_input", {"error": "uncertainty"}))
    if out:
        return out
    ok, report = validate(contract, bundle, uncertainty[1] if uncertainty else None)
    if recorded_ok != ok or recorded_report != report:
        out.append(("validation_result", {"recorded": recorded_ok, "computed": ok}))
    return out


def bundle_validated_problems(validated: Any, validation_report_: Any,
                              latest: Optional[Tuple[Any, Any]]) -> List[Problem]:
    """``bundle_validated`` {field ∈ validated, report}: the bundle's flag or
    report differs from its latest validation's ``(ok, report)`` (``False`` /
    ``None`` without a validation)."""
    ok, report = latest if latest is not None else (False, None)
    out: List[Problem] = []
    if validated != ok:
        out.append(("bundle_validated", {"field": "validated"}))
    if validation_report_ != report:
        out.append(("bundle_validated", {"field": "report"}))
    return out
