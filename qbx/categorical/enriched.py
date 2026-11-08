"""
Enriched categories (Phase 1, sprint 5).

An enriched category records, over a set of objects, one hom-value per ordered
pair.  Two families are supported, exactly as in migration 008.

**Quantale enrichment** (kinds ``metric``, ``ordered``, ``quantale``).  The
base V is a commutative monoid (⊗, unit) with a compatible order ≤_V; the
values form a V-category iff

    unit law          unit ≤_V h(x, x)               for every object x
    composition law   h(x, y) ⊗ h(y, z) ≤_V h(x, z)  for all objects x, y, z

A missing hom is the bottom of V (distance ∞, truth value 0).

    quantale      carrier   ≤_V  ⊗    unit  missing  value key
    lawvere       [0, ∞]    ≥    +    0     ∞        distance | value
    ultrametric   [0, ∞]    ≥    max  0     ∞        distance | value
    boolean       {0, 1}    ≤    min  1     0        holds | value
    goedel        [0, 1]    ≤    min  1     0        value
    product       [0, 1]    ≤    ×    1     0        value

``metric`` = lawvere, ``ordered`` = boolean.

**Probabilistic** (kind ``probabilistic``).  Each value is a finite stochastic
kernel ``{"kernel": {s: {t: p}}}``; the kernels must be stochastic, share one
state space per source object, charge only states of their target, be the
identity on recorded loops, and satisfy Chapman–Kolmogorov
``h(x, z) = h(x, y) ; h(y, z)`` on every recorded triple.

Arithmetic is exact (``fractions.Fraction``; floats are read through their
shortest decimal representation, as the database reads JSON numbers), with an
optional tolerance.  This module is the in-memory reference implementation of
the checker migration 008 runs in Postgres (same violation reasons, same
STRICT / PERMISSIVE modes).

Formal backing (``Formal/Enriched.lean``, registry H-022 – H-024):

* ``exists_enriched_iff``: the two laws are sound and complete for
  enrichment in an ordered commutative monoid (a thin monoidal category);
* ``lawvere_enriched_iff``: the metric case — d(x, x) = 0 and the triangle
  inequality; ``triangle_iff_finite``: only finite first and second legs need
  checking;
* ``unit_law_not_sufficient``, ``composition_law_not_sufficient``: both laws
  are needed.
"""

from __future__ import annotations

import logging
import math
from dataclasses import dataclass, field
from decimal import Decimal
from fractions import Fraction
from typing import Any, Callable, Dict, List, Optional, Tuple, Union

from qbx.core.enforced_functor import EnforcementMode
from qbx.core.exceptions import QBXError

logger = logging.getLogger(__name__)

Number = Union[Fraction, float]          # float only for math.inf
INF: float = math.inf
Kernel = Dict[str, Dict[str, Fraction]]
Problem = Tuple[str, Dict[str, Any]]

KINDS = ("metric", "probabilistic", "ordered", "quantale")


class EnrichedViolation(QBXError):
    """Raised (STRICT mode) when an enriched-category check fails."""

    def __init__(self, subject: str, reason: str, details: dict):
        self.subject = subject
        self.reason = reason
        self.details = details
        super().__init__(f"{subject}: {reason} {details}")


# ---------------------------------------------------------------------------
# Quantales
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Quantale:
    name: str
    reversed: bool                       # ≤_V is ≥ on the carrier
    tensor: Callable[[Number, Number], Number]
    unit: Number
    bottom: Number                       # value of a missing hom
    keys: Tuple[str, ...]                # accepted value keys, in priority order

    def leq(self, a: Number, b: Number, tol: Fraction = Fraction(0)) -> bool:
        """``a ≤_V b``, relaxed by ``tol``."""
        return a + tol >= b if self.reversed else a <= b + tol

    def in_range(self, v: Number) -> bool:
        if self.reversed:
            return v >= 0
        if self.name == "boolean":
            return v in (0, 1)
        return 0 <= v <= 1


QUANTALES: Dict[str, Quantale] = {
    "lawvere": Quantale("lawvere", True, lambda a, b: a + b, Fraction(0), INF, ("distance", "value")),
    "ultrametric": Quantale("ultrametric", True, max, Fraction(0), INF, ("distance", "value")),
    "boolean": Quantale("boolean", False, min, Fraction(1), Fraction(0), ("holds", "value")),
    "goedel": Quantale("goedel", False, min, Fraction(1), Fraction(0), ("value",)),
    "product": Quantale("product", False, lambda a, b: a * b, Fraction(1), Fraction(0), ("value",)),
}


def quantale_of(kind: str, quantale: Optional[str] = None) -> Optional[Quantale]:
    """The quantale of an enrichment kind (``None`` for ``probabilistic``)."""
    if kind not in KINDS:
        raise ValueError(f"unknown enrichment kind {kind!r}")
    if kind == "metric":
        return QUANTALES["lawvere"]
    if kind == "ordered":
        return QUANTALES["boolean"]
    if kind == "quantale":
        if quantale not in QUANTALES:
            raise ValueError(f"unknown quantale {quantale!r}")
        return QUANTALES[quantale]
    return None


def to_number(x: Any) -> Optional[Fraction]:
    """An exact number from a JSON / Python number (``None`` if not a number)."""
    if isinstance(x, bool):
        return None
    if isinstance(x, (int, Fraction)):
        return Fraction(x)
    if isinstance(x, Decimal):
        return Fraction(x) if x.is_finite() else None
    if isinstance(x, float):
        return Fraction(repr(x)) if math.isfinite(x) else None
    return None


def parse_value(q: Quantale, value: Any) -> Optional[Number]:
    """The hom-value as a number, or ``None`` if malformed for ``q``."""
    if not isinstance(value, dict):
        return None
    j = next((value[k] for k in q.keys if k in value and value[k] is not None), None)
    if j is None:
        return None
    if isinstance(j, bool):
        return (Fraction(1) if j else Fraction(0)) if q.name == "boolean" else None
    if isinstance(j, float) and j == INF and q.reversed:
        return INF
    if isinstance(j, str):
        return INF if q.reversed and j.lower() in ("infinity", "inf") else None
    return to_number(j)


# ---------------------------------------------------------------------------
# Finite stochastic kernels
# ---------------------------------------------------------------------------
def parse_kernel(value: Any) -> Optional[Kernel]:
    """The kernel of a hom-value ``{"kernel": {s: {t: p}}}`` or ``None``."""
    if not isinstance(value, dict) or not isinstance(value.get("kernel"), dict):
        return None
    k = value["kernel"]
    if not k:
        return None
    out: Kernel = {}
    for s, row in k.items():
        if not isinstance(row, dict):
            return None
        out[s] = {}
        for t, p in row.items():
            n = to_number(p)
            if n is None:
                return None
            out[s][t] = n
    return out


def kernel_bad_rows(k: Kernel, tol: Fraction = Fraction(0)) -> List[str]:
    """Rows that are not probability distributions."""
    return sorted(
        s for s, row in k.items()
        if any(p < 0 for p in row.values()) or abs(sum(row.values(), Fraction(0)) - 1) > tol
    )


def kernel_unsupported(f: Kernel, g: Kernel) -> List[str]:
    """States charged by ``f`` that are not rows of ``g``."""
    return sorted({t for row in f.values() for t, p in row.items() if p != 0 and t not in g})


def compose_kernels(f: Kernel, g: Kernel) -> Kernel:
    """``f ; g`` (f first): ``(f ; g)(s, u) = Σ_t f(s, t) g(t, u)``."""
    out: Kernel = {}
    for s, row in f.items():
        acc: Dict[str, Fraction] = {}
        for t, p in row.items():
            for u, q in g.get(t, {}).items():
                acc[u] = acc.get(u, Fraction(0)) + p * q
        out[s] = acc
    return out


def kernels_equal(a: Kernel, b: Kernel, tol: Fraction = Fraction(0)) -> bool:
    if set(a) != set(b):
        return False
    for s in a:
        for t in set(a[s]) | set(b[s]):
            if abs(a[s].get(t, Fraction(0)) - b[s].get(t, Fraction(0))) > tol:
                return False
    return True


def identity_kernel(states) -> Kernel:
    return {s: {s: Fraction(1)} for s in states}


# ---------------------------------------------------------------------------
# Enriched categories
# ---------------------------------------------------------------------------
@dataclass
class EnrichedCategory:
    """Hom-values over ``objects``; ``homs[(x, y)]`` is the JSON-like value."""

    objects: List[str]
    kind: str
    homs: Dict[Tuple[str, str], Any] = field(default_factory=dict)
    quantale: Optional[str] = None
    tolerance: Fraction = Fraction(0)

    def __post_init__(self) -> None:
        self.q = quantale_of(self.kind, self.quantale)
        self.tolerance = to_number(self.tolerance) or Fraction(0)

    # -- single homs ------------------------------------------------------
    def hom_problems(self, key: Tuple[str, str]) -> List[Problem]:
        x, y = key
        value = self.homs[key]
        out: List[Problem] = []
        if x not in self.objects or y not in self.objects:
            out.append(("foreign_object", {"source": x, "target": y}))
        if self.q is None:
            k = parse_kernel(value)
            if k is None:
                out.append(("malformed_value", {"source": x, "target": y, "value": value}))
            elif kernel_bad_rows(k, self.tolerance):
                out.append(("not_stochastic", {"source": x, "target": y,
                                               "rows": kernel_bad_rows(k, self.tolerance)}))
        else:
            v = parse_value(self.q, value)
            if v is None:
                out.append(("malformed_value", {"source": x, "target": y, "value": value}))
            elif not self.q.in_range(v):
                out.append(("out_of_range", {"source": x, "target": y, "value": v}))
        return out

    def values(self) -> Dict[Tuple[str, str], Number]:
        """Well-formed quantale values."""
        assert self.q is not None
        return {key: parse_value(self.q, v) for key, v in self.homs.items()
                if not self.hom_problems(key)}

    def kernels(self) -> Dict[Tuple[str, str], Kernel]:
        """Well-formed stochastic kernels."""
        return {key: parse_kernel(v) for key, v in self.homs.items()
                if not self.hom_problems(key)}

    # -- laws -------------------------------------------------------------
    def problems(self) -> List[Problem]:
        out: List[Problem] = []
        for key in self.homs:
            out.extend(self.hom_problems(key))
        if self.q is not None:
            out.extend(self._quantale_problems())
        else:
            out.extend(self._kernel_problems())
        return out

    def _quantale_problems(self) -> List[Problem]:
        q, tol, hv = self.q, self.tolerance, self.values()
        out: List[Problem] = []
        for x in self.objects:
            v = hv.get((x, x), q.bottom)
            if not q.leq(q.unit, v, tol):
                out.append(("unit_law", {"object": x, "value": v, "missing": (x, x) not in hv}))
        for (x, y), a in hv.items():
            for (y2, z), b in hv.items():
                if y2 != y:
                    continue
                through = q.tensor(a, b)
                if through == q.bottom:
                    continue
                direct = hv.get((x, z), q.bottom)
                if not q.leq(through, direct, tol):
                    out.append(("composition_law", {"source": x, "middle": y, "target": z,
                                                    "direct": direct, "through": through,
                                                    "missing": (x, z) not in hv}))
        return out

    def _kernel_problems(self) -> List[Problem]:
        tol, hk = self.tolerance, self.kernels()
        out: List[Problem] = []
        keys = sorted(hk)
        for i, (x, y) in enumerate(keys):
            for (x2, y2) in keys[i + 1:]:
                if x2 == x and set(hk[(x, y)]) != set(hk[(x2, y2)]):
                    out.append(("state_space", {"object": x, "hom": (x, y), "other_hom": (x2, y2)}))
        for (x, y), f in hk.items():
            for (y2, z), g in hk.items():
                if y2 == y and kernel_unsupported(f, g):
                    out.append(("kernel_support", {"hom": (x, y), "object": y,
                                                   "states": kernel_unsupported(f, g)}))
                    break
        for (x, y), k in hk.items():
            if x == y and not kernels_equal(k, identity_kernel(k), tol):
                out.append(("identity_kernel", {"hom": (x, y), "object": x}))
        for (x, y), f in hk.items():
            for (y2, z), g in hk.items():
                if y2 != y or (x, z) not in hk or kernel_unsupported(f, g):
                    continue
                through = compose_kernels(f, g)
                if not kernels_equal(through, hk[(x, z)], tol):
                    out.append(("chapman_kolmogorov", {"source": x, "middle": y, "target": z,
                                                       "through": through}))
        return out

    def composition_problems(self, left: Tuple[str, str], right: Tuple[str, str],
                             composed: Any) -> List[Problem]:
        """Problems of a recorded composite ``left ∘ right`` (``right`` first)."""
        if (left not in self.homs or right not in self.homs or right[1] != left[0]):
            return [("composition_typing", {"left": left, "right": right})]
        if self.hom_problems(left) or self.hom_problems(right):
            return [("composition_typing", {"left": left, "right": right, "invalid_factor": True})]
        x, y, z = right[0], right[1], left[1]
        tol = self.tolerance
        out: List[Problem] = []
        if self.q is None:
            f, g = parse_kernel(self.homs[right]), parse_kernel(self.homs[left])
            if kernel_unsupported(f, g):
                return [("kernel_support", {"hom": right, "object": y,
                                            "states": kernel_unsupported(f, g)})]
            expected = compose_kernels(f, g)
            c = parse_kernel(composed)
            if c is None or not kernels_equal(c, expected, tol):
                out.append(("composition_value", {"recorded": composed, "expected": expected}))
            direct = parse_kernel(self.homs.get((x, z)))
            if direct is not None and not kernels_equal(direct, expected, tol):
                out.append(("chapman_kolmogorov", {"source": x, "middle": y, "target": z,
                                                   "through": expected}))
            return out
        q = self.q
        through = q.tensor(parse_value(q, self.homs[right]), parse_value(q, self.homs[left]))
        c = parse_value(q, composed)
        if c is None or (c != through and (c == INF or through == INF or abs(c - through) > tol)):
            out.append(("composition_value", {"recorded": composed, "expected": through}))
        direct = parse_value(q, self.homs.get((x, z))) if (x, z) in self.homs else None
        if through != q.bottom and not q.leq(through, q.bottom if direct is None else direct, tol):
            out.append(("composition_law", {"source": x, "middle": y, "target": z,
                                            "direct": q.bottom if direct is None else direct,
                                            "through": through, "missing": direct is None}))
        return out

    def is_enriched(self) -> bool:
        return not self.problems()


class EnrichedChecker:
    """Runs the checks, logging every problem and raising in STRICT mode."""

    def __init__(self, mode: Optional[EnforcementMode] = None):
        self.mode = mode or EnforcementMode.from_env()
        self.violations: List[Problem] = []

    def _report(self, subject: str, problems: List[Problem]) -> bool:
        for reason, details in problems:
            logger.warning("%s: %s %s", subject, reason, details)
            self.violations.append((reason, details))
        if problems and self.mode == EnforcementMode.STRICT:
            reason, details = problems[0]
            raise EnrichedViolation(subject, reason, details)
        return not problems

    def check(self, ec: EnrichedCategory, subject: str = "enriched category") -> bool:
        return self._report(subject, ec.problems())

    def check_composition(self, ec: EnrichedCategory, left, right, composed,
                          subject: str = "enriched composition") -> bool:
        return self._report(subject, ec.composition_problems(left, right, composed))
