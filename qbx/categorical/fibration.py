"""
Fibrations and opfibrations (Phase 1, sprint 7).

A fibration is recorded as a functor ``p : E → B`` (object map, morphism map)
between two in-memory categories (``qbx.core.enforced_functor.Category``)
together with registered lifts ``(φ, u)``: a morphism ``φ`` of ``E`` claimed to
be a cartesian lift of the base morphism ``u = p(φ)`` at its target (kind
``"fibration"``) or a cocartesian lift at its source (kind ``"opfibration"``).

The checker reports, with the same reasons and details as migration 010:

    fibration_typing        the functor does not go from E to B
    lift_typing             φ not in E, u not in B, or wrong recorded endpoints
    lift_not_over_base      p(φ) ≠ u   (details.image = p(φ) or None)
    cartesian_existence     φ : a → b over u : x → y, h : z → b, w : p(z) → x with
                            u ∘ w = p(h), but no k : z → a with p(k) = w, φ ∘ k = h
    cartesian_uniqueness    ... more than one such k (details.count)
    cocartesian_existence   the dual for opfibrations (h : a → z, w : y → p(z),
    cocartesian_uniqueness  w ∘ u = p(h), k : b → z with p(k) = w, k ∘ φ = h)
    missing_lift            a base morphism u and an object e over its target
                            (opfibration: source) such that no morphism of E over
                            u ending (starting) at e passes the check

Composites are read with the unit laws for identities and the composition
table otherwise; the universal property is checked against the recorded
morphisms and composites.  This module is the in-memory reference
implementation of the checker migration 010 runs in Postgres (same reasons,
same STRICT / PERMISSIVE modes).

Formal backing (``Formal/Fibration.lean``, registry H-028 – H-030):

* ``isStronglyCartesian_iff_check`` / ``isStronglyCocartesian_iff_check``: the
  check is exactly Mathlib's strongly (co)cartesian morphism;
* ``isFibered_iff_cleavageCheck``: "every ``(u, e)`` has a lift passing the
  check" is exactly ``Functor.IsFibered``;
* ``cartesian_existence_not_sufficient`` / ``cartesian_uniqueness_not_sufficient``:
  both halves of the check are needed;
* ``isStronglyCartesian_star_iff_isIso``: over a one-object base the cartesian
  morphisms are exactly the isomorphisms — so a monoid recorded over the
  terminal base (``monoid_over_point``) has exactly its units as cartesian lifts.
"""

from __future__ import annotations

import itertools
import logging
from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Optional, Tuple

from qbx.categorical.natural_transformation import compose
from qbx.core.enforced_functor import Category, EnforcementMode
from qbx.core.exceptions import QBXError

logger = logging.getLogger(__name__)

Problem = Tuple[str, Dict[str, Any]]

KINDS = ("fibration", "opfibration")

REASONS = (
    "fibration_typing",
    "lift_typing",
    "lift_not_over_base",
    "cartesian_existence",
    "cartesian_uniqueness",
    "cocartesian_existence",
    "cocartesian_uniqueness",
    "missing_lift",
)


class FibrationViolation(QBXError):
    """Raised (STRICT mode) when a fibration check fails."""

    def __init__(self, subject: str, reason: str, details: dict):
        self.subject = subject
        self.reason = reason
        self.details = details
        super().__init__(f"{subject}: {reason} {details}")


@dataclass
class Lift:
    """A registered lift: ``morphism`` of E over ``base``, with the recorded endpoints."""

    morphism: str
    base: str
    source: Optional[str] = None
    target: Optional[str] = None


@dataclass
class Fibration:
    """Recorded data of a (claimed) fibration ``p : total → base``."""

    total: Category
    base: Category
    object_map: Dict[str, str] = field(default_factory=dict)
    morphism_map: Dict[str, str] = field(default_factory=dict)
    kind: str = "fibration"
    lifts: List[Lift] = field(default_factory=list)
    functor: str = "p"
    functor_source: Optional[str] = None   # category ids; None = total / base
    functor_target: Optional[str] = None

    def __post_init__(self) -> None:
        if self.kind not in KINDS:
            raise ValueError(f"kind must be one of {KINDS}")

    # -- recording --------------------------------------------------------
    def register_lift(self, morphism: str, base: str, source: Optional[str] = None,
                      target: Optional[str] = None) -> Lift:
        """Mirror of ``register_cartesian_lift``: refuses ill-formed lifts and
        never replaces an existing one."""
        for lift in self.lifts:
            if lift.morphism == morphism:
                if lift.base != base:
                    raise ValueError(f"{morphism} is already registered over another base morphism")
                return lift
        if morphism not in self.total.morphisms or base not in self.base.morphisms:
            raise KeyError("morphism(s) not found")
        s, t = self.total.morphisms[morphism]
        if (source is not None and source != s) or (target is not None and target != t):
            raise ValueError("source / target are not those of the lift morphism")
        if self.morphism_map.get(morphism) != base:
            raise ValueError("the lift does not lie over the base morphism (p(lift) <> base)")
        lift = Lift(morphism, base, s, t)
        self.lifts.append(lift)
        return lift

    # -- problems ---------------------------------------------------------
    def typing_problems(self) -> List[Problem]:
        src = self.functor_source if self.functor_source is not None else self.total.id
        tgt = self.functor_target if self.functor_target is not None else self.base.id
        if src != self.total.id or tgt != self.base.id:
            return [("fibration_typing", {"functor": self.functor, "total": self.total.id,
                                          "base": self.base.id})]
        return []

    def lift_problems(self, lift: Lift) -> List[Problem]:
        out: List[Problem] = []
        st = self.total.morphisms.get(lift.morphism)
        if (st is None or lift.base not in self.base.morphisms
                or (lift.source, lift.target) != st):
            out.append(("lift_typing", {"lift": lift.morphism, "base": lift.base}))
        image = self.morphism_map.get(lift.morphism)
        if image != lift.base:
            out.append(("lift_not_over_base", {"lift": lift.morphism, "base": lift.base,
                                               "image": image}))
        return out

    def cartesian_problems(self, phi: str, u: str) -> List[Problem]:
        """The (co)cartesian check of ``phi`` over ``u`` (one problem per failing (h, w))."""
        E, B, p = self.total, self.base, self.morphism_map
        if phi not in E.morphisms or u not in B.morphisms:
            return []
        a, b = E.morphisms[phi]
        x, y = B.morphisms[u]
        out: List[Problem] = []
        fib = self.kind == "fibration"
        for h, (hs, ht) in E.morphisms.items():
            if (ht if fib else hs) != (b if fib else a):
                continue
            ph = p.get(h)
            if ph is None:
                continue
            for w, (ws, wt) in B.morphisms.items():
                if fib:
                    if wt != x or compose(B, w, u) != ph:
                        continue
                    ks = [k for k, (ks_, kt) in E.morphisms.items()
                          if ks_ == hs and kt == a and p.get(k) == w and compose(E, k, phi) == h]
                else:
                    if ws != y or compose(B, u, w) != ph:
                        continue
                    ks = [k for k, (ks_, kt) in E.morphisms.items()
                          if ks_ == b and kt == ht and p.get(k) == w and compose(E, phi, k) == h]
                details = {"lift": phi, "base": u, "h": h, "w": w}
                prefix = "cartesian" if fib else "cocartesian"
                if not ks:
                    out.append((f"{prefix}_existence", details))
                elif len(ks) > 1:
                    out.append((f"{prefix}_uniqueness", {**details, "count": len(ks)}))
        return out

    def is_cartesian(self, phi: str, u: Optional[str] = None) -> bool:
        u = self.morphism_map.get(phi) if u is None else u
        return u is not None and not self.cartesian_problems(phi, u)

    def has_lift(self, u: str, e: str) -> bool:
        fib = self.kind == "fibration"
        for m, (s, t) in self.total.morphisms.items():
            if (t if fib else s) == e and self.morphism_map.get(m) == u \
                    and not self.cartesian_problems(m, u):
                return True
        return False

    def problems(self) -> List[Problem]:
        out = list(self.typing_problems())
        for lift in self.lifts:
            lp = self.lift_problems(lift)
            out.extend(lp)
            if not lp:
                out.extend(self.cartesian_problems(lift.morphism, lift.base))
        fib = self.kind == "fibration"
        for u, (x, y) in self.base.morphisms.items():
            for e in self.total.objects:
                if self.object_map.get(e) == (y if fib else x) and not self.has_lift(u, e):
                    out.append(("missing_lift", {"base": u, "object": e}))
        return out

    def is_valid(self) -> bool:
        return not self.problems()


class FibrationChecker:
    """Runs the checks, logging every problem and raising in STRICT mode."""

    def __init__(self, mode: Optional[EnforcementMode] = None):
        self.mode = mode or EnforcementMode.from_env()
        self.violations: List[Problem] = []

    def check(self, fib: Fibration, subject: str = "fibration") -> bool:
        problems = fib.problems()
        for reason, details in problems:
            logger.warning("%s: %s %s", subject, reason, details)
            self.violations.append((reason, details))
        if problems and self.mode == EnforcementMode.STRICT:
            reason, details = problems[0]
            raise FibrationViolation(subject, reason, details)
        return not problems


# ---------------------------------------------------------------------------
# Builders
# ---------------------------------------------------------------------------
def category(cid: str, objects: Iterable[str], morphisms: Dict[str, Tuple[str, str]],
             compositions: Dict[Tuple[str, str], str]) -> Category:
    """A category with identities ``id_<o>`` for every object.

    ``compositions[(g, f)] = h`` records ``h = g ∘ f`` (``f`` first, the
    convention of the composition table of migration 001).
    """
    cat = Category(id=cid, name=cid)
    for o in objects:
        cat.add_object(o, o)
        cat.add_identity(o, f"id_{o}")
    for m, (s, t) in morphisms.items():
        cat.add_morphism(m, s, t)
    for (g, f), h in compositions.items():
        cat.add_composition(f, g, h)
    return cat


def monoid_over_point(elements: Iterable[str], unit: str,
                      mul: Dict[Tuple[str, str], str]) -> Fibration:
    """A monoid as a one-object category ``*`` (elements as morphisms, ``unit``
    the identity, ``mul[(g, f)] = g ∘ f``) over the one-object base ``pt``,
    every element registered as a lift of ``id_pt``.  By
    ``isStronglyCartesian_star_iff_isIso`` the cartesian elements are exactly
    the units of the monoid."""
    elems = [e for e in elements if e != unit]
    E = Category(id="E", name="E")
    E.add_object("*", "*")
    E.add_identity("*", unit)
    for e in elems:
        E.add_morphism(e, "*", "*")
    for (g, f), h in mul.items():
        if g != unit and f != unit:
            E.add_composition(f, g, h)
    B = category("B", ["pt"], {}, {})
    fib = Fibration(E, B, {"*": "pt"}, {m: "id_pt" for m in E.morphisms})
    for e in [unit, *elems]:
        fib.register_lift(e, "id_pt")
    return fib


def units(elements: Iterable[str], unit: str, mul: Dict[Tuple[str, str], str]) -> List[str]:
    elems = list(elements)
    return [a for a in elems
            if any(mul.get((a, b), b if a == unit else a if b == unit else None) == unit
                   and mul.get((b, a), a if b == unit else b if a == unit else None) == unit
                   for b in elems)]


def all_monoids(elements: List[str], unit: str):
    """Every monoid structure on ``elements`` with identity ``unit`` (as a dict
    ``(g, f) -> g ∘ f``); feasible for 3 elements (81 tables)."""
    others = [e for e in elements if e != unit]
    pairs = list(itertools.product(others, repeat=2))
    for values in itertools.product(elements, repeat=len(pairs)):
        mul = dict(zip(pairs, values))

        def m(a, b):
            if a == unit:
                return b
            if b == unit:
                return a
            return mul[(a, b)]

        if all(m(m(a, b), c) == m(a, m(b, c)) for a in elements for b in elements for c in elements):
            yield {(a, b): m(a, b) for a in elements for b in elements}
