"""
Limits and colimits (Phase 1, sprint 4).

A diagram in a category C is a graph: nodes labelled by objects of C and
arrows labelled by morphisms of C between the node objects.  Its shape is the
free category on the graph, so a family of legs is a cone as soon as the
triangle of every arrow commutes:

    cone   (L, π), π_n : L → D(n):   π_tgt = a ∘ π_src
    cocone (L, ι), ι_n : D(n) → L:   ι_src = ι_tgt ∘ a

A cone is a limit iff every cone (X, σ) has a mediator m : X → L with
π_n ∘ m = σ_n for all n (*existence*) and the legs are jointly monic
(*uniqueness*); dually for colimits.  Neither half implies the other.

This module is the in-memory reference implementation of the checker that
migration 007 runs in Postgres (same violation reasons, same STRICT /
PERMISSIVE modes).  In addition to checking against a given list of cones, it
can check universality *exhaustively* — against every cone over the diagram
— when the category is finite and its composition table is complete.

Formal backing (`Formal/Limits.lean`, registry H-019 – H-021):

* `coneOfEdges` / `coneOfGenerators` (and cocone duals): commuting triangles on
  the arrows (generators) give a cone with exactly these legs;
* `nonempty_isLimit_iff` / `nonempty_isColimit_iff`: limit iff existence and
  joint monicity (colimit iff existence and joint epicity);
* `existence_not_sufficient`, `jointlyMonic_not_sufficient`: both are needed.
"""

from __future__ import annotations

import itertools
import logging
from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, Iterator, List, Optional, Tuple

from qbx.categorical.natural_transformation import compose
from qbx.core.enforced_functor import Category, EnforcementMode
from qbx.core.exceptions import QBXError

logger = logging.getLogger(__name__)


class LimitViolation(QBXError):
    """Raised (STRICT mode) when a cone or a limit check fails."""

    def __init__(self, subject: str, reason: str, details: dict):
        self.subject = subject
        self.reason = reason
        self.details = details
        super().__init__(f"{subject}: {reason} {details}")


@dataclass
class Diagram:
    """A graph-shaped diagram in ``category``."""

    category: Category
    nodes: Dict[str, Optional[str]] = field(default_factory=dict)          # node → object
    arrows: Dict[str, Tuple[str, str, Optional[str]]] = field(default_factory=dict)
    # arrow label → (source node, target node, morphism)

    def add_node(self, node: str, obj: Optional[str]) -> None:
        self.nodes[node] = obj

    def add_arrow(self, label: str, src: str, tgt: str, morphism: Optional[str]) -> None:
        self.arrows[label] = (src, tgt, morphism)


@dataclass
class Cone:
    """A cone (``cocone=False``) or cocone (``cocone=True``) over a diagram."""

    diagram: Diagram
    apex: str
    legs: Dict[str, str] = field(default_factory=dict)  # node → morphism
    cocone: bool = False
    name: str = "cone"


def cone_problems(c: Cone) -> List[Tuple[str, Dict[str, Any]]]:
    """Every problem of a cone / cocone (pure).  Reasons match migration 007."""
    d, cat = c.diagram, c.diagram.category
    out: List[Tuple[str, Dict[str, Any]]] = []
    if c.apex not in cat.objects:
        out.append(("apex_category", {"apex": c.apex}))
    bad = set()
    for n, obj in d.nodes.items():
        if obj is None:
            out.append(("node_without_object", {"node": n}))
            bad.add(n)
            continue
        if obj not in cat.objects:
            out.append(("node_category", {"node": n}))
        leg = c.legs.get(n)
        if leg is None:
            out.append(("missing_leg", {"node": n}))
            bad.add(n)
            continue
        expected = (obj, c.apex) if c.cocone else (c.apex, obj)
        if cat.morphisms.get(leg) != expected:
            out.append(("leg_typing", {"node": n, "leg": leg}))
            bad.add(n)
    for n in c.legs:
        if n not in d.nodes:
            out.append(("foreign_leg", {"node": n}))
    for label, (s, t, m) in d.arrows.items():
        if m is None:
            out.append(("arrow_without_morphism", {"arrow": label}))
            continue
        so, to = d.nodes.get(s), d.nodes.get(t)
        if so is None or to is None or cat.morphisms.get(m) != (so, to):
            out.append(("arrow_typing", {"arrow": label}))
            continue
        if s in bad or t in bad:
            continue
        if c.cocone:
            lhs, rhs = c.legs[s], compose(cat, m, c.legs[t])          # ι_s vs ι_t ∘ a
        else:
            lhs, rhs = c.legs[t], compose(cat, c.legs[s], m)          # π_t vs a ∘ π_s
        if rhs is None:
            out.append(("missing_composite", {"arrow": label}))
        elif rhs != lhs:
            out.append(("non_commuting_triangle", {"arrow": label, "composed": rhs}))
    return out


def is_cone(c: Cone) -> bool:
    return not cone_problems(c)


def _through(cat: Category, m: str, leg: str, cocone: bool) -> Optional[str]:
    """Cone: π ∘ m (m first).  Cocone: m ∘ ι (ι first)."""
    return compose(cat, leg, m) if cocone else compose(cat, m, leg)


def mediators(limit: Cone, other: Cone) -> List[str]:
    """Morphisms mediating between ``other`` and ``limit`` (into / out of the apex)."""
    cat = limit.diagram.category
    want = (limit.apex, other.apex) if limit.cocone else (other.apex, limit.apex)
    return sorted(
        m for m, st in cat.morphisms.items() if st == want and all(
            _through(cat, m, limit.legs[n], limit.cocone) == other.legs.get(n)
            for n in limit.diagram.nodes)
    )


def all_cones(d: Diagram, cocone: bool = False) -> Iterator[Cone]:
    """Every cone (cocone) over ``d`` in its finite category.

    Exhaustive only if every composite the triangles need is recorded."""
    cat = d.category
    nodes = list(d.nodes)
    for x in cat.objects:
        choices = []
        for n in nodes:
            obj = d.nodes[n]
            want = (obj, x) if cocone else (x, obj)
            choices.append([m for m, st in cat.morphisms.items() if st == want])
        for legs in itertools.product(*choices):
            c = Cone(d, x, dict(zip(nodes, legs)), cocone)
            if is_cone(c):
                yield c


class LimitChecker:
    """Checks limits / colimits; records violations like migration 007."""

    def __init__(self, mode: Optional[EnforcementMode] = None):
        self.mode = mode or EnforcementMode.from_env()
        self.violations: List[Dict[str, Any]] = []

    def _record(self, subject: str, reason: str, details: Dict[str, Any]) -> None:
        self.violations.append({"subject": subject, "reason": reason, "details": details})
        logger.warning("limit violation %s: %s %s", subject, reason, details)
        if self.mode == EnforcementMode.STRICT:
            raise LimitViolation(subject, reason, details)

    def reasons(self) -> List[str]:
        return sorted(v["reason"] for v in self.violations)

    def check_cone(self, c: Cone) -> bool:
        problems = cone_problems(c)
        for reason, details in problems:
            self._record(c.name, reason, details)
        return not problems

    def verify_universality(self, limit: Cone,
                            others: Optional[Iterable[Cone]] = None) -> bool:
        """Existence against ``others`` (default: every cone, exhaustively) and
        joint monicity / epicity over every morphism into / out of the apex."""
        problems = cone_problems(limit)
        if problems:
            self._record(limit.name, "invalid_cone", {"problems": problems})
            return False
        before = len(self.violations)
        cat = limit.diagram.category
        if others is None:
            others = all_cones(limit.diagram, limit.cocone)
        for o in others:
            if o is limit or o.cocone != limit.cocone or not is_cone(o):
                continue
            ms = mediators(limit, o)
            if not ms:
                self._record(limit.name, "no_mediator", {"other": o.name, "apex": o.apex})
            elif len(ms) > 1:
                self._record(limit.name, "non_unique_mediator",
                             {"other": o.name, "mediators": ms})
        reason = "legs_not_jointly_epic" if limit.cocone else "legs_not_jointly_monic"
        side = 0 if limit.cocone else 1
        mors = sorted(m for m, st in cat.morphisms.items() if st[side] == limit.apex)
        for m1, m2 in itertools.combinations(mors, 2):
            if cat.morphisms[m1] != cat.morphisms[m2]:
                continue
            pairs = [(_through(cat, m1, limit.legs[n], limit.cocone),
                      _through(cat, m2, limit.legs[n], limit.cocone)) for n in limit.diagram.nodes]
            separated = any(x is not None and y is not None and x != y for x, y in pairs)
            undefined = any(x is None or y is None for x, y in pairs)
            if not separated and not undefined:
                self._record(limit.name, reason, {"m1": m1, "m2": m2})
            elif not separated:
                self._record(limit.name, "missing_composite", {"m1": m1, "m2": m2})
        return len(self.violations) == before


def is_limit(c: Cone) -> bool:
    """Exhaustive check: is ``c`` a limit (colimit) in its finite category?

    Defined directly — every cone has exactly one mediator — rather than by
    the existence + joint-monicity split, so tests can compare the two."""
    if not is_cone(c):
        return False
    return all(len(mediators(c, o)) == 1 for o in all_cones(c.diagram, c.cocone))
