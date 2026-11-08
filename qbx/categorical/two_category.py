"""
2-categories (Phase 1, sprint 6).

A strict 2-category is recorded over a base category (objects, 1-morphisms,
identities, a composition table ``(g, f) -> g ∘ f``).  On top of it:

* 2-cells ``α : f ⇒ f'`` between parallel 1-morphisms;
* identity 2-cells ``1_f : f ⇒ f`` (at most one per 1-morphism);
* vertical composites ``(upper, lower) -> upper ∘ᵥ lower`` (lower first);
* horizontal composites ``(left, right) -> left ⋆ right`` for
  ``right = α : f ⇒ f'`` (``f, f' : A → B``) and ``left = β : g ⇒ g'``
  (``g, g' : B → C``); the result is a 2-cell ``g ∘ f ⇒ g' ∘ f'``.

The checker reports, with the same reasons and details as migration 009:

    cell_typing, identity_typing, vertical_typing, horizontal_typing
    vertical_unit           1_f' ∘ᵥ α = α,  β ∘ᵥ 1_f = β
    horizontal_unit         1_(1_B) ⋆ α = α,  β ⋆ 1_(1_B) = β
    identity_preservation   1_g ⋆ 1_f = 1_(g ∘ f)   (when 1_(g ∘ f) is recorded)
    vertical_associativity  (γ ∘ᵥ β) ∘ᵥ α = γ ∘ᵥ (β ∘ᵥ α)
    horizontal_associativity (γ ⋆ β) ⋆ α = γ ⋆ (β ⋆ α)
    interchange             (β' ∘ᵥ β) ⋆ (α' ∘ᵥ α) = (β' ⋆ α') ∘ᵥ (β ⋆ α)

Each law is checked wherever all the composites it mentions are recorded;
2-cells are compared by name.  This module is the in-memory reference
implementation of the checker migration 009 runs in Postgres (same reasons,
same STRICT / PERMISSIVE modes).

Formal backing (``Formal/TwoCategory.lean``, registry H-025 – H-027):

* ``exists_bifunctor_iff``: identity preservation + interchange are exactly
  functoriality of horizontal composition ``Hom(B, C) × Hom(A, B) ⥤ Hom(A, C)``;
* ``interchange_not_implied``, ``identity_preservation_not_implied``: both
  checks are needed;
* ``eckmannHilton_two_cells``: on the 2-cells of an identity 1-morphism the
  laws force vertical = horizontal composition, and it is commutative — so a
  non-commutative monoid recorded there must fail (``one_cell_two_category``).
"""

from __future__ import annotations

import itertools
import logging
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, List, Optional, Tuple

from qbx.core.enforced_functor import EnforcementMode
from qbx.core.exceptions import QBXError

logger = logging.getLogger(__name__)

Problem = Tuple[str, Dict[str, Any]]

REASONS = (
    "cell_typing",
    "identity_typing",
    "vertical_typing",
    "horizontal_typing",
    "vertical_unit",
    "horizontal_unit",
    "identity_preservation",
    "vertical_associativity",
    "horizontal_associativity",
    "interchange",
)


class TwoCategoryViolation(QBXError):
    """Raised (STRICT mode) when a 2-category check fails."""

    def __init__(self, subject: str, reason: str, details: dict):
        self.subject = subject
        self.reason = reason
        self.details = details
        super().__init__(f"{subject}: {reason} {details}")


@dataclass
class TwoCategory:
    """Recorded data of a strict 2-category (all names are strings)."""

    morphisms: Dict[str, Tuple[str, str]] = field(default_factory=dict)       # f -> (A, B)
    identities: Dict[str, str] = field(default_factory=dict)                  # A -> 1_A
    compositions: Dict[Tuple[str, str], str] = field(default_factory=dict)    # (g, f) -> g∘f
    cells: Dict[str, Tuple[str, str]] = field(default_factory=dict)           # α -> (f, f')
    identity_cells: Dict[str, str] = field(default_factory=dict)              # f -> 1_f
    vertical: Dict[Tuple[str, str], str] = field(default_factory=dict)        # (β, α) -> β∘ᵥα
    horizontal: Dict[Tuple[str, str], str] = field(default_factory=dict)      # (β, α) -> β⋆α

    # -- recording --------------------------------------------------------
    def add_cell(self, name: str, source: str, target: str) -> str:
        self.cells[name] = (source, target)
        return name

    def identity_cell(self, f: str) -> str:
        """``1_f``, created (as a 2-cell ``f ⇒ f``) if not yet recorded."""
        if f not in self.identity_cells:
            if f not in self.morphisms:
                raise KeyError(f"1-morphism {f!r} not found")
            name = f"id2({f})"
            self.add_cell(name, f, f)
            self.identity_cells[f] = name
        return self.identity_cells[f]

    def _is_identity(self, cell: Optional[str]) -> bool:
        return cell is not None and cell in self.identity_cells.values()

    def _is_unit_cell(self, cell: Optional[str]) -> bool:
        ids = set(self.identities.values())
        return any(c == cell and f in ids for f, c in self.identity_cells.items())

    def compose_vertical(self, upper: str, lower: str, result: Optional[str] = None) -> str:
        """Mirror of ``compose_two_vertical``."""
        if (upper, lower) in self.vertical:
            existing = self.vertical[(upper, lower)]
            if result is not None and result != existing:
                raise ValueError(f"{upper} ∘ᵥ {lower} is already recorded as {existing}")
            return existing
        if upper not in self.cells or lower not in self.cells:
            raise KeyError("2-cell(s) not found")
        if self.cells[lower][1] != self.cells[upper][0]:
            raise ValueError("target(lower) <> source(upper)")
        if result is None:
            if self._is_identity(upper):
                result = lower
            elif self._is_identity(lower):
                result = upper
            else:
                result = self.add_cell(f"({upper} ∘v {lower})", self.cells[lower][0],
                                       self.cells[upper][1])
        self.vertical[(upper, lower)] = result
        return result

    def compose_horizontal(self, left: str, right: str, result: Optional[str] = None) -> str:
        """Mirror of ``compose_two_horizontal``."""
        if (left, right) in self.horizontal:
            existing = self.horizontal[(left, right)]
            if result is not None and result != existing:
                raise ValueError(f"{left} ⋆ {right} is already recorded as {existing}")
            return existing
        if left not in self.cells or right not in self.cells:
            raise KeyError("2-cell(s) not found")
        (g, g2), (f, f2) = self.cells[left], self.cells[right]
        if self.morphisms[f][1] != self.morphisms[g][0]:
            raise ValueError("the 1-morphisms do not compose")
        src, tgt = self.compositions.get((g, f)), self.compositions.get((g2, f2))
        if src is None or tgt is None:
            raise ValueError("composite 1-morphism not recorded")
        if result is None:
            if self._is_unit_cell(left):
                result = right
            elif self._is_unit_cell(right):
                result = left
            elif self.identity_cells.get(g) == left and self.identity_cells.get(f) == right:
                result = self.identity_cell(src)
            else:
                result = self.add_cell(f"({left} ⋆ {right})", src, tgt)
        self.horizontal[(left, right)] = result
        return result

    # -- row problems -----------------------------------------------------
    def cell_problems(self, cell: str) -> List[Problem]:
        s, t = self.cells[cell]
        ms, mt = self.morphisms.get(s), self.morphisms.get(t)
        if ms is None or mt is None or ms != mt:
            return [("cell_typing", {"cell": cell, "source": s, "target": t})]
        return []

    def identity_problems(self, f: str, cell: str) -> List[Problem]:
        if f not in self.morphisms or self.cells.get(cell) != (f, f):
            return [("identity_typing", {"morphism": f, "cell": cell})]
        return []

    def vertical_problems(self, upper: str, lower: str, result: str) -> List[Problem]:
        out: List[Problem] = []
        d = {"upper": upper, "lower": lower, "result": result}
        u, l, r = self.cells.get(upper), self.cells.get(lower), self.cells.get(result)
        if u is None or l is None or r is None or l[1] != u[0] or r[0] != l[0] or r[1] != u[1]:
            out.append(("vertical_typing", dict(d)))
        if self._is_identity(upper) and result != lower:
            out.append(("vertical_unit", {**d, "expected": lower}))
        if self._is_identity(lower) and result != upper:
            out.append(("vertical_unit", {**d, "expected": upper}))
        return out

    def horizontal_problems(self, left: str, right: str, result: str) -> List[Problem]:
        out: List[Problem] = []
        d = {"left": left, "right": right, "result": result}
        b, a, r = self.cells.get(left), self.cells.get(right), self.cells.get(result)
        f_tgt = g_src = src = tgt = None
        if a is not None and a[0] in self.morphisms:
            f_tgt = self.morphisms[a[0]][1]
        if b is not None and b[0] in self.morphisms:
            g_src = self.morphisms[b[0]][0]
        if a is not None and b is not None:
            src = self.compositions.get((b[0], a[0]))
            tgt = self.compositions.get((b[1], a[1]))
        if (b is None or a is None or r is None or f_tgt != g_src or src is None or tgt is None
                or r[0] != src or r[1] != tgt):
            missing = (f_tgt is not None and f_tgt == g_src) and (src is None or tgt is None)
            out.append(("horizontal_typing", {**d, "missing_composite": missing}))
        if self._is_unit_cell(left) and result != right:
            out.append(("horizontal_unit", {**d, "expected": right}))
        if self._is_unit_cell(right) and result != left:
            out.append(("horizontal_unit", {**d, "expected": left}))
        if a is not None and b is not None:
            if self.identity_cells.get(b[0]) == left and self.identity_cells.get(a[0]) == right:
                expected = self.identity_cells.get(src) if src is not None else None
                if expected is not None and expected != result:
                    out.append(("identity_preservation", {**d, "expected": expected}))
        return out

    # -- all problems -----------------------------------------------------
    def problems(self) -> List[Problem]:
        out: List[Problem] = []
        for c in self.cells:
            out += self.cell_problems(c)
        for f, c in self.identity_cells.items():
            out += self.identity_problems(f, c)
        for (u, l), r in self.vertical.items():
            out += self.vertical_problems(u, l, r)
        for (b, a), r in self.horizontal.items():
            out += self.horizontal_problems(b, a, r)
        out += self._associativity(self.vertical, "vertical_associativity")
        out += self._associativity(self.horizontal, "horizontal_associativity")
        out += self._interchange()
        return out

    @staticmethod
    def _associativity(comp: Dict[Tuple[str, str], str], reason: str) -> List[Problem]:
        out: List[Problem] = []
        for (c, b), cb in comp.items():
            for (cb2, a), x in comp.items():
                if cb2 != cb:
                    continue
                ba = comp.get((b, a))
                y = comp.get((c, ba)) if ba is not None else None
                if y is not None and x != y:
                    out.append((reason, {"c": c, "b": b, "a": a,
                                         "left_assoc": x, "right_assoc": y}))
        return out

    def _interchange(self) -> List[Problem]:
        out: List[Problem] = []
        for ((b2, b1), bres), ((a2, a1), ares) in itertools.product(self.vertical.items(),
                                                                    repeat=2):
            x = self.horizontal.get((bres, ares))
            p = self.horizontal.get((b2, a2))
            q = self.horizontal.get((b1, a1))
            if x is None or p is None or q is None:
                continue
            y = self.vertical.get((p, q))
            if y is not None and x != y:
                out.append(("interchange", {"beta2": b2, "beta1": b1, "alpha2": a2, "alpha1": a1,
                                            "horizontal_of_vertical": x,
                                            "vertical_of_horizontal": y}))
        return out

    def is_valid(self) -> bool:
        return not self.problems()


class TwoCategoryChecker:
    """Runs the checks, logging every problem and raising in STRICT mode."""

    def __init__(self, mode: Optional[EnforcementMode] = None):
        self.mode = mode or EnforcementMode.from_env()
        self.violations: List[Problem] = []

    def check(self, tc: TwoCategory, subject: str = "2-category") -> bool:
        problems = tc.problems()
        for reason, details in problems:
            logger.warning("%s: %s %s", subject, reason, details)
            self.violations.append((reason, details))
        if problems and self.mode == EnforcementMode.STRICT:
            reason, details = problems[0]
            raise TwoCategoryViolation(subject, reason, details)
        return not problems


# ---------------------------------------------------------------------------
# Builders
# ---------------------------------------------------------------------------
def base_category(objects: Iterable[str], morphisms: Dict[str, Tuple[str, str]],
                  compositions: Dict[Tuple[str, str], str]) -> TwoCategory:
    """A 2-category with no 2-cells over a base category.

    Identity 1-morphisms ``id_A`` are added for every object, together with
    their composites ``id ∘ f = f = f ∘ id``.
    """
    tc = TwoCategory()
    for o in objects:
        tc.morphisms[f"id_{o}"] = (o, o)
        tc.identities[o] = f"id_{o}"
    tc.morphisms.update(morphisms)
    for f, (s, t) in list(tc.morphisms.items()):
        tc.compositions[(tc.identities[t], f)] = f
        tc.compositions[(f, tc.identities[s])] = f
    tc.compositions.update(compositions)
    return tc


def codiscrete_two_category(objects: Iterable[str], morphisms: Dict[str, Tuple[str, str]],
                            compositions: Dict[Tuple[str, str], str]) -> TwoCategory:
    """The codiscrete (chaotic) 2-category: exactly one 2-cell between any two
    parallel 1-morphisms, with every composite recorded.  It satisfies every
    law, provided the composition table is a category."""
    tc = base_category(objects, morphisms, compositions)
    cell = {}
    for f, g in itertools.product(tc.morphisms, repeat=2):
        if tc.morphisms[f] == tc.morphisms[g]:
            cell[(f, g)] = tc.add_cell(f"{f}=>{g}", f, g)
    for f in tc.morphisms:
        tc.identity_cells[f] = cell[(f, f)]
    for (f, g), lower in cell.items():
        for (g2, h), upper in cell.items():
            if g2 == g:
                tc.vertical[(upper, lower)] = cell[(f, h)]
    for (f, f2), right in cell.items():
        for (g, g2), left in cell.items():
            if tc.morphisms[f][1] == tc.morphisms[g][0]:
                tc.horizontal[(left, right)] = cell[(tc.compositions[(g, f)],
                                                     tc.compositions[(g2, f2)])]
    return tc


def one_cell_two_category(elements: Iterable[str], unit: str,
                          vertical: Callable[[str, str], str],
                          horizontal: Callable[[str, str], str]) -> TwoCategory:
    """One object ``*``, one 1-morphism ``id_*``, 2-cells ``elements`` with
    ``unit`` as the identity 2-cell; ``vertical(β, α)`` and
    ``horizontal(β, α)`` give the composites.  By Eckmann–Hilton
    (``eckmannHilton_two_cells``) all laws hold iff both operations are
    unital, associative, equal, and commutative."""
    tc = base_category(["*"], {}, {})
    elems = list(elements)
    for e in elems:
        tc.add_cell(e, "id_*", "id_*")
    tc.identity_cells["id_*"] = unit
    for b, a in itertools.product(elems, repeat=2):
        tc.vertical[(b, a)] = vertical(b, a)
        tc.horizontal[(b, a)] = horizontal(b, a)
    return tc
