"""
Topos kernel: subobject classifiers (Phase 1, sprint 8).

A subobject classifier is recorded on an in-memory category
(``qbx.core.enforced_functor.Category``) as an object ``omega`` and a morphism
``truth : 1 → Ω`` (the terminal object ``1`` is the source of ``truth``),
together with registered subobjects (a morphism ``m : U → X`` claimed to be a
monomorphism into ``X``), their characteristic morphisms ``χ : X → Ω`` and named
truth values (global elements ``1 → Ω``).

The checker reports, with the same reasons and details as migration 011:

    classifier_typing          Ω not an object, truth missing / not a morphism
                               ending at Ω  (details: omega, truth) — nothing
                               else is checked then
    terminal_existence         an object Z with no morphism Z → 1 (object)
    terminal_uniqueness        several (object, count)
    truth_value_typing         a truth value that is not 1 → Ω (name, morphism)
    subobject_typing           m not a morphism, or not ending at the recorded
                               object (mono, object)
    not_mono                   g ≠ h : Z → U with m ∘ g = m ∘ h  (mono, count =
                               number of unordered pairs)
    characteristic_typing      χ not a morphism X → Ω (mono, chi)
    pullback_not_commuting     χ ∘ m ≠ truth ∘ !_U, or not recorded (mono, chi)
    pullback_existence         f : Z → X with χ ∘ f = truth ∘ !_Z and no
                               g : Z → U with m ∘ g = f (mono, chi, f)
    pullback_uniqueness        several such g (mono, chi, f, count)
    unclassified_mono          a morphism that is mono on the recorded data with
                               no χ passing the pullback check (mono)
    characteristic_not_unique  ... with several (mono, count)

The terminal, pullback and classification checks run only when the classifier
is well typed; the pullback and classification checks only when ``1`` passes
the terminal check.  Composites are read with the unit laws for identities and
the composition table otherwise; everything is checked against the recorded
morphisms and composites.  This module is the in-memory reference
implementation of the checker migration 011 runs in Postgres (same reasons,
same STRICT / PERMISSIVE modes).

Formal backing (``Formal/Topos.lean``, registry H-031 – H-033):

* ``isPullback_iff_pullbackCheck``: the pullback check is exactly Mathlib's
  ``IsPullback``;
* ``classifierCheck_of_classifier``, ``Classifier.ofCheck``,
  ``hasClassifier_iff_exists_check``: "every mono has exactly one χ passing the
  check" is exactly Mathlib's ``Classifier``;
* ``classifier_existence_not_sufficient`` / ``classifier_uniqueness_not_sufficient``:
  both halves are needed (the first is sets with a three-element Ω, see
  ``finite_sets``);
* ``chi_id_eq``: χ(id_X) = truth ∘ !_X;
* ``partialOrder_hasClassifier_iff``: a nonempty partial order has a classifier
  iff it has one element — the oracle for ``poset``.
"""

from __future__ import annotations

import itertools
import logging
from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from qbx.categorical.natural_transformation import compose
from qbx.core.enforced_functor import Category, EnforcementMode
from qbx.core.exceptions import QBXError

logger = logging.getLogger(__name__)

Problem = Tuple[str, Dict[str, Any]]

REASONS = (
    "classifier_typing",
    "terminal_existence",
    "terminal_uniqueness",
    "truth_value_typing",
    "subobject_typing",
    "not_mono",
    "characteristic_typing",
    "pullback_not_commuting",
    "pullback_existence",
    "pullback_uniqueness",
    "unclassified_mono",
    "characteristic_not_unique",
)


class ToposViolation(QBXError):
    """Raised (STRICT mode) when a subobject-classifier check fails."""

    def __init__(self, subject: str, reason: str, details: dict):
        self.subject = subject
        self.reason = reason
        self.details = details
        super().__init__(f"{subject}: {reason} {details}")


@dataclass
class Subobject:
    """A registered subobject: ``mono`` claimed to be a monomorphism into ``of_object``."""

    mono: str
    of_object: str


@dataclass
class SubobjectClassifier:
    """Recorded data of a (claimed) subobject classifier ``truth : 1 → omega``."""

    category: Category
    omega: str
    truth: Optional[str]
    subobjects: List[Subobject] = field(default_factory=list)
    characteristics: Dict[str, str] = field(default_factory=dict)    # mono -> χ
    truth_values: Dict[str, Optional[str]] = field(default_factory=dict)  # name -> morphism

    # -- helpers ----------------------------------------------------------
    @property
    def terminal(self) -> Optional[str]:
        st = self.category.morphisms.get(self.truth) if self.truth is not None else None
        return st[0] if st else None

    def homs(self, src: str, tgt: str) -> List[str]:
        return [m for m, st in self.category.morphisms.items() if st == (src, tgt)]

    def bang(self, z: str) -> Optional[str]:
        """The unique morphism ``z → 1`` (None if none or several)."""
        ms = self.homs(z, self.terminal)
        return ms[0] if len(ms) == 1 else None

    def subobject(self, mono: str) -> Optional[Subobject]:
        for s in self.subobjects:
            if s.mono == mono:
                return s
        return None

    # -- recording --------------------------------------------------------
    def register_subobject(self, mono: str, of_object: Optional[str] = None) -> Subobject:
        """Mirror of ``register_subobject``: refuses ill-typed input, returns
        the existing row for a morphism registered before."""
        if mono not in self.category.morphisms:
            raise KeyError(f"morphism {mono} not found")
        target = self.category.morphisms[mono][1]
        if of_object is not None and of_object != target:
            raise ValueError("the object is not the target of the morphism")
        existing = self.subobject(mono)
        if existing is not None:
            return existing
        sub = Subobject(mono, target)
        self.subobjects.append(sub)
        return sub

    def attach_characteristic(self, mono: str, chi: str) -> None:
        """Mirror of ``attach_characteristic``: never replaces an attached χ."""
        sub = self.subobject(mono)
        if sub is None:
            raise KeyError(f"subobject {mono} not found")
        if mono in self.characteristics:
            if self.characteristics[mono] == chi:
                return
            raise ValueError(f"subobject {mono} already has a characteristic morphism")
        if self.category.morphisms.get(chi) != (sub.of_object, self.omega):
            raise ValueError("χ is not a morphism X → Ω of the category")
        self.characteristics[mono] = chi

    # -- problems ---------------------------------------------------------
    def typing_problems(self) -> List[Problem]:
        st = self.category.morphisms.get(self.truth) if self.truth is not None else None
        if self.omega not in self.category.objects or st is None or st[1] != self.omega:
            return [("classifier_typing", {"omega": self.omega, "truth": self.truth})]
        return []

    def terminal_problems(self) -> List[Problem]:
        out: List[Problem] = []
        for z in self.category.objects:
            n = len(self.homs(z, self.terminal))
            if n == 0:
                out.append(("terminal_existence", {"object": z}))
            elif n > 1:
                out.append(("terminal_uniqueness", {"object": z, "count": n}))
        return out

    def ready(self) -> bool:
        return not self.typing_problems() and not self.terminal_problems()

    def mono_failures(self, m: str) -> int:
        """Unordered pairs ``g ≠ h : Z → U`` with ``m ∘ g = m ∘ h`` (recorded)."""
        C = self.category
        u = C.morphisms[m][0]
        into = [(g, C.morphisms[g][0], compose(C, g, m))
                for g, (_, t) in C.morphisms.items() if t == u]
        return sum(1 for (g, zg, rg), (h, zh, rh) in itertools.combinations(into, 2)
                   if zg == zh and rg is not None and rg == rh)

    def is_mono(self, m: str) -> bool:
        return self.mono_failures(m) == 0

    def _cone_morphisms(self, chi: str, x: str):
        """The ``f : Z → x`` with ``χ ∘ f = truth ∘ !_Z`` (both recorded)."""
        C = self.category
        for f, (z, t) in C.morphisms.items():
            if t != x:
                continue
            a = compose(C, f, chi)
            b = compose(C, self.bang(z), self.truth) if self.bang(z) else None
            if a is not None and a == b:
                yield f, z

    def _commutes(self, m: str, chi: str) -> bool:
        C = self.category
        u = C.morphisms[m][0]
        a = compose(C, m, chi)
        b = compose(C, self.bang(u), self.truth) if self.bang(u) else None
        return a is not None and b is not None and a == b

    def _factorizations(self, m: str, f: str, z: str) -> int:
        C = self.category
        u = C.morphisms[m][0]
        return sum(1 for g, st in C.morphisms.items() if st == (z, u) and compose(C, g, m) == f)

    def pullback_problems(self, m: str, chi: str) -> List[Problem]:
        """The pullback check of ``chi`` for ``m`` (classifier assumed ready)."""
        out: List[Problem] = []
        details = {"mono": m, "chi": chi}
        if not self._commutes(m, chi):
            out.append(("pullback_not_commuting", dict(details)))
        x = self.category.morphisms[m][1]
        for f, z in self._cone_morphisms(chi, x):
            n = self._factorizations(m, f, z)
            if n == 0:
                out.append(("pullback_existence", {**details, "f": f}))
            elif n > 1:
                out.append(("pullback_uniqueness", {**details, "f": f, "count": n}))
        return out

    def pullback_ok(self, m: str, chi: str) -> bool:
        if not self._commutes(m, chi):
            return False
        x = self.category.morphisms[m][1]
        return all(self._factorizations(m, f, z) == 1 for f, z in self._cone_morphisms(chi, x))

    def characteristics_of(self, m: str) -> List[str]:
        """Every ``χ : X → Ω`` passing the pullback check for ``m``."""
        x = self.category.morphisms[m][1]
        return [chi for chi in self.homs(x, self.omega) if self.pullback_ok(m, chi)]

    def classify(self, m: str) -> Optional[str]:
        """Mirror of ``classify_mono``: the unique characteristic morphism, or None."""
        if not self.ready() or m not in self.category.morphisms:
            return None
        chis = self.characteristics_of(m)
        return chis[0] if len(chis) == 1 else None

    def problems(self) -> List[Problem]:
        out = list(self.typing_problems())
        if out:
            return out
        terminal = self.terminal_problems()
        out.extend(terminal)
        ready = not terminal
        C = self.category
        one = self.terminal
        for name, mor in self.truth_values.items():
            if mor is not None and C.morphisms.get(mor) != (one, self.omega):
                out.append(("truth_value_typing", {"name": name, "morphism": mor}))
        for sub in self.subobjects:
            st = C.morphisms.get(sub.mono)
            sub_ok = st is not None and st[1] == sub.of_object
            if not sub_ok:
                out.append(("subobject_typing", {"mono": sub.mono, "object": sub.of_object}))
            else:
                n = self.mono_failures(sub.mono)
                if n:
                    out.append(("not_mono", {"mono": sub.mono, "count": n}))
            chi = self.characteristics.get(sub.mono)
            if chi is None:
                continue
            chi_ok = C.morphisms.get(chi) == (sub.of_object, self.omega)
            if not chi_ok:
                out.append(("characteristic_typing", {"mono": sub.mono, "chi": chi}))
            if sub_ok and chi_ok and ready:
                out.extend(self.pullback_problems(sub.mono, chi))
        if ready:
            for m in C.morphisms:
                if not self.is_mono(m):
                    continue
                n = len(self.characteristics_of(m))
                if n == 0:
                    out.append(("unclassified_mono", {"mono": m}))
                elif n > 1:
                    out.append(("characteristic_not_unique", {"mono": m, "count": n}))
        return out

    def is_valid(self) -> bool:
        return not self.problems()


class ToposChecker:
    """Runs the checks, logging every problem and raising in STRICT mode."""

    def __init__(self, mode: Optional[EnforcementMode] = None):
        self.mode = mode or EnforcementMode.from_env()
        self.violations: List[Problem] = []

    def check(self, cls: SubobjectClassifier, subject: str = "subobject_classifier") -> bool:
        problems = cls.problems()
        for reason, details in problems:
            logger.warning("%s: %s %s", subject, reason, details)
            self.violations.append((reason, details))
        if problems and self.mode == EnforcementMode.STRICT:
            reason, details = problems[0]
            raise ToposViolation(subject, reason, details)
        return not problems


# ---------------------------------------------------------------------------
# Builders
# ---------------------------------------------------------------------------
def _new_category(cid: str, objects: Iterable[str]) -> Category:
    cat = Category(id=cid, name=cid)
    for o in objects:
        cat.add_object(o, o)
        cat.add_identity(o, f"id_{o}")
    return cat


def finite_sets(sizes: Sequence[int], omega_size: int = 2, truth_value: int = 1,
                cid: str = "Set") -> SubobjectClassifier:
    """The full subcategory of finite sets on ``{0, …, n-1}`` for ``n`` in
    ``sizes`` (objects ``s<n>``, every function recorded, every composite
    recorded), with ``Ω = s<omega_size>`` and ``truth : s1 → Ω`` picking
    ``truth_value``.  ``s1`` must be among the sizes.

    A function ``a → b`` is named ``s<a>s<b>_<values>`` (identities ``id_s<n>``).
    With ``omega_size = 2`` this is a subobject classifier; with
    ``omega_size = 3`` every mono has a characteristic morphism but the
    non-surjective ones have several (``classifier_existence_not_sufficient``).
    """
    sizes = sorted(set(sizes))
    objs = [f"s{n}" for n in sizes]
    cat = _new_category(cid, objs)
    func: Dict[Tuple[int, int, Tuple[int, ...]], str] = {}
    for a in sizes:
        for b in sizes:
            for values in itertools.product(range(b), repeat=a):
                if a == b and values == tuple(range(a)):
                    name = f"id_s{a}"
                else:
                    name = f"s{a}s{b}_{''.join(map(str, values))}"
                    cat.add_morphism(name, f"s{a}", f"s{b}")
                func[(a, b, values)] = name
    for (a, b, f), fn in func.items():
        for (b2, c, g), gn in func.items():
            if b2 != b or fn.startswith("id_") or gn.startswith("id_"):
                continue
            cat.add_composition(fn, gn, func[(a, c, tuple(g[i] for i in f))])
    truth = func[(1, omega_size, (truth_value,))]
    return SubobjectClassifier(cat, f"s{omega_size}", truth)


def poset(elements: Sequence[str], leq: Iterable[Tuple[str, str]], terminal: str,
          omega: str, cid: str = "P") -> SubobjectClassifier:
    """A partial order as a thin category: one morphism ``a<=b`` for each
    ``a ≤ b`` (``leq`` must be reflexive-transitively closed apart from the
    diagonal, which is added), every composite recorded, and the classifier
    candidate ``truth = terminal<=omega``."""
    rel = {(a, b) for a, b in leq} | {(a, a) for a in elements}
    cat = _new_category(cid, elements)
    name = {(a, a): f"id_{a}" for a in elements}
    for a, b in sorted(rel):
        if a != b:
            name[(a, b)] = f"{a}<={b}"
            cat.add_morphism(name[(a, b)], a, b)
    for (a, b) in rel:
        for (b2, c) in rel:
            if b2 == b and a != b and b != c:
                cat.add_composition(name[(a, b)], name[(b, c)], name[(a, c)])
    return SubobjectClassifier(cat, omega, name.get((terminal, omega)))


def all_partial_orders(elements: Sequence[str]):
    """Every partial order on ``elements`` (as a set of pairs ``(a, b)``, a ≠ b, a ≤ b)."""
    pairs = [(a, b) for a in elements for b in elements if a != b]
    for bits in itertools.product((False, True), repeat=len(pairs)):
        rel = {p for p, on in zip(pairs, bits) if on}
        if any((b, a) in rel for a, b in rel):
            continue
        if all((a, c) in rel for a, b in rel for b2, c in rel if b2 == b and a != c):
            yield rel
