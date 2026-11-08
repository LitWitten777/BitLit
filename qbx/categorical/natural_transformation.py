"""
Natural Transformation Checker (Phase 1, sprint 1).

A natural transformation η: F ⇒ G between functors F, G: C → D assigns to
every object X of C a component η_X: F(X) → G(X) in D such that, for every
morphism f: X → Y of C, the naturality square commutes:

    F(X) --F(f)--> F(Y)
     |              |
    η_X            η_Y
     v              v
    G(X) --G(f)--> G(Y)

    η_Y ∘ F(f) = G(f) ∘ η_X        (written f-first: F(f) ; η_Y = η_X ; G(f))

This module is the in-memory reference implementation of the checker that
migration 004 runs in Postgres.  It reuses the frozen Phase 0 `Category` and
`EnforcedFunctor` and the same STRICT / PERMISSIVE enforcement modes.

Formal backing (`Formal/Naturality.lean`, registry H-010 – H-012):

* Checking the squares of a *generating* set of morphisms suffices
  (`QBX.Formal.naturality_of_generators`).  `verify_naturality(generators=…)`
  only takes this shortcut after `generates` has confirmed that the set
  generates every morphism under the recorded compositions.
* Incremental enforcement is complete: when `η_X` is registered, the squares
  of every morphism with one endpoint X and the other endpoint X or already
  registered are checked — morphisms *into* X and endomorphisms included
  (`QBX.Formal.checkedBy_of_mem`).  The original migration-004 trigger only
  walked morphisms *out of* X and skipped all endomorphisms; it misses the
  square of f: X → Y whenever η_X is registered before η_Y
  (`QBX.Formal.trigger_misses_forward`, `QBX.Formal.trigger_misses_endo`).
"""

from __future__ import annotations

import logging
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

from qbx.core.canonical import canonical_cbor
from qbx.core.enforced_functor import Category, EnforcedFunctor, EnforcementMode
from qbx.core.exceptions import QBXError
from qbx.core.hashing import pq_hash
from qbx.core.signing import SignedBlob, StubSigner

logger = logging.getLogger(__name__)


class NaturalityViolation(QBXError):
    """Raised (STRICT mode) when a natural-transformation law is violated."""

    def __init__(self, transformation_id: str, law: str, details: dict):
        self.transformation_id = transformation_id
        self.law = law
        self.details = details
        super().__init__(
            f"Natural transformation {transformation_id} violated {law}: {details}"
        )


# ----------------------------------------------------------------------------
# Helpers on the Phase 0 in-memory category
# ----------------------------------------------------------------------------


def _is_identity(cat: Category, m: str) -> bool:
    src_tgt = cat.morphisms.get(m)
    return src_tgt is not None and cat.identities.get(src_tgt[0]) == m


def compose(cat: Category, f: str, g: str) -> Optional[str]:
    """`g ∘ f` (f first), using the unit laws for identities.

    Returns None when f and g are not composable or the composite is not
    recorded in the category's composition table.
    """
    if f not in cat.morphisms or g not in cat.morphisms:
        return None
    if cat.morphisms[f][1] != cat.morphisms[g][0]:
        return None
    if _is_identity(cat, f):
        return g
    if _is_identity(cat, g):
        return f
    return cat.compose(f, g)


def generates(cat: Category, generators: Iterable[str]) -> bool:
    """Do `generators` generate every morphism of `cat`?

    Computes the closure of the generators and the identities under the
    recorded compositions (the multiplicative closure of
    `Formal/Naturality.lean`) and compares it with all morphisms.
    """
    closure: Set[str] = set(cat.identities.values())
    closure.update(g for g in generators if g in cat.morphisms)
    changed = True
    while changed:
        changed = False
        for (f, g), h in cat.compositions.items():
            if f in closure and g in closure and h not in closure:
                closure.add(h)
                changed = True
    return closure >= set(cat.morphisms)


# ----------------------------------------------------------------------------
# Which squares does an incremental checker evaluate?
# ----------------------------------------------------------------------------


def incremental_checked_morphisms(cat: Category, order: Sequence[str]) -> Set[str]:
    """Morphisms whose square the Phase 1 incremental checker evaluates when
    components are registered in `order` (model `checkedAt` in Lean)."""
    checked: Set[str] = set()
    seen: Set[str] = set()
    for x in order:
        for m, (s, t) in cat.morphisms.items():
            if (s == x and (t == x or t in seen)) or (t == x and (s == x or s in seen)):
                checked.add(m)
        seen.add(x)
    return checked


def legacy_trigger_checked_morphisms(cat: Category, order: Sequence[str]) -> Set[str]:
    """Morphisms whose square the *original* migration-004 trigger evaluated
    (out-of-X only, endomorphisms skipped; model `triggerCheckedAt` in Lean)."""
    checked: Set[str] = set()
    seen: Set[str] = set()
    for x in order:
        for m, (s, t) in cat.morphisms.items():
            if s == x and t != x and t in seen:
                checked.add(m)
        seen.add(x)
    return checked


# ----------------------------------------------------------------------------
# NaturalTransformation
# ----------------------------------------------------------------------------


class NaturalTransformation:
    """A natural transformation η: F ⇒ G with enforced laws.

    `F` and `G` are Phase 0 `EnforcedFunctor`s with the same source and target
    categories whose object/morphism maps have been populated.
    """

    def __init__(
        self,
        transformation_id: str,
        name: str,
        source_functor: EnforcedFunctor,
        target_functor: EnforcedFunctor,
        mode: Optional[EnforcementMode] = None,
        signer: Optional[StubSigner] = None,
    ):
        if source_functor.source is not target_functor.source:
            raise ValueError("F and G must have the same source category")
        if source_functor.target is not target_functor.target:
            raise ValueError("F and G must have the same target category")
        self.transformation_id = transformation_id
        self.name = name
        self.F = source_functor
        self.G = target_functor
        self.mode = mode or EnforcementMode.from_env()
        self.signer = signer or StubSigner()
        self.components: Dict[str, str] = {}
        self.violations: List[Dict[str, Any]] = []

    @property
    def source(self) -> Category:
        return self.F.source

    @property
    def target(self) -> Category:
        return self.F.target

    # ---- Component registration ------------------------------------------

    def set_component(self, obj_id: str, morph_id: str, check: bool = True) -> bool:
        """Register η_X and (if `check`) verify everything that became checkable.

        Checks the typing η_X: F(X) → G(X) and the square of every morphism
        with one endpoint X whose other endpoint is X or already has a
        component — morphisms into X and endomorphisms of X included.
        """
        if obj_id not in self.source.objects:
            self._record("component_unknown_object", {"obj_id": obj_id})
            return False
        self.components[obj_id] = morph_id
        if not check:
            return True
        ok = self._check_typing(obj_id)
        for m, (s, t) in sorted(self.source.morphisms.items()):
            touches = (s == obj_id and t in self.components) or (
                t == obj_id and s in self.components
            )
            if touches and not self._check_square(m):
                ok = False
        return ok

    # ---- Batch verification ----------------------------------------------

    def verify_typing(self) -> bool:
        """Every object has a component, and η_X: F(X) → G(X)."""
        ok = True
        for obj_id in sorted(self.source.objects):
            if obj_id not in self.components:
                self._record("component_missing", {"obj_id": obj_id})
                ok = False
            elif not self._check_typing(obj_id):
                ok = False
        return ok

    def verify_naturality(self, generators: Optional[Iterable[str]] = None) -> bool:
        """Check naturality squares.

        Without `generators`, checks the square of every morphism of the
        source category.  With `generators`, checks only those morphisms; this
        is sound (Lean: `naturality_of_generators`) and is used only when
        `generates` confirms that they generate the category — otherwise
        every morphism is checked.
        """
        morphisms: List[str] = sorted(self.source.morphisms)
        if generators is not None:
            gens = sorted(set(generators))
            if generates(self.source, gens):
                morphisms = [g for g in gens if g in self.source.morphisms]
            else:
                logger.warning(
                    "NT %s: %s does not generate %s; checking all morphisms",
                    self.transformation_id, gens, self.source.id,
                )
        ok = True
        for m in morphisms:
            if not self._check_square(m):
                ok = False
        return ok

    def verify_all_laws(self, generators: Optional[Iterable[str]] = None) -> bool:
        typing_ok = self.verify_typing()
        nat_ok = self.verify_naturality(generators)
        return typing_ok and nat_ok

    # ---- Constructions ----------------------------------------------------

    @classmethod
    def identity(
        cls, functor: EnforcedFunctor, transformation_id: str, name: str = "id",
        mode: Optional[EnforcementMode] = None,
    ) -> "NaturalTransformation":
        """The identity transformation id_F: F ⇒ F."""
        nt = cls(transformation_id, name, functor, functor, mode=mode)
        for x in sorted(functor.source.objects):
            fx = functor.object_map.get(x)
            ident = functor.target.identities.get(fx) if fx is not None else None
            if ident is None:
                nt._record("identity_missing", {"obj_id": x, "F(X)": fx})
                continue
            nt.components[x] = ident
        return nt

    def vcompose(
        self, other: "NaturalTransformation", transformation_id: str, name: str = "",
    ) -> "NaturalTransformation":
        """Vertical composite (other ∘ self): F ⇒ H for self: F ⇒ G, other: G ⇒ H.

        Component X is η_X ; θ_X, which must be recorded in the target category.
        """
        if other.F is not self.G:
            raise ValueError("vertical composition needs self: F ⇒ G and other: G ⇒ H")
        nt = NaturalTransformation(
            transformation_id, name or f"{other.name}∘{self.name}",
            self.F, other.G, mode=self.mode, signer=self.signer,
        )
        for x in sorted(self.source.objects):
            a, b = self.components.get(x), other.components.get(x)
            c = compose(self.target, a, b) if a is not None and b is not None else None
            if c is None:
                nt._record("vcompose_missing", {"obj_id": x, "eta_x": a, "theta_x": b})
                continue
            nt.components[x] = c
        return nt

    # ---- Signed intent ----------------------------------------------------

    def serialize_intent(self) -> Tuple[bytes, SignedBlob]:
        intent = {
            "transformation_id": self.transformation_id,
            "name": self.name,
            "source_functor_id": self.F.functor_id,
            "target_functor_id": self.G.functor_id,
            "components": dict(sorted(self.components.items())),
        }
        canonical = canonical_cbor(intent)
        return canonical, self.signer.sign(pq_hash(canonical))

    # ---- Internal ---------------------------------------------------------

    def _check_typing(self, obj_id: str) -> bool:
        eta = self.components[obj_id]
        expected = (self.F.object_map.get(obj_id), self.G.object_map.get(obj_id))
        actual = self.target.morphisms.get(eta)
        if None in expected or actual != expected:
            self._record(
                "component_typing",
                {"obj_id": obj_id, "eta_x": eta, "expected": expected, "actual": actual},
            )
            return False
        return True

    def _check_square(self, m: str) -> bool:
        x, y = self.source.morphisms[m]
        eta_x, eta_y = self.components.get(x), self.components.get(y)
        Ff, Gf = self.F.morphism_map.get(m), self.G.morphism_map.get(m)
        details: Dict[str, Any] = {
            "f": m, "X": x, "Y": y, "eta_x": eta_x, "eta_y": eta_y, "Ff": Ff, "Gf": Gf,
        }
        if None in (eta_x, eta_y, Ff, Gf):
            self._record("naturality_missing_data", details)
            return False
        left = compose(self.target, Ff, eta_y)    # η_Y ∘ F(f)
        right = compose(self.target, eta_x, Gf)   # G(f) ∘ η_X
        details.update({"eta_y∘Ff": left, "Gf∘eta_x": right})
        if left is None or right is None:
            self._record("naturality_composite_missing", details)
            return False
        if left != right:
            self._record("naturality_square", details)
            return False
        return True

    def _record(self, law: str, details: Dict[str, Any]) -> None:
        self.violations.append({"law": law, "details": details})
        if self.mode == EnforcementMode.STRICT:
            raise NaturalityViolation(self.transformation_id, law, details)
        logger.warning(
            "Natural transformation %s violation [%s]: %s",
            self.transformation_id, law, details,
        )
