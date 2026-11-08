"""
Adjunction Engine (Phase 1, sprint 2).

An adjunction F ⊣ G between F: C → D and G: D → C is given by a unit
η: Id_C ⇒ G∘F and a counit ε: F∘G ⇒ Id_D satisfying the triangle identities

    left   ε_{F(X)} ∘ F(η_X) = id_{F(X)}      for every object X of C
    right  G(ε_Y) ∘ η_{G(Y)} = id_{G(Y)}      for every object Y of D

This module is the in-memory reference implementation of the checker that
migration 005 runs in Postgres.  It reuses the frozen Phase 0 `Category` and
`EnforcedFunctor`, the Phase 1 `NaturalTransformation`, and the same
STRICT / PERMISSIVE enforcement modes.

Formal backing (`Formal/Adjunction.lean`, registry H-013 – H-015):

* Soundness and completeness: natural η, ε are the unit and counit of an
  adjunction iff both triangle identities hold at every object
  (`QBX.Formal.exists_adjunction_iff_triangles`); data passing every check
  (naturality, possibly on generators, and both triangles) is an adjunction
  (`QBX.Formal.adjunctionOfChecks`) whose hom-set bijection is
  `left_adjunct` / `right_adjunct` below
  (`QBX.Formal.adjunctionOfChecks_homEquiv`, `…_homEquiv_symm`).
* Neither triangle identity implies the other, even for natural η and ε
  (`QBX.Formal.right_triangle_not_implies_left`,
  `QBX.Formal.left_triangle_not_implies_right`), so both are checked.

Violation laws (shared with the `adjunction_violation.law` column of 005):
`adjunction_typing`, `unit_functor_mismatch`, `counit_functor_mismatch`,
`unit_component_missing`, `counit_component_missing`, `unit_component_typing`,
`counit_component_typing`, `triangle_left_missing`, `triangle_right_missing`,
`triangle_left_composite_missing`, `triangle_right_composite_missing`,
`triangle_left`, `triangle_right`.  Naturality failures of η and ε are
recorded by their own `NaturalTransformation` objects (and, in STRICT mode,
raise `NaturalityViolation`).
"""

from __future__ import annotations

import logging
from typing import Any, Dict, Iterable, List, Optional, Tuple

from qbx.categorical.natural_transformation import NaturalTransformation, compose
from qbx.core.canonical import canonical_cbor
from qbx.core.enforced_functor import Category, EnforcedFunctor, EnforcementMode
from qbx.core.exceptions import QBXError
from qbx.core.hashing import pq_hash
from qbx.core.signing import SignedBlob, StubSigner

logger = logging.getLogger(__name__)


class AdjunctionViolation(QBXError):
    """Raised (STRICT mode) when an adjunction law is violated."""

    def __init__(self, adjunction_id: str, law: str, details: dict):
        self.adjunction_id = adjunction_id
        self.law = law
        self.details = details
        super().__init__(f"Adjunction {adjunction_id} violated {law}: {details}")


class Adjunction:
    """F ⊣ G with unit η: Id_C ⇒ G∘F and counit ε: F∘G ⇒ Id_D.

    `unit.F` / `unit.G` must agree with Id_C / G∘F and `counit.F` /
    `counit.G` with F∘G / Id_D on every object and morphism (use
    `qbx.categorical.functors.IdentityFunctor` and `ComposedFunctor`).
    """

    def __init__(
        self,
        adjunction_id: str,
        name: str,
        left: EnforcedFunctor,
        right: EnforcedFunctor,
        unit: NaturalTransformation,
        counit: NaturalTransformation,
        mode: Optional[EnforcementMode] = None,
        signer: Optional[StubSigner] = None,
    ):
        self.adjunction_id = adjunction_id
        self.name = name
        self.F = left
        self.G = right
        self.unit = unit
        self.counit = counit
        self.mode = mode or EnforcementMode.from_env()
        self.signer = signer or StubSigner()
        self.violations: List[Dict[str, Any]] = []

    @property
    def C(self) -> Category:
        return self.F.source

    @property
    def D(self) -> Category:
        return self.F.target

    # ---- Batch verification ----------------------------------------------

    def verify_typing(self) -> bool:
        """Categories fit: F: C → D, G: D → C, η over C, ε over D."""
        C, D = self.C, self.D
        ok = (
            self.G.source is D and self.G.target is C
            and self.unit.source is C and self.unit.target is C
            and self.counit.source is D and self.counit.target is D
        )
        if not ok:
            self._record("adjunction_typing", {
                "F": (C.id, D.id),
                "G": (self.G.source.id, self.G.target.id),
                "unit": (self.unit.source.id, self.unit.target.id),
                "counit": (self.counit.source.id, self.counit.target.id),
            })
        return ok

    def verify_functors(self) -> bool:
        """unit: Id_C ⇒ G∘F and counit: F∘G ⇒ Id_D, on objects and morphisms."""
        ok = True
        F, G = self.F, self.G
        uF, uG, cF, cG = self.unit.F, self.unit.G, self.counit.F, self.counit.G
        for x in sorted(self.C.objects):
            gfx = G.object_map.get(F.object_map.get(x))
            if uF.object_map.get(x) != x or gfx is None or uG.object_map.get(x) != gfx:
                ok = False
                self._record("unit_functor_mismatch", {
                    "object": x, "source": uF.object_map.get(x),
                    "target": uG.object_map.get(x), "expected_target": gfx})
        for m in sorted(self.C.morphisms):
            gfm = G.morphism_map.get(F.morphism_map.get(m))
            if uF.morphism_map.get(m) != m or gfm is None or uG.morphism_map.get(m) != gfm:
                ok = False
                self._record("unit_functor_mismatch", {
                    "morphism": m, "source": uF.morphism_map.get(m),
                    "target": uG.morphism_map.get(m), "expected_target": gfm})
        for y in sorted(self.D.objects):
            fgy = F.object_map.get(G.object_map.get(y))
            if fgy is None or cF.object_map.get(y) != fgy or cG.object_map.get(y) != y:
                ok = False
                self._record("counit_functor_mismatch", {
                    "object": y, "source": cF.object_map.get(y),
                    "target": cG.object_map.get(y), "expected_source": fgy})
        for m in sorted(self.D.morphisms):
            fgm = F.morphism_map.get(G.morphism_map.get(m))
            if fgm is None or cF.morphism_map.get(m) != fgm or cG.morphism_map.get(m) != m:
                ok = False
                self._record("counit_functor_mismatch", {
                    "morphism": m, "source": cF.morphism_map.get(m),
                    "target": cG.morphism_map.get(m), "expected_source": fgm})
        return ok

    def verify_components(self) -> bool:
        """η_X: X → G(F(X)) for X ∈ C and ε_Y: F(G(Y)) → Y for Y ∈ D."""
        ok = True
        for x in sorted(self.C.objects):
            eta = self.unit.components.get(x)
            if eta is None:
                ok = False
                self._record("unit_component_missing", {"object": x})
                continue
            expected = (x, self.G.object_map.get(self.F.object_map.get(x)))
            if None in expected or self.C.morphisms.get(eta) != expected:
                ok = False
                self._record("unit_component_typing", {
                    "object": x, "eta_x": eta, "expected": expected,
                    "actual": self.C.morphisms.get(eta)})
        for y in sorted(self.D.objects):
            eps = self.counit.components.get(y)
            if eps is None:
                ok = False
                self._record("counit_component_missing", {"object": y})
                continue
            expected = (self.F.object_map.get(self.G.object_map.get(y)), y)
            if None in expected or self.D.morphisms.get(eps) != expected:
                ok = False
                self._record("counit_component_typing", {
                    "object": y, "eps_y": eps, "expected": expected,
                    "actual": self.D.morphisms.get(eps)})
        return ok

    def verify_left_triangle(self) -> bool:
        """ε_{F(X)} ∘ F(η_X) = id_{F(X)} for every X ∈ C."""
        ok = True
        for x in sorted(self.C.objects):
            fx = self.F.object_map.get(x)
            eta = self.unit.components.get(x)
            f_eta = self.F.morphism_map.get(eta) if eta is not None else None
            eps = self.counit.components.get(fx) if fx is not None else None
            ident = self.D.identities.get(fx) if fx is not None else None
            details = {"X": x, "F(X)": fx, "eta_X": eta, "F(eta_X)": f_eta,
                       "eps_F(X)": eps, "id_F(X)": ident}
            if None in (fx, eta, f_eta, eps, ident):
                ok = False
                self._record("triangle_left_missing", details)
                continue
            comp = compose(self.D, f_eta, eps)
            if comp is None:
                ok = False
                self._record("triangle_left_composite_missing", details)
            elif comp != ident:
                ok = False
                self._record("triangle_left", {**details, "composite": comp})
        return ok

    def verify_right_triangle(self) -> bool:
        """G(ε_Y) ∘ η_{G(Y)} = id_{G(Y)} for every Y ∈ D."""
        ok = True
        for y in sorted(self.D.objects):
            gy = self.G.object_map.get(y)
            eps = self.counit.components.get(y)
            g_eps = self.G.morphism_map.get(eps) if eps is not None else None
            eta = self.unit.components.get(gy) if gy is not None else None
            ident = self.C.identities.get(gy) if gy is not None else None
            details = {"Y": y, "G(Y)": gy, "eps_Y": eps, "G(eps_Y)": g_eps,
                       "eta_G(Y)": eta, "id_G(Y)": ident}
            if None in (gy, eps, g_eps, eta, ident):
                ok = False
                self._record("triangle_right_missing", details)
                continue
            comp = compose(self.C, eta, g_eps)
            if comp is None:
                ok = False
                self._record("triangle_right_composite_missing", details)
            elif comp != ident:
                ok = False
                self._record("triangle_right", {**details, "composite": comp})
        return ok

    def verify_triangles(self) -> bool:
        left_ok = self.verify_left_triangle()
        right_ok = self.verify_right_triangle()
        return left_ok and right_ok

    def verify_all_laws(
        self,
        unit_generators: Optional[Iterable[str]] = None,
        counit_generators: Optional[Iterable[str]] = None,
    ) -> bool:
        """Typing, functors, components, naturality of η and ε, both triangles.

        `unit_generators` / `counit_generators` are passed to
        `NaturalTransformation.verify_naturality` (generator shortcut,
        `naturality_of_generators`).
        """
        if not self.verify_typing():
            return False
        functors_ok = self.verify_functors()
        components_ok = self.verify_components()
        unit_ok = self.unit.verify_naturality(unit_generators)
        counit_ok = self.counit.verify_naturality(counit_generators)
        triangles_ok = self.verify_triangles()
        return functors_ok and components_ok and unit_ok and counit_ok and triangles_ok

    # ---- Hom-set bijection -----------------------------------------------

    def left_adjunct(self, f: str) -> Optional[str]:
        """f: F(X) → Y  ↦  G(f) ∘ η_X : X → G(Y)  (`adjunctionOfChecks_homEquiv`).

        None if f is not a morphism out of some F(X) or the composite is not
        recorded.  When several X have F(X) = source(f), the transpose is not
        determined by f alone; use `left_adjunct_at`.
        """
        src = self.D.morphisms.get(f, (None, None))[0]
        xs = [x for x in sorted(self.C.objects) if self.F.object_map.get(x) == src]
        return self.left_adjunct_at(xs[0], f) if len(xs) == 1 else None

    def left_adjunct_at(self, x: str, f: str) -> Optional[str]:
        eta, gf = self.unit.components.get(x), self.G.morphism_map.get(f)
        if eta is None or gf is None:
            return None
        return compose(self.C, eta, gf)

    def right_adjunct(self, x: str, g: str) -> Optional[str]:
        """g: X → G(Y)  ↦  ε_Y ∘ F(g) : F(X) → Y  (`adjunctionOfChecks_homEquiv_symm`).

        `x` is the source of g; Y is found from its target, which must be
        G(Y) for exactly one Y.
        """
        if self.C.morphisms.get(g, (None, None))[0] != x:
            return None
        tgt = self.C.morphisms[g][1]
        ys = [y for y in sorted(self.D.objects) if self.G.object_map.get(y) == tgt]
        if len(ys) != 1:
            return None
        fg, eps = self.F.morphism_map.get(g), self.counit.components.get(ys[0])
        if fg is None or eps is None:
            return None
        return compose(self.D, fg, eps)

    # ---- Signed intent ----------------------------------------------------

    def serialize_intent(self) -> Tuple[bytes, SignedBlob]:
        intent = {
            "adjunction_id": self.adjunction_id,
            "name": self.name,
            "left_functor_id": self.F.functor_id,
            "right_functor_id": self.G.functor_id,
            "unit_id": self.unit.transformation_id,
            "counit_id": self.counit.transformation_id,
            "unit_components": dict(sorted(self.unit.components.items())),
            "counit_components": dict(sorted(self.counit.components.items())),
        }
        canonical = canonical_cbor(intent)
        return canonical, self.signer.sign(pq_hash(canonical))

    # ---- Internal ---------------------------------------------------------

    def _record(self, law: str, details: Dict[str, Any]) -> None:
        self.violations.append({"law": law, "details": details})
        if self.mode == EnforcementMode.STRICT:
            raise AdjunctionViolation(self.adjunction_id, law, details)
        logger.warning("Adjunction %s violation [%s]: %s", self.adjunction_id, law, details)
