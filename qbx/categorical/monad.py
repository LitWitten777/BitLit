"""
Monad / comonad law enforcement (Phase 1, sprint 3).

A monad on a category C is an endofunctor T with natural transformations
η: Id_C ⇒ T and μ: T∘T ⇒ T such that, for every object X,

    left_unit      μ_X ∘ T(η_X)   = id_{T(X)}
    right_unit     μ_X ∘ η_{T(X)} = id_{T(X)}
    associativity  μ_X ∘ T(μ_X)   = μ_X ∘ μ_{T(X)}

A comonad (G, ε: G ⇒ Id_C, δ: G ⇒ G∘G) satisfies the duals

    left_counit      ε_{G(X)} ∘ δ_X = id_{G(X)}
    right_counit     G(ε_X) ∘ δ_X   = id_{G(X)}
    coassociativity  δ_{G(X)} ∘ δ_X = G(δ_X) ∘ δ_X

This module is the in-memory reference implementation of the checker that
migration 006 runs in Postgres (same violation law names, same STRICT /
PERMISSIVE modes).  Mathlib's `CategoryTheory.Monad` names the two unit laws
the other way round (its `left_unit` is η_{T(X)} ≫ μ_X = 𝟙, i.e. `right_unit`
here).

Formal backing (`Formal/Monad.lean`, registry H-016 – H-018):

* `QBX.Formal.monadOfChecks` / `comonadOfChecks`: data passing every check
  (naturality, possibly only on generators, and the three laws) is a genuine
  Mathlib monad / comonad; `exists_monad_iff_laws` /
  `exists_comonad_iff_laws`: the checks are also necessary.
* `QBX.Formal.left_unit_independent` / `right_unit_independent` /
  `assoc_independent`: none of the three monad laws follows from the other two,
  even for natural η and μ, so all three are checked.
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


class MonadViolation(QBXError):
    """Raised (STRICT mode) when a monad or comonad law is violated."""

    def __init__(self, monad_id: str, law: str, details: dict):
        self.monad_id = monad_id
        self.law = law
        self.details = details
        super().__init__(f"Monad {monad_id} violated {law}: {details}")


class _EndoStructure:
    """Shared machinery: an endofunctor with two structure transformations."""

    kind = "monad"

    def __init__(self, structure_id: str, name: str, endofunctor: EnforcedFunctor,
                 first: NaturalTransformation, second: NaturalTransformation,
                 mode: Optional[EnforcementMode] = None,
                 signer: Optional[StubSigner] = None):
        self.structure_id = structure_id
        self.name = name
        self.T = endofunctor
        self.first = first
        self.second = second
        self.mode = mode or EnforcementMode.from_env()
        self.signer = signer or StubSigner()
        self.violations: List[Dict[str, Any]] = []

    @property
    def C(self) -> Category:
        return self.T.source

    # ---- helpers ------------------------------------------------------------

    def _tobj(self, x: Optional[str]) -> Optional[str]:
        return None if x is None else self.T.object_map.get(x)

    def _tmor(self, m: Optional[str]) -> Optional[str]:
        return None if m is None else self.T.morphism_map.get(m)

    def _expected(self, spec: str, kind: str, a: str) -> Optional[str]:
        """Image of `a` under Id ('1'), T ('T') or T∘T ('TT')."""
        step = self._tobj if kind == "object" else self._tmor
        if spec == "1":
            return a
        if spec == "T":
            return step(a)
        return step(step(a))

    def verify_typing(self) -> bool:
        C = self.C
        ok = self.T.target is C and all(
            nt.source is C and nt.target is C for nt in (self.first, self.second))
        if not ok:
            self._record(f"{self.kind}_typing", {
                "T": (self.T.source.id, self.T.target.id),
                "first": (self.first.source.id, self.first.target.id),
                "second": (self.second.source.id, self.second.target.id),
            })
        return ok

    def _verify_functor_pair(self, nt: NaturalTransformation, law: str,
                             src_spec: str, tgt_spec: str) -> bool:
        ok = True
        for kind, items, attr in (("object", self.C.objects, "object_map"),
                                  ("morphism", self.C.morphisms, "morphism_map")):
            for a in sorted(items):
                es = self._expected(src_spec, kind, a)
                et = self._expected(tgt_spec, kind, a)
                s = getattr(nt.F, attr).get(a)
                t = getattr(nt.G, attr).get(a)
                if es is None or et is None or s != es or t != et:
                    ok = False
                    self._record(law, {kind: a, "source": s, "target": t,
                                       "expected_source": es, "expected_target": et})
        return ok

    def _verify_components_of(self, nt: NaturalTransformation, name: str,
                              src_spec: str, tgt_spec: str) -> bool:
        ok = True
        for x in sorted(self.C.objects):
            comp = nt.components.get(x)
            if comp is None:
                ok = False
                self._record(f"{name}_component_missing", {"object": x})
                continue
            expected = (self._expected(src_spec, "object", x),
                        self._expected(tgt_spec, "object", x))
            if None in expected or self.C.morphisms.get(comp) != expected:
                ok = False
                self._record(f"{name}_component_typing", {
                    "object": x, "component": comp, "expected": expected,
                    "actual": self.C.morphisms.get(comp)})
        return ok

    def _check_identity_law(self, law: str, x: str, first: Optional[str],
                            second: Optional[str], ident: Optional[str],
                            details: Dict[str, Any]) -> bool:
        """second ∘ first = ident."""
        details = {"X": x, **details}
        if None in (first, second, ident):
            self._record(f"{law}_missing", details)
            return False
        comp = compose(self.C, first, second)
        if comp is None:
            self._record(f"{law}_composite_missing", details)
            return False
        if comp != ident:
            self._record(law, {**details, "composite": comp, "identity": ident})
            return False
        return True

    def _check_equal_composites(self, law: str, x: str,
                                lhs_pair: Tuple[Optional[str], Optional[str]],
                                rhs_pair: Tuple[Optional[str], Optional[str]],
                                details: Dict[str, Any]) -> bool:
        details = {"X": x, **details}
        if None in lhs_pair or None in rhs_pair:
            self._record(f"{law}_missing", details)
            return False
        lhs = compose(self.C, *lhs_pair)
        rhs = compose(self.C, *rhs_pair)
        if lhs is None or rhs is None:
            self._record(f"{law}_composite_missing", {**details, "lhs": lhs, "rhs": rhs})
            return False
        if lhs != rhs:
            self._record(law, {**details, "lhs": lhs, "rhs": rhs})
            return False
        return True

    def _record(self, law: str, details: Dict[str, Any]) -> None:
        self.violations.append({"law": law, "details": details})
        if self.mode == EnforcementMode.STRICT:
            raise MonadViolation(self.structure_id, law, details)
        logger.warning("%s %s violation [%s]: %s", self.kind, self.structure_id, law, details)

    def serialize_intent(self) -> Tuple[bytes, SignedBlob]:
        intent = {
            f"{self.kind}_id": self.structure_id,
            "name": self.name,
            "endofunctor_id": self.T.functor_id,
            "first_id": self.first.transformation_id,
            "second_id": self.second.transformation_id,
            "first_components": dict(sorted(self.first.components.items())),
            "second_components": dict(sorted(self.second.components.items())),
        }
        canonical = canonical_cbor(intent)
        return canonical, self.signer.sign(pq_hash(canonical))


class Monad(_EndoStructure):
    """(T, η: Id ⇒ T, μ: T∘T ⇒ T).  `unit.F`/`unit.G` must agree with Id/T and
    `multiplication.F`/`multiplication.G` with T∘T/T (use `IdentityFunctor`,
    `ComposedFunctor(T, T)`)."""

    kind = "monad"

    def __init__(self, monad_id: str, name: str, endofunctor: EnforcedFunctor,
                 unit: NaturalTransformation, multiplication: NaturalTransformation,
                 mode: Optional[EnforcementMode] = None,
                 signer: Optional[StubSigner] = None):
        super().__init__(monad_id, name, endofunctor, unit, multiplication, mode, signer)

    @property
    def unit(self) -> NaturalTransformation:
        return self.first

    @property
    def multiplication(self) -> NaturalTransformation:
        return self.second

    def verify_functors(self) -> bool:
        a = self._verify_functor_pair(self.unit, "unit_functor_mismatch", "1", "T")
        b = self._verify_functor_pair(self.multiplication,
                                      "multiplication_functor_mismatch", "TT", "T")
        return a and b

    def verify_components(self) -> bool:
        a = self._verify_components_of(self.unit, "unit", "1", "T")
        b = self._verify_components_of(self.multiplication, "multiplication", "TT", "T")
        return a and b

    def verify_laws(self) -> bool:
        ok = True
        eta, mu = self.unit.components, self.multiplication.components
        for x in sorted(self.C.objects):
            tx = self._tobj(x)
            ident = self.C.identities.get(tx) if tx is not None else None
            mu_x = mu.get(x)
            t_eta = self._tmor(eta.get(x))
            eta_t = eta.get(tx) if tx is not None else None
            t_mu = self._tmor(mu_x)
            mu_t = mu.get(tx) if tx is not None else None
            ok &= self._check_identity_law("left_unit", x, t_eta, mu_x, ident,
                                           {"mu_X": mu_x, "T(eta_X)": t_eta})
            ok &= self._check_identity_law("right_unit", x, eta_t, mu_x, ident,
                                           {"mu_X": mu_x, "eta_T(X)": eta_t})
            ok &= self._check_equal_composites(
                "associativity", x, (t_mu, mu_x), (mu_t, mu_x),
                {"mu_X": mu_x, "T(mu_X)": t_mu, "mu_T(X)": mu_t})
        return bool(ok)

    def verify_all_laws(self, unit_generators: Optional[Iterable[str]] = None,
                        multiplication_generators: Optional[Iterable[str]] = None) -> bool:
        """Typing, functors, components, naturality of η and μ, the three laws."""
        if not self.verify_typing():
            return False
        functors_ok = self.verify_functors()
        components_ok = self.verify_components()
        unit_ok = self.unit.verify_naturality(unit_generators)
        mult_ok = self.multiplication.verify_naturality(multiplication_generators)
        laws_ok = self.verify_laws()
        return functors_ok and components_ok and unit_ok and mult_ok and laws_ok

    # ---- Kleisli composition ---------------------------------------------

    def kleisli_compose(self, f: str, g: str, z: Optional[str] = None) -> Optional[str]:
        """For f: X → T(Y) and g: Y → T(Z), the Kleisli composite
        μ_Z ∘ T(g) ∘ f : X → T(Z).

        `z` names Z; it may be omitted when exactly one object Z has
        T(Z) = target(g).  None if any piece is not recorded."""
        if f not in self.C.morphisms or g not in self.C.morphisms:
            return None
        z_t = self.C.morphisms[g][1]
        if z is None:
            zs = [o for o in sorted(self.C.objects) if self._tobj(o) == z_t]
            if len(zs) != 1:
                return None
            z = zs[0]
        elif self._tobj(z) != z_t:
            return None
        mu_z, tg = self.multiplication.components.get(z), self._tmor(g)
        if mu_z is None or tg is None:
            return None
        step = compose(self.C, f, tg)
        return None if step is None else compose(self.C, step, mu_z)


class Comonad(_EndoStructure):
    """(G, ε: G ⇒ Id, δ: G ⇒ G∘G)."""

    kind = "comonad"

    def __init__(self, comonad_id: str, name: str, endofunctor: EnforcedFunctor,
                 counit: NaturalTransformation, comultiplication: NaturalTransformation,
                 mode: Optional[EnforcementMode] = None,
                 signer: Optional[StubSigner] = None):
        super().__init__(comonad_id, name, endofunctor, counit, comultiplication, mode, signer)

    @property
    def counit(self) -> NaturalTransformation:
        return self.first

    @property
    def comultiplication(self) -> NaturalTransformation:
        return self.second

    def verify_functors(self) -> bool:
        a = self._verify_functor_pair(self.counit, "counit_functor_mismatch", "T", "1")
        b = self._verify_functor_pair(self.comultiplication,
                                      "comultiplication_functor_mismatch", "T", "TT")
        return a and b

    def verify_components(self) -> bool:
        a = self._verify_components_of(self.counit, "counit", "T", "1")
        b = self._verify_components_of(self.comultiplication, "comultiplication", "T", "TT")
        return a and b

    def verify_laws(self) -> bool:
        ok = True
        eps, delta = self.counit.components, self.comultiplication.components
        for x in sorted(self.C.objects):
            gx = self._tobj(x)
            ident = self.C.identities.get(gx) if gx is not None else None
            d_x = delta.get(x)
            eps_g = eps.get(gx) if gx is not None else None
            g_eps = self._tmor(eps.get(x))
            d_g = delta.get(gx) if gx is not None else None
            g_d = self._tmor(d_x)
            ok &= self._check_identity_law("left_counit", x, d_x, eps_g, ident,
                                           {"delta_X": d_x, "eps_G(X)": eps_g})
            ok &= self._check_identity_law("right_counit", x, d_x, g_eps, ident,
                                           {"delta_X": d_x, "G(eps_X)": g_eps})
            ok &= self._check_equal_composites(
                "coassociativity", x, (d_x, d_g), (d_x, g_d),
                {"delta_X": d_x, "delta_G(X)": d_g, "G(delta_X)": g_d})
        return bool(ok)

    def verify_all_laws(self, counit_generators: Optional[Iterable[str]] = None,
                        comultiplication_generators: Optional[Iterable[str]] = None) -> bool:
        if not self.verify_typing():
            return False
        functors_ok = self.verify_functors()
        components_ok = self.verify_components()
        counit_ok = self.counit.verify_naturality(counit_generators)
        comult_ok = self.comultiplication.verify_naturality(comultiplication_generators)
        laws_ok = self.verify_laws()
        return functors_ok and components_ok and counit_ok and comult_ok and laws_ok
