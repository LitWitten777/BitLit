"""
EnforcedFunctor: the core of Phase 0.

A functor F: C → D must satisfy:

- Identity law:      F(id_X) = id_{F(X)}
- Composition law:   F(g ∘ f) = F(g) ∘ F(f)

This module provides both:

- A runtime base class that validates mappings before commit.
- A serialization helper that produces a "signed mapping intent" so DB
  triggers can verify the mapping independently.

Two enforcement modes:

- STRICT:     raise FunctorLawViolation on any violation.
- PERMISSIVE: log + quarantine; return None for the offending mapping.
"""

from __future__ import annotations

import logging
import os
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional, Tuple

from qbx.core.canonical import canonical_cbor
from qbx.core.exceptions import (
    FunctorLawViolation,
    CanonicalizationError,
)
from qbx.core.hashing import pq_hash
from qbx.core.signing import SignedBlob, StubSigner

logger = logging.getLogger(__name__)


class EnforcementMode(str, Enum):
    STRICT = "strict"
    PERMISSIVE = "permissive"

    @classmethod
    def from_env(cls) -> "EnforcementMode":
        raw = os.getenv("QBX_ENFORCEMENT_MODE", "permissive").lower()
        try:
            return cls(raw)
        except ValueError:
            logger.warning("Unknown enforcement mode %r, defaulting to permissive", raw)
            return cls.PERMISSIVE


# ----------------------------------------------------------------------------
# Minimal in-memory category model — used for runtime law checks.
# The real system uses Postgres; this is a self-contained reference impl.
# ----------------------------------------------------------------------------


@dataclass
class Category:
    """A small in-memory category for law testing."""

    id: str
    name: str
    objects: Dict[str, str] = field(default_factory=dict)  # obj_id → name
    morphisms: Dict[str, Tuple[str, str]] = field(default_factory=dict)  # morph_id → (src, tgt)
    identities: Dict[str, str] = field(default_factory=dict)  # obj_id → identity morph_id
    compositions: Dict[Tuple[str, str], str] = field(default_factory=dict)
    # compositions[(f, g)] = h  means  h = g ∘ f  (f then g)

    def add_object(self, obj_id: str, name: str) -> None:
        self.objects[obj_id] = name

    def add_morphism(self, morph_id: str, src: str, tgt: str) -> None:
        self.morphisms[morph_id] = (src, tgt)

    def add_identity(self, obj_id: str, morph_id: str) -> None:
        self.morphisms[morph_id] = (obj_id, obj_id)
        self.identities[obj_id] = morph_id

    def add_composition(self, f: str, g: str, h: str) -> None:
        """h = g ∘ f  (apply f first, then g)."""
        self.compositions[(f, g)] = h

    def compose(self, f: str, g: str) -> Optional[str]:
        return self.compositions.get((f, g))


# ----------------------------------------------------------------------------
# EnforcedFunctor
# ----------------------------------------------------------------------------


class EnforcedFunctor:
    """
    Base class for functors with enforced laws.

    Subclasses override `_map_object` and `_map_morphism` to define the functor's
    action. This class provides law verification and signed-intent serialization.
    """

    def __init__(
        self,
        functor_id: str,
        name: str,
        source: Category,
        target: Category,
        mode: Optional[EnforcementMode] = None,
        signer: Optional[StubSigner] = None,
    ):
        self.functor_id = functor_id
        self.name = name
        self.source = source
        self.target = target
        self.mode = mode or EnforcementMode.from_env()
        self.signer = signer or StubSigner()

        self.object_map: Dict[str, str] = {}
        self.morphism_map: Dict[str, str] = {}
        self.violations: List[Dict[str, Any]] = []

    # ---- Subclass hooks ---------------------------------------------------

    def _map_object(self, obj_id: str) -> str:
        raise NotImplementedError("Subclasses must implement _map_object")

    def _map_morphism(self, morph_id: str) -> str:
        raise NotImplementedError("Subclasses must implement _map_morphism")

    # ---- Public API -------------------------------------------------------

    def map_object(self, obj_id: str) -> Optional[str]:
        try:
            target_obj = self._map_object(obj_id)
        except Exception as e:
            self._record("object_map_error", {"obj_id": obj_id, "error": str(e)})
            return None
        self.object_map[obj_id] = target_obj
        return target_obj

    def map_morphism(self, morph_id: str) -> Optional[str]:
        try:
            target_morph = self._map_morphism(morph_id)
        except Exception as e:
            self._record("morphism_map_error", {"morph_id": morph_id, "error": str(e)})
            return None
        self.morphism_map[morph_id] = target_morph
        return target_morph

    def verify_identity_law(self) -> bool:
        """F(id_X) = id_{F(X)} for all X."""
        ok = True
        for obj_id, id_morph in self.source.identities.items():
            if obj_id not in self.object_map:
                self._record("identity_missing_object_map", {"obj_id": obj_id})
                ok = False
                continue
            target_obj = self.object_map[obj_id]
            if target_obj not in self.target.identities:
                self._record(
                    "identity_missing_target_identity",
                    {"obj_id": obj_id, "target_obj": target_obj},
                )
                ok = False
                continue
            mapped_id = self.morphism_map.get(id_morph)
            expected = self.target.identities[target_obj]
            if mapped_id != expected:
                self._record(
                    "identity_law",
                    {
                        "obj_id": obj_id,
                        "source_identity": id_morph,
                        "mapped": mapped_id,
                        "expected": expected,
                    },
                )
                ok = False
        return ok

    def verify_composition_law(self) -> bool:
        """F(g ∘ f) = F(g) ∘ F(f) for all composable pairs."""
        ok = True
        for (f, g), h in self.source.compositions.items():
            Ff = self.morphism_map.get(f)
            Fg = self.morphism_map.get(g)
            Fh = self.morphism_map.get(h)
            if Ff is None or Fg is None or Fh is None:
                self._record(
                    "composition_missing_map",
                    {"f": f, "g": g, "h": h, "Ff": Ff, "Fg": Fg, "Fh": Fh},
                )
                ok = False
                continue
            composed = self.target.compose(Ff, Fg)
            if composed != Fh:
                self._record(
                    "composition_law",
                    {
                        "f": f, "g": g, "h": h,
                        "Ff": Ff, "Fg": Fg, "Fh": Fh,
                        "target_compose(Ff,Fg)": composed,
                    },
                )
                ok = False
        return ok

    def verify_all_laws(self) -> bool:
        id_ok = self.verify_identity_law()
        comp_ok = self.verify_composition_law()
        return id_ok and comp_ok

    # ---- Signed mapping intent -------------------------------------------

    def serialize_mapping_intent(self) -> Tuple[bytes, SignedBlob]:
        """
        Produce a canonical CBOR encoding of the functor's mappings, hash it,
        and sign the hash. DB triggers can verify the intent independently.
        """
        intent = {
            "functor_id": self.functor_id,
            "name": self.name,
            "source_category_id": self.source.id,
            "target_category_id": self.target.id,
            "object_map": dict(sorted(self.object_map.items())),
            "morphism_map": dict(sorted(self.morphism_map.items())),
        }
        try:
            canonical = canonical_cbor(intent)
        except CanonicalizationError as e:
            raise FunctorLawViolation(
                self.functor_id, "canonicalization", {"error": str(e)}
            )
        digest = pq_hash(canonical)
        blob = self.signer.sign(digest)
        return canonical, blob

    # ---- Internal ---------------------------------------------------------

    def _record(self, law: str, details: Dict[str, Any]) -> None:
        entry = {"law": law, "details": details}
        self.violations.append(entry)
        if self.mode == EnforcementMode.STRICT:
            raise FunctorLawViolation(self.functor_id, law, details)
        else:
            logger.warning(
                "Functor %s law violation [%s]: %s",
                self.functor_id, law, details,
            )
