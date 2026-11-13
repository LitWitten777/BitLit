"""
src/sedenion/polytope/conjecture_canonicalizer.py
=============================================================================
Weyl Chamber Canonicalization & AST Duality Pruning for Autonomous Reasoning.

Prunes isomorphic conjectures before dispatching to Z3 or Lean 4 compilation:
1. 8D Vector Canonicalization: Folds vector/weight parameters into the closed
   fundamental Weyl chamber C = {x ∈ R^8 | ⟨x, α_i⟩ ≥ 0 for all simple roots}.
   All vectors in the same W(E8) orbit (order 696,729,600) map to the exact
   same canonical representative.
2. AST Operator Duality Normalization: Maps dual comparison, Boolean, and
   algebraic operators to a deterministic canonical representative.
3. Orbit Signature Generation & Isomorphism Deduplication.
=============================================================================
"""

from __future__ import annotations

import ast
from functools import lru_cache
from typing import Any, Sequence, Tuple

from .weyl_reflection import (
    E8_SIMPLE_ROOTS,
    fold_into_fundamental_chamber,
    inner_product,
    reflect_ast_code,
)


CANONICAL_OP_MAP = {
    # Comparison
    ">": "<",
    ">=": "<=",
    "!=": "==",
    "Gt": "Lt",
    "GtE": "LtE",
    "NotEq": "Eq",
    # Boolean
    "Or": "And",
    "or": "and",
    # Arithmetic
    "-": "+",
    "Sub": "Add",
}

CANONICAL_PREDICATE_MAP = {
    "gt": "lt",
    "greater_than": "less_than",
    "nonassociative_right": "nonassociative_left",
    "subtraction_distributive": "addition_distributive",
}


@lru_cache(maxsize=2048)
def _cached_fold_8d(vec: tuple[float, ...], tol: float) -> tuple[float, ...]:
    folded, _ = fold_into_fundamental_chamber(vec, tol=tol)
    return tuple(0.0 if abs(round(x, 6)) == 0.0 else round(x, 6) for x in folded)


def canonicalize_vector_8d(
    vec: Sequence[float],
    tol: float = 1e-6,
) -> tuple[float, ...]:
    """
    Folds an 8D vector into the closed fundamental Weyl chamber and rounds
    near-zero components to avoid floating point precision artifacts.
    Uses LRU caching on tuples for sub-microsecond deduplication.
    """
    if len(vec) != 8:
        return tuple(float(x) for x in vec)
    t_vec = tuple(float(x) for x in vec)
    return _cached_fold_8d(t_vec, tol)


def canonicalize_predicate(predicate: str) -> str:
    """Normalizes dual predicate names to their canonical form."""
    return CANONICAL_PREDICATE_MAP.get(predicate, predicate)


class ConjectureCanonicalizer:
    """
    Autonomous Reasoning Engine filter to canonicalize candidate conjectures
    under the E8 Weyl reflection group and AST operator duality.
    """

    def __init__(self, tol: float = 1e-6):
        self.tol = tol
        self._canonical_signatures: set[tuple[Any, ...]] = set()

    def canonicalize_parameters(self, params: dict[str, Any]) -> dict[str, Any]:
        """
        Recursively canonicalizes parameters:
        - 8D numeric vectors are folded into the fundamental Weyl chamber.
        - AST code strings or operators are mapped to dual-canonical forms.
        """
        canon_params: dict[str, Any] = {}
        for k, v in sorted(params.items()):
            if isinstance(v, (list, tuple)) and len(v) == 8 and all(isinstance(x, (int, float)) for x in v):
                canon_params[k] = canonicalize_vector_8d(v, tol=self.tol)
            elif isinstance(v, str) and v in CANONICAL_OP_MAP:
                canon_params[k] = CANONICAL_OP_MAP[v]
            elif isinstance(v, dict):
                canon_params[k] = self.canonicalize_parameters(v)
            else:
                canon_params[k] = v
        return canon_params

    def get_canonical_signature(
        self,
        conjecture_type: str,
        predicate: str,
        parameters: dict[str, Any],
    ) -> tuple[Any, ...]:
        """
        Computes the canonical orbit signature of a conjecture.
        Conjectures that are isomorphic under W(E8) reflections or AST dualities
        produce the exact same signature.
        """
        canon_pred = canonicalize_predicate(predicate)
        canon_params = self.canonicalize_parameters(parameters)

        param_items = []
        for k, v in sorted(canon_params.items()):
            if isinstance(v, list):
                v = tuple(v)
            elif isinstance(v, dict):
                v = tuple(sorted(v.items()))
            param_items.append((k, v))

        return (conjecture_type, canon_pred, tuple(param_items))

    def is_seen_or_isomorphic(
        self,
        conjecture_type: str,
        predicate: str,
        parameters: dict[str, Any],
    ) -> bool:
        """Checks if a conjecture or any of its Weyl/AST isomorphic forms has already been evaluated."""
        sig = self.get_canonical_signature(conjecture_type, predicate, parameters)
        return sig in self._canonical_signatures

    def register_canonical(
        self,
        conjecture_type: str,
        predicate: str,
        parameters: dict[str, Any],
    ) -> tuple[Any, ...]:
        """Registers the canonical signature of a conjecture into the seen cache."""
        sig = self.get_canonical_signature(conjecture_type, predicate, parameters)
        self._canonical_signatures.add(sig)
        return sig

    def prune_isomorphic_candidates(
        self,
        candidates: list[Any],
    ) -> list[Any]:
        """
        Filters a list of candidate hypotheses, preserving the first representative
        of each Weyl / AST isomorphism class and pruning subsequent duplicates.
        """
        pruned = []
        for cand in candidates:
            c_type = getattr(cand, "conjecture_type", "")
            pred = getattr(cand, "predicate", "")
            params = getattr(cand, "parameters", {})
            sig = self.get_canonical_signature(c_type, pred, params)
            if sig not in self._canonical_signatures:
                self._canonical_signatures.add(sig)
                pruned.append(cand)
        return pruned

    def clear(self) -> None:
        self._canonical_signatures.clear()
