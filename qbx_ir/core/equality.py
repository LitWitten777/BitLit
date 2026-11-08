"""
The five equalities of QBX-IR (QBX.md §20).

- SYNTACTIC:      B1 ≡ B2 iff same strand count and identical generator words.
- WORD:           B1 = B2 in the braid group B_n.  Decided *exactly* by
                  comparing Garside left normal forms.
- TOPOLOGICAL:    B1 ≃ B2.  For braids (isotopy rel endpoints) this coincides
                  with WORD equality by Artin's theorem; with ``closure=True``
                  it compares the *closures* as links, which is only
                  semi-decided: certified-equal if the braids are equal,
                  certified-different if a link invariant separates them,
                  otherwise undetermined (``certain=False``).
- REPRESENTATION: ρ(B1) = ρ(B2) for a chosen representation (numerically, up to
                  a tolerance, or exactly when the representation function returns
                  :class:`qbx_ir.quantum.exact.ExactMatrix`, e.g.
                  :class:`qbx_ir.quantum.exact.ExactSL2Representation`).
- PHYSICAL:       B1 ~ B2 under a user-supplied physical equivalence.

These are NEVER conflated: a caller must explicitly choose which equality.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Callable, Optional

from qbx_ir.core.braid import Braid


class EqualityKind(str, Enum):
    SYNTACTIC = "syntactic"
    WORD = "word"
    TOPOLOGICAL = "topological"
    REPRESENTATION = "representation"
    PHYSICAL = "physical"


@dataclass
class EqualityResult:
    kind: EqualityKind
    equal: bool
    witness: Optional[Any] = None
    details: Optional[str] = None
    certain: bool = True

    def __bool__(self) -> bool:
        return self.equal


def check_equality(
    b1: Braid,
    b2: Braid,
    kind: EqualityKind,
    representation_fn: Optional[Callable[[Braid], Any]] = None,
    physical_fn: Optional[Callable[[Braid, Braid], bool]] = None,
    tol: float = 1e-9,
    closure: bool = False,
) -> EqualityResult:
    """Check a specific kind of equality between two braids."""
    kind = EqualityKind(kind)
    if kind == EqualityKind.SYNTACTIC:
        return _check_syntactic(b1, b2)
    if kind == EqualityKind.WORD:
        return _check_word(b1, b2)
    if kind == EqualityKind.TOPOLOGICAL:
        return _check_topological(b1, b2, closure)
    if kind == EqualityKind.REPRESENTATION:
        return _check_representation(b1, b2, representation_fn, tol)
    if kind == EqualityKind.PHYSICAL:
        return _check_physical(b1, b2, physical_fn)
    raise ValueError(f"Unknown equality kind: {kind}")


def _check_syntactic(b1: Braid, b2: Braid) -> EqualityResult:
    """Same strand count, same word (as generators)."""
    equal = b1.strand_count == b2.strand_count and b1.word == b2.word
    return EqualityResult(
        kind=EqualityKind.SYNTACTIC,
        equal=equal,
        witness=(b1.short_form(), b2.short_form()),
    )


def _check_word(b1: Braid, b2: Braid) -> EqualityResult:
    """Equality in B_n via Garside left normal forms (exact)."""
    from qbx_ir.algebra.garside import left_normal_form

    if b1.strand_count != b2.strand_count:
        return EqualityResult(EqualityKind.WORD, False, details="Different strand counts")
    n1 = left_normal_form(b1)
    n2 = left_normal_form(b2)
    return EqualityResult(
        kind=EqualityKind.WORD,
        equal=(n1 == n2),
        witness=(str(n1), str(n2)),
        details="Garside left normal form comparison (exact)",
    )


def _check_topological(b1: Braid, b2: Braid, closure: bool) -> EqualityResult:
    from qbx_ir.algebra.garside import braid_group_equal
    from qbx_ir.algebra.invariants import closure_components, linking_number, permutation, writhe

    if not closure:
        if b1.strand_count != b2.strand_count:
            return EqualityResult(EqualityKind.TOPOLOGICAL, False,
                                  details="Different strand counts")
        equal = braid_group_equal(b1, b2)
        return EqualityResult(
            kind=EqualityKind.TOPOLOGICAL,
            equal=equal,
            witness=(permutation(b1), permutation(b2), writhe(b1), writhe(b2)),
            details="Braid isotopy rel endpoints = equality in B_n (Artin); "
                    "decided via Garside normal form",
        )

    # Closure (link) comparison: semi-decision.
    if b1.strand_count == b2.strand_count and braid_group_equal(b1, b2):
        return EqualityResult(EqualityKind.TOPOLOGICAL, True,
                              details="Equal braids have isotopic closures")
    from qbx_ir.algebra.polynomial_invariants import (
        MAX_STATE_SUM_CROSSINGS,
        alexander_polynomial,
        jones_polynomial,
    )

    inv1 = [("components", len(closure_components(b1))),
            ("linking_number", linking_number(b1))]
    inv2 = [("components", len(closure_components(b2))),
            ("linking_number", linking_number(b2))]
    inv1.append(("alexander", alexander_polynomial(b1)))
    inv2.append(("alexander", alexander_polynomial(b2)))
    if max(len(b1), len(b2)) <= MAX_STATE_SUM_CROSSINGS:
        inv1.append(("jones", jones_polynomial(b1)))
        inv2.append(("jones", jones_polynomial(b2)))
    for (name, v1), (_, v2) in zip(inv1, inv2):
        if v1 != v2:
            return EqualityResult(
                EqualityKind.TOPOLOGICAL, False, witness=(name, v1, v2),
                details=f"Closures separated by invariant '{name}'",
            )
    return EqualityResult(
        EqualityKind.TOPOLOGICAL, False, certain=False,
        details="Closure invariants agree; link isotopy undetermined",
    )


def _check_representation(
    b1: Braid,
    b2: Braid,
    representation_fn: Optional[Callable[[Braid], Any]],
    tol: float,
) -> EqualityResult:
    """ρ(B1) = ρ(B2) for the supplied representation function."""
    if representation_fn is None:
        return EqualityResult(
            kind=EqualityKind.REPRESENTATION,
            equal=False,
            details="No representation function supplied",
            certain=False,
        )
    u1 = representation_fn(b1)
    u2 = representation_fn(b2)
    from qbx_ir.quantum.exact import ExactMatrix

    if isinstance(u1, ExactMatrix) and isinstance(u2, ExactMatrix):
        # Exact arithmetic (qbx_ir.quantum.exact): reduced fractions are unique, so
        # comparing them compares the matrices exactly (Lean: repCert_eq_iff).
        return EqualityResult(
            kind=EqualityKind.REPRESENTATION,
            equal=(u1 == u2),
            witness=(u1.denominator, u2.denominator),
            details="exact comparison of reduced rational matrices",
        )
    try:
        diff = float(abs(u1 - u2).max())
    except Exception as e:  # pragma: no cover - defensive
        return EqualityResult(
            kind=EqualityKind.REPRESENTATION,
            equal=False,
            details=f"Comparison failed: {e}",
            certain=False,
        )
    return EqualityResult(
        kind=EqualityKind.REPRESENTATION,
        equal=diff < tol,
        witness=diff,
        details=f"max |U1 - U2| = {diff:.3e}",
    )


def _check_physical(
    b1: Braid,
    b2: Braid,
    physical_fn: Optional[Callable[[Braid, Braid], bool]],
) -> EqualityResult:
    """Physical equivalence via user-supplied predicate."""
    if physical_fn is None:
        return EqualityResult(
            kind=EqualityKind.PHYSICAL,
            equal=False,
            details="No physical predicate supplied",
            certain=False,
        )
    return EqualityResult(kind=EqualityKind.PHYSICAL, equal=bool(physical_fn(b1, b2)))
