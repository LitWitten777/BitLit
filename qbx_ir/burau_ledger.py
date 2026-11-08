"""
Reference implementation of the reduced Burau / Alexander certificates (migration 024).

Migration ``024_braid_burau.sql`` stores, for a braid of the braid ledger
(migration 019, :mod:`qbx_ir.ledger`), the **symbolic** reduced Burau matrix
``ρ̄(B) ∈ GL_{n-1}(ℤ[t, t⁻¹])`` of
:func:`qbx_ir.algebra.polynomial_invariants.burau_matrix` (generators multiplied
in word order) and the Alexander polynomial of the closure of
:func:`qbx_ir.algebra.polynomial_invariants.alexander_polynomial`, table
``braid_burau``:

* ``size``         — ``n - 1``;
* ``exp_min``, ``width`` — the common exponent window of the entries: every
  non-zero coefficient has exponent in ``[exp_min, exp_min + width)``, and the
  window is the smallest one (some entry has a non-zero coefficient at
  ``exp_min`` and some entry at ``exp_min + width - 1``); ``exp_min = width = 0``
  for the empty matrix (``n = 1``);
* ``coefficients`` — ``size² · width`` integers: the coefficient of
  ``t^(exp_min + k)`` in entry ``(i, j)`` (0-indexed) is at index
  ``(i · size + j) · width + k``;
* ``alexander``    — the coefficients ``c_0, c_1, …`` of the Alexander
  polynomial normalised up to ``±t^k`` (lowest degree 0, lowest coefficient
  positive); empty when it is 0 (split closures);
* ``braid_hash``   — the hash of the certified braid, copied for tamper evidence.

Because the window is the smallest one, the encoding of a matrix is unique: two
certificates are equal **iff** the two Burau matrices are equal.  Uses:

* ``braid_burau_equal(a, b)``: TRUE — ``ρ̄(a) = ρ̄(b)`` (representation equality;
  the reduced Burau representation is not faithful for ``n ≥ 5``, so this does
  **not** prove ``a = b``); FALSE — the braids are different elements of
  ``B_n``; NULL — not comparable;
* ``braid_alexander_equal(a, b)``: FALSE — the braids are not conjugate in
  ``B_n`` (the Alexander numerator ``det(I - ρ̄(B))`` is a conjugacy invariant);
* transport: along every accepted rewrite and derivation the certificates must
  agree (matrix and Alexander polynomial);
* consistency with migration 021: two braids certified equal by their normal
  forms must not have different certificates.

This module is the in-memory reference: the database reports exactly the
problems listed here, in the same order, with the same details
(``tests/live_db/test_braid_burau_db.py``).

Lean: ``QBX/Formal/BurauRep.lean`` (the generator matrices satisfy the braid
relations for every ``n`` — ``burauRep``, ``Word.burau_eq_of_eval_eq``; the
characteristic polynomial and ``det(I - ρ̄)`` are conjugacy invariants —
``Word.burau_charpoly_conj``, ``Word.alexNum_conj``) and
``QBX/Formal/BraidBurauCert.lean`` (the encoding is unique —
``burauCert_eq_iff``; equal braids have equal certificates; the Lean model
gives exactly this module's values on test vectors) — registry H-063, H-064.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from qbx_ir.algebra.polynomial_invariants import alexander_polynomial, burau_matrix
from qbx_ir.core.braid import Braid
from qbx_ir.ledger import BraidRow, braid_problems
from qbx_ir.normal_form_ledger import NFRow, normal_forms_equal

Problem = Tuple[str, Dict[str, object]]

#: Largest strand count accepted.
MAX_BURAU_STRANDS = 12


@dataclass(frozen=True)
class BurauValues:
    size: int
    exp_min: int
    width: int
    coefficients: Tuple[int, ...]
    alexander: Tuple[int, ...]


def _int(v) -> int:
    if v.denominator != 1:
        raise AssertionError("non-integer Burau coefficient")
    return int(v)


def encode_matrix(mat) -> Tuple[int, int, int, Tuple[int, ...]]:
    """``(size, exp_min, width, coefficients)`` of a matrix of Laurent polynomials."""
    m = len(mat)
    exps = [e for row in mat for x in row for e in x.coeffs]
    if not exps:
        return m, 0, 0, ()
    lo, hi = min(exps), max(exps)
    width = hi - lo + 1
    out: List[int] = []
    for i in range(m):
        for j in range(m):
            c = mat[i][j].coeffs
            out.extend(_int(c[lo + k]) if (lo + k) in c else 0 for k in range(width))
    return m, lo, width, tuple(out)


def alexander_coefficients(poly) -> Tuple[int, ...]:
    """The normalised Alexander polynomial as ``(c_0, c_1, …)``; ``()`` for 0."""
    if poly.is_zero():
        return ()
    d = poly.to_int_dict()
    assert min(d) == 0
    return tuple(d.get(k, 0) for k in range(max(d) + 1))


def burau_values(strand_count: int, word: Sequence[int]) -> BurauValues:
    """The certificate fields of a well-formed braid (``braid_burau_values``)."""
    b = Braid.from_short_form(strand_count, list(word))
    size, lo, width, coeffs = encode_matrix(burau_matrix(b))
    return BurauValues(size, lo, width, coeffs, alexander_coefficients(alexander_polynomial(b)))


@dataclass(frozen=True)
class BurauRow:
    """A row of ``braid_burau``."""

    braid: BraidRow
    braid_hash: str
    size: int
    exp_min: int
    width: int
    coefficients: Tuple[int, ...]
    alexander: Tuple[int, ...]

    @classmethod
    def of(cls, braid: BraidRow) -> "BurauRow":
        """The certificate ``certify_braid_burau`` writes (raises like it)."""
        if braid_problems(braid):
            raise ValueError("braid_not_well_formed")
        if braid.strand_count > MAX_BURAU_STRANDS:
            raise ValueError("strand_count_too_large")
        v = burau_values(braid.strand_count, braid.word)
        return cls(braid, braid.braid_hash, v.size, v.exp_min, v.width, v.coefficients,
                   v.alexander)


def _first_difference(a: Sequence[int], b: Sequence[int]) -> int:
    for k, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return k
    return min(len(a), len(b))


def certificate_problems(row: BurauRow) -> List[Problem]:
    """Problems of a ``braid_burau`` row."""
    if braid_problems(row.braid):
        return [("braid_not_well_formed", {})]
    if row.braid.strand_count > MAX_BURAU_STRANDS:
        return [("strand_count_too_large",
                 {"strand_count": row.braid.strand_count, "max": MAX_BURAU_STRANDS})]
    out: List[Problem] = []
    if row.braid_hash != row.braid.braid_hash:
        out.append(("braid_hash_mismatch",
                    {"recorded": row.braid_hash, "expected": row.braid.braid_hash}))
    v = burau_values(row.braid.strand_count, row.braid.word)
    if row.size != v.size:
        out.append(("size_mismatch", {"recorded": row.size, "expected": v.size}))
    if row.exp_min != v.exp_min or row.width != v.width:
        out.append(("window_mismatch",
                    {"recorded": [row.exp_min, row.width], "expected": [v.exp_min, v.width]}))
    if tuple(row.coefficients) != tuple(v.coefficients):
        out.append(("coefficients_mismatch",
                    {"recorded_length": len(row.coefficients),
                     "expected_length": len(v.coefficients),
                     "first_index": _first_difference(row.coefficients, v.coefficients)}))
    if tuple(row.alexander) != tuple(v.alexander):
        out.append(("alexander_mismatch",
                    {"recorded": [str(x) for x in row.alexander],
                     "expected": [str(x) for x in v.alexander]}))
    return out


def certificate_is_valid(row: Optional[BurauRow]) -> bool:
    return row is not None and not certificate_problems(row)


def _comparable(a: Optional[BurauRow], b: Optional[BurauRow]) -> bool:
    return (certificate_is_valid(a) and certificate_is_valid(b)
            and a.braid.strand_count == b.braid.strand_count)


def burau_equal(a: Optional[BurauRow], b: Optional[BurauRow]) -> Optional[bool]:
    """``braid_burau_equal``: None unless both certificates are valid and the strand counts
    agree; True iff the Burau matrices are equal (Lean: ``burauCert_eq_iff``).

    True: ``ρ̄(a) = ρ̄(b)`` (representation equality, not equality in B_n).
    False: the braids are different elements of B_n (Lean: ``eval_ne_of_burauCert_ne``).
    """
    if not _comparable(a, b):
        return None
    return (a.exp_min, a.width, tuple(a.coefficients)) == \
        (b.exp_min, b.width, tuple(b.coefficients))


def alexander_equal(a: Optional[BurauRow], b: Optional[BurauRow]) -> Optional[bool]:
    """``braid_alexander_equal``: None unless comparable; True iff the Alexander polynomials
    agree.  False: the braids are not conjugate in B_n (Lean: ``Word.alexNum_conj``)."""
    if not _comparable(a, b):
        return None
    return tuple(a.alexander) == tuple(b.alexander)


def inequality_certified(a: Optional[BurauRow], b: Optional[BurauRow]) -> bool:
    """``braid_burau_inequality_certified``."""
    return burau_equal(a, b) is False


def non_conjugacy_certified(a: Optional[BurauRow], b: Optional[BurauRow]) -> bool:
    """``braid_burau_non_conjugacy_certified``."""
    return alexander_equal(a, b) is False


def transport_problems(accepted: bool, cert_a: Optional[BurauRow],
                       cert_b: Optional[BurauRow]) -> List[Problem]:
    """Problems of an accepted rewrite or derivation between braids with certificates
    ``cert_a`` and ``cert_b`` (``accepted`` False: nothing is checked)."""
    if not accepted:
        return []
    out: List[Problem] = []
    if burau_equal(cert_a, cert_b) is False:
        out.append(("burau_not_preserved", {}))
    if alexander_equal(cert_a, cert_b) is False:
        out.append(("alexander_not_preserved", {}))
    return out


def nf_consistency_problems(
    row: BurauRow,
    row_nf: Optional[NFRow],
    others: Sequence[Tuple[BurauRow, Optional[NFRow]]],
) -> List[Problem]:
    """``braid_burau_nf_problems``: for a valid certificate ``row`` of a braid with normal-form
    certificate ``row_nf``, no *other* braid certified equal by the normal forms may have a
    different valid certificate.  Reported in the order of the other braid's hash."""
    if not certificate_is_valid(row):
        return []
    out: List[Problem] = []
    for other, other_nf in sorted(others, key=lambda t: t[0].braid.braid_hash):
        if other.braid.key == row.braid.key:
            continue
        if normal_forms_equal(row_nf, other_nf) is not True:
            continue
        if burau_equal(row, other) is False or alexander_equal(row, other) is False:
            out.append(("burau_contradicts_normal_form",
                        {"other_braid_hash": other.braid.braid_hash}))
    return out
