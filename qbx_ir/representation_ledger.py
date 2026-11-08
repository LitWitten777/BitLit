"""
Reference implementation of the exact representation certificates (migration 022).

Migration ``022_braid_representations.sql`` stores, for a braid of the braid
ledger (migration 019, :mod:`qbx_ir.ledger`) and a non-zero rational parameter
``q = q_num / q_den`` (lowest terms, ``q_den > 0``), the **exact** matrix of the
braid in the ``U_q(sl_2)`` quantum representation on ``(ℚ²)^{⊗n}``
(:class:`qbx_ir.quantum.r_matrix.SL2RMatrix`), table ``braid_representation``:

* ``dimension``   — ``2^n``;
* ``numerators``  — the integer numerators, flattened row-major;
* ``denominator`` — the positive common denominator, with
  ``gcd(denominator, numerators) = 1``;
* ``braid_hash``  — the hash of the certified braid, copied for tamper evidence.

The values are those of :func:`qbx_ir.quantum.exact.exact_sl2_matrix`
(integers only: scaled generators, then one reduction).  Because the reduced
fraction is unique, two certificates at the same ``q`` are equal **iff** the
two exact representation matrices are equal — this decides
``EqualityKind.REPRESENTATION`` exactly, with no tolerance.

Uses of the certificates:

* ``braid_representation_equal(a, b, q)``: TRUE — ``ρ_q(a) = ρ_q(b)`` exactly
  (representation equality; it does **not** prove ``a = b`` in ``B_n``, the
  representation need not be faithful); FALSE — the braids are different
  elements of ``B_n``; NULL — not comparable;
* transport: along every accepted rewrite and derivation the certificates at
  each common ``q`` must agree;
* consistency with migration 021: two braids certified equal by their normal
  forms must not have different certificates.

This module is the in-memory reference: the database reports exactly the
problems listed here, in the same order, with the same details
(``tests/live_db/test_braid_representations_db.py``).

Lean: ``QBX/Formal/BraidRepCert.lean`` — the letter-by-letter matrix is the
matrix of the quantum operator (``toLin'_repMat``), so equal braids have equal
matrices (``repMat_eq_of_eval_eq``); the integer computation is ``(p r)^len``
times the rational matrix (``scaledMat_cast``); the reduced fraction is unique
(``reduced_unique``), so certificates are equal iff the matrices are
(``repCert_eq_iff``), equal braids have equal certificates
(``repCert_eq_of_eval_eq``) and different certificates prove different braids
(``eval_ne_of_repCert_ne``); the model agrees with this module on test vectors
(``repCert_agrees_with_python``) — registry H-058, H-059.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from qbx_ir.ledger import BraidRow, braid_problems
from qbx_ir.normal_form_ledger import NFRow, normal_forms_equal
from qbx_ir.quantum.exact import ExactMatrix, exact_sl2_matrix, parameter_problem

Problem = Tuple[str, Dict[str, object]]

#: Largest strand count accepted (the matrix has 4^n entries).
MAX_REP_STRANDS = 6


def representation_values(strand_count: int, word: Sequence[int], q_num: int,
                          q_den: int) -> ExactMatrix:
    """The certificate fields of a well-formed braid (``braid_representation_values``)."""
    return exact_sl2_matrix(strand_count, list(word), q_num, q_den)


@dataclass(frozen=True)
class RepRow:
    """A row of ``braid_representation``."""

    braid: BraidRow
    q_num: int
    q_den: int
    braid_hash: str
    dimension: int
    numerators: Tuple[int, ...]
    denominator: int

    @classmethod
    def of(cls, braid: BraidRow, q_num: int = 2, q_den: int = 1) -> "RepRow":
        """The certificate ``certify_braid_representation`` writes (raises like it)."""
        if braid_problems(braid):
            raise ValueError("braid_not_well_formed")
        if parameter_problem(q_num, q_den):
            raise ValueError("parameter_invalid")
        if braid.strand_count > MAX_REP_STRANDS:
            raise ValueError("strand_count_too_large")
        v = representation_values(braid.strand_count, braid.word, q_num, q_den)
        return cls(braid, q_num, q_den, braid.braid_hash, v.dimension, v.numerators,
                   v.denominator)

    @property
    def q(self) -> Tuple[int, int]:
        return (self.q_num, self.q_den)


def _first_difference(a: Sequence[int], b: Sequence[int]) -> int:
    for k, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return k
    return min(len(a), len(b))


def certificate_problems(row: RepRow) -> List[Problem]:
    """Problems of a ``braid_representation`` row."""
    if braid_problems(row.braid):
        return [("braid_not_well_formed", {})]
    if parameter_problem(row.q_num, row.q_den):
        return [("parameter_invalid", {"q_num": row.q_num, "q_den": row.q_den})]
    if row.braid.strand_count > MAX_REP_STRANDS:
        return [("strand_count_too_large",
                 {"strand_count": row.braid.strand_count, "max": MAX_REP_STRANDS})]
    out: List[Problem] = []
    if row.braid_hash != row.braid.braid_hash:
        out.append(("braid_hash_mismatch",
                    {"recorded": row.braid_hash, "expected": row.braid.braid_hash}))
    v = representation_values(row.braid.strand_count, row.braid.word, row.q_num, row.q_den)
    if row.dimension != v.dimension:
        out.append(("dimension_mismatch", {"recorded": row.dimension, "expected": v.dimension}))
    if row.denominator != v.denominator:
        out.append(("denominator_mismatch",
                    {"recorded": str(row.denominator), "expected": str(v.denominator)}))
    if tuple(row.numerators) != tuple(v.numerators):
        out.append(("numerators_mismatch",
                    {"recorded_length": len(row.numerators),
                     "expected_length": len(v.numerators),
                     "first_index": _first_difference(row.numerators, v.numerators)}))
    return out


def certificate_is_valid(row: Optional[RepRow]) -> bool:
    return row is not None and not certificate_problems(row)


def representations_equal(a: Optional[RepRow], b: Optional[RepRow]) -> Optional[bool]:
    """``braid_representation_equal``: None unless both certificates are valid, at the same
    ``q``, for braids with the same strand count; True iff the exact matrices are equal.

    True: ``ρ_q(a) = ρ_q(b)`` (representation equality, not equality in B_n).
    False: the braids are different elements of B_n (Lean: ``eval_ne_of_repCert_ne``).
    """
    if not (certificate_is_valid(a) and certificate_is_valid(b)):
        return None
    if a.q != b.q or a.braid.strand_count != b.braid.strand_count:
        return None
    return a.denominator == b.denominator and tuple(a.numerators) == tuple(b.numerators)


def inequality_certified(a: Optional[RepRow], b: Optional[RepRow]) -> bool:
    """``braid_representation_inequality_certified``."""
    return representations_equal(a, b) is False


def _at(certs: Sequence[RepRow], q: Tuple[int, int]) -> Optional[RepRow]:
    for c in certs:
        if c.q == q:
            return c
    return None


def transport_problems(accepted: bool, certs_a: Sequence[RepRow],
                       certs_b: Sequence[RepRow]) -> List[Problem]:
    """Problems of an accepted rewrite or derivation from a braid with certificates
    ``certs_a`` to one with certificates ``certs_b``: at every parameter, the certificates
    must agree (``accepted`` False: nothing is checked)."""
    if not accepted:
        return []
    out: List[Problem] = []
    for c in sorted(certs_a, key=lambda c: c.q):
        if representations_equal(c, _at(certs_b, c.q)) is False:
            out.append(("representation_not_preserved", {"q_num": c.q_num, "q_den": c.q_den}))
    return out


def nf_consistency_problems(
    row: RepRow,
    row_nf: Optional[NFRow],
    others: Sequence[Tuple[RepRow, Optional[NFRow]]],
) -> List[Problem]:
    """``braid_rep_nf_problems``: for a valid certificate ``row`` of a braid with normal-form
    certificate ``row_nf``, no *other* braid (``others``: its representation certificate and
    normal-form certificate) certified equal by the normal forms may have a different valid
    certificate at the same ``q`` (Lean: ``eval_eq_of_leftNormalForm_eq`` and
    ``repCert_eq_of_eval_eq``).  Reported in the order of the other braid's hash."""
    if not certificate_is_valid(row):
        return []
    out: List[Problem] = []
    for other, other_nf in sorted(others, key=lambda t: t[0].braid.braid_hash):
        if other.braid.key == row.braid.key or other.q != row.q:
            continue
        if normal_forms_equal(row_nf, other_nf) is not True:
            continue
        if representations_equal(row, other) is False:
            out.append(("representation_contradicts_normal_form",
                        {"other_braid_hash": other.braid.braid_hash}))
    return out
