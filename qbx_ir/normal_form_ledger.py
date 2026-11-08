"""
Reference implementation of the Garside normal-form certificates (migration 021).

Migration ``021_braid_normal_forms.sql`` stores, for a braid of the braid ledger
(migration 019, :mod:`qbx_ir.ledger`), a *normal-form certificate*
(table ``braid_normal_form``):

* ``power``       — the exponent ``r`` of ``Δ`` in the left normal form
  ``Δ^r · A_1 ⋯ A_k`` (:func:`qbx_ir.algebra.garside.left_normal_form_from_short`);
* ``factors``     — the simple factors ``A_1 … A_k`` as 0-indexed permutations
  (``factors[j][k]`` = final position of the strand that starts at position
  ``k``), exactly the tuples of :class:`~qbx_ir.algebra.garside.GarsideNormalForm`;
* ``normal_word`` — the short form of the normal form
  (:meth:`~qbx_ir.algebra.garside.GarsideNormalForm.to_short_form`);
* ``braid_hash``  — the hash of the certified braid, copied for tamper evidence.

The database recomputes every field from the word.  Uses of the certificates:

* ``braid_normal_form_equal(a, b)`` — TRUE when two braids with the same strand
  count have the same valid normal form: a certificate that they are *equal* in
  B_n (proved in Lean); FALSE when the normal forms differ, which means
  *different* only by Garside's uniqueness theorem (provisional registry entry
  H-057; formalized only for at most two strands); NULL when a valid certificate is missing or the strand
  counts differ.  ``braid_nf_equality_certified`` is the TRUE case only.
* transport: along every accepted rewrite and derivation whose ends have valid
  certificates, the normal forms must agree (relies on H-057);
* consistency with the invariant certificates (migration 020): two braids with
  the same valid normal form must have the same valid invariant certificates
  (relies only on proved results).

This module is the in-memory reference: the database reports exactly the
problems listed here, in the same order, with the same details
(``tests/live_db/test_braid_normal_forms_db.py``).

Lean: ``QBX/Formal/BraidNormalForm.lean`` — the algorithm is modelled step for
step (``leftNormalForm``) and proved sound: the normal form stands for the braid
of the word (``nfValue_leftNormalForm``), so equal normal forms prove equal
braids (``eval_eq_of_leftNormalForm_eq``) and equal invariant certificates
(``cert_eq_of_leftNormalForm_eq``); the model agrees with this module on test
vectors (``leftNormalForm_agrees_with_python``) — registry H-054 – H-056.
Uniqueness (``LeftNormalFormComplete``) is proved for at most two strands
(``leftNormalFormComplete_of_le_two``) and provisional (H-057) otherwise.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from qbx_ir.algebra.garside import left_normal_form_from_short
from qbx_ir.invariant_ledger import CertRow, differences
from qbx_ir.ledger import BraidRow, braid_problems

Problem = Tuple[str, Dict[str, object]]

FIELDS = ("power", "factors", "normal_word")


@dataclass(frozen=True)
class NormalFormValues:
    """The recomputed fields of a normal-form certificate."""

    power: int
    factors: Tuple[Tuple[int, ...], ...]
    normal_word: Tuple[int, ...]


def normal_form_values(strand_count: int, word: Sequence[int]) -> NormalFormValues:
    """The certificate fields of a well-formed braid (``braid_normal_form_values``)."""
    nf = left_normal_form_from_short(strand_count, list(word))
    return NormalFormValues(
        power=nf.power,
        factors=tuple(tuple(f) for f in nf.factors),
        normal_word=tuple(nf.to_short_form()),
    )


@dataclass(frozen=True)
class NFRow:
    """A row of ``braid_normal_form``."""

    braid: BraidRow
    braid_hash: str
    power: int
    factors: Tuple[Tuple[Optional[int], ...], ...]
    normal_word: Tuple[Optional[int], ...]

    @classmethod
    def of(cls, braid: BraidRow) -> "NFRow":
        """The certificate ``certify_braid_normal_form`` writes (raises if not well formed)."""
        if braid_problems(braid):
            raise ValueError("braid_not_well_formed")
        v = normal_form_values(braid.strand_count, braid.word)
        return cls(braid, braid.braid_hash, v.power, v.factors, v.normal_word)

    def value(self, name: str):
        return getattr(self, name)


def _json(value):
    if isinstance(value, tuple):
        return [_json(x) for x in value]
    return value


def certificate_problems(row: NFRow) -> List[Problem]:
    """Problems of a ``braid_normal_form`` row."""
    if braid_problems(row.braid):
        return [("braid_not_well_formed", {})]
    out: List[Problem] = []
    if row.braid_hash != row.braid.braid_hash:
        out.append(("braid_hash_mismatch",
                    {"recorded": row.braid_hash, "expected": row.braid.braid_hash}))
    expected = normal_form_values(row.braid.strand_count, row.braid.word)
    for name in FIELDS:
        got, want = row.value(name), getattr(expected, name)
        if _json(got) != _json(want):
            out.append((f"{name}_mismatch", {"recorded": _json(got), "expected": _json(want)}))
    return out


def certificate_is_valid(row: Optional[NFRow]) -> bool:
    return row is not None and not certificate_problems(row)


def normal_forms_equal(a: Optional[NFRow], b: Optional[NFRow]) -> Optional[bool]:
    """``braid_normal_form_equal``: None unless both certificates are valid and the strand
    counts agree; True iff the normal forms (power and factors) coincide.

    True certifies that the braids are equal in B_n (Lean: ``eval_eq_of_leftNormalForm_eq``);
    False means different only under Garside's uniqueness theorem (H-057, provisional).
    """
    if not (certificate_is_valid(a) and certificate_is_valid(b)):
        return None
    if a.braid.strand_count != b.braid.strand_count:
        return None
    return a.power == b.power and _json(a.factors) == _json(b.factors)


def equality_certified(a: Optional[NFRow], b: Optional[NFRow]) -> bool:
    """``braid_nf_equality_certified``: the proved direction only."""
    return normal_forms_equal(a, b) is True


def transport_problems(accepted: bool, a: Optional[NFRow], b: Optional[NFRow]) -> List[Problem]:
    """Problems of an accepted rewrite or derivation from a braid certified by ``a`` to one
    certified by ``b``: the normal forms must agree (``accepted`` False: nothing is checked)."""
    if accepted and normal_forms_equal(a, b) is False:
        return [("normal_form_not_preserved", {})]
    return []


def invariant_consistency_problems(
    row: NFRow,
    inv: Optional[CertRow],
    others: Sequence[Tuple[NFRow, Optional[CertRow]]],
) -> List[Problem]:
    """``braid_nf_invariant_problems``: for a valid normal-form certificate ``row`` of a braid
    with invariant certificate ``inv``, every *other* braid (``others``: its normal-form
    certificate and invariant certificate, in ledger order) whose valid normal form equals
    this one must not have a different valid invariant certificate (Lean:
    ``cert_eq_of_leftNormalForm_eq``).  Reported in the order of the other braid's hash."""
    if not certificate_is_valid(row):
        return []
    out: List[Problem] = []
    for other, other_inv in sorted(others, key=lambda t: t[0].braid.braid_hash):
        if other.braid.key == row.braid.key:
            continue
        if normal_forms_equal(row, other) is not True:
            continue
        diff = differences(inv, other_inv)
        if diff:
            out.append(("invariants_contradict_normal_form",
                        {"other_braid_hash": other.braid.braid_hash, "invariants": diff}))
    return out
