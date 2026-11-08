"""
Reference implementation of the braid invariant certificates (migration 020).

Migration ``020_braid_invariants.sql`` stores, for a braid of the braid ledger
(migration 019, :mod:`qbx_ir.ledger`), an *invariant certificate*
(table ``braid_invariant``):

* ``permutation`` — :func:`qbx_ir.algebra.invariants.permutation`
  (``permutation[p-1]`` = the strand that ends at position ``p``);
* ``writhe``      — :func:`qbx_ir.algebra.invariants.writhe`;
* ``components``  — for each strand ``s`` (1-indexed), the 0-based index of its
  closure component in :func:`qbx_ir.algebra.invariants.closure_components`
  (components are the cycles of the permutation, numbered by smallest strand);
* ``linking``     — the linking numbers ``lk(C_a, C_b)`` of
  :func:`qbx_ir.algebra.invariants.linking_matrix` for ``a < b`` in
  lexicographic order;
* ``braid_hash``  — the hash of the certified braid, copied for tamper evidence.

The database recomputes every field from the word.  It also checks that the
certificates at the two ends of every accepted rewrite and derivation agree
(they must: every field is a braid invariant), and certifies two braids
*unequal* when their certificates differ (``braid_inequality_certified``).

This module is the in-memory reference: the database reports exactly the
problems listed here, in the same order, with the same details
(``tests/live_db/test_braid_invariants_db.py``).

Lean: ``QBX/Formal/BraidInvariantCert.lean`` proves that the crossing loop
behind every field depends only on the braid group element
(``cert_eq_of_eval_eq``, ``linkTotal_eq_of_eval_eq``), so a valid certificate
can never change along an accepted rewrite or derivation, and different
certificates prove different braids (``eval_ne_of_cert_ne``); the stored
linking numbers are exact halves (``linkTotal_even``) — registry H-052, H-053.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from qbx_ir.algebra.invariants import (
    closure_components,
    linking_matrix,
    permutation,
    writhe,
)
from qbx_ir.core.braid import Braid
from qbx_ir.ledger import BraidRow, braid_problems

Problem = Tuple[str, Dict[str, object]]

INVARIANTS = ("permutation", "writhe", "components", "linking")


@dataclass(frozen=True)
class InvariantValues:
    """The recomputed fields of a certificate."""

    permutation: Tuple[int, ...]
    writhe: int
    components: Tuple[int, ...]
    linking: Tuple[int, ...]


def invariant_values(strand_count: int, word: Sequence[int]) -> InvariantValues:
    """The certificate fields of a well-formed braid (``braid_invariant_values``)."""
    b = Braid.from_short_form(strand_count, list(word))
    comps = closure_components(b)
    label = [0] * strand_count
    for idx, comp in enumerate(comps):
        for s in comp:
            label[s - 1] = idx
    lk = linking_matrix(b)
    return InvariantValues(
        permutation=tuple(permutation(b)),
        writhe=writhe(b),
        components=tuple(label),
        linking=tuple(lk[key] for key in sorted(lk)),
    )


@dataclass(frozen=True)
class CertRow:
    """A row of ``braid_invariant``."""

    braid: BraidRow
    braid_hash: str
    permutation: Tuple[Optional[int], ...]
    writhe: int
    components: Tuple[Optional[int], ...]
    linking: Tuple[Optional[int], ...]

    @classmethod
    def of(cls, braid: BraidRow) -> "CertRow":
        """The certificate ``certify_braid_invariants`` writes (raises if not well formed)."""
        if braid_problems(braid):
            raise ValueError("braid_not_well_formed")
        v = invariant_values(braid.strand_count, braid.word)
        return cls(braid, braid.braid_hash, v.permutation, v.writhe, v.components, v.linking)

    def value(self, name: str):
        return getattr(self, name)


def _json(value):
    return list(value) if isinstance(value, tuple) else value


def certificate_problems(row: CertRow) -> List[Problem]:
    """Problems of a ``braid_invariant`` row."""
    if braid_problems(row.braid):
        return [("braid_not_well_formed", {})]
    out: List[Problem] = []
    if row.braid_hash != row.braid.braid_hash:
        out.append(("braid_hash_mismatch",
                    {"recorded": row.braid_hash, "expected": row.braid.braid_hash}))
    expected = invariant_values(row.braid.strand_count, row.braid.word)
    for name in INVARIANTS:
        got, want = row.value(name), getattr(expected, name)
        if got != want:
            out.append((f"{name}_mismatch", {"recorded": _json(got), "expected": _json(want)}))
    return out


def certificate_is_valid(row: Optional[CertRow]) -> bool:
    return row is not None and not certificate_problems(row)


def differences(a: Optional[CertRow], b: Optional[CertRow]) -> Optional[List[str]]:
    """The invariants on which two braids' certificates differ (``braid_invariant_differences``).

    None unless both certificates are valid and the braids have the same strand count.
    A non-empty list certifies that the two braids are different elements of B_n.
    """
    if not (certificate_is_valid(a) and certificate_is_valid(b)):
        return None
    if a.braid.strand_count != b.braid.strand_count:
        return None
    return [name for name in INVARIANTS if a.value(name) != b.value(name)]


def transport_problems(accepted: bool, a: Optional[CertRow], b: Optional[CertRow]) -> List[Problem]:
    """Problems of an accepted rewrite or derivation from a braid certified by ``a`` to one
    certified by ``b``: every invariant must agree (``accepted`` False: nothing is checked)."""
    if not accepted:
        return []
    diff = differences(a, b)
    return [("invariant_not_preserved", {"invariant": name}) for name in (diff or [])]
