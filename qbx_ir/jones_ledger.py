"""
Reference implementation of the Kauffman bracket / Jones certificates (migration 023).

Migration ``023_braid_jones.sql`` (written 2026-10-15; its algorithm is checked
against this module by ``tests/qbx_ir/test_jones_sql_model.py``, and
``tests/live_db/test_braid_jones_db.py`` compares the database with this module
where PostgreSQL is available) stores, for a braid of the braid ledger
(migration 019, :mod:`qbx_ir.ledger`), the Kauffman bracket of its closure
(:func:`qbx_ir.algebra.polynomial_invariants.kauffman_bracket`, ``⟨O⟩ = 1``) and
its Jones polynomial in the variable ``A`` (``V = (−A³)^{−w} ⟨B̂⟩``, ``A = t^{−1/4}``;
:func:`qbx_ir.algebra.polynomial_invariants.jones_polynomial` returns the same
polynomial after the change of variable ``A^k ↦ t^{−k/4}``), table ``braid_jones``:

* ``bracket_exp_min``, ``bracket_width``, ``bracket_coefficients`` — the bracket
  ``Σ_k c_k A^(exp_min + k)``, ``0 ≤ k < width``, in the smallest window
  (``c_0 ≠ 0`` and ``c_(width-1) ≠ 0``); ``exp_min = width = 0`` for 0;
* ``jones_exp_min``, ``jones_width``, ``jones_coefficients`` — the Jones
  polynomial in ``A``, same encoding;
* ``braid_hash`` — the hash of the certified braid, copied for tamper evidence.

Because the window is the smallest one, the encoding is unique: two
certificates are equal **iff** the polynomials are equal.  Uses:

* ``braid_bracket_equal(a, b)`` (same strand count): FALSE — the braids are
  different elements of ``B_n`` and are not conjugate (the bracket is a
  conjugacy invariant);
* ``braid_jones_equal(a, b)`` (any strand counts): FALSE — the closures are
  **not isotopic** links (the Jones polynomial is invariant under Markov's
  moves);
* transport: along every accepted rewrite and derivation the certificates must
  agree;
* consistency with migration 021: two braids certified equal by their normal
  forms must not have different certificates.

This module is the in-memory reference (``tests/qbx_ir/test_jones_ledger.py``).

Lean: ``QBX/Formal/KauffmanBracket/`` — the bracket recursion is the quantum
trace (``quantumTrace_eq_bracket``: ``Tr(μ^{⊗n} ρ(B)) = (−A)^w (−A² − A⁻²) ⟨B̂⟩``
at ``q = −A²``), so the Jones polynomial is a Markov invariant
(``jonesPoly_markov``), the bracket is a braid and conjugacy invariant
(``bracketPoly_eq_of_eval_eq``, ``bracketPoly_conj``), the encoding is unique
(``certPoly_inj``), different Jones certificates prove non-isotopic closures
(``not_markovEquiv_of_jonesCert_ne``), and the Lean model gives exactly this
module's values on test vectors (``jones_checks_pass``) — registry H-278 … H-281.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from qbx_ir.algebra.invariants import writhe
from qbx_ir.algebra.polynomial_invariants import kauffman_bracket
from qbx_ir.core.braid import Braid
from qbx_ir.ledger import BraidRow, braid_problems
from qbx_ir.normal_form_ledger import NFRow, normal_forms_equal

Problem = Tuple[str, Dict[str, object]]

#: Largest strand count accepted (the TL state space has Catalan(n) diagrams).
MAX_JONES_STRANDS = 12


@dataclass(frozen=True)
class JonesValues:
    bracket_exp_min: int
    bracket_width: int
    bracket_coefficients: Tuple[int, ...]
    jones_exp_min: int
    jones_width: int
    jones_coefficients: Tuple[int, ...]


def _int(v) -> int:
    if v.denominator != 1:
        raise AssertionError("non-integer bracket coefficient")
    return int(v)


def encode_poly(poly) -> Tuple[int, int, Tuple[int, ...]]:
    """``(exp_min, width, coefficients)`` of a Laurent polynomial (smallest window)."""
    c = poly.coeffs
    if not c:
        return 0, 0, ()
    lo, hi = min(c), max(c)
    return lo, hi - lo + 1, tuple(_int(c[k]) if k in c else 0 for k in range(lo, hi + 1))


def jones_values(strand_count: int, word: Sequence[int]) -> JonesValues:
    """The certificate fields of a well-formed braid (``braid_jones_values``)."""
    b = Braid.from_short_form(strand_count, list(word))
    bracket = kauffman_bracket(b)
    w = writhe(b)
    jones = bracket.shift(-3 * w) * (-1 if w % 2 else 1)
    return JonesValues(*encode_poly(bracket), *encode_poly(jones))


@dataclass(frozen=True)
class JonesRow:
    """A row of ``braid_jones``."""

    braid: BraidRow
    braid_hash: str
    bracket_exp_min: int
    bracket_width: int
    bracket_coefficients: Tuple[int, ...]
    jones_exp_min: int
    jones_width: int
    jones_coefficients: Tuple[int, ...]

    @classmethod
    def of(cls, braid: BraidRow) -> "JonesRow":
        """The certificate ``certify_braid_jones`` writes (raises like it)."""
        if braid_problems(braid):
            raise ValueError("braid_not_well_formed")
        if braid.strand_count > MAX_JONES_STRANDS:
            raise ValueError("strand_count_too_large")
        v = jones_values(braid.strand_count, braid.word)
        return cls(braid, braid.braid_hash, v.bracket_exp_min, v.bracket_width,
                   v.bracket_coefficients, v.jones_exp_min, v.jones_width, v.jones_coefficients)


def _first_difference(a: Sequence[int], b: Sequence[int]) -> int:
    for k, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return k
    return min(len(a), len(b))


def certificate_problems(row: JonesRow) -> List[Problem]:
    """Problems of a ``braid_jones`` row."""
    if braid_problems(row.braid):
        return [("braid_not_well_formed", {})]
    if row.braid.strand_count > MAX_JONES_STRANDS:
        return [("strand_count_too_large",
                 {"strand_count": row.braid.strand_count, "max": MAX_JONES_STRANDS})]
    out: List[Problem] = []
    if row.braid_hash != row.braid.braid_hash:
        out.append(("braid_hash_mismatch",
                    {"recorded": row.braid_hash, "expected": row.braid.braid_hash}))
    v = jones_values(row.braid.strand_count, row.braid.word)
    if (row.bracket_exp_min, row.bracket_width) != (v.bracket_exp_min, v.bracket_width):
        out.append(("bracket_window_mismatch",
                    {"recorded": [row.bracket_exp_min, row.bracket_width],
                     "expected": [v.bracket_exp_min, v.bracket_width]}))
    if tuple(row.bracket_coefficients) != tuple(v.bracket_coefficients):
        out.append(("bracket_coefficients_mismatch",
                    {"recorded_length": len(row.bracket_coefficients),
                     "expected_length": len(v.bracket_coefficients),
                     "first_index": _first_difference(row.bracket_coefficients,
                                                      v.bracket_coefficients)}))
    if (row.jones_exp_min, row.jones_width) != (v.jones_exp_min, v.jones_width):
        out.append(("jones_window_mismatch",
                    {"recorded": [row.jones_exp_min, row.jones_width],
                     "expected": [v.jones_exp_min, v.jones_width]}))
    if tuple(row.jones_coefficients) != tuple(v.jones_coefficients):
        out.append(("jones_coefficients_mismatch",
                    {"recorded_length": len(row.jones_coefficients),
                     "expected_length": len(v.jones_coefficients),
                     "first_index": _first_difference(row.jones_coefficients,
                                                      v.jones_coefficients)}))
    return out


def certificate_is_valid(row: Optional[JonesRow]) -> bool:
    return row is not None and not certificate_problems(row)


def bracket_equal(a: Optional[JonesRow], b: Optional[JonesRow]) -> Optional[bool]:
    """``braid_bracket_equal``: None unless both certificates are valid and the strand counts
    agree; True iff the brackets are equal (Lean: ``bracketCert_eq_iff``).

    False: the braids are different and not conjugate in B_n (Lean:
    ``bracketCert_eq_of_eval_eq``, ``bracketPoly_conj``).
    """
    if not (certificate_is_valid(a) and certificate_is_valid(b)
            and a.braid.strand_count == b.braid.strand_count):
        return None
    return (a.bracket_exp_min, a.bracket_width, tuple(a.bracket_coefficients)) == \
        (b.bracket_exp_min, b.bracket_width, tuple(b.bracket_coefficients))


def jones_equal(a: Optional[JonesRow], b: Optional[JonesRow]) -> Optional[bool]:
    """``braid_jones_equal``: None unless both certificates are valid (strand counts may
    differ); True iff the Jones polynomials are equal.

    False: the closures are not isotopic (Lean: ``not_markovEquiv_of_jonesCert_ne``).
    """
    if not (certificate_is_valid(a) and certificate_is_valid(b)):
        return None
    return (a.jones_exp_min, a.jones_width, tuple(a.jones_coefficients)) == \
        (b.jones_exp_min, b.jones_width, tuple(b.jones_coefficients))


def non_conjugacy_certified(a: Optional[JonesRow], b: Optional[JonesRow]) -> bool:
    """``braid_bracket_non_conjugacy_certified``."""
    return bracket_equal(a, b) is False


def non_isotopy_certified(a: Optional[JonesRow], b: Optional[JonesRow]) -> bool:
    """``braid_jones_non_isotopy_certified``."""
    return jones_equal(a, b) is False


def transport_problems(accepted: bool, cert_a: Optional[JonesRow],
                       cert_b: Optional[JonesRow]) -> List[Problem]:
    """Problems of an accepted rewrite or derivation between braids with certificates
    ``cert_a`` and ``cert_b`` (``accepted`` False: nothing is checked)."""
    if not accepted:
        return []
    out: List[Problem] = []
    if bracket_equal(cert_a, cert_b) is False:
        out.append(("bracket_not_preserved", {}))
    if jones_equal(cert_a, cert_b) is False:
        out.append(("jones_not_preserved", {}))
    return out


def nf_consistency_problems(
    row: JonesRow,
    row_nf: Optional[NFRow],
    others: Sequence[Tuple[JonesRow, Optional[NFRow]]],
) -> List[Problem]:
    """``braid_jones_nf_problems``: for a valid certificate ``row`` of a braid with normal-form
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
        if bracket_equal(row, other) is False or jones_equal(row, other) is False:
            out.append(("jones_contradicts_normal_form",
                        {"other_braid_hash": other.braid.braid_hash}))
    return out
