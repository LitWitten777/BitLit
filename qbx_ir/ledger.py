"""
Reference implementation of the braid ledger checks (migration 019).

Migration ``019_braid_ledger.sql`` persists QBX-IR braids and their rewrite
history in the Categorical Ledger:

* ``braid_word``       — a braid ``(strand_count, word)`` with its hash
  (:func:`qbx_ir.algebra.rewriting.braid_hash`);
* ``braid_rewrite``    — the provenance record of one rewrite
  (:class:`qbx_ir.algebra.rewriting.Transformation`): input braid, rule,
  position, output braid, both hashes and the rule's declaration;
* ``braid_derivation`` — a chain of rewrite records, each used forwards
  (input → output) or backwards (output → input), from a source braid to a
  target braid: a certificate that the two braids are equal in B_n.

This module is the in-memory reference for those checks.  The database
reports exactly the problems listed here, in the same order, with the same
details (``tests/live_db/test_braid_ledger_db.py``).  Words are short forms
(``+i`` = σ_i, ``-i`` = σ_i⁻¹, 1-indexed) and positions are 0-based, as in
:func:`qbx_ir.algebra.rewriting.apply_rule`.

Lean: ``QBX/Formal/BraidLedger.lean`` proves that a rewrite record passes the
check iff it is one QBX rewrite step, and that an accepted derivation exists
between two words iff they are equal in B_n (registry H-048, H-049).
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from qbx_ir.algebra.rewriting import ALL_RULES

Problem = Tuple[str, Dict[str, object]]

RULES = {r.name: r for r in ALL_RULES}


def word_hash(strand_count: int, word: Sequence[int]) -> str:
    """``braid_hash`` of the braid with this short form."""
    payload = json.dumps({"n": strand_count, "word": list(word)},
                         sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha3_256(payload).hexdigest()


def _sign(x: int) -> int:
    return (x > 0) - (x < 0)


def apply_short(word: Sequence[int], rule_id: str, position: Optional[int]) -> Optional[List[int]]:
    """The word after applying the rule at ``position``, or None if it does not apply.

    The matchers of :mod:`qbx_ir.algebra.rewriting` on short forms.
    """
    w = list(word)
    if rule_id not in RULES or position is None or position < 0:
        return None
    k = position
    if rule_id in ("R01", "R02"):
        if k + 1 >= len(w):
            return None
        a, b = w[k], w[k + 1]
        if rule_id == "R01":
            if abs(a) == abs(b) and _sign(a) == -_sign(b):
                return w[:k] + w[k + 2:]
            return None
        if abs(abs(a) - abs(b)) >= 2:
            return w[:k] + [b, a] + w[k + 2:]
        return None
    if k + 2 >= len(w):
        return None
    a, b, c = w[k], w[k + 1], w[k + 2]
    if not (_sign(a) == _sign(b) == _sign(c) and abs(a) == abs(c)):
        return None
    if abs(abs(a) - abs(b)) != 1:
        return None
    return w[:k] + [b, a, b] + w[k + 3:]


@dataclass(frozen=True)
class BraidRow:
    """A row of ``braid_word``."""

    strand_count: int
    word: Tuple[Optional[int], ...]
    braid_hash: str

    @classmethod
    def of(cls, strand_count: int, word: Sequence[int]) -> "BraidRow":
        return cls(strand_count, tuple(word), word_hash(strand_count, word))

    @property
    def key(self) -> Tuple[int, Tuple[Optional[int], ...]]:
        return (self.strand_count, self.word)


def braid_problems(row: BraidRow) -> List[Problem]:
    """Problems of a ``braid_word`` row."""
    n = row.strand_count
    if n < 1:
        return [("strand_count", {"strand_count": n})]
    out: List[Problem] = []
    for k, g in enumerate(row.word):
        if g is None or g == 0 or abs(g) >= n:
            out.append(("letter", {"position": k, "letter": g}))
    if not out:
        expected = word_hash(n, row.word)
        if row.braid_hash != expected:
            out.append(("hash", {"recorded": row.braid_hash, "expected": expected}))
    return out


@dataclass(frozen=True)
class RewriteRow:
    """A row of ``braid_rewrite``."""

    input: BraidRow
    rule_id: str
    position: Optional[int]
    output: BraidRow
    input_hash: str
    output_hash: str
    preserved: Tuple[str, ...]
    changed: Tuple[str, ...]


def record_rewrite(input_row: BraidRow, rule_id: str, position: int) -> RewriteRow:
    """The record ``record_braid_rewrite`` writes (raises if the rule does not apply)."""
    out = apply_short(input_row.word, rule_id, position)
    if out is None:
        raise ValueError(f"Rule {rule_id} does not apply at position {position}")
    rule = RULES[rule_id]
    output_row = BraidRow.of(input_row.strand_count, out)
    return RewriteRow(input_row, rule_id, position, output_row, input_row.braid_hash,
                      output_row.braid_hash, rule.preserved, rule.changed)


def rewrite_problems(row: RewriteRow) -> List[Problem]:
    """Problems of a ``braid_rewrite`` row."""
    out: List[Problem] = []
    in_ok = not braid_problems(row.input)
    out_ok = not braid_problems(row.output)
    if not in_ok:
        out.append(("input_not_well_formed", {}))
    if not out_ok:
        out.append(("output_not_well_formed", {}))
    if row.input.strand_count != row.output.strand_count:
        out.append(("strand_count_mismatch",
                    {"input": row.input.strand_count, "output": row.output.strand_count}))
    rule = RULES.get(row.rule_id)
    if rule is None:
        out.append(("rule_unknown", {"rule": row.rule_id}))
    else:
        if in_ok:
            expected = apply_short(row.input.word, row.rule_id, row.position)
            if expected is None:
                out.append(("not_applicable", {"rule": row.rule_id, "position": row.position}))
            elif list(row.output.word) != expected:
                out.append(("output_mismatch",
                            {"expected": expected, "recorded": list(row.output.word)}))
        if tuple(row.preserved) != rule.preserved or tuple(row.changed) != rule.changed:
            out.append(("declaration_mismatch",
                        {"preserved": list(row.preserved), "changed": list(row.changed),
                         "expected_preserved": list(rule.preserved),
                         "expected_changed": list(rule.changed)}))
    if in_ok and row.input_hash != row.input.braid_hash:
        out.append(("input_hash_mismatch",
                    {"recorded": row.input_hash, "expected": row.input.braid_hash}))
    if out_ok and row.output_hash != row.output.braid_hash:
        out.append(("output_hash_mismatch",
                    {"recorded": row.output_hash, "expected": row.output.braid_hash}))
    return out


def derivation_problems(source: BraidRow, target: BraidRow,
                        steps: Sequence[Optional[RewriteRow]],
                        directions: Sequence[Optional[bool]]) -> List[Problem]:
    """Problems of a ``braid_derivation`` row.

    ``steps[k]`` is the k-th rewrite record (None: no such record) and
    ``directions[k]`` is True when it is used forwards (input → output),
    False when it is used backwards (output → input).
    """
    if len(steps) != len(directions) or any(d is None for d in directions):
        return [("steps_shape", {"steps": len(steps), "directions": len(directions)})]
    out: List[Problem] = []
    current = source.key
    for k, (step, forward) in enumerate(zip(steps, directions)):
        if step is None:
            out.append(("step_unknown", {"step": k}))
            return out
        if rewrite_problems(step):
            out.append(("step_invalid", {"step": k}))
        start, end = (step.input, step.output) if forward else (step.output, step.input)
        if start.key != current:
            out.append(("step_disconnected", {"step": k}))
            return out
        current = end.key
    if current != target.key:
        out.append(("target_mismatch", {}))
    return out


def derivation_end(source: BraidRow, steps: Sequence[RewriteRow],
                   directions: Sequence[bool]) -> Optional[BraidRow]:
    """The braid an accepted chain from ``source`` ends at (None if it is not accepted)."""
    current = source
    for step, forward in zip(steps, directions):
        start, end = (step.input, step.output) if forward else (step.output, step.input)
        if rewrite_problems(step) or start.key != current.key:
            return None
        current = end
    return current
