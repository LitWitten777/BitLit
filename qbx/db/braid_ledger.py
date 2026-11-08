"""
PostgreSQL backend of the QBX-IR ↔ ledger adapter (Phase 2 sprint 5).

:class:`PostgresBraidLedger` implements
:class:`qbx_ir.ledger_adapter.BraidLedgerBackend` on a database with
migrations 001–022 applied.  Writes go through the SQL writers
(``register_braid``, ``record_braid_rewrite``, ``record_braid_derivation``,
``certify_braid_invariants``, ``certify_braid_normal_form``,
``certify_braid_representation``); reads select the stored rows and call the
ledger's own checks (``braid_derivation_problems``, ``braid_equality_certified``,
``braid_invariant_differences``, ``braid_normal_form_equal``,
``braid_representation_equal``).

A refused write raises :class:`qbx_ir.ledger_adapter.LedgerRefusal`.  When the
connection is inside a transaction (``autocommit`` off) each writer runs under a
savepoint, so a refusal leaves the transaction usable.
"""

from __future__ import annotations

from typing import List, Optional, Sequence, Tuple

import psycopg2

from qbx_ir.ledger import BraidRow, Problem, RewriteRow
from qbx_ir.ledger_adapter import (
    DEFAULT_Q,
    MAX_REPRESENTATION_STRANDS,
    DerivationRecord,
    LedgerRefusal,
)


class PostgresBraidLedger:
    """The braid ledger of migrations 019–022 on a psycopg2 connection."""

    def __init__(self, conn) -> None:
        self.conn = conn

    # -- low level -----------------------------------------------------
    def _rows(self, sql: str, *args):
        with self.conn.cursor() as cur:
            cur.execute(sql, args)
            return cur.fetchall() if cur.description is not None else []

    def _one(self, sql: str, *args):
        rows = self._rows(sql, *args)
        return rows[0][0] if rows else None

    def _write(self, sql: str, *args):
        """Run a writer; a database error becomes a LedgerRefusal."""
        savepoint = not self.conn.autocommit
        with self.conn.cursor() as cur:
            if savepoint:
                cur.execute("SAVEPOINT qbx_ledger_adapter")
            try:
                cur.execute(sql, args)
                value = cur.fetchone()[0]
            except psycopg2.Error as e:
                if savepoint:
                    cur.execute("ROLLBACK TO SAVEPOINT qbx_ledger_adapter")
                raise LedgerRefusal(str(e).strip()) from e
            if savepoint:
                cur.execute("RELEASE SAVEPOINT qbx_ledger_adapter")
            return value

    # -- writers -------------------------------------------------------
    def register_braid(self, strand_count: int, word: Sequence[int],
                       name: Optional[str] = None) -> str:
        return self._write("SELECT register_braid(%s, %s::int[], %s)",
                           strand_count, list(word), name)

    def record_rewrite(self, input_id: str, rule_id: str, position: int) -> str:
        return self._write("SELECT record_braid_rewrite(%s, %s, %s)", input_id, rule_id, position)

    def record_derivation(self, source_id: str, steps: Sequence[str],
                          directions: Sequence[bool], name: Optional[str] = None) -> str:
        return self._write("SELECT record_braid_derivation(%s, %s::uuid[], %s::boolean[], %s)",
                           source_id, list(steps), list(directions), name)

    # -- readers -------------------------------------------------------
    def braid_row(self, braid_id: str) -> Optional[BraidRow]:
        rows = self._rows("SELECT strand_count, word, braid_hash FROM braid_word WHERE id = %s",
                          braid_id)
        if not rows:
            return None
        n, word, h = rows[0]
        return BraidRow(n, tuple(word), h)

    def braid_name(self, braid_id: str) -> Optional[str]:
        return self._one("SELECT name FROM braid_word WHERE id = %s", braid_id)

    def rewrite_ends(self, rewrite_id: str) -> Optional[Tuple[str, str]]:
        rows = self._rows("SELECT input_braid_id, output_braid_id FROM braid_rewrite "
                          "WHERE id = %s", rewrite_id)
        return (str(rows[0][0]), str(rows[0][1])) if rows else None

    def rewrite_row(self, rewrite_id: str) -> Optional[RewriteRow]:
        rows = self._rows(
            "SELECT input_braid_id, rule_id, position, output_braid_id, input_hash, "
            "output_hash, preserved, changed FROM braid_rewrite WHERE id = %s", rewrite_id)
        if not rows:
            return None
        i, rule, pos, o, ih, oh, preserved, changed = rows[0]
        return RewriteRow(self.braid_row(i), rule, pos, self.braid_row(o), ih, oh,
                          tuple(preserved), tuple(changed))

    def derivation(self, derivation_id: str) -> Optional[DerivationRecord]:
        rows = self._rows("SELECT source_braid_id, target_braid_id, steps::text[], directions, name "
                          "FROM braid_derivation WHERE id = %s", derivation_id)
        if not rows:
            return None
        s, t, steps, directions, name = rows[0]
        return DerivationRecord(str(s), str(t), tuple(str(x) for x in steps),
                                tuple(directions), name)

    def derivation_problems(self, derivation_id: str) -> List[Problem]:
        return [(r, d) for r, d in
                self._rows("SELECT * FROM braid_derivation_problems(%s)", derivation_id)]

    def equality_certified(self, a: str, b: str) -> bool:
        return bool(self._one("SELECT braid_equality_certified(%s, %s)", a, b))

    # -- certificates --------------------------------------------------
    def certify(self, braid_id: str) -> None:
        self._write("SELECT certify_braid_invariants(%s)", braid_id)
        self._write("SELECT certify_braid_normal_form(%s)", braid_id)
        n = self._one("SELECT strand_count FROM braid_word WHERE id = %s", braid_id)
        if n is not None and n <= MAX_REPRESENTATION_STRANDS:
            self._write("SELECT certify_braid_representation(%s, %s, %s)", braid_id, *DEFAULT_Q)

    def invariant_differences(self, a: str, b: str) -> Optional[List[str]]:
        v = self._one("SELECT braid_invariant_differences(%s, %s)", a, b)
        return None if v is None else list(v)

    def normal_forms_equal(self, a: str, b: str) -> Optional[bool]:
        return self._one("SELECT braid_normal_form_equal(%s, %s)", a, b)

    def representations_equal(self, a: str, b: str, q_num: int, q_den: int) -> Optional[bool]:
        return self._one("SELECT braid_representation_equal(%s, %s, %s, %s)", a, b, q_num, q_den)


__all__ = ["PostgresBraidLedger"]
