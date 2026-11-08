"""
QBX-IR ↔ Categorical Ledger adapter (Phase 2 sprint 5).

Writes a QBX-IR :class:`~qbx_ir.core.braid.Braid` and a trace of
:class:`~qbx_ir.algebra.rewriting.Transformation` records (for example the
trace of :func:`~qbx_ir.algebra.rewriting.normal_form_with_trace`) through the
ledger writers of migration 019, reads everything back, and verifies that what
the ledger holds is exactly what was written.

The adapter talks to a *backend* with the interface of :class:`BraidLedgerBackend`:

* :class:`InMemoryBraidLedger` (this module) — the in-memory reference.  Its
  writers behave like the SQL writers ``register_braid``,
  ``record_braid_rewrite`` and ``record_braid_derivation`` (content
  addressing, recomputed outputs, refusal of input with a problem), using the
  reference checks of :mod:`qbx_ir.ledger`, :mod:`qbx_ir.invariant_ledger`,
  :mod:`qbx_ir.normal_form_ledger` and :mod:`qbx_ir.representation_ledger`.
* :class:`qbx.db.braid_ledger.PostgresBraidLedger` — the same interface on a
  PostgreSQL database with migrations 001–022 applied.

The database recomputes every rewrite from the input word, so the adapter
never sends an output word: it sends ``(input braid, rule, position)`` and
checks that the record the ledger computed is the Transformation it was given.

Main entry points:

* :func:`trace_problems` — check a trace before anything is written (the same
  reasons as :func:`qbx_ir.ledger.rewrite_problems`, plus connectivity);
* :func:`write_trace` / :func:`persist_normal_form` — write;
* :func:`read_braid`, :func:`read_transformation`, :func:`read_trace` — read back;
* :func:`verify_trace` — compare the ledger's contents with the original
  braid and trace (an empty list means the round trip is exact);
* :func:`certify_trace` / :func:`certificate_problems_of_trace` — attach the
  invariant (020), normal-form (021) and exact representation (022)
  certificates to both ends and check that they agree.

Lean: ``QBX/Formal/BraidTrace.lean`` proves that the derivation written by
:func:`persist_normal_form` is always accepted by the ledger and ends at the
reduced word (registry H-060, H-061).
"""

from __future__ import annotations

import uuid
from dataclasses import dataclass
from typing import Dict, List, Optional, Protocol, Sequence, Tuple

from qbx_ir import invariant_ledger, normal_form_ledger, representation_ledger
from qbx_ir.algebra.rewriting import Transformation, braid_hash, normal_form_with_trace
from qbx_ir.core.braid import Braid
from qbx_ir.ledger import (
    RULES,
    BraidRow,
    Problem,
    RewriteRow,
    apply_short,
    braid_problems,
    derivation_problems,
    rewrite_problems,
    word_hash,
)

#: Largest strand count for which representation certificates are written
#: (migration 022 accepts braids with up to 6 strands: the matrix has 4ⁿ entries).
MAX_REPRESENTATION_STRANDS = 6

#: The parameter q = 2 / 1 used for representation certificates.
DEFAULT_Q: Tuple[int, int] = (2, 1)


class LedgerRefusal(Exception):
    """A ledger writer refused its input (the SQL writers raise an exception)."""


class LedgerMismatch(Exception):
    """The ledger holds something other than what the adapter wrote."""


@dataclass(frozen=True)
class DerivationRecord:
    """A row of ``braid_derivation``."""

    source_id: str
    target_id: str
    steps: Tuple[str, ...]
    directions: Tuple[bool, ...]
    name: Optional[str] = None


@dataclass(frozen=True)
class TraceRecord:
    """The ids the adapter wrote for one braid and its trace."""

    source_id: str
    rewrite_ids: Tuple[str, ...]
    derivation_id: str
    target_id: str


class BraidLedgerBackend(Protocol):
    """The ledger operations the adapter uses (migrations 019–022)."""

    # writers (migration 019)
    def register_braid(self, strand_count: int, word: Sequence[int],
                       name: Optional[str] = None) -> str: ...
    def record_rewrite(self, input_id: str, rule_id: str, position: int) -> str: ...
    def record_derivation(self, source_id: str, steps: Sequence[str],
                          directions: Sequence[bool], name: Optional[str] = None) -> str: ...

    # readers
    def braid_row(self, braid_id: str) -> Optional[BraidRow]: ...
    def braid_name(self, braid_id: str) -> Optional[str]: ...
    def rewrite_row(self, rewrite_id: str) -> Optional[RewriteRow]: ...
    def rewrite_ends(self, rewrite_id: str) -> Optional[Tuple[str, str]]: ...
    def derivation(self, derivation_id: str) -> Optional[DerivationRecord]: ...
    def derivation_problems(self, derivation_id: str) -> List[Problem]: ...
    def equality_certified(self, a: str, b: str) -> bool: ...

    # certificates (migrations 020–022)
    def certify(self, braid_id: str) -> None: ...
    def invariant_differences(self, a: str, b: str) -> Optional[List[str]]: ...
    def normal_forms_equal(self, a: str, b: str) -> Optional[bool]: ...
    def representations_equal(self, a: str, b: str, q_num: int, q_den: int) -> Optional[bool]: ...


# ---------------------------------------------------------------------------
# Conversions between QBX-IR objects and ledger rows
# ---------------------------------------------------------------------------

def braid_row_of(braid: Braid) -> BraidRow:
    """The ``braid_word`` row of a QBX-IR braid (its hash is :func:`braid_hash`)."""
    return BraidRow(braid.strand_count, tuple(braid.short_form()), braid_hash(braid))


def rewrite_row_of(strand_count: int, t: Transformation) -> RewriteRow:
    """The ``braid_rewrite`` row that records the Transformation ``t`` verbatim.

    The braid rows carry the hashes recorded in ``t``, so a wrong hash in ``t``
    shows up as a ``hash`` problem of the braid (``input_not_well_formed`` or
    ``output_not_well_formed``), exactly as for a row inserted directly.
    """
    return RewriteRow(
        input=BraidRow(strand_count, tuple(t.input_word), t.input_hash),
        rule_id=t.rule_id,
        position=t.position,
        output=BraidRow(strand_count, tuple(t.output_word), t.output_hash),
        input_hash=t.input_hash,
        output_hash=t.output_hash,
        preserved=tuple(t.preserved_properties),
        changed=tuple(t.changed_properties),
    )


def transformation_of(row: RewriteRow) -> Transformation:
    """The Transformation a ``braid_rewrite`` row records."""
    return Transformation(
        input_hash=row.input_hash,
        rule_id=row.rule_id,
        position=row.position,
        output_hash=row.output_hash,
        preserved_properties=tuple(row.preserved),
        changed_properties=tuple(row.changed),
        input_word=tuple(row.input.word),
        output_word=tuple(row.output.word),
    )


def braid_of(row: BraidRow, name: Optional[str] = None) -> Braid:
    """The QBX-IR braid of a well-formed ``braid_word`` row."""
    if braid_problems(row):
        raise LedgerMismatch(f"braid row is not well formed: {braid_problems(row)}")
    return Braid.from_short_form(row.strand_count, list(row.word), name=name or "B")


# ---------------------------------------------------------------------------
# The in-memory reference backend
# ---------------------------------------------------------------------------

def _refuse(what: str, problems: List[Problem]) -> None:
    if problems:
        reason, details = problems[0]
        raise LedgerRefusal(f"{what}: {reason} ({details})")


class InMemoryBraidLedger:
    """In-memory reference for the ledger writers and readers of migrations 019–022."""

    def __init__(self) -> None:
        self.braids: Dict[str, BraidRow] = {}
        self.names: Dict[str, Optional[str]] = {}
        self.braid_by_key: Dict[Tuple[int, Tuple[int, ...]], str] = {}
        self.rewrites: Dict[str, Tuple[str, RewriteRow, str]] = {}
        self.derivations: Dict[str, DerivationRecord] = {}
        self.invariant_certs: Dict[str, invariant_ledger.CertRow] = {}
        self.nf_certs: Dict[str, normal_form_ledger.NFRow] = {}
        self.rep_certs: Dict[Tuple[str, Tuple[int, int]], representation_ledger.RepRow] = {}

    @staticmethod
    def _new_id() -> str:
        return str(uuid.uuid4())

    # -- writers ---------------------------------------------------------
    def register_braid(self, strand_count: int, word: Sequence[int],
                       name: Optional[str] = None) -> str:
        w = tuple(word)
        h = word_hash(strand_count, w) if strand_count >= 1 and None not in w else None
        _refuse("register_braid", braid_problems(BraidRow(strand_count, w, h)))
        key = (strand_count, w)
        if key in self.braid_by_key:
            return self.braid_by_key[key]
        bid = self._new_id()
        self.braids[bid] = BraidRow(strand_count, w, h)
        self.names[bid] = name
        self.braid_by_key[key] = bid
        return bid

    def record_rewrite(self, input_id: str, rule_id: str, position: int) -> str:
        bi = self.braids.get(input_id)
        if bi is None:
            raise LedgerRefusal(f"record_braid_rewrite: unknown braid {input_id}")
        if braid_problems(bi):
            raise LedgerRefusal(f"record_braid_rewrite: braid {input_id} is not well formed")
        if rule_id not in RULES:
            raise LedgerRefusal(f"record_braid_rewrite: rule_unknown ({rule_id})")
        out = apply_short(bi.word, rule_id, position)
        if out is None:
            raise LedgerRefusal(
                f"record_braid_rewrite: not_applicable (rule {rule_id}, position {position})")
        out_id = self.register_braid(bi.strand_count, out)
        bo = self.braids[out_id]
        rule = RULES[rule_id]
        row = RewriteRow(bi, rule_id, position, bo, bi.braid_hash, bo.braid_hash,
                         rule.preserved, rule.changed)
        _refuse("record_braid_rewrite", rewrite_problems(row))
        rid = self._new_id()
        self.rewrites[rid] = (input_id, row, out_id)
        return rid

    def _chain(self, steps: Sequence[str]):
        return [self.rewrites[s][1] if s in self.rewrites else None for s in steps]

    def _chain_end_id(self, source_id: str, steps: Sequence[str],
                      directions: Sequence[bool]) -> Optional[str]:
        if len(steps) != len(directions):
            return None
        cur = source_id
        for s, fwd in zip(steps, directions):
            if s not in self.rewrites:
                return None
            i, _, o = self.rewrites[s]
            start, end = (i, o) if fwd else (o, i)
            if start != cur:
                return None
            cur = end
        return cur

    def record_derivation(self, source_id: str, steps: Sequence[str],
                          directions: Sequence[bool], name: Optional[str] = None) -> str:
        if source_id not in self.braids:
            raise LedgerRefusal(f"record_braid_derivation: unknown braid {source_id}")
        tgt = self._chain_end_id(source_id, steps, directions)
        problems = derivation_problems(self.braids[source_id],
                                       self.braids[tgt] if tgt else self.braids[source_id],
                                       self._chain(steps), list(directions))
        problems = [p for p in problems if p[0] != "target_mismatch"]
        _refuse("record_braid_derivation", problems)
        did = self._new_id()
        self.derivations[did] = DerivationRecord(source_id, tgt, tuple(steps),
                                                 tuple(directions), name)
        return did

    # -- readers ---------------------------------------------------------
    def braid_row(self, braid_id: str) -> Optional[BraidRow]:
        return self.braids.get(braid_id)

    def braid_name(self, braid_id: str) -> Optional[str]:
        return self.names.get(braid_id)

    def rewrite_row(self, rewrite_id: str) -> Optional[RewriteRow]:
        r = self.rewrites.get(rewrite_id)
        return r[1] if r else None

    def rewrite_ends(self, rewrite_id: str) -> Optional[Tuple[str, str]]:
        r = self.rewrites.get(rewrite_id)
        return (r[0], r[2]) if r else None

    def derivation(self, derivation_id: str) -> Optional[DerivationRecord]:
        return self.derivations.get(derivation_id)

    def derivation_problems(self, derivation_id: str) -> List[Problem]:
        d = self.derivations[derivation_id]
        return derivation_problems(self.braids[d.source_id], self.braids[d.target_id],
                                   self._chain(d.steps), list(d.directions))

    def equality_certified(self, a: str, b: str) -> bool:
        if a == b:
            return True
        return any({d.source_id, d.target_id} == {a, b} and not self.derivation_problems(did)
                   for did, d in self.derivations.items())

    # -- certificates ----------------------------------------------------
    def certify(self, braid_id: str) -> None:
        row = self.braids.get(braid_id)
        if row is None or braid_problems(row):
            raise LedgerRefusal(f"certify: braid {braid_id} is unknown or not well formed")
        self.invariant_certs.setdefault(braid_id, invariant_ledger.CertRow.of(row))
        self.nf_certs.setdefault(braid_id, normal_form_ledger.NFRow.of(row))
        if row.strand_count <= MAX_REPRESENTATION_STRANDS:
            self.rep_certs.setdefault((braid_id, DEFAULT_Q),
                                      representation_ledger.RepRow.of(row, *DEFAULT_Q))

    def invariant_differences(self, a: str, b: str) -> Optional[List[str]]:
        return invariant_ledger.differences(self.invariant_certs.get(a),
                                            self.invariant_certs.get(b))

    def normal_forms_equal(self, a: str, b: str) -> Optional[bool]:
        return normal_form_ledger.normal_forms_equal(self.nf_certs.get(a), self.nf_certs.get(b))

    def representations_equal(self, a: str, b: str, q_num: int, q_den: int) -> Optional[bool]:
        q = (q_num, q_den)
        return representation_ledger.representations_equal(self.rep_certs.get((a, q)),
                                                           self.rep_certs.get((b, q)))


# ---------------------------------------------------------------------------
# Checking a trace before writing it
# ---------------------------------------------------------------------------

def trace_problems(braid: Braid, trace: Sequence[Transformation]) -> List[Problem]:
    """Problems of a trace, found before anything is written.

    For step ``k`` the problems of :func:`qbx_ir.ledger.rewrite_problems` on the
    row that records ``trace[k]`` verbatim are reported as
    ``("step_problem", {"step": k, "reason": ..., "details": ...})``; a step that
    does not start where the previous one ended (or, for step 0, at ``braid``)
    is reported as ``("step_disconnected", {"step": k})`` and stops the check.
    An empty list means the ledger writers will accept every step and record
    exactly these Transformations.
    """
    n = braid.strand_count
    out: List[Problem] = []
    src = braid_row_of(braid)
    for reason, details in braid_problems(src):
        out.append(("source_problem", {"reason": reason, "details": details}))
    if out:
        return out
    cur = src
    for k, t in enumerate(trace):
        row = rewrite_row_of(n, t)
        if (tuple(t.input_word), t.input_hash) != (cur.word, cur.braid_hash):
            out.append(("step_disconnected", {"step": k}))
            return out
        for reason, details in rewrite_problems(row):
            out.append(("step_problem", {"step": k, "reason": reason, "details": details}))
        cur = row.output
    return out


# ---------------------------------------------------------------------------
# Writing
# ---------------------------------------------------------------------------

def write_trace(ledger: BraidLedgerBackend, braid: Braid, trace: Sequence[Transformation],
                name: Optional[str] = None) -> TraceRecord:
    """Write ``braid``, one rewrite record per Transformation, and the forward
    derivation along them; return the ids.

    Raises :class:`ValueError` (nothing written) if :func:`trace_problems`
    finds a problem, :class:`LedgerRefusal` if a writer refuses, and
    :class:`LedgerMismatch` if a record the ledger computed differs from the
    Transformation it should record.
    """
    problems = trace_problems(braid, trace)
    if problems:
        raise ValueError(f"trace refused before writing: {problems[0]}")
    source_id = ledger.register_braid(braid.strand_count, braid.short_form(),
                                      name if name is not None else braid.name)
    cur = source_id
    rewrite_ids: List[str] = []
    for k, t in enumerate(trace):
        rid = ledger.record_rewrite(cur, t.rule_id, t.position)
        recorded = read_transformation(ledger, rid)
        if recorded != t:
            raise LedgerMismatch(f"step {k}: ledger recorded {recorded.to_dict()}, "
                                 f"expected {t.to_dict()}")
        rewrite_ids.append(rid)
        cur = ledger.rewrite_ends(rid)[1]
    did = ledger.record_derivation(source_id, rewrite_ids, [True] * len(rewrite_ids), name)
    d = ledger.derivation(did)
    if d is None or d.target_id != cur:
        raise LedgerMismatch("the derivation does not end where the trace ends")
    return TraceRecord(source_id, tuple(rewrite_ids), did, cur)


def persist_normal_form(ledger: BraidLedgerBackend, braid: Braid,
                        name: Optional[str] = None, certify: bool = False
                        ) -> Tuple[Braid, List[Transformation], TraceRecord]:
    """Reduce ``braid`` with :func:`normal_form_with_trace` and write the braid,
    its trace and the derivation to the reduced word (optionally with
    certificates at both ends, :func:`certify_trace`)."""
    reduced, trace = normal_form_with_trace(braid)
    record = write_trace(ledger, braid, trace, name)
    if certify:
        certify_trace(ledger, record)
    return reduced, trace, record


def certify_trace(ledger: BraidLedgerBackend, record: TraceRecord) -> None:
    """Attach invariant, normal-form and representation certificates (q = 2) to
    the source and the target of a written trace."""
    for bid in dict.fromkeys((record.source_id, record.target_id)):
        ledger.certify(bid)


# ---------------------------------------------------------------------------
# Reading back
# ---------------------------------------------------------------------------

def read_braid(ledger: BraidLedgerBackend, braid_id: str) -> Braid:
    """The QBX-IR braid stored under ``braid_id``."""
    row = ledger.braid_row(braid_id)
    if row is None:
        raise LedgerMismatch(f"unknown braid {braid_id}")
    return braid_of(row, ledger.braid_name(braid_id))


def read_transformation(ledger: BraidLedgerBackend, rewrite_id: str) -> Transformation:
    """The Transformation recorded under ``rewrite_id``."""
    row = ledger.rewrite_row(rewrite_id)
    if row is None:
        raise LedgerMismatch(f"unknown rewrite record {rewrite_id}")
    return transformation_of(row)


def read_trace(ledger: BraidLedgerBackend, derivation_id: str
               ) -> Tuple[Braid, List[Tuple[Transformation, bool]], Braid]:
    """Source braid, steps (Transformation, used forwards?) and target braid of a derivation."""
    d = ledger.derivation(derivation_id)
    if d is None:
        raise LedgerMismatch(f"unknown derivation {derivation_id}")
    steps = [(read_transformation(ledger, s), fwd) for s, fwd in zip(d.steps, d.directions)]
    return read_braid(ledger, d.source_id), steps, read_braid(ledger, d.target_id)


# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------

def verify_trace(ledger: BraidLedgerBackend, record: TraceRecord, braid: Braid,
                 trace: Sequence[Transformation]) -> List[Problem]:
    """Compare what the ledger holds for ``record`` with ``braid`` and ``trace``.

    Problems, in this order:

    * ``derivation_unknown`` — the derivation is missing (nothing else is checked);
    * ``source_mismatch`` — the stored source (strand count, word, hash) is not ``braid``'s;
    * ``trace_length`` — the derivation has a different number of steps;
    * ``step_id_mismatch`` / ``step_direction`` / ``step_mismatch`` — step ``k``
      is not the recorded rewrite, is used backwards, or records a different Transformation;
    * ``target_mismatch`` — the stored target is not where the trace ends;
    * ``derivation_problem`` — the ledger's own check of the derivation fails;
    * ``not_certified`` — the ledger does not certify that the braids the
      adapter wrote as source and target (``record``) are equal.

    An empty list means the round trip is exact and the ledger certifies that
    ``braid`` and the end of ``trace`` are equal in B_n.
    """
    out: List[Problem] = []
    d = ledger.derivation(record.derivation_id)
    if d is None:
        return [("derivation_unknown", {})]
    src_row = ledger.braid_row(d.source_id)
    expected_src = braid_row_of(braid)
    if src_row is None or (src_row.strand_count, src_row.word, src_row.braid_hash) != (
            expected_src.strand_count, expected_src.word, expected_src.braid_hash):
        out.append(("source_mismatch", {
            "expected": [expected_src.strand_count, list(expected_src.word)],
            "recorded": None if src_row is None else [src_row.strand_count, list(src_row.word)]}))
    if len(d.steps) != len(trace):
        out.append(("trace_length", {"expected": len(trace), "recorded": len(d.steps)}))
    for k, (sid, fwd, t) in enumerate(zip(d.steps, d.directions, trace)):
        if k < len(record.rewrite_ids) and sid != record.rewrite_ids[k]:
            out.append(("step_id_mismatch", {"step": k}))
        if not fwd:
            out.append(("step_direction", {"step": k}))
        row = ledger.rewrite_row(sid)
        recorded = None if row is None else transformation_of(row)
        if recorded != t:
            out.append(("step_mismatch", {
                "step": k, "expected": t.to_dict(),
                "recorded": None if recorded is None else recorded.to_dict()}))
    end_word = tuple(trace[-1].output_word) if trace else expected_src.word
    tgt_row = ledger.braid_row(d.target_id)
    if tgt_row is None or (tgt_row.strand_count, tgt_row.word) != (braid.strand_count, end_word):
        out.append(("target_mismatch", {
            "expected": list(end_word),
            "recorded": None if tgt_row is None else list(tgt_row.word)}))
    for reason, details in ledger.derivation_problems(record.derivation_id):
        out.append(("derivation_problem", {"reason": reason, "details": details}))
    if not ledger.equality_certified(record.source_id, record.target_id):
        out.append(("not_certified", {}))
    return out


def certificate_problems_of_trace(ledger: BraidLedgerBackend, record: TraceRecord
                                  ) -> List[Problem]:
    """Check the certificates at the two ends of a written trace.

    The two ends are equal in B_n, so (proved, Lean ``cert_eq_of_eval_eq`` and
    ``repCert_eq_of_eval_eq``) their invariant certificates show no difference
    and their representation certificates are equal.  Their normal-form
    certificates are expected to be equal too; for 3 or more strands that
    expectation is Garside's uniqueness theorem (H-057, provisional), so a
    ``normal_form_differs`` problem would refute H-057 or reveal a bug.

    Problems: ``invariant_missing`` / ``invariant_differs`` {"invariants": [...]},
    ``normal_form_missing`` / ``normal_form_differs``, ``representation_missing``
    / ``representation_differs`` (only for at most 6 strands).
    """
    a, b = record.source_id, record.target_id
    out: List[Problem] = []
    diffs = ledger.invariant_differences(a, b)
    if diffs is None:
        out.append(("invariant_missing", {}))
    elif diffs:
        out.append(("invariant_differs", {"invariants": list(diffs)}))
    nf = ledger.normal_forms_equal(a, b)
    if nf is None:
        out.append(("normal_form_missing", {}))
    elif not nf:
        out.append(("normal_form_differs", {}))
    row = ledger.braid_row(a)
    if row is not None and row.strand_count <= MAX_REPRESENTATION_STRANDS:
        rep = ledger.representations_equal(a, b, *DEFAULT_Q)
        if rep is None:
            out.append(("representation_missing", {}))
        elif not rep:
            out.append(("representation_differs", {}))
    return out


def round_trip(ledger: BraidLedgerBackend, braid: Braid, certify: bool = False
               ) -> Tuple[TraceRecord, List[Problem]]:
    """Persist ``braid``'s normal-form trace, read it back and verify it.

    Returns the record and every problem found (:func:`verify_trace`, then, with
    ``certify``, :func:`certificate_problems_of_trace`).
    """
    _, trace, record = persist_normal_form(ledger, braid, certify=certify)
    problems = verify_trace(ledger, record, braid, trace)
    if certify:
        problems += certificate_problems_of_trace(ledger, record)
    return record, problems


__all__ = [
    "BraidLedgerBackend",
    "DerivationRecord",
    "InMemoryBraidLedger",
    "LedgerMismatch",
    "LedgerRefusal",
    "TraceRecord",
    "braid_of",
    "braid_row_of",
    "certificate_problems_of_trace",
    "certify_trace",
    "persist_normal_form",
    "read_braid",
    "read_trace",
    "read_transformation",
    "rewrite_row_of",
    "round_trip",
    "trace_problems",
    "transformation_of",
    "verify_trace",
    "write_trace",
]
