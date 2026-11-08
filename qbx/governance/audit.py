"""
The audit log as a hash chain (migration 015).

``audit_record`` is append-only.  On insert the database numbers the record
(``seq`` = 1, 2, …), links it to the previous record (``prev_hash``, the
previous ``record_hash``; :data:`GENESIS` for the first) and stores

    record_hash = hex(SHA-256(payload))

where the payload is the concatenation of the fields ``prev_hash``, ``seq``,
``actor``, ``action``, ``artifact_id``, ``morphism_id``, ``details`` (its
``jsonb`` text), ``signature`` (lowercase hex) and ``created_at`` (microseconds
since the Unix epoch), each encoded as ``-`` when NULL and otherwise as
``<number of UTF-8 bytes>:<UTF-8 bytes>`` — a prefix code, so the payload
determines the fields.  By ``Formal/Modality.lean`` (``chainHash_injective``),
when the step hash is collision-free and never yields the genesis value, the
newest ``record_hash`` determines the whole log.

:func:`chain_problems` is the reference for ``governance_audit_chain_problems``.
"""

from __future__ import annotations

import hashlib
from datetime import datetime, timezone
from typing import Any, List, Optional, Sequence, Tuple

from qbx.governance.modality import Problem
from qbx.governance.policy import is_blank

GENESIS = "0" * 64
_EPOCH = datetime(1970, 1, 1, tzinfo=timezone.utc)


def encode_field(value: Optional[str]) -> bytes:
    if value is None:
        return b"-"
    b = value.encode("utf-8")
    return str(len(b)).encode() + b":" + b


def epoch_micros(ts: datetime) -> int:
    d = ts - _EPOCH
    return (d.days * 86400 + d.seconds) * 1_000_000 + d.microseconds


def record_payload(prev_hash: Optional[str], seq: Optional[int], actor: Optional[str],
                   action: Optional[str], artifact_id: Optional[str],
                   morphism_id: Optional[str], details_text: Optional[str],
                   signature: Optional[bytes], created_at: Optional[datetime]) -> bytes:
    fields = [prev_hash, None if seq is None else str(seq), actor, action,
              None if artifact_id is None else str(artifact_id),
              None if morphism_id is None else str(morphism_id), details_text,
              None if signature is None else bytes(signature).hex(),
              None if created_at is None else str(epoch_micros(created_at))]
    return b"".join(encode_field(f) for f in fields)


def record_hash(*fields: Any) -> str:
    """``audit_record_hash``: SHA-256 (hex) of :func:`record_payload`."""
    return hashlib.sha256(record_payload(*fields)).hexdigest()


def audit_problems(actor: Optional[str], action: Optional[str], details: Any) -> List[Problem]:
    """``audit_typing`` {error: actor | action} (blank), {error: details} (not
    a JSON object)."""
    out: List[Problem] = []
    if is_blank(actor):
        out.append(("audit_typing", {"error": "actor"}))
    if is_blank(action):
        out.append(("audit_typing", {"error": "action"}))
    if not isinstance(details, dict):
        out.append(("audit_typing", {"error": "details"}))
    return out


#: A stored record: (seq, prev_hash, record_hash, actor, action, artifact_id,
#: morphism_id, details_text, signature, created_at).
Record = Tuple[Any, ...]


def chain_problems(records: Sequence[Record]) -> List[Tuple[int, Problem]]:
    """``governance_audit_chain_problems``: walk the records in ``seq`` order
    and return (index, problem) pairs, ``audit_chain`` with error gap {seq,
    expected} (seq is not the previous seq + 1, 1 for the first), link {seq}
    (prev_hash is not the previous record_hash, the genesis value for the
    first), hash {seq} (record_hash is not the hash of the stored fields)."""
    out: List[Tuple[int, Problem]] = []
    expected_prev, expected_seq = GENESIS, 1
    for i, r in enumerate(records):
        seq, prev, rh = r[0], r[1], r[2]
        if seq != expected_seq:
            out.append((i, ("audit_chain", {"error": "gap", "seq": seq,
                                            "expected": expected_seq})))
        if prev != expected_prev:
            out.append((i, ("audit_chain", {"error": "link", "seq": seq})))
        if rh != record_hash(prev, seq, *r[3:]):
            out.append((i, ("audit_chain", {"error": "hash", "seq": seq})))
        expected_prev = rh
        expected_seq = (seq or 0) + 1
    return out
