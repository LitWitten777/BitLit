"""
AddressV2: the content address of a path signature.

The payload is the one :meth:`qbx.path.signature.PathSignature.build` hashes
(byte fields as lowercase hex text)::

    {
      "version": 2,
      "universe_id": "<uuid>",            # lowercase canonical form
      "artifact_id": null | "<uuid>",
      "path_signature": "<hex>",          # the canonical path bytes, non-empty
      "coords": "<hex>",                  # may be empty
      "coords_scale": uint,
      "semantic_tags": ["<hex>", ...],
      "trust_hint": {"trust_score": float in [0, 1], "verification_depth": uint},
      "routing_hint": null | {text: text},
      "timestamp": uint,
      "nonce": "<32 hex digits>"          # 16 bytes
    }

encoded with :func:`qbx.core.canonical.canonical_cbor` and hashed with
:func:`qbx.core.hashing.pq_hash`.  :func:`address_problems` is the reference
for ``addr_address_problems`` in migration ``013_addressing_protocol.sql``:
it reports the same problems, with the same details.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Optional, Tuple

from qbx.addressing.cbor_strict import decode_strict
from qbx.core.canonical import canonical_cbor
from qbx.core.hashing import pq_hash

Problem = Tuple[str, Dict[str, Any]]

NIL_UUID = "00000000-0000-0000-0000-000000000000"
HASH_ALGOS = ("SHA3-256", "SHA3-512", "SHA-256", "PQ-HASH-1")
FIELDS = ("version", "universe_id", "artifact_id", "path_signature", "coords", "coords_scale",
          "semantic_tags", "trust_hint", "routing_hint", "timestamp", "nonce")
TRUST_FIELDS = ("trust_score", "verification_depth")

UUID_RE = re.compile(r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}")
HEX_RE = re.compile(r"(?:[0-9a-f]{2})*")
NONCE_RE = re.compile(r"[0-9a-f]{32}")
_HASH_RE = {
    "SHA3-256": re.compile(r"[0-9a-f]{64}"),
    "SHA-256": re.compile(r"[0-9a-f]{64}"),
    "SHA3-512": re.compile(r"[0-9a-f]{128}"),
    "PQ-HASH-1": re.compile(r"PQ1:[0-9a-f]{128}"),
}


def hash_format_ok(address_hash: Any, algo: Any) -> bool:
    """Is ``address_hash`` a well-formed digest of algorithm ``algo``?"""
    return (isinstance(address_hash, str) and algo in _HASH_RE
            and _HASH_RE[algo].fullmatch(address_hash) is not None)


def is_address_hash(address_hash: Any) -> bool:
    """Is ``address_hash`` a well-formed digest of some supported algorithm?"""
    return any(hash_format_ok(address_hash, a) for a in HASH_ALGOS)


@dataclass(frozen=True)
class AddressV2:
    """An AddressV2 value.  ``encode`` gives the canonical CBOR bytes."""

    path_signature: bytes
    universe_id: str = NIL_UUID
    artifact_id: Optional[str] = None
    coords: bytes = b""
    coords_scale: int = 0
    semantic_tags: Tuple[bytes, ...] = ()
    trust_score: float = 0.0
    verification_depth: int = 0
    routing_hint: Optional[Dict[str, str]] = None
    timestamp: int = 0
    nonce: bytes = bytes(16)

    def payload(self) -> Dict[str, Any]:
        return {
            "version": 2,
            "universe_id": self.universe_id,
            "artifact_id": self.artifact_id,
            "path_signature": self.path_signature.hex(),
            "coords": self.coords.hex(),
            "coords_scale": self.coords_scale,
            "semantic_tags": [t.hex() for t in self.semantic_tags],
            "trust_hint": {"trust_score": float(self.trust_score),
                           "verification_depth": int(self.verification_depth)},
            "routing_hint": self.routing_hint,
            "timestamp": self.timestamp,
            "nonce": self.nonce.hex(),
        }

    def encode(self) -> bytes:
        return canonical_cbor(self.payload())

    def address_hash(self, algo: str = "SHA3-256") -> str:
        return pq_hash(self.encode(), algo)

    @classmethod
    def decode(cls, data: bytes) -> "AddressV2":
        """Decode canonical bytes; raises ``ValueError`` listing the problems."""
        d = decode_strict(data)
        probs: List[Problem] = []
        if not d.ok:
            probs.append(("cbor_malformed", d.malformed))
        else:
            probs += [("cbor_non_canonical", e) for e in d.non_canonical]
            probs += schema_problems(d.value)
        if probs:
            raise ValueError(f"not a canonical AddressV2: {probs}")
        m = d.value["$map"]
        th = m["trust_hint"]["$map"]
        return cls(
            path_signature=bytes.fromhex(m["path_signature"]),
            universe_id=m["universe_id"],
            artifact_id=m["artifact_id"],
            coords=bytes.fromhex(m["coords"]),
            coords_scale=m["coords_scale"],
            semantic_tags=tuple(bytes.fromhex(t) for t in m["semantic_tags"]),
            trust_score=th["trust_score"]["$float"],
            verification_depth=th["verification_depth"],
            routing_hint=None if m["routing_hint"] is None else dict(m["routing_hint"]["$map"]),
            timestamp=m["timestamp"],
            nonce=bytes.fromhex(m["nonce"]),
        )


# ---------------------------------------------------------------------------
# Schema
# ---------------------------------------------------------------------------
def _is_int(v: Any) -> bool:
    return type(v) is int


def _is_map(v: Any) -> bool:
    return isinstance(v, dict) and "$map" in v


def _is_float(v: Any) -> bool:
    return isinstance(v, dict) and "$float" in v


def _hex(v: Any, nonempty: bool = False) -> bool:
    return isinstance(v, str) and HEX_RE.fullmatch(v) is not None and (v != "" or not nonempty)


def _schema(field_name: str, error: str) -> Problem:
    return ("address_schema", {"field": field_name, "error": error})


def trust_score_ok(v: Any) -> bool:
    return _is_float(v) and 0.0 <= float(v["$float"]) <= 1.0


def depth_ok(v: Any) -> bool:
    return _is_int(v) and v >= 0


def schema_problems(value: Any) -> List[Problem]:
    """``address_schema`` problems of a decoded (tagged) value."""
    if not _is_map(value):
        return [_schema("", "not_a_map")]
    m = value["$map"]
    out: List[Problem] = []
    for k in FIELDS:
        if k not in m:
            out.append(_schema(k, "missing"))
    for k in m:
        if k not in FIELDS:
            out.append(_schema(k, "unknown"))

    def check(name: str, ok_type: Callable[[Any], bool], ok_value: Callable[[Any], bool],
              value_error: str) -> None:
        if name not in m:
            return
        if not ok_type(m[name]):
            out.append(_schema(name, "type"))
        elif not ok_value(m[name]):
            out.append(_schema(name, value_error))

    def uuid_ok(v: Any) -> bool:
        return UUID_RE.fullmatch(v) is not None

    is_str = lambda v: isinstance(v, str)  # noqa: E731
    check("version", _is_int, lambda v: v == 2, "value")
    check("universe_id", is_str, uuid_ok, "format")
    check("artifact_id", lambda v: v is None or is_str(v), lambda v: v is None or uuid_ok(v),
          "format")
    check("path_signature", is_str, lambda v: _hex(v, nonempty=True), "format")
    check("coords", is_str, _hex, "format")
    check("coords_scale", _is_int, lambda v: v >= 0, "range")
    check("semantic_tags", lambda v: isinstance(v, list), lambda v: all(_hex(t) for t in v),
          "element")
    check("routing_hint", lambda v: v is None or _is_map(v),
          lambda v: v is None or all(is_str(x) for x in v["$map"].values()), "element")
    check("timestamp", _is_int, lambda v: v >= 0, "range")
    check("nonce", is_str, lambda v: NONCE_RE.fullmatch(v) is not None, "format")
    if "trust_hint" in m:
        th = m["trust_hint"]
        if not _is_map(th):
            out.append(_schema("trust_hint", "type"))
        else:
            t = th["$map"]
            for k in TRUST_FIELDS:
                if k not in t:
                    out.append(_schema(f"trust_hint.{k}", "missing"))
            for k in t:
                if k not in TRUST_FIELDS:
                    out.append(_schema(f"trust_hint.{k}", "unknown"))
            if "trust_score" in t:
                if not _is_float(t["trust_score"]):
                    out.append(_schema("trust_hint.trust_score", "type"))
                elif not trust_score_ok(t["trust_score"]):
                    out.append(_schema("trust_hint.trust_score", "range"))
            if "verification_depth" in t:
                if not _is_int(t["verification_depth"]):
                    out.append(_schema("trust_hint.verification_depth", "type"))
                elif not depth_ok(t["verification_depth"]):
                    out.append(_schema("trust_hint.verification_depth", "range"))
    return out


def trust_hint_of(value: Any) -> Tuple[Optional[float], Optional[int]]:
    """The valid trust score / verification depth of a decoded value (``None`` if invalid)."""
    if not _is_map(value) or not _is_map(value["$map"].get("trust_hint")):
        return None, None
    t = value["$map"]["trust_hint"]["$map"]
    score = float(t["trust_score"]["$float"]) if trust_score_ok(t.get("trust_score")) else None
    depth = t["verification_depth"] if depth_ok(t.get("verification_depth")) else None
    return score, depth


# ---------------------------------------------------------------------------
# Problems of one registry row
# ---------------------------------------------------------------------------
def pointer_problems(pointers: Any) -> List[Problem]:
    """``pointer_typing``: pointers must be a list of distinct non-empty strings."""
    if not isinstance(pointers, list):
        return [("pointer_typing", {"error": "not_array"})]
    out: List[Problem] = []
    if not all(isinstance(p, str) and p != "" for p in pointers):
        out.append(("pointer_typing", {"error": "element"}))
    elif len(set(pointers)) != len(pointers):
        out.append(("pointer_typing", {"error": "duplicate"}))
    return out


def address_problems(address_cbor: bytes, address_hash: Any, hash_algo: Any = "SHA3-256",
                     trust_score: Any = None, verification_depth: Any = None,
                     check_trust: bool = True) -> List[Problem]:
    """Every problem of an address: hash format and integrity, CBOR, schema and
    (with ``check_trust``) agreement of the recorded trust columns with the hint."""
    out: List[Problem] = []
    if not hash_format_ok(address_hash, hash_algo):
        out.append(("address_hash_format", {"algo": hash_algo}))
    elif pq_hash(bytes(address_cbor), hash_algo) != address_hash:
        out.append(("address_hash_mismatch", {"algo": hash_algo}))
    d = decode_strict(bytes(address_cbor))
    if not d.ok:
        out.append(("cbor_malformed", d.malformed))
        return out
    out += [("cbor_non_canonical", e) for e in d.non_canonical]
    out += schema_problems(d.value)
    if check_trust:
        score, depth = trust_hint_of(d.value)
        if score is not None and not (isinstance(trust_score, float) and trust_score == score):
            out.append(("trust_mismatch", {"column": "trust_score"}))
        if depth is not None and verification_depth != depth:
            out.append(("trust_mismatch", {"column": "verification_depth"}))
    return out


def for_path(canonical_path_bytes: bytes, **kw: Any) -> AddressV2:
    """The AddressV2 of a path signature's canonical bytes."""
    return AddressV2(path_signature=canonical_path_bytes, **kw)
