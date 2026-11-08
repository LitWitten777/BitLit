"""
Canonical serialization.

Rules (from specs/canonical_serialization.md):

- CBOR deterministic (RFC 8949) for addresses and paths.
- Canonical JSON (RFC 8785-style) for JSON payloads.
- Protobuf deterministic for core artifacts (handled by callers).

This module provides the canonicalization helpers. It does NOT do
cryptographic hashing — see qbx.core.hashing for that.
"""

from __future__ import annotations

import json
import unicodedata
from typing import Any

import cbor2

from qbx.core.exceptions import CanonicalizationError


def _normalize_unicode(value: Any) -> Any:
    """Recursively normalize strings to NFC."""
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, dict):
        return {_normalize_unicode(k): _normalize_unicode(v) for k, v in value.items()}
    if isinstance(value, list):
        return [_normalize_unicode(v) for v in value]
    if isinstance(value, tuple):
        return tuple(_normalize_unicode(v) for v in value)
    return value


def _normalize_numbers(value: Any) -> Any:
    """Normalize floats to shortest decimal form (minimal representation)."""
    if isinstance(value, float):
        # Use repr for shortest round-trip
        s = repr(value)
        # Avoid -0.0
        if s == "-0.0":
            return 0.0
        return float(s)
    if isinstance(value, dict):
        return {k: _normalize_numbers(v) for k, v in value.items()}
    if isinstance(value, list):
        return [_normalize_numbers(v) for v in value]
    return value


def canonical_json(obj: Any) -> bytes:
    """
    Produce canonical JSON bytes:

    - NFC-normalized strings
    - Sorted object keys (lexicographic by Unicode codepoint)
    - No insignificant whitespace
    - Minimal number representation
    - UTF-8 encoded

    Note: this is a pragmatic RFC-8785-style implementation. For strict
    compliance, use a dedicated library. This module prioritizes determinism.
    """
    try:
        normalized = _normalize_numbers(_normalize_unicode(obj))
        # Python's json.dumps with sort_keys=True handles key ordering.
        # ensure_ascii=False + UTF-8 encode gives us canonical bytes.
        s = json.dumps(
            normalized,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
        return s.encode("utf-8")
    except (TypeError, ValueError) as e:
        raise CanonicalizationError(f"Canonical JSON failed: {e}") from e


def canonical_cbor(obj: Any) -> bytes:
    """
    Produce deterministic CBOR bytes (RFC 8949 deterministic encoding).

    cbor2 supports canonical=True which implements deterministic encoding:

    - Shortest form for integers
    - Sorted map keys (by length then bytewise)
    - Definite-length for all arrays/maps/strings
    """
    try:
        normalized = _normalize_unicode(obj)
        return cbor2.dumps(normalized, canonical=True)
    except (TypeError, ValueError) as e:
        raise CanonicalizationError(f"Canonical CBOR failed: {e}") from e


def canonical_bytes(obj: Any, format_hint: str = "cbor") -> bytes:
    """
    Dispatch to the appropriate canonical encoder.

    format_hint:

    - "cbor"  → canonical CBOR (default for addresses/paths)
    - "json"  → canonical JSON
    - "protobuf" → caller must supply pre-serialized bytes; raise if dict
    """
    if format_hint == "cbor":
        return canonical_cbor(obj)
    if format_hint == "json":
        return canonical_json(obj)
    if format_hint == "protobuf":
        if isinstance(obj, (bytes, bytearray)):
            return bytes(obj)
        raise CanonicalizationError(
            "Protobuf canonicalization requires pre-serialized bytes"
        )
    raise CanonicalizationError(f"Unknown canonical format: {format_hint}")


def decode_cbor(data: bytes) -> Any:
    """Decode CBOR bytes back to Python object."""
    return cbor2.loads(data)
