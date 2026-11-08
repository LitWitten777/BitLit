"""
Wire format for chunk summaries — the unit a QBX node stores and exchanges.

Two summary kinds travel on the wire; both are the monoid elements that the
certified scheduler combines (Lean: ``QBX.Formal.MultiProver.Scheduler``,
``QBX.Formal.TextManifold.mapReduce``), so a receiver can merge what it
decodes without ever seeing the underlying text.

``chunk-reading`` (:class:`qbx_ir.algebra.multiprover.ChunkReading`)
    ``(n, σ, w, B)`` — strand count, permutation, writhe and the *exact*
    reduced Burau matrix over ℤ[t, t⁻¹].

``text-summary`` (:class:`qbx_bible.manifold.ChunkSummary`)
    ``(n, σ, w, B mod p, h, words, …)`` — everything mergeable about a piece of
    text, with the Burau fingerprint over GF(p) and the polynomial hash.

Encoding of a Laurent matrix (``B`` of size ``m × m``)
------------------------------------------------------
``{"rows": m, "emin": e₀, "emax": e₁, "coeffs": [...]}`` with
``coeffs`` the flat row-major list of ``m · m · (e₁ − e₀ + 1)`` integers:
entry ``(r, c)`` is ``Σ_k coeffs[(r·m + c)·W + k] · t^(e₀ + k)``, ``W = e₁ − e₀ + 1``.
The exponent window ``[e₀, e₁]`` is the tightest one containing every non-zero
coefficient (``[0, 0]`` for the zero matrix and for ``m = 0``), so the encoding
is canonical: equal matrices give equal bytes.  The Burau representation is
integral, so non-integer coefficients are rejected.

Every message carries ``"v"`` (format version) and ``"kind"``.  Bytes are
produced with :func:`qbx.core.canonical.canonical_cbor` (RFC 8949 deterministic
encoding) or :func:`~qbx.core.canonical.canonical_json`; :func:`digest` is the
SHA-256 of the canonical CBOR bytes and is the content address of a summary.

Decoding validates the shape (lengths, permutation, window) and raises
:class:`WireError` on malformed input.
"""

from __future__ import annotations

import hashlib
from fractions import Fraction
from typing import Any, Dict, List, Sequence, Tuple

from qbx.core.canonical import canonical_cbor, canonical_json, decode_cbor
from qbx_ir.algebra.laurent import Laurent
from qbx_ir.algebra.multiprover import ChunkReading

#: Wire format version.  Bump on any incompatible change (it is part of cache keys).
WIRE_VERSION = 1

KIND_READING = "chunk-reading"
KIND_TEXT = "text-summary"


class WireError(ValueError):
    """A message does not decode to a well-formed summary."""


# ----------------------------------------------------------------------------- Laurent matrices

def encode_laurent_matrix(mat: Sequence[Sequence[Laurent]]) -> Dict[str, Any]:
    """Exponent window + flat integer coefficients (see the module docstring)."""
    m = len(mat)
    exps = [k for row in mat for e in row for k, v in e.coeffs.items() if v != 0]
    if any(len(row) != m for row in mat):
        raise WireError("Burau matrix is not square")
    emin, emax = (min(exps), max(exps)) if exps else (0, 0)
    width = emax - emin + 1
    flat: List[int] = []
    for row in mat:
        for e in row:
            block = [0] * width
            for k, v in e.coeffs.items():
                if v == 0:
                    continue
                if Fraction(v).denominator != 1:
                    raise WireError("non-integer Burau coefficient")
                block[k - emin] = int(v)
            flat.extend(block)
    return {"rows": m, "emin": emin, "emax": emax, "coeffs": flat}


def decode_laurent_matrix(obj: Dict[str, Any]) -> Tuple[Tuple[Laurent, ...], ...]:
    try:
        m, emin, emax, flat = obj["rows"], obj["emin"], obj["emax"], obj["coeffs"]
    except (KeyError, TypeError) as e:
        raise WireError(f"bad Laurent matrix: {e}") from e
    if not all(isinstance(x, int) for x in (m, emin, emax)) or m < 0 or emax < emin:
        raise WireError("bad Laurent matrix header")
    width = emax - emin + 1
    if not isinstance(flat, list) or len(flat) != m * m * width:
        raise WireError("coefficient list has the wrong length")
    if not all(isinstance(x, int) for x in flat):
        raise WireError("non-integer coefficient")
    rows = []
    for r in range(m):
        row = []
        for c in range(m):
            base = (r * m + c) * width
            row.append(Laurent({emin + k: flat[base + k] for k in range(width) if flat[base + k]}))
        rows.append(tuple(row))
    out = tuple(rows)
    if encode_laurent_matrix(out) != obj:
        raise WireError("non-canonical exponent window")
    return out


def _check_perm(perm: Any, n: int) -> Tuple[int, ...]:
    if not isinstance(perm, list) or sorted(perm) != list(range(1, n + 1)):
        raise WireError("perm is not a permutation of 1..n")
    return tuple(perm)


# ----------------------------------------------------------------------------- chunk readings

def encode_reading(r: ChunkReading) -> Dict[str, Any]:
    return {
        "v": WIRE_VERSION,
        "kind": KIND_READING,
        "n": r.strand_count,
        "perm": list(r.perm),
        "writhe": r.writhe,
        "burau": encode_laurent_matrix(r.burau),
    }


def decode_reading(obj: Dict[str, Any]) -> ChunkReading:
    _check_header(obj, KIND_READING)
    n = obj.get("n")
    if not isinstance(n, int) or n < 1:
        raise WireError("bad strand count")
    writhe = obj.get("writhe")
    if not isinstance(writhe, int):
        raise WireError("bad writhe")
    burau = decode_laurent_matrix(obj.get("burau"))
    if len(burau) != n - 1:
        raise WireError("Burau matrix size is not n − 1")
    return ChunkReading(n, _check_perm(obj.get("perm"), n), writhe, burau)


# ----------------------------------------------------------------------------- text summaries

def encode_text_summary(s) -> Dict[str, Any]:
    """Encode a :class:`qbx_bible.manifold.ChunkSummary`."""
    return {
        "v": WIRE_VERSION,
        "kind": KIND_TEXT,
        "n": s.strand_count,
        "letters": s.letters,
        "finals": s.finals,
        "writhe": s.writhe,
        "perm": list(s.positions),
        "crossings": [[a, b, v] for (a, b), v in s.crossings],
        "burau_mod_p": [list(row) for row in s.burau],
        "hash": [s.hash_scale, s.hash_value],
        "words": s.words,
        "edges": [s.starts_in_word, s.ends_in_word, s.empty],
        "short": None if s.short is None else list(s.short),
    }


def decode_text_summary(obj: Dict[str, Any]):
    from qbx_bible.manifold import PRIME, ChunkSummary

    _check_header(obj, KIND_TEXT)
    try:
        n = obj["n"]
        perm = _check_perm(obj["perm"], n)
        cross = tuple(((a, b), v) for a, b, v in obj["crossings"])
        burau = tuple(tuple(row) for row in obj["burau_mod_p"])
        scale, value = obj["hash"]
        starts, ends, empty = obj["edges"]
        short = None if obj["short"] is None else tuple(obj["short"])
        s = ChunkSummary(n, obj["letters"], obj["finals"], obj["writhe"], perm, cross, burau,
                         scale, value, obj["words"], starts, ends, empty, short)
    except (KeyError, TypeError, ValueError) as e:
        raise WireError(f"bad text summary: {e}") from e
    if len(burau) != n or any(len(row) != n for row in burau):
        raise WireError("Burau fingerprint has the wrong size")
    if any(not (0 <= x < PRIME) for row in burau for x in row):
        raise WireError("Burau fingerprint entry out of range")
    if any(not (1 <= a < b <= n) for (a, b), _ in cross) or list(cross) != sorted(cross):
        raise WireError("bad crossing table")
    return s


# ----------------------------------------------------------------------------- bytes

def _check_header(obj: Any, kind: str) -> None:
    if not isinstance(obj, dict):
        raise WireError("message is not a map")
    if obj.get("v") != WIRE_VERSION:
        raise WireError(f"unsupported wire version {obj.get('v')!r}")
    if obj.get("kind") != kind:
        raise WireError(f"expected kind {kind!r}, got {obj.get('kind')!r}")


def encode(summary) -> Dict[str, Any]:
    """Encode either summary kind to a plain (JSON/CBOR-ready) object."""
    if isinstance(summary, ChunkReading):
        return encode_reading(summary)
    return encode_text_summary(summary)


def decode(obj: Dict[str, Any]):
    """Decode a plain object produced by :func:`encode`."""
    if isinstance(obj, dict) and obj.get("kind") == KIND_TEXT:
        return decode_text_summary(obj)
    return decode_reading(obj)


def to_cbor(summary) -> bytes:
    return canonical_cbor(encode(summary))


def from_cbor(data: bytes):
    try:
        obj = decode_cbor(data)
    except Exception as e:  # noqa: BLE001 — any decoder failure is a wire error
        raise WireError(f"undecodable CBOR: {e}") from e
    return decode(obj)


def to_json(summary) -> bytes:
    return canonical_json(encode(summary))


def from_json(data: bytes):
    import json

    try:
        obj = json.loads(data)
    except ValueError as e:
        raise WireError(f"undecodable JSON: {e}") from e
    return decode(obj)


def digest(summary) -> str:
    """Content address: SHA-256 (hex) of the canonical CBOR bytes."""
    return hashlib.sha256(to_cbor(summary)).hexdigest()
