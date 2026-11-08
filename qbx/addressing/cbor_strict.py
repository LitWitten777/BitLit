"""
Strict deterministic-CBOR decoder: the reference for ``addr_cbor_decode`` in
migration ``013_addressing_protocol.sql``.

It accepts exactly the subset that :func:`qbx.core.canonical.canonical_cbor`
produces (integers, byte and text strings, arrays, maps with text keys,
``false`` / ``true`` / ``null`` and floats), and reports

* the first **malformation** — decoding stops there (one finding), and
* every departure from the **deterministic encoding** (RFC 8949 §4.2 with
  the length-first key order used by ``cbor2``'s ``canonical=True``):
  non-minimal heads, keys out of order, floats that a narrower width holds
  exactly, text not in Unicode NFC.

Decoded values are tagged exactly as in the database, so the two can be
compared directly:

==============================  ==================================================
CBOR                            decoded value
==============================  ==================================================
unsigned / negative integer     ``int``
text string                     ``str``
byte string                     ``{"$bytes": "<hex>"}``
float                           ``{"$float": float}`` (the database holds the
                                ``float8`` text, e.g. ``"-0"``, ``"NaN"``)
array                           ``list``
map (text keys)                 ``{"$map": {key: value}}``
false / true / null             ``False`` / ``True`` / ``None``
==============================  ==================================================

Malformation codes: ``truncated``, ``reserved_info``, ``indefinite_length``,
``invalid_utf8`` (also a NUL character, which PostgreSQL text cannot hold),
``unsupported_tag``, ``unsupported_simple``, ``trailing_bytes``,
``non_text_key``, ``duplicate_key``, ``too_deep`` (nesting beyond
:data:`MAX_DEPTH`).

Non-canonical codes: ``non_minimal_head``, ``unsorted_keys``,
``non_shortest_float``, ``non_nfc_text``.
"""

from __future__ import annotations

import math
import struct
import unicodedata
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

MAX_DEPTH = 16

#: (significant bits, minimum normal exponent, maximum exponent)
HALF = (11, -14, 15)
SINGLE = (24, -126, 127)


class CborMalformed(Exception):
    def __init__(self, offset: int, error: str) -> None:
        super().__init__(f"{error} at {offset}")
        self.offset = offset
        self.error = error


@dataclass
class Decoded:
    value: Any = None
    malformed: Optional[Dict[str, Any]] = None
    non_canonical: List[Dict[str, Any]] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return self.malformed is None


def float_fits(m: int, e: int, fmt: Tuple[int, int, int]) -> bool:
    """Can the finite float ``m·2^e`` (``m > 0``) be written exactly in ``fmt``?"""
    p, emin, emax = fmt
    while m % 2 == 0:
        m //= 2
        e += 1
    bl = m.bit_length()
    return bl <= p and e >= emin - p + 1 and e + bl - 1 <= emax


def decode_float(bits: int, width: int) -> Tuple[Any, bool]:
    """(tagged value, canonical?) of a float of ``width`` bits."""
    eb, fb = {16: (5, 10), 32: (8, 23), 64: (11, 52)}[width]
    bias = 2 ** (eb - 1) - 1
    sgn = bits >> (width - 1)
    ex = (bits >> fb) & (2 ** eb - 1)
    fr = bits & (2 ** fb - 1)
    if ex == 2 ** eb - 1:
        v = math.nan if fr else (-math.inf if sgn else math.inf)
        return {"$float": v}, width == 16
    if ex == 0:
        m, e = fr, 1 - bias - fb
    else:
        m, e = fr + 2 ** fb, ex - bias - fb
    if m == 0:
        v, canon = 0.0, width == 16
    else:
        v = math.ldexp(float(m), e)
        canon = (width == 16
                 or (width == 32 and not float_fits(m, e, HALF))
                 or (width == 64 and not float_fits(m, e, HALF) and not float_fits(m, e, SINGLE)))
    if sgn:
        v = -v
    return {"$float": v}, canon


def _item(data: bytes, pos: int, depth: int, nc: List[Dict[str, Any]]) -> Tuple[Any, int]:
    n = len(data)
    o = pos
    if depth > MAX_DEPTH:
        raise CborMalformed(o, "too_deep")
    if pos >= n:
        raise CborMalformed(o, "truncated")
    ib = data[pos]
    mt, ai = ib >> 5, ib & 31
    pos += 1
    if 28 <= ai <= 30:
        raise CborMalformed(o, "reserved_info")
    if ai == 31:
        raise CborMalformed(o, "indefinite_length")
    if ai < 24:
        arg = ai
    else:
        k = {24: 1, 25: 2, 26: 4, 27: 8}[ai]
        if pos + k > n:
            raise CborMalformed(o, "truncated")
        arg = int.from_bytes(data[pos:pos + k], "big")
        pos += k

    if mt == 7:
        if ai == 20:
            return False, pos
        if ai == 21:
            return True, pos
        if ai == 22:
            return None, pos
        if ai in (25, 26, 27):
            v, canon = decode_float(arg, {25: 16, 26: 32, 27: 64}[ai])
            if not canon:
                nc.append({"offset": o, "error": "non_shortest_float"})
            return v, pos
        raise CborMalformed(o, "unsupported_simple")

    if ((ai == 24 and arg < 24) or (ai == 25 and arg < 256) or (ai == 26 and arg < 65536)
            or (ai == 27 and arg < 2 ** 32)):
        nc.append({"offset": o, "error": "non_minimal_head"})

    if mt == 6:
        raise CborMalformed(o, "unsupported_tag")
    if mt == 0:
        return arg, pos
    if mt == 1:
        return -1 - arg, pos

    if mt in (2, 3):
        if arg > n - pos:
            raise CborMalformed(o, "truncated")
        raw = data[pos:pos + arg]
        pos += arg
        if mt == 2:
            return {"$bytes": raw.hex()}, pos
        try:
            txt = raw.decode("utf-8")
        except UnicodeDecodeError:
            raise CborMalformed(o, "invalid_utf8") from None
        if "\x00" in txt:
            raise CborMalformed(o, "invalid_utf8")
        if not unicodedata.is_normalized("NFC", txt):
            nc.append({"offset": o, "error": "non_nfc_text"})
        return txt, pos

    if mt == 4:
        if arg > n - pos:
            raise CborMalformed(o, "truncated")
        items = []
        for _ in range(arg):
            v, pos = _item(data, pos, depth + 1, nc)
            items.append(v)
        return items, pos

    # mt == 5: a map
    if 2 * arg > n - pos:
        raise CborMalformed(o, "truncated")
    obj: Dict[str, Any] = {}
    prev: Optional[bytes] = None
    for _ in range(arg):
        ko = pos
        key, pos = _item(data, pos, depth + 1, nc)
        if not isinstance(key, str):
            raise CborMalformed(ko, "non_text_key")
        if key in obj:
            raise CborMalformed(ko, "duplicate_key")
        kraw = data[ko:pos]
        if prev is not None and (len(kraw), kraw) < (len(prev), prev):
            nc.append({"offset": ko, "error": "unsorted_keys"})
        prev = kraw
        v, pos = _item(data, pos, depth + 1, nc)
        obj[key] = v
    return {"$map": obj}, pos


def decode_strict(data: bytes) -> Decoded:
    """Decode ``data`` as one deterministic-CBOR item."""
    nc: List[Dict[str, Any]] = []
    try:
        v, pos = _item(bytes(data), 0, 0, nc)
        if pos < len(data):
            raise CborMalformed(pos, "trailing_bytes")
    except CborMalformed as e:
        return Decoded(None, {"offset": e.offset, "error": e.error}, [])
    return Decoded(v, None, nc)


def untag(value: Any) -> Any:
    """The plain Python value (bytes for ``$bytes``, float for ``$float``, dict for ``$map``)."""
    if isinstance(value, list):
        return [untag(v) for v in value]
    if isinstance(value, dict):
        if "$map" in value:
            return {k: untag(v) for k, v in value["$map"].items()}
        if "$bytes" in value:
            return bytes.fromhex(value["$bytes"])
        if "$float" in value:
            return float(value["$float"])
    return value


def pack_float(v: float, width: int) -> bytes:
    """The CBOR item for ``v`` at a fixed width (helper for tests and examples)."""
    head = {16: b"\xf9", 32: b"\xfa", 64: b"\xfb"}[width]
    return head + struct.pack({16: ">e", 32: ">f", 64: ">d"}[width], v)
