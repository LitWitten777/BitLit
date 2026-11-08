"""
Gematria mapping.

Hebrew letter values.  The 22 standard letters use the standard values
(mispar hechrachi); the five final forms use the extended values 500–900
(as in mispar gadol), matching the `hebrew_letter` seed in migration 014:
א=1, ב=2, ג=3, ד=4, ה=5, ו=6, ז=7, ח=8, ט=9,
י=10, כ=20, ל=30, מ=40, נ=50, ס=60, ע=70, פ=80, צ=90,
ק=100, ר=200, ש=300, ת=400
Finals: ך=500, ם=600, ן=700, ף=800, ץ=900

This module also provides a deterministic 256-dim "gematria embedding"
that is used for invariant hash mixing.
"""

from __future__ import annotations

import hashlib
from typing import Dict, List

GEMATRIA: Dict[str, int] = {
    "א": 1, "ב": 2, "ג": 3, "ד": 4, "ה": 5, "ו": 6, "ז": 7, "ח": 8, "ט": 9,
    "י": 10, "כ": 20, "ל": 30, "מ": 40, "נ": 50, "ס": 60, "ע": 70, "פ": 80,
    "צ": 90, "ק": 100, "ר": 200, "ש": 300, "ת": 400,
    # Finals
    "ך": 500, "ם": 600, "ן": 700, "ף": 800, "ץ": 900,
}


def gematria_value(word: str) -> int:
    """Sum of gematria values of the letters in `word`."""
    return sum(GEMATRIA.get(ch, 0) for ch in word)


def gematria_vector(word: str, dim: int = 256) -> List[float]:
    """
    Deterministic 256-dim float vector derived from the gematria value.

    Uses SHA-256 of the canonical decimal string, expanded to `dim` floats
    in [-1, 1). This is NOT a semantic embedding — it is a deterministic
    mixing primitive. For semantic embeddings, use a proper Hebrew-aware model.
    """
    total = gematria_value(word)
    h = hashlib.sha256(str(total).encode("utf-8")).digest()
    # Repeat digest to fill `dim` bytes
    reps = (dim // len(h)) + 1
    full = h * reps
    vec = [((b - 128) / 128.0) for b in full[:dim]]
    return vec


def gematria_bytes(word: str) -> bytes:
    """Canonical bytes of gematria value (big-endian 8-byte integer)."""
    return gematria_value(word).to_bytes(8, "big", signed=False)


# ---------------------------------------------------------------------------
# Gematria schemes (decision GEM-001, 2026-10-13).  The valuation is a *parameter*, as in Lean
# (`QBX.Formal.Gematria.wordValue v`, any `v`).  Two conventions are live in the project:
#
#   "standard" -- finals 500-900 (mispar gadol for finals); this module's GEMATRIA, migration 014,
#                 Lean `Gematria.standard`;
#   "base"     -- a final form has the value of its base letter (mispar hechrachi proper);
#                 used by tests/test_bible_braid.py.
#
# Neither is "the" right one: they record different historical layers of the practice (the 500-900
# final values are a later extension).  Every result must say which scheme it used.
# ---------------------------------------------------------------------------

FINAL_BASE: Dict[str, str] = {"ך": "כ", "ם": "מ", "ן": "נ", "ף": "פ", "ץ": "צ"}

SCHEMES: Dict[str, Dict[str, int]] = {
    "standard": dict(GEMATRIA),
    "base": {**{c: v for c, v in GEMATRIA.items() if c not in FINAL_BASE},
             **{f: GEMATRIA[b] for f, b in FINAL_BASE.items()}},
}


def gematria_value_scheme(word: str, scheme: str = "standard") -> int:
    """Sum of letter values of ``word`` under a named scheme (``SCHEMES``)."""
    try:
        table = SCHEMES[scheme]
    except KeyError:
        raise ValueError(f"unknown gematria scheme {scheme!r}; known: {sorted(SCHEMES)}") from None
    return sum(table.get(ch, 0) for ch in word)
