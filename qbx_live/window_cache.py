"""
Window cache — content-addressed chunk summaries (local; no network yet).

A text is cut into consecutive *windows* of ``k`` characters.  Each window's
:class:`qbx_bible.manifold.ChunkSummary` is looked up in the cache, computed
on a miss, and the summaries are combined with the balanced reduction tree.
Because summarising is a monoid homomorphism out of the free monoid on
characters, *any* cut gives the summary of the whole text
(Lean: ``QBX.Formal.TextManifold.mapReduce`` and
``Sovereign.Combinatorics.HomomorphismDecomposition.hom_flatten``); the cache
only changes where each piece comes from, never the result.
``tests/qbx_live/test_window_cache.py`` checks this field by field against a
single sequential pass.

Keys
----
``window_key`` is SHA-256 over the *length-prefixed* fields
``(alphabet_id, scheme, strand_count, sofit_rule, keep_word, wire version, window)``.
Length prefixes make the encoding injective: plain concatenation
``alphabet_id || window || …`` is ambiguous (``"ab" + "c"`` = ``"a" + "bc"``).

Normalisation and the size bound
--------------------------------
Combining marks are stripped (exactly as :func:`qbx_bible.manifold.summarize`
does), and every character that is not a letter is replaced by one space.
This is exact: every non-letter has the same summary (the separator), so the
summary of a window depends only on its normalised form.  The number of
distinct normalised windows of length ``k`` over an alphabet of ``a`` letters
is at most ``(a + 1)^k`` — for Hebrew (22 letters + 5 final forms) and
``k = 4`` that is ``28⁴ = 614 656`` (the separator is the ``+ 1``; the figure
``27⁴`` in the design notes leaves it out).

Collisions (design question 3.2)
--------------------------------
The window itself is stored next to its summary.  Writes are verified: a
second write under the same key with a *different* window raises
:class:`CacheCollision` and is counted; the stored entry is never replaced.
Reads are verified too, because a window is at most ``k`` characters and the
comparison costs nothing; ``verify_reads=False`` switches to trusting the hash.

Storage is SQLite (``":memory:"`` by default, or a file path for a persistent
cache); entries are stored in the wire format of :mod:`qbx_live.wire`.
"""

from __future__ import annotations

import hashlib
import sqlite3
from dataclasses import dataclass
from typing import List, Optional, Sequence, Tuple

from qbx_bible.encode import SCHEME, Encoding, classify, strip_marks
from qbx_bible import manifold as mf
from qbx_live import wire

DEFAULT_K = 4


class CacheCollision(RuntimeError):
    """Two different windows produced the same key."""


def normalize(text: str) -> str:
    """Strip marks and map every non-letter to a single space (summary-preserving)."""
    return "".join(c if classify(c) is not None else " " for c in strip_marks(text))


def window_key(window: str, alphabet_id: str, encoding: Encoding = Encoding(),
               keep_word: bool = True, version: int = wire.WIRE_VERSION) -> str:
    """SHA-256 (hex) over the length-prefixed key fields."""
    h = hashlib.sha256()
    for field in (alphabet_id, SCHEME, str(encoding.strand_count), str(int(encoding.sofit_rule)),
                  str(int(keep_word)), str(version), window):
        b = field.encode("utf-8")
        h.update(len(b).to_bytes(8, "big"))
        h.update(b)
    return h.hexdigest()


def windows_of(text: str, k: int = DEFAULT_K) -> List[str]:
    """The consecutive length-``k`` windows of the normalised text (the last may be shorter)."""
    if k < 1:
        raise ValueError("k must be ≥ 1")
    t = normalize(text)
    return [t[i:i + k] for i in range(0, len(t), k)]


@dataclass
class CacheStats:
    hits: int = 0
    misses: int = 0
    writes: int = 0
    collisions: int = 0


class WindowCache:
    """SQLite-backed map ``key → (window, summary)``."""

    def __init__(self, path: str = ":memory:", verify_reads: bool = True):
        self.path = path
        self.verify_reads = verify_reads
        self.stats = CacheStats()
        self._db = sqlite3.connect(path)
        self._db.execute(
            "CREATE TABLE IF NOT EXISTS windows ("
            " key TEXT PRIMARY KEY, window TEXT NOT NULL, summary BLOB NOT NULL)")
        self._db.commit()

    def close(self) -> None:
        self._db.close()

    def __len__(self) -> int:
        return self._db.execute("SELECT COUNT(*) FROM windows").fetchone()[0]

    def _row(self, key: str) -> Optional[Tuple[str, bytes]]:
        return self._db.execute("SELECT window, summary FROM windows WHERE key = ?",
                                (key,)).fetchone()

    def get(self, key: str, window: str):
        """The stored summary, or ``None``.  Raises :class:`CacheCollision` if
        ``verify_reads`` and the stored window differs."""
        row = self._row(key)
        if row is None:
            return None
        stored_window, blob = row
        if self.verify_reads and stored_window != window:
            self.stats.collisions += 1
            raise CacheCollision(f"key {key[:16]}… holds {stored_window!r}, asked for {window!r}")
        return wire.from_cbor(blob)

    def put(self, key: str, window: str, summary) -> None:
        """Store a summary; verify-on-write (never overwrites a different window)."""
        row = self._row(key)
        if row is not None:
            if row[0] != window:
                self.stats.collisions += 1
                raise CacheCollision(f"key {key[:16]}… already holds {row[0]!r}, not {window!r}")
            return
        self._db.execute("INSERT INTO windows (key, window, summary) VALUES (?, ?, ?)",
                         (key, window, wire.to_cbor(summary)))
        self._db.commit()
        self.stats.writes += 1

    def summary(self, window: str, alphabet_id: str, encoding: Encoding = Encoding(),
                keep_word: bool = True):
        """The summary of one normalised window: cached, or computed and stored."""
        key = window_key(window, alphabet_id, encoding, keep_word)
        s = self.get(key, window)
        if s is not None:
            self.stats.hits += 1
            return s
        self.stats.misses += 1
        s = mf.summarize(window, encoding, keep_word)
        self.put(key, window, s)
        return s


def summarize_cached(text: str, cache: WindowCache, alphabet_id: str = "hebrew-wlc",
                     encoding: Encoding = Encoding(), k: int = DEFAULT_K,
                     keep_word: bool = True) -> mf.ChunkSummary:
    """The summary of ``text`` assembled from cached window summaries (equal to
    ``manifold.summarize(text, encoding, keep_word)``)."""
    parts: Sequence[mf.ChunkSummary] = [
        cache.summary(w, alphabet_id, encoding, keep_word) for w in windows_of(text, k)]
    if not parts:
        return mf.identity(encoding, keep_word)
    return mf.reduce_tree(list(parts), encoding)
