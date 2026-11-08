"""
Processing Bible texts at scale: scale out, skip, and run as a manifold.

Everything :mod:`qbx_bible.encode` and the invariants of
:mod:`qbx_ir.algebra.invariants` compute from a text is one of two kinds of
quantity, and both can be split up and recombined *exactly*:

* **Homomorphic quantities** — the braid word, its permutation, writhe and
  letter counts, the strand-pair crossing matrix (which gives every linking
  number of the closure), a Burau fingerprint and a polynomial (Rabin–Karp)
  hash.  A :class:`ChunkSummary` holds all of them for one piece of text, and
  :func:`merge` combines the summaries of two adjacent pieces into the summary
  of their concatenation.  ``merge`` is associative with identity
  :func:`identity`, so the pieces can be summarised by any number of workers
  and combined in any bracketing (:func:`summarize_parallel`, a balanced tree
  of depth ⌈log₂ chunks⌉).  Lean: ``QBX.Formal.TextManifold.mapReduce``,
  ``ReduceTree.eval_eq_prod``, ``balanced_depth_le``, ``perm_writhe_chunks``.

* **k-local quantities** — sums over all windows of ``k`` consecutive letters
  (k-gram counts, sliding cocycle phases).  :func:`atlas` cuts the letters into
  *charts*, each extended by a *collar* of the next ``k − 1`` letters; the
  windows of the whole text are exactly the windows of the charts, each counted
  once (:func:`kgram_counts_atlas`).  Lean: ``windows_flatten_atlas``,
  ``windowSum_atlas``.

**Skip.**  The Burau fingerprint lives in a group (invertible matrices over
GF(p)), so after one pass :class:`PrefixIndex` answers "what is the
fingerprint / writhe / permutation / hash of verses i … j−1" in time
independent of the length of the passage: ``P(i)⁻¹ · P(j)``.  Lean:
``segment_eq_prefix``, ``convert_segment``, ``horner_segment``.  A block
repeated ``k`` times is summarised with O(log k) merges (:func:`power`; Lean:
``powBin_eq_pow``), and repeated words are summarised once
(:func:`summarize_words_memo`; Lean: ``memo_correct``).

Word counting is the one statistic that is *not* a plain homomorphism (a word
can straddle a cut); the summary carries whether the piece starts and ends
inside a word, which is enough to merge counts exactly.
"""

from __future__ import annotations

from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from functools import lru_cache
from typing import Dict, List, Optional, Sequence, Tuple

from qbx_bible.encode import Encoding, classify, strip_marks

#: Prime modulus of the Burau fingerprint and the rolling hash.
PRIME = 2_147_483_647          # 2³¹ − 1
#: Burau parameter t (any unit mod PRIME other than 1 gives a faithful-enough fingerprint).
BURAU_T = 5
#: Base of the rolling hash.
HASH_BASE = 1_000_003

Matrix = Tuple[Tuple[int, ...], ...]


# ----------------------------------------------------------------------------- matrices mod p

def _mat_identity(n: int) -> Matrix:
    return tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n))


def _mat_mul(a: Matrix, b: Matrix) -> Matrix:
    n = len(a)
    bt = list(zip(*b))
    return tuple(tuple(sum(x * y for x, y in zip(row, col)) % PRIME for col in bt) for row in a)


def _mat_inv(a: Matrix) -> Matrix:
    """Inverse mod PRIME by Gauss–Jordan elimination."""
    n = len(a)
    m = [list(row) + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(a)]
    for c in range(n):
        piv = next(r for r in range(c, n) if m[r][c] % PRIME)
        m[c], m[piv] = m[piv], m[c]
        inv = pow(m[c][c], PRIME - 2, PRIME)
        m[c] = [x * inv % PRIME for x in m[c]]
        for r in range(n):
            if r != c and m[r][c]:
                f = m[r][c]
                m[r] = [(x - f * y) % PRIME for x, y in zip(m[r], m[c])]
    return tuple(tuple(row[n:]) for row in m)


@lru_cache(maxsize=None)
def _burau_generator(n: int, gen: int) -> Matrix:
    """Unreduced Burau matrix of σ_|gen|^±1 on n strands at t = BURAU_T, mod PRIME."""
    i = abs(gen) - 1
    t = BURAU_T
    m = [list(row) for row in _mat_identity(n)]
    if gen > 0:
        block = [[(1 - t) % PRIME, t], [1, 0]]
    else:
        ti = pow(t, PRIME - 2, PRIME)
        block = [[0, 1], [ti, (1 - ti) % PRIME]]
    for r in range(2):
        for c in range(2):
            m[i + r][i + c] = block[r][c]
    return tuple(tuple(row) for row in m)


# ----------------------------------------------------------------------------- summaries

@dataclass(frozen=True)
class ChunkSummary:
    """Everything mergeable about one piece of text, for a fixed encoding.

    ``positions[p]`` is the (1-based) strand label at position ``p + 1`` after the
    piece, as in :func:`qbx_ir.algebra.invariants.permutation`; ``crossings`` maps a
    pair of strand labels ``(a, b)``, ``a < b``, to the signed number of crossings
    between them.  Labels are positions at the *start* of the piece.
    """

    strand_count: int
    letters: int
    finals: int
    writhe: int
    positions: Tuple[int, ...]
    crossings: Tuple[Tuple[Tuple[int, int], int], ...]
    burau: Matrix
    hash_scale: int
    hash_value: int
    words: int
    starts_in_word: bool
    ends_in_word: bool
    empty: bool                       # no characters at all (identity)
    short: Optional[Tuple[int, ...]] = None   # the braid word itself, if kept

    @property
    def crossing_dict(self) -> Dict[Tuple[int, int], int]:
        return dict(self.crossings)


def identity(encoding: Encoding = Encoding(), keep_word: bool = True) -> ChunkSummary:
    n = encoding.strand_count
    return ChunkSummary(n, 0, 0, 0, tuple(range(1, n + 1)), (), _mat_identity(n), 1, 0, 0,
                        False, False, True, () if keep_word else None)


def _letter_summary(gen: int, final: bool, encoding: Encoding, keep_word: bool) -> ChunkSummary:
    n = encoding.strand_count
    i = abs(gen)
    positions = list(range(1, n + 1))
    positions[i - 1], positions[i] = positions[i], positions[i - 1]
    sign = 1 if gen > 0 else -1
    return ChunkSummary(n, 1, int(final), sign, tuple(positions), (((i, i + 1), sign),),
                        _burau_generator(n, gen), HASH_BASE % PRIME, gen % PRIME, 1,
                        True, True, False, (gen,) if keep_word else None)


def _separator_summary(encoding: Encoding, keep_word: bool) -> ChunkSummary:
    s = identity(encoding, keep_word)
    return ChunkSummary(s.strand_count, 0, 0, 0, s.positions, (), s.burau, 1, 0, 0,
                        False, False, False, s.short)


def merge(a: ChunkSummary, b: ChunkSummary) -> ChunkSummary:
    """The summary of the concatenation of two adjacent pieces (associative, unit
    :func:`identity`)."""
    if a.strand_count != b.strand_count:
        raise ValueError("summaries for different strand counts")
    if a.empty:
        return b
    if b.empty:
        return a
    # b's labels are positions at the start of b, i.e. the strands a.positions[label-1].
    relabel = a.positions
    cross = dict(a.crossings)
    for (x, y), v in b.crossings:
        u, w = relabel[x - 1], relabel[y - 1]
        key = (min(u, w), max(u, w))
        cross[key] = cross.get(key, 0) + v
    cross = {k: v for k, v in cross.items() if v}
    joined = a.ends_in_word and b.starts_in_word
    words = a.words + b.words - (1 if joined else 0)
    short = a.short + b.short if a.short is not None and b.short is not None else None
    return ChunkSummary(
        a.strand_count, a.letters + b.letters, a.finals + b.finals, a.writhe + b.writhe,
        tuple(a.positions[p - 1] for p in b.positions), tuple(sorted(cross.items())),
        _mat_mul(a.burau, b.burau), a.hash_scale * b.hash_scale % PRIME,
        (a.hash_value * b.hash_scale + b.hash_value) % PRIME, words, a.starts_in_word,
        b.ends_in_word, False, short)


def summarize(text: str, encoding: Encoding = Encoding(), keep_word: bool = True) -> ChunkSummary:
    """The summary of one piece of text (sequential, one pass)."""
    acc = identity(encoding, keep_word)
    for ch in strip_marks(text):
        letter = classify(ch)
        if letter is None:
            acc = merge(acc, _separator_summary(encoding, keep_word))
        else:
            acc = merge(acc, _letter_summary(encoding.generator(letter), letter.final,
                                             encoding, keep_word))
    return acc


def reduce_tree(parts: Sequence[ChunkSummary], encoding: Encoding = Encoding()) -> ChunkSummary:
    """Combine summaries with a balanced tree (depth ⌈log₂ len⌉); the result does not depend
    on the bracketing."""
    if not parts:
        return identity(encoding)
    level = list(parts)
    while len(level) > 1:
        level = [merge(level[i], level[i + 1]) if i + 1 < len(level) else level[i]
                 for i in range(0, len(level), 2)]
    return level[0]


def _summarize_job(args) -> ChunkSummary:
    text, n, sofit, keep = args
    return summarize(text, Encoding(n, sofit), keep)


def summarize_parallel(chunks: Sequence[str], encoding: Encoding = Encoding(),
                       workers: int = 0, keep_word: bool = False) -> ChunkSummary:
    """Scale out: summarise the chunks independently (in ``workers`` processes when
    ``workers > 1``), then reduce with a balanced tree."""
    jobs = [(c, encoding.strand_count, encoding.sofit_rule, keep_word) for c in chunks]
    if workers and workers > 1 and len(chunks) > 1:
        with ProcessPoolExecutor(max_workers=workers) as pool:
            parts = list(pool.map(_summarize_job, jobs))
    else:
        parts = [_summarize_job(j) for j in jobs]
    return reduce_tree(parts, encoding)


def power(s: ChunkSummary, k: int) -> ChunkSummary:
    """The summary of a piece repeated ``k`` times, with O(log k) merges."""
    result = identity(Encoding(s.strand_count), s.short is not None)
    base = s
    while k:
        if k & 1:
            result = merge(result, base)
        base = merge(base, base)
        k >>= 1
    return result


def summarize_words_memo(text: str, encoding: Encoding = Encoding(),
                         keep_word: bool = False) -> Tuple[ChunkSummary, int]:
    """Summarise a text word by word, computing each distinct word once.  Returns the
    summary and the number of distinct words actually summarised."""
    cache: Dict[str, ChunkSummary] = {}
    sep = _separator_summary(encoding, keep_word)
    acc = identity(encoding, keep_word)
    current: List[str] = []

    def flush():
        nonlocal acc
        if current:
            w = "".join(current)
            if w not in cache:
                cache[w] = summarize(w, encoding, keep_word)
            acc = merge(acc, cache[w])
            current.clear()

    for ch in strip_marks(text):
        if classify(ch) is None:
            flush()
            acc = merge(acc, sep)
        else:
            current.append(ch)
    flush()
    return acc, len(cache)


# ----------------------------------------------------------------------------- invariants

def closure_components(s: ChunkSummary) -> List[List[int]]:
    """Closure components (cycles of the permutation), in the order of
    :func:`qbx_ir.algebra.invariants.closure_components`."""
    n = s.strand_count
    dest = [0] * n
    for j, label in enumerate(s.positions):
        dest[label - 1] = j + 1
    seen = [False] * n
    comps: List[List[int]] = []
    for start in range(1, n + 1):
        if seen[start - 1]:
            continue
        comp, cur = [], start
        while not seen[cur - 1]:
            seen[cur - 1] = True
            comp.append(cur)
            cur = dest[cur - 1]
        comps.append(comp)
    return comps


def linking_matrix(s: ChunkSummary) -> Dict[Tuple[int, int], int]:
    """Pairwise linking numbers of the closure, from the crossing matrix alone
    (same convention as :func:`qbx_ir.algebra.invariants.linking_matrix`)."""
    comps = closure_components(s)
    comp_of = {x: i for i, c in enumerate(comps) for x in c}
    totals = {(a, b): 0 for a in range(len(comps)) for b in range(a + 1, len(comps))}
    for (x, y), v in s.crossings:
        a, b = comp_of[x], comp_of[y]
        if a != b:
            totals[(min(a, b), max(a, b))] += v
    return {k: v // 2 for k, v in totals.items()}


# ----------------------------------------------------------------------------- skip

class PrefixIndex:
    """Prefix summaries of a sequence of pieces (verses).  ``segment(i, j)`` gives the
    fingerprint, writhe, letter count, permutation and hash of pieces ``i … j−1`` in time
    independent of ``j − i``."""

    def __init__(self, pieces: Sequence[str], encoding: Encoding = Encoding()):
        self.encoding = encoding
        self.prefix: List[ChunkSummary] = [identity(encoding, False)]
        for p in pieces:
            self.prefix.append(merge(self.prefix[-1], summarize(p, encoding, False)))
        self._inv: Dict[int, Matrix] = {}

    def _burau_inv(self, i: int) -> Matrix:
        if i not in self._inv:
            self._inv[i] = _mat_inv(self.prefix[i].burau)
        return self._inv[i]

    def segment(self, i: int, j: int) -> Dict[str, object]:
        if not 0 <= i <= j < len(self.prefix):
            raise IndexError("segment out of range")
        a, b = self.prefix[i], self.prefix[j]
        # permutation of the segment, in its own labels: positions_seg[p] = a⁻¹(b[p])
        where = {label: k + 1 for k, label in enumerate(a.positions)}
        positions = tuple(where[label] for label in b.positions)
        scale = pow(HASH_BASE, b.letters - a.letters, PRIME)
        return {
            "letters": b.letters - a.letters,
            "finals": b.finals - a.finals,
            "writhe": b.writhe - a.writhe,
            "positions": positions,
            "burau": _mat_mul(self._burau_inv(i), b.burau),
            "hash": (b.hash_value - a.hash_value * scale) % PRIME,
        }


# ----------------------------------------------------------------------------- manifold

def letter_ordinals(text: str) -> List[int]:
    """The letters of a text as ordinals (separators and marks dropped)."""
    return [l.ordinal for ch in strip_marks(text) if (l := classify(ch)) is not None]


def windows(seq: Sequence, k: int) -> List[tuple]:
    return [tuple(seq[i:i + k]) for i in range(len(seq) + 1 - k)] if len(seq) >= k else []


def atlas(chunks: Sequence[Sequence], k: int) -> List[list]:
    """Charts: each chunk followed by a collar of the next ``k − 1`` items of the text."""
    charts = []
    for idx, c in enumerate(chunks):
        collar: List = []
        for later in chunks[idx + 1:]:
            if len(collar) >= k - 1:
                break
            collar.extend(later[:k - 1 - len(collar)])
        charts.append(list(c) + collar)
    return charts


def kgram_counts(seq: Sequence, k: int) -> Counter:
    return Counter(windows(seq, k))


def _kgram_job(args) -> Counter:
    chart, k = args
    return kgram_counts(chart, k)


def kgram_counts_atlas(seq: Sequence, k: int, chunk_size: int, workers: int = 0) -> Counter:
    """k-gram counts computed chart by chart (each chart independently, optionally in
    parallel) and added up.  Equal to :func:`kgram_counts` for every ``chunk_size ≥ 1``."""
    if k < 1:
        raise ValueError("k must be at least 1")
    chunks = [seq[i:i + chunk_size] for i in range(0, len(seq), chunk_size)]
    jobs = [(chart, k) for chart in atlas(chunks, k)]
    if workers and workers > 1 and len(jobs) > 1:
        with ProcessPoolExecutor(max_workers=workers) as pool:
            parts = list(pool.map(_kgram_job, jobs))
    else:
        parts = [_kgram_job(j) for j in jobs]
    total: Counter = Counter()
    for p in parts:
        total.update(p)
    return total
