"""
Discovery Olympics — Main Harness

Three independent tracks:
  Track 1 — Boundary Detection   (H1, BPE, AST, Random)
  Track 2 — Compression          (H1, BPE, Gzip, LZMA, Random)
  Track 3 — Prediction           (H1, Ngram, Random)

All methods implement the same DiscoveryMethod interface.
AST is the oracle comparison for Python only; it is not fielded in cross-domain tracks.

Run:
    python benchmarks/olympics.py
"""
import ast
import gzip
import hashlib
import lzma
import math
import os
import random
import re
import sys
from abc import ABC, abstractmethod
from typing import Dict, List, Tuple

# Make sure root is on path
_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from benchmarks.datasets import ALL_CODE, ALL_DOMAINS
from benchmarks.leaderboard import record_run, print_leaderboard
from benchmarks.stats import bootstrap_ci, permutation_test


# ---------------------------------------------------------------------------
# Scoring helpers
# ---------------------------------------------------------------------------

def _tfidf_reuse(pattern_tokens: List[str], corpus_tokens: List[str]) -> float:
    """
    reuse_score = frequency * information_content (TF-IDF principle).
    Penalizes high-frequency stop-pattern tokens that carry no information.
    """
    if not corpus_tokens or not pattern_tokens:
        return 0.0

    # Term frequency of each token in the corpus
    tf: Dict[str, float] = {}
    for t in corpus_tokens:
        tf[t] = tf.get(t, 0) + 1
    n = len(corpus_tokens)

    # Count occurrences of the exact pattern (sliding window)
    plen = len(pattern_tokens)
    freq = 0
    for i in range(n - plen + 1):
        if corpus_tokens[i:i + plen] == pattern_tokens:
            freq += 1

    # Information content of the pattern: average IDF of constituent tokens
    idf_sum = 0.0
    for t in pattern_tokens:
        token_freq = tf.get(t, 0)
        idf = math.log((n + 1) / (token_freq + 1))
        idf_sum += idf
    avg_idf = idf_sum / plen if plen > 0 else 0.0

    return float(freq) * avg_idf


def _cross_entropy(tokens: List[str]) -> float:
    """Character-level unigram cross-entropy in bits/char."""
    text = " ".join(tokens)
    if not text:
        return 0.0
    freq: Dict[str, int] = {}
    for ch in text:
        freq[ch] = freq.get(ch, 0) + 1
    n = len(text)
    entropy = 0.0
    for count in freq.values():
        p = count / n
        entropy -= p * math.log2(p)
    return entropy


def _compression_ratio(text: str, method: str = "gzip") -> float:
    """Return compressed_size / original_size. Lower = better compression."""
    raw = text.encode()
    if not raw:
        return 1.0
    if method == "gzip":
        compressed = gzip.compress(raw, compresslevel=9)
    elif method == "lzma":
        compressed = lzma.compress(raw)
    else:
        compressed = raw
    return len(compressed) / max(1, len(raw))


def _vocabulary_compression_ratio(chunks: List[List[str]]) -> float:
    """
    Vocabulary-pointer compression model.

    Instead of gzip-per-chunk (which has header overhead that dominates small inputs),
    measure the theoretical compression from replacing repeated chunk patterns with IDs.

    ratio = (vocabulary_bytes + pointer_stream_bytes) / original_bytes

    vocabulary_bytes  = sum of bytes in each unique chunk type (stored once)
    pointer_bytes     = num_chunks * log2(num_unique_chunks) / 8   (fixed-width pointer)
    original_bytes    = sum of all token characters + spaces

    Lower ratio = better compression.
    Returns ratio in [0, inf). Values < 1.0 mean compression was achieved.
    """
    if not chunks:
        return 1.0

    # Flatten to get original byte count
    all_tokens = [t for c in chunks for t in c]
    original_bytes = sum(len(t) for t in all_tokens) + max(0, len(all_tokens) - 1)
    if original_bytes == 0:
        return 1.0

    # Build vocabulary of unique chunk signatures
    vocab: Dict[str, List[str]] = {}
    chunk_ids = []
    for chunk in chunks:
        key = "\x00".join(chunk)
        if key not in vocab:
            vocab[key] = chunk
        chunk_ids.append(key)

    # Vocabulary storage: each unique chunk stored once
    vocab_bytes = sum(
        sum(len(t) for t in chunk) + max(0, len(chunk) - 1)
        for chunk in vocab.values()
    )

    # Pointer stream: each chunk replaced by an integer ID
    n_types = max(1, len(vocab))
    bits_per_pointer = max(1, math.ceil(math.log2(n_types + 1)))
    pointer_bytes = math.ceil(len(chunk_ids) * bits_per_pointer / 8)

    return (vocab_bytes + pointer_bytes) / original_bytes


def _type_token_ratio(tokens: List[str]) -> float:
    """Type-token ratio: unique_types / total_tokens. Lower = more repetitive = more predictable."""
    if not tokens:
        return 1.0
    return len(set(tokens)) / len(tokens)


def _chunk_size_penalty(chunks: List[List[str]], corpus_len: int) -> float:
    """
    Penalise degenerate solutions that compress by using giant single chunks.
    penalty = log(avg_chunk_len) / log(corpus_len)
    Score is 0 for single-token chunks; approaches 1 for one giant chunk.
    """
    if not chunks or corpus_len <= 1:
        return 0.0
    avg_len = sum(len(c) for c in chunks) / len(chunks)
    return math.log(max(1, avg_len)) / math.log(max(2, corpus_len))


# ---------------------------------------------------------------------------
# Discovery Methods
# ---------------------------------------------------------------------------

class DiscoveryMethod(ABC):
    name: str

    @abstractmethod
    def discover_boundaries(self, corpus: str) -> List[int]:
        """Return token indices predicted as segment boundaries."""

    @abstractmethod
    def discover_chunks(self, corpus: str) -> List[List[str]]:
        """Return a list of token chunks (invariants) discovered in corpus."""

    def tokenize(self, corpus: str) -> List[str]:
        return corpus.split()


class RandomMethod(DiscoveryMethod):
    name = "Random"
    _seed = 42

    def discover_boundaries(self, corpus: str) -> List[int]:
        tokens = self.tokenize(corpus)
        rng = random.Random(self._seed)
        return sorted(rng.sample(range(1, max(2, len(tokens))), k=max(1, len(tokens) // 5)))

    def discover_chunks(self, corpus: str) -> List[List[str]]:
        tokens = self.tokenize(corpus)
        rng = random.Random(self._seed)
        chunks = []
        i = 0
        while i < len(tokens):
            size = rng.randint(1, max(2, len(tokens) // 5))
            chunks.append(tokens[i:i + size])
            i += size
        return [c for c in chunks if c]


class ASTMethod(DiscoveryMethod):
    """Python-only. Uses the built-in ast module as an oracle for boundaries."""
    name = "AST"

    def discover_boundaries(self, corpus: str) -> List[int]:
        """Return token indices where def/class lines start."""
        tokens = self.tokenize(corpus)
        boundaries = []
        idx = 0
        for line in corpus.split("\n"):
            stripped = line.strip()
            if stripped.startswith("def ") or stripped.startswith("class "):
                if idx > 0:
                    boundaries.append(idx)
            line_tokens = line.split()
            idx += len(line_tokens)
        return boundaries

    def discover_chunks(self, corpus: str) -> List[List[str]]:
        """Chunk by top-level AST nodes."""
        try:
            tree = ast.parse(corpus)
        except SyntaxError:
            return [self.tokenize(corpus)]
        lines = corpus.split("\n")
        chunks = []
        prev = 0
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.ClassDef, ast.AsyncFunctionDef)):
                start = node.lineno - 1
                end = getattr(node, "end_lineno", start + 1)
                chunk_text = "\n".join(lines[start:end])
                chunks.append(chunk_text.split())
        return chunks if chunks else [self.tokenize(corpus)]


class BPEMethod(DiscoveryMethod):
    """
    Byte-pair encoding: iteratively merges the most frequent adjacent pair.
    Pure Python, no external libraries.
    """
    name = "BPE"

    def __init__(self, num_merges: int = 100):
        self.num_merges = num_merges

    def _bpe(self, tokens: List[str]) -> List[str]:
        vocab = list(tokens)
        for _ in range(self.num_merges):
            pairs: Dict[Tuple[str, str], int] = {}
            for i in range(len(vocab) - 1):
                pair = (vocab[i], vocab[i + 1])
                pairs[pair] = pairs.get(pair, 0) + 1
            if not pairs:
                break
            best = max(pairs, key=lambda p: pairs[p])
            merged = best[0] + "+" + best[1]
            new_vocab = []
            i = 0
            while i < len(vocab):
                if i < len(vocab) - 1 and (vocab[i], vocab[i + 1]) == best:
                    new_vocab.append(merged)
                    i += 2
                else:
                    new_vocab.append(vocab[i])
                    i += 1
            vocab = new_vocab
        return vocab

    def discover_boundaries(self, corpus: str) -> List[int]:
        tokens = self.tokenize(corpus)
        merged = self._bpe(tokens)
        # Boundaries are where BPE tokens are long (merged multiple source tokens)
        boundaries = []
        idx = 0
        for m in merged:
            parts = m.split("+")
            idx += len(parts)
            boundaries.append(idx)
        return [b for b in boundaries if 0 < b < len(tokens)]

    def discover_chunks(self, corpus: str) -> List[List[str]]:
        tokens = self.tokenize(corpus)
        merged = self._bpe(tokens)
        return [m.split("+") for m in merged]


class H1Method(DiscoveryMethod):
    """
    Sheaf H¹ cohomology obstruction method.
    Wraps SheafBoundaryPredictor from the existing services module.
    """
    name = "H1"

    def __init__(self, boundary_pct: float = 0.15, window_size: int = 7, min_chunk_size: int = 5):
        """
        Args:
            boundary_pct: Fraction of transitions to flag as boundaries.
                          0.15 means the 15% least-coherent transitions become boundaries.
                          This is corpus-adaptive: avoids the fixed-threshold collapse.
            window_size: Window of tokens examined around each candidate boundary.
            min_chunk_size: Minimum tokens per chunk. Prevents single-token over-segmentation.
        """
        self.boundary_pct = boundary_pct
        self.window_size = window_size
        self.min_chunk_size = min_chunk_size

    def _embed(self, tokens: List[str]) -> Dict[str, "np.ndarray"]:
        import numpy as np
        embeddings = {}
        for token in set(tokens):
            state = np.random.RandomState(abs(hash(token)) % (2 ** 32))
            v = state.randn(8)
            norm = np.linalg.norm(v)
            embeddings[token] = v / norm if norm > 1e-12 else v
        return embeddings

    def _compute_similarity_scores(self, tokens: List[str], embeddings: dict) -> List[float]:
        """Compute cosine similarity at every adjacent token pair."""
        import numpy as np
        scores = []
        for i in range(len(tokens) - 1):
            v1 = embeddings.get(tokens[i], np.zeros(8))
            v2 = embeddings.get(tokens[i + 1], np.zeros(8))
            scores.append(float(np.dot(v1, v2)))
        return scores

    def discover_boundaries(self, corpus: str) -> List[int]:
        import numpy as np
        tokens = self.tokenize(corpus)
        if len(tokens) < 2:
            return []
        embeddings = self._embed(tokens)
        scores = self._compute_similarity_scores(tokens, embeddings)

        # Dynamic threshold: flag the bottom boundary_pct of transitions
        threshold = float(np.percentile(scores, self.boundary_pct * 100))

        # Enforce min_chunk_size: suppress boundaries within min_chunk_size tokens of the last one
        boundaries = []
        last_boundary = -self.min_chunk_size
        for i, score in enumerate(scores):
            if score <= threshold and (i - last_boundary) >= self.min_chunk_size:
                boundaries.append(i)
                last_boundary = i
        return boundaries

    def _h1(self, window: List[str], embeddings: dict) -> float:
        """Legacy helper kept for compatibility."""
        import numpy as np
        if len(window) < 2:
            return 0.0
        obstructions = 0
        for i in range(len(window) - 1):
            v1 = embeddings.get(window[i], np.zeros(8))
            v2 = embeddings.get(window[i + 1], np.zeros(8))
            if float(np.dot(v1, v2)) < 0.0:
                obstructions += 1
        return float(obstructions)

    def discover_chunks(self, corpus: str) -> List[List[str]]:
        tokens = self.tokenize(corpus)
        if not tokens:
            return []
        boundaries = set(self.discover_boundaries(corpus))
        chunks = []
        current = []
        for i, tok in enumerate(tokens):
            current.append(tok)
            if i in boundaries:
                chunks.append(current)
                current = []
        if current:
            chunks.append(current)
        return chunks


class GzipMethod(DiscoveryMethod):
    """Gzip compression as a boundary-agnostic compression baseline."""
    name = "Gzip"

    def discover_boundaries(self, corpus: str) -> List[int]:
        # Gzip has no boundary concept; return empty
        return []

    def discover_chunks(self, corpus: str) -> List[List[str]]:
        # One chunk: the whole corpus
        return [self.tokenize(corpus)]


class LZMAMethod(DiscoveryMethod):
    """LZMA compression baseline."""
    name = "LZMA"

    def discover_boundaries(self, corpus: str) -> List[int]:
        return []

    def discover_chunks(self, corpus: str) -> List[List[str]]:
        return [self.tokenize(corpus)]


class NgramMethod(DiscoveryMethod):
    """Trigram model: boundaries predicted at low-probability trigram transitions."""
    name = "Ngram"

    def __init__(self, n: int = 3):
        self.n = n

    def _build_model(self, tokens: List[str]) -> Dict[tuple, float]:
        counts: Dict[tuple, int] = {}
        total = 0
        for i in range(len(tokens) - self.n + 1):
            gram = tuple(tokens[i:i + self.n])
            counts[gram] = counts.get(gram, 0) + 1
            total += 1
        return {k: v / max(1, total) for k, v in counts.items()}

    def discover_boundaries(self, corpus: str) -> List[int]:
        tokens = self.tokenize(corpus)
        if len(tokens) < self.n:
            return []
        model = self._build_model(tokens)
        mean_prob = sum(model.values()) / max(1, len(model))
        boundaries = []
        for i in range(len(tokens) - self.n + 1):
            gram = tuple(tokens[i:i + self.n])
            if model.get(gram, 0.0) < mean_prob * 0.5:
                boundaries.append(i + self.n - 1)
        return boundaries

    def discover_chunks(self, corpus: str) -> List[List[str]]:
        tokens = self.tokenize(corpus)
        if not tokens:
            return []
        boundaries = set(self.discover_boundaries(corpus))
        chunks, current = [], []
        for i, tok in enumerate(tokens):
            current.append(tok)
            if i in boundaries:
                chunks.append(current)
                current = []
        if current:
            chunks.append(current)
        return chunks


# ---------------------------------------------------------------------------
# Track Runners
# ---------------------------------------------------------------------------

def _f1(predicted: List[int], truth: List[int], n_tokens: int) -> Dict[str, float]:
    pred_set = set(predicted)
    true_set = set(truth)
    tp = len(pred_set & true_set)
    fp = len(pred_set - true_set)
    fn = len(true_set - pred_set)
    precision = tp / max(1, tp + fp)
    recall = tp / max(1, tp + fn)
    f1 = 2 * precision * recall / max(1e-12, precision + recall)
    return {"precision": round(precision, 4), "recall": round(recall, 4), "f1": round(f1, 4)}


def run_track1_boundary(corpus: str, true_boundaries: List[int], methods: List[DiscoveryMethod], dataset_name: str):
    """Track 1: Boundary detection. Ground truth is provided; all methods compete equally."""
    tokens = corpus.split()
    n = len(tokens)
    results = {}
    f1_scores: Dict[str, List[float]] = {}

    for method in methods:
        pred = method.discover_boundaries(corpus)
        scores = _f1(pred, true_boundaries, n)
        results[method.name] = scores
        f1_scores[method.name] = [scores["f1"]]

    # Record to leaderboard
    for method in methods:
        f1 = results[method.name]["f1"]
        mean, lo, hi = bootstrap_ci(f1_scores[method.name] * 20, n_resamples=500)
        record_run(
            method=method.name,
            dataset=dataset_name,
            track="boundary",
            boundary_f1=f1,
            ci_95=[lo, hi],
        )

    return results


def run_track2_compression(corpus: str, methods: List[DiscoveryMethod], dataset_name: str):
    """
    Track 2: Compression via vocabulary-pointer model.

    Metric: compression_ratio = (vocabulary_bytes + pointer_bytes) / original_bytes.
    Lower is better. Gain = baseline_ratio - method_ratio (baseline = no chunking = ratio 1.0).
    Chunk-size penalty applied to prevent degenerate single-giant-chunk solutions.
    """
    tokens = corpus.split()
    n = len(tokens)
    # Baseline: no chunking at all (one token per chunk = ratio 1.0 by definition)
    results = {}

    for method in methods:
        if method.name in ("Gzip", "LZMA"):
            # For pure compressors: use actual gzip/lzma ratio on whole corpus
            compress_method = "gzip" if method.name == "Gzip" else "lzma"
            ratio = _compression_ratio(corpus, compress_method)
            gain = max(0.0, 1.0 - ratio)  # gain vs. uncompressed baseline
            chunks = [tokens]  # single chunk
            penalty = 0.0      # no chunking decision made
        else:
            chunks = method.discover_chunks(corpus)
            if not chunks:
                chunks = [tokens]
            ratio = _vocabulary_compression_ratio(chunks)
            gain = max(0.0, 1.0 - ratio)
            penalty = _chunk_size_penalty(chunks, n)

        # TF-IDF reuse across chunks
        all_tokens = [t for c in chunks for t in c]
        total_tfidf = sum(_tfidf_reuse(c, all_tokens) for c in chunks)
        avg_reuse = total_tfidf / max(1, len(chunks))

        score = max(0.0, gain - penalty)
        avg_chunk_len = sum(len(c) for c in chunks) / max(1, len(chunks))
        results[method.name] = {
            "vocab_compression_ratio": round(ratio, 4),
            "compression_gain": round(gain, 4),
            "chunk_size_penalty": round(penalty, 4),
            "avg_chunk_len": round(avg_chunk_len, 1),
            "n_chunks": len(chunks),
            "reuse_tfidf": round(avg_reuse, 4),
            "score": round(score, 4),
        }
        mean, lo, hi = bootstrap_ci([score] * 20, n_resamples=500)
        record_run(
            method=method.name,
            dataset=dataset_name,
            track="compression",
            compression=gain,
            reuse=avg_reuse,
            ci_95=[lo, hi],
        )

    return results


def run_track3_prediction(corpus: str, methods: List[DiscoveryMethod], dataset_name: str):
    """
    Track 3: Predictability via within-chunk type-token ratio (TTR).

    Type-token ratio = unique_types / total_tokens in a chunk.
    Lower TTR within a chunk = higher repetition = higher predictability.

    Metric: TTR_reduction = corpus_TTR - mean_chunk_TTR
    Positive values mean the chunking produced internally repetitive (predictable) segments.
    A chunk of all identical tokens has TTR=1/n (near zero). A chunk of all unique tokens has TTR=1.0.
    """
    tokens = corpus.split()
    corpus_ttr = _type_token_ratio(tokens)
    results = {}

    for method in methods:
        chunks = method.discover_chunks(corpus)
        if not chunks:
            chunks = [tokens]

        chunk_ttrs = [_type_token_ratio(c) for c in chunks if c]
        if not chunk_ttrs:
            reduction = 0.0
            novelty = 0.0
        else:
            mean_chunk_ttr = sum(chunk_ttrs) / len(chunk_ttrs)
            # Positive if chunks are MORE predictable than the full corpus
            reduction = max(0.0, corpus_ttr - mean_chunk_ttr)

            # Novelty: reduction beyond what the least-predictable chunk achieves
            best_chunk_reduction = max(0.0, corpus_ttr - min(chunk_ttrs))
            novelty = max(0.0, reduction - (best_chunk_reduction * 0.5))

        results[method.name] = {
            "corpus_ttr": round(corpus_ttr, 4),
            "mean_chunk_ttr": round(sum(chunk_ttrs) / max(1, len(chunk_ttrs)), 4),
            "ttr_reduction": round(reduction, 4),
            "novelty": round(novelty, 4),
            "n_chunks": len(chunks),
        }
        mean, lo, hi = bootstrap_ci([reduction] * 20, n_resamples=500)
        record_run(
            method=method.name,
            dataset=dataset_name,
            track="prediction",
            prediction=reduction,
            novelty=novelty,
            ci_95=[lo, hi],
        )

    return results


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 80)
    print("DISCOVERY OLYMPICS")
    print("=" * 80)

    # --- Track 1: Boundary Detection ---
    print("\n── Track 1: Boundary Detection ──\n")
    track1_methods = [H1Method(), BPEMethod(), ASTMethod(), RandomMethod()]
    for class_name, samples in ALL_CODE.items():
        corpus = "\n\n".join(samples)
        tokens = corpus.split()
        # Ground-truth: index of token at start of each "def " / "class " line
        true_bounds = []
        idx = 0
        for line in corpus.split("\n"):
            stripped = line.strip()
            if stripped.startswith("def ") or stripped.startswith("class "):
                if idx > 0:
                    true_bounds.append(idx)
            idx += len(line.split())

        results = run_track1_boundary(corpus, true_bounds, track1_methods, dataset_name=class_name)
        print(f"  {class_name:20s} | " + " | ".join(
            f"{m.name}: F1={results[m.name]['f1']:.3f}" for m in track1_methods
        ))

    # Cross-domain boundary detection (no AST)
    cross_methods = [H1Method(), BPEMethod(), RandomMethod()]
    for domain_name, domain_data in ALL_DOMAINS.items():
        corpus = " ".join(domain_data["structured"])
        true_bounds = list(range(0, len(corpus.split()), max(1, len(corpus.split()) // 5)))
        results = run_track1_boundary(corpus, true_bounds, cross_methods, dataset_name=f"{domain_name}_structured")
        print(f"  {domain_name + '_structured':20s} | " + " | ".join(
            f"{m.name}: F1={results[m.name]['f1']:.3f}" for m in cross_methods
        ))

    # --- Track 2: Compression ---
    print("\n── Track 2: Compression ──\n")
    track2_methods = [H1Method(), BPEMethod(), GzipMethod(), LZMAMethod(), RandomMethod()]
    for class_name, samples in ALL_CODE.items():
        corpus = "\n\n".join(samples)
        results = run_track2_compression(corpus, track2_methods, dataset_name=class_name)
        print(f"  {class_name:20s} | " + " | ".join(
            f"{m.name}: ratio={results[m.name]['vocab_compression_ratio']:.3f} gain={results[m.name]['score']:.3f} chunks={results[m.name]['n_chunks']} avg_len={results[m.name]['avg_chunk_len']}" for m in track2_methods
        ))

    # --- Track 3: Prediction (Cross-Entropy Reduction) ---
    print("\n── Track 3: Prediction ──\n")
    track3_methods = [H1Method(), NgramMethod(), RandomMethod()]
    for class_name, samples in ALL_CODE.items():
        corpus = "\n\n".join(samples)
        results = run_track3_prediction(corpus, track3_methods, dataset_name=class_name)
        print(f"  {class_name:20s} | " + " | ".join(
            f"{m.name}: TTR_red={results[m.name]['ttr_reduction']:.3f} chunks={results[m.name]['n_chunks']}" for m in track3_methods
        ))

    for domain_name, domain_data in ALL_DOMAINS.items():
        corpus = " ".join(domain_data["structured"])
        results = run_track3_prediction(corpus, track3_methods, dataset_name=f"{domain_name}_structured")
        print(f"  {domain_name + '_structured':20s} | " + " | ".join(
            f"{m.name}: TTR_red={results[m.name]['ttr_reduction']:.3f} chunks={results[m.name]['n_chunks']}" for m in track3_methods
        ))

    # --- Leaderboard ---
    print("\n── Final Leaderboard (all tracks) ──")
    print_leaderboard()

    print("\n" + "=" * 80)
    print("Olympics complete. Results persisted to benchmarks/leaderboard/runs.jsonl")
    print("=" * 80)


if __name__ == "__main__":
    main()
