"""
Structural Olympics — Benchmark Suite

Tests what the Compression Olympics cannot: geometric and structural properties
of discovered chunks, independent of compression or prediction.

Four tracks:
  Track S1 — Projection Stability
             Embed chunk, project to lower dims, measure pairwise distance preservation.
             High score = the structure is real, not a dimensionality artifact.

  Track S2 — Orbit Stability
             Apply E8 Weyl reflections (8 simple roots) to chunk embeddings.
             Measure variance across the orbit. Low variance = genuine lattice invariant.

  Track S3 — Cross-Domain Persistence
             Embed chunks from code and genomics/math/music.
             Measure whether nearest-neighbor rank ordering is preserved under projection.

  Track S4 — Lattice Utility
             k-NN consistency: if A is near B and B is near C, is A near C?
             Measures whether chunks form coherent clusters in embedding space.

Key design decision:
  The embeddings tested here are:
    (a) RandomHash  — current H1 baseline (expected to fail: no semantic content)
    (b) StructuralFeature — code-aware: keyword density, bracket depth, token entropy
    (c) TFIDFVector — corpus-aware: token frequency weighted

  The chunk sources tested are:
    H1, BPE, AST, Random

  This lets us decouple the question:
    "Is H1 chunking bad?"   from
    "Is the embedding bad?"

Run:
    python benchmarks/structural_olympics.py
"""
import math
import os
import random
import sys
from abc import ABC, abstractmethod
from typing import Dict, List, Tuple

import numpy as np

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from benchmarks.datasets import ALL_CODE, ALL_DOMAINS
from benchmarks.olympics import H1Method, BPEMethod, ASTMethod, RandomMethod, NgramMethod
from benchmarks.leaderboard import record_run

# E8 simple roots in 8D (from geometric_rl_steering.py)
_E8_SIMPLE_ROOTS_8D = np.array([
    [0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5, 0.5],
    [1.0,  1.0,  0.0,  0.0,  0.0,  0.0,  0.0, 0.0],
    [-1.0, 1.0,  0.0,  0.0,  0.0,  0.0,  0.0, 0.0],
    [0.0, -1.0,  1.0,  0.0,  0.0,  0.0,  0.0, 0.0],
    [0.0,  0.0, -1.0,  1.0,  0.0,  0.0,  0.0, 0.0],
    [0.0,  0.0,  0.0, -1.0,  1.0,  0.0,  0.0, 0.0],
    [0.0,  0.0,  0.0,  0.0, -1.0,  1.0,  0.0, 0.0],
    [0.0,  0.0,  0.0,  0.0,  0.0, -1.0,  1.0, 0.0],
], dtype=float)

# Normalize
for _i in range(len(_E8_SIMPLE_ROOTS_8D)):
    _n = np.linalg.norm(_E8_SIMPLE_ROOTS_8D[_i])
    if _n > 1e-12:
        _E8_SIMPLE_ROOTS_8D[_i] /= _n


# ---------------------------------------------------------------------------
# Embedding Strategies
# ---------------------------------------------------------------------------

class ChunkEmbedder(ABC):
    name: str
    dim: int

    @abstractmethod
    def embed(self, chunk: List[str], corpus_tokens: List[str]) -> np.ndarray:
        """Return a fixed-length embedding vector for a chunk."""

    def embed_batch(self, chunks: List[List[str]], corpus_tokens: List[str]) -> np.ndarray:
        """Return (N, dim) matrix of embeddings."""
        vecs = [self.embed(c, corpus_tokens) for c in chunks if c]
        if not vecs:
            return np.zeros((0, self.dim))
        return np.stack(vecs)


class RandomHashEmbedder(ChunkEmbedder):
    """
    Current H1 baseline: each token mapped to a random unit vector via hash seed.
    The chunk embedding is the mean of its token embeddings.
    This is expected to have poor structural properties because it encodes
    no semantic or syntactic information — it can only reflect hash distribution.
    """
    name = "RandomHash"
    dim = 8

    def embed(self, chunk: List[str], corpus_tokens: List[str]) -> np.ndarray:
        if not chunk:
            return np.zeros(self.dim)
        vecs = []
        for token in chunk:
            state = np.random.RandomState(abs(hash(token)) % (2 ** 32))
            v = state.randn(self.dim)
            n = np.linalg.norm(v)
            vecs.append(v / n if n > 1e-12 else v)
        mean = np.mean(vecs, axis=0)
        n = np.linalg.norm(mean)
        return mean / n if n > 1e-12 else mean


class StructuralFeatureEmbedder(ChunkEmbedder):
    """
    Code-structure aware embedding. Computes:
      - Keyword density (per keyword type)
      - Bracket/indent depth statistics
      - Token length statistics
      - Character-level unigram entropy
      - Type-token ratio

    These are deterministic, semantic, and corpus-independent.
    Expected to show real structural signal for code, and reduced signal for noise.
    """
    name = "StructuralFeature"
    dim = 16

    _KEYWORDS = [
        "def", "class", "return", "if", "else", "elif", "for", "while",
        "import", "from", "try", "except", "with", "yield", "lambda",
        "and", "or", "not",
    ]

    def embed(self, chunk: List[str], corpus_tokens: List[str]) -> np.ndarray:
        if not chunk:
            return np.zeros(self.dim)
        text = " ".join(chunk)
        n = len(chunk)
        v = np.zeros(self.dim)

        # [0:6] keyword densities (grouped)
        kw_counts = {k: 0 for k in self._KEYWORDS}
        for tok in chunk:
            if tok in kw_counts:
                kw_counts[tok] += 1
        control_kw  = sum(kw_counts[k] for k in ["if", "elif", "else", "for", "while", "try", "except"])
        def_kw      = sum(kw_counts[k] for k in ["def", "class", "lambda", "yield"])
        import_kw   = sum(kw_counts[k] for k in ["import", "from"])
        logic_kw    = sum(kw_counts[k] for k in ["and", "or", "not"])
        v[0] = control_kw / max(1, n)
        v[1] = def_kw / max(1, n)
        v[2] = import_kw / max(1, n)
        v[3] = logic_kw / max(1, n)

        # [4] avg token length
        v[4] = sum(len(t) for t in chunk) / max(1, n)

        # [5] type-token ratio
        v[5] = len(set(chunk)) / max(1, n)

        # [6] bracket depth
        depth = 0
        max_depth = 0
        for ch in text:
            if ch in "([{":
                depth += 1
                max_depth = max(max_depth, depth)
            elif ch in ")]}":
                depth = max(0, depth - 1)
        v[6] = max_depth / max(1, len(text))

        # [7] dot-access density (object-oriented code pattern)
        v[7] = text.count(".") / max(1, n)

        # [8] character-level entropy
        freq: Dict[str, int] = {}
        for ch in text:
            freq[ch] = freq.get(ch, 0) + 1
        total = len(text)
        entropy = 0.0
        for count in freq.values():
            p = count / total
            entropy -= p * math.log2(p)
        v[8] = entropy / 8.0  # normalize to ~[0,1]; max char entropy ~= 8 bits

        # [9] punctuation density
        punct = sum(1 for ch in text if ch in ".,;:!?")
        v[9] = punct / max(1, len(text))

        # [10] digit density
        v[10] = sum(1 for ch in text if ch.isdigit()) / max(1, len(text))

        # [11] uppercase density
        v[11] = sum(1 for ch in text if ch.isupper()) / max(1, len(text))

        # [12-13] chunk length (normalized)
        v[12] = min(1.0, n / 50.0)   # normalized chunk length
        v[13] = min(1.0, len(text) / 500.0)  # normalized char length

        # [14] self-reference density (return/self)
        v[14] = sum(1 for t in chunk if t in ("return", "self", "cls", "super")) / max(1, n)

        # [15] comment density
        v[15] = text.count("#") / max(1, n)

        norm = np.linalg.norm(v)
        return v / norm if norm > 1e-12 else v


class TFIDFEmbedder(ChunkEmbedder):
    """
    Corpus-aware TF-IDF embedding.
    Vocabulary is built from the corpus. Chunk embedding is the TF-IDF weighted
    sum of token hash vectors. This captures relative importance in context.
    """
    name = "TFIDF"
    dim = 8

    def _idf(self, corpus_tokens: List[str]) -> Dict[str, float]:
        """Inverse document frequency using token frequency in corpus."""
        freq: Dict[str, int] = {}
        for t in corpus_tokens:
            freq[t] = freq.get(t, 0) + 1
        n = len(corpus_tokens)
        return {t: math.log((n + 1) / (c + 1)) for t, c in freq.items()}

    def embed(self, chunk: List[str], corpus_tokens: List[str]) -> np.ndarray:
        if not chunk:
            return np.zeros(self.dim)
        idf = self._idf(corpus_tokens)
        n_corpus = max(1, len(corpus_tokens))

        # TF for this chunk
        chunk_freq: Dict[str, int] = {}
        for t in chunk:
            chunk_freq[t] = chunk_freq.get(t, 0) + 1
        n_chunk = max(1, len(chunk))

        acc = np.zeros(self.dim)
        weight_sum = 0.0
        for token, count in chunk_freq.items():
            tf = count / n_chunk
            weight = tf * idf.get(token, 0.0)
            state = np.random.RandomState(abs(hash(token)) % (2 ** 32))
            tok_vec = state.randn(self.dim)
            norm = np.linalg.norm(tok_vec)
            if norm > 1e-12:
                tok_vec /= norm
            acc += weight * tok_vec
            weight_sum += weight

        if weight_sum < 1e-12:
            return np.zeros(self.dim)
        acc /= weight_sum
        norm = np.linalg.norm(acc)
        return acc / norm if norm > 1e-12 else acc


# ---------------------------------------------------------------------------
# Weyl Reflection
# ---------------------------------------------------------------------------

def weyl_reflect(v: np.ndarray, root: np.ndarray) -> np.ndarray:
    """
    Apply Weyl reflection along root: s_α(v) = v - 2⟨v,α⟩/⟨α,α⟩ · α
    """
    alpha_sq = np.dot(root, root)
    if alpha_sq < 1e-12:
        return v.copy()
    proj = 2.0 * np.dot(v, root) / alpha_sq
    return v - proj * root


def weyl_orbit_sample(v: np.ndarray, roots: np.ndarray) -> List[np.ndarray]:
    """
    Apply each of the 8 simple Weyl reflections independently.
    Returns a list of 8 transformed vectors (the first-order orbit neighbourhood).
    """
    orbit = []
    for root in roots:
        # Operate only on first 8 dims if v is larger
        if len(v) > 8:
            v8 = v[:8].copy()
            reflected_8 = weyl_reflect(v8, root)
            reflected = v.copy()
            reflected[:8] = reflected_8
        else:
            reflected = weyl_reflect(v, root)
        orbit.append(reflected)
    return orbit


# ---------------------------------------------------------------------------
# Structural Metrics
# ---------------------------------------------------------------------------

def _pairwise_distances(X: np.ndarray) -> np.ndarray:
    """Return upper-triangle pairwise Euclidean distances for matrix X (N, d)."""
    n = X.shape[0]
    dists = []
    for i in range(n):
        for j in range(i + 1, n):
            dists.append(float(np.linalg.norm(X[i] - X[j])))
    return np.array(dists) if dists else np.array([0.0])


def _pearson(x: np.ndarray, y: np.ndarray) -> float:
    """Pearson correlation between two arrays. Returns 0 if constant."""
    if len(x) < 2:
        return 0.0
    x_std = x.std()
    y_std = y.std()
    if x_std < 1e-12 or y_std < 1e-12:
        return 0.0
    return float(np.corrcoef(x, y)[0, 1])


def track_s1_projection_stability(
    chunks: List[List[str]],
    corpus_tokens: List[str],
    embedder: ChunkEmbedder,
    projection_dims: Tuple[int, ...] = (2, 4),
) -> Dict:
    """
    Track S1: Projection Stability.

    For each target dimension d in projection_dims:
      1. Embed all chunks in full dim D.
      2. Project to d dims using a random orthonormal matrix.
      3. Measure Pearson correlation between pairwise distances in D-dim and d-dim.

    High correlation = distance structure is preserved under projection = geometry is real.
    Low correlation = geometry is an artifact of dimensionality.

    Returns mean Pearson correlation across all projection targets.
    """
    if len(chunks) < 3:
        return {"mean_projection_stability": 0.0, "per_dim": {}}

    X = embedder.embed_batch(chunks, corpus_tokens)
    if X.shape[0] < 3:
        return {"mean_projection_stability": 0.0, "per_dim": {}}

    D = X.shape[1]
    original_dists = _pairwise_distances(X)
    rng = np.random.RandomState(42)  # fixed seed for reproducibility

    results = {}
    for d in projection_dims:
        if d >= D:
            continue
        # Random orthonormal projection (D → d)
        proj_matrix = rng.randn(D, d)
        proj_matrix, _ = np.linalg.qr(proj_matrix)
        proj_matrix = proj_matrix[:, :d]  # (D, d)

        X_proj = X @ proj_matrix  # (N, d)
        projected_dists = _pairwise_distances(X_proj)

        corr = _pearson(original_dists, projected_dists)
        results[d] = round(corr, 4)

    mean_stability = sum(results.values()) / max(1, len(results))
    return {
        "mean_projection_stability": round(mean_stability, 4),
        "per_dim": results,
    }


def track_s2_orbit_stability(
    chunks: List[List[str]],
    corpus_tokens: List[str],
    embedder: ChunkEmbedder,
) -> Dict:
    """
    Track S2: Orbit Stability under E8 Weyl Reflections.

    For each chunk embedding v:
      1. Apply each of the 8 simple Weyl reflections to produce 8 transformed vectors.
      2. Compute the cosine similarity between the original and each transformed vector.
      3. Orbit stability = 1 - std(cosine_similarities).

    High stability (low std) = the vector is symmetric under the Weyl group = geometrically invariant.
    Low stability (high std) = the vector is an asymmetric point in the space.

    Returns mean orbit stability across all chunks.
    """
    if not chunks:
        return {"mean_orbit_stability": 0.0, "mean_orbit_cos_similarity": 0.0}

    X = embedder.embed_batch(chunks, corpus_tokens)
    if X.shape[0] == 0:
        return {"mean_orbit_stability": 0.0, "mean_orbit_cos_similarity": 0.0}

    stabilities = []
    cos_similarities = []

    for i in range(X.shape[0]):
        v = X[i]
        orbit = weyl_orbit_sample(v, _E8_SIMPLE_ROOTS_8D)

        cos_sims = []
        for ov in orbit:
            # Operate on same-length prefix
            v_ref = v[:8] if len(v) >= 8 else v
            ov_ref = ov[:8] if len(ov) >= 8 else ov

            v_norm = np.linalg.norm(v_ref)
            ov_norm = np.linalg.norm(ov_ref)
            if v_norm > 1e-12 and ov_norm > 1e-12:
                cos = float(np.dot(v_ref / v_norm, ov_ref / ov_norm))
                cos_sims.append(cos)

        if cos_sims:
            stability = 1.0 - float(np.std(cos_sims))
            stabilities.append(stability)
            cos_similarities.append(float(np.mean(cos_sims)))

    return {
        "mean_orbit_stability": round(sum(stabilities) / max(1, len(stabilities)), 4),
        "mean_orbit_cos_similarity": round(sum(cos_similarities) / max(1, len(cos_similarities)), 4),
        "n_chunks": len(chunks),
    }


def track_s3_cross_domain_persistence(
    source_chunks: List[List[str]],
    source_tokens: List[str],
    target_chunks: List[List[str]],
    target_tokens: List[str],
    embedder: ChunkEmbedder,
    projection_dims: Tuple[int, ...] = (2, 4),
) -> Dict:
    """
    Track S3: Cross-Domain Persistence.

    Measures whether the nearest-neighbor rank structure between source and target
    domain chunks is preserved under random projection.

    Method:
      1. Embed source and target chunks together in full dim D.
      2. For each source chunk, find its nearest target chunk (by rank in distance list).
      3. Project to d dims, repeat.
      4. Measure rank correlation (Spearman) between full-dim and projected ranks.

    High rank correlation = the cross-domain relationships are real, not artifacts.
    """
    if len(source_chunks) < 2 or len(target_chunks) < 2:
        return {"mean_cross_domain_persistence": 0.0}

    all_chunks = source_chunks + target_chunks
    all_tokens = source_tokens + target_tokens
    X = embedder.embed_batch(all_chunks, all_tokens)
    if X.shape[0] < 4:
        return {"mean_cross_domain_persistence": 0.0}

    n_src = len(source_chunks)
    X_src = X[:n_src]
    X_tgt = X[n_src:]

    def nearest_target_ranks(X_s, X_t):
        """For each source chunk, rank all target chunks by distance."""
        ranks = []
        for i in range(X_s.shape[0]):
            dists = [float(np.linalg.norm(X_s[i] - X_t[j])) for j in range(X_t.shape[0])]
            order = sorted(range(len(dists)), key=lambda x: dists[x])
            ranks.append(order[0])  # index of nearest target
        return ranks

    full_ranks = nearest_target_ranks(X_src, X_tgt)
    D = X.shape[1]
    rng = np.random.RandomState(42)

    persistence_scores = []
    for d in projection_dims:
        if d >= D:
            continue
        proj_matrix = rng.randn(D, d)
        proj_matrix, _ = np.linalg.qr(proj_matrix)
        proj_matrix = proj_matrix[:, :d]

        X_proj = X @ proj_matrix
        X_src_p = X_proj[:n_src]
        X_tgt_p = X_proj[n_src:]

        projected_ranks = nearest_target_ranks(X_src_p, X_tgt_p)

        # Rank agreement: fraction where nearest neighbor is the same
        agreement = sum(1 for a, b in zip(full_ranks, projected_ranks) if a == b)
        persistence_scores.append(agreement / max(1, len(full_ranks)))

    return {
        "mean_cross_domain_persistence": round(
            sum(persistence_scores) / max(1, len(persistence_scores)), 4
        ),
        "per_dim": {str(d): round(s, 4) for d, s in zip(projection_dims, persistence_scores)},
    }


def track_s4_lattice_utility(
    chunks: List[List[str]],
    corpus_tokens: List[str],
    embedder: ChunkEmbedder,
    k: int = 3,
) -> Dict:
    """
    Track S4: Lattice Utility (k-NN Consistency).

    Measures whether chunks form coherent clusters in embedding space.

    For each chunk i, find its k nearest neighbors.
    For each pair (j, k_neighbor) in those neighbors, check if they are also
    mutually near each other (triangular consistency).

    Consistency = fraction of neighbor triplets that are mutually consistent.
    High consistency = chunks form a coherent lattice structure.
    Low consistency = chunks are scattered, no cluster structure.
    """
    if len(chunks) < k + 2:
        return {"knn_consistency": 0.0, "mean_nn_distance": 0.0}

    X = embedder.embed_batch(chunks, corpus_tokens)
    n = X.shape[0]
    if n < k + 2:
        return {"knn_consistency": 0.0, "mean_nn_distance": 0.0}

    # Compute pairwise distance matrix
    dist_matrix = np.zeros((n, n))
    for i in range(n):
        for j in range(i + 1, n):
            d = float(np.linalg.norm(X[i] - X[j]))
            dist_matrix[i, j] = d
            dist_matrix[j, i] = d

    # k-NN for each point
    knn = []
    for i in range(n):
        row = [(dist_matrix[i, j], j) for j in range(n) if j != i]
        row.sort()
        knn.append([j for _, j in row[:k]])

    # Triangular consistency: for each (i, j in knn[i]), is i in knn[j]?
    consistent = 0
    total = 0
    for i in range(n):
        for j in knn[i]:
            total += 1
            if i in knn[j]:
                consistent += 1

    consistency = consistent / max(1, total)

    # Mean nearest-neighbor distance (lower = more compact clusters)
    mean_nn_dist = float(np.mean([dist_matrix[i, knn[i][0]] for i in range(n)]))

    return {
        "knn_consistency": round(consistency, 4),
        "mean_nn_distance": round(mean_nn_dist, 4),
    }


# ---------------------------------------------------------------------------
# StructuralFitness: composite scorer
# ---------------------------------------------------------------------------

class StructuralFitness:
    """
    Composite structural fitness scorer.

    Weights:
      0.35 × projection_stability  (is the geometry real?)
      0.30 × orbit_stability       (is the vector a lattice invariant?)
      0.20 × lattice_utility       (does it form coherent clusters?)
      0.15 × cross_domain          (does structure persist across domains?)
    """
    W_PROJ   = 0.35
    W_ORBIT  = 0.30
    W_LATTICE = 0.20
    W_CROSS  = 0.15

    def score(
        self,
        chunks: List[List[str]],
        corpus_tokens: List[str],
        embedder: ChunkEmbedder,
        cross_chunks: List[List[str]] = None,
        cross_tokens: List[str] = None,
    ) -> Dict:
        s1 = track_s1_projection_stability(chunks, corpus_tokens, embedder)
        s2 = track_s2_orbit_stability(chunks, corpus_tokens, embedder)
        s4 = track_s4_lattice_utility(chunks, corpus_tokens, embedder)

        if cross_chunks and cross_tokens:
            s3 = track_s3_cross_domain_persistence(
                chunks, corpus_tokens, cross_chunks, cross_tokens, embedder
            )
        else:
            s3 = {"mean_cross_domain_persistence": 0.0}

        proj   = s1["mean_projection_stability"]
        orbit  = s2["mean_orbit_stability"]
        knn    = s4["knn_consistency"]
        cross  = s3["mean_cross_domain_persistence"]

        composite = (
            self.W_PROJ   * proj
            + self.W_ORBIT  * orbit
            + self.W_LATTICE * knn
            + self.W_CROSS  * cross
        )

        return {
            "projection_stability": proj,
            "orbit_stability": orbit,
            "knn_consistency": knn,
            "cross_domain_persistence": cross,
            "composite": round(composite, 4),
            "s1_detail": s1,
            "s2_detail": s2,
            "s4_detail": s4,
        }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 90)
    print("STRUCTURAL OLYMPICS")
    print("=" * 90)
    print()
    print("Question: Do H1 chunks have geometric structure that random/BPE chunks lack?")
    print("Null hypothesis: all methods score equivalently on structural metrics.")
    print()

    fitness = StructuralFitness()
    embedders = [
        RandomHashEmbedder(),
        StructuralFeatureEmbedder(),
        TFIDFEmbedder(),
    ]
    chunk_methods = [H1Method(), BPEMethod(), ASTMethod(), RandomMethod()]

    # Cross-domain reference: genomics
    genomics_corpus = " ".join(ALL_DOMAINS["genomics"]["structured"])
    genomics_tokens = genomics_corpus.split()
    genomics_chunks = [s.split() for s in ALL_DOMAINS["genomics"]["structured"]]

    # Run on A_cpython (largest, most structure)
    for class_name, samples in ALL_CODE.items():
        corpus = "\n\n".join(samples)
        tokens = corpus.split()
        print(f"\n{'='*70}")
        print(f"  Dataset: {class_name}  ({len(tokens)} tokens)")
        print(f"{'='*70}")

        for embedder in embedders:
            print(f"\n  Embedder: {embedder.name} ({embedder.dim}D)")
            print(f"  {'Method':<10} {'ProjStab':>10} {'OrbitStab':>10} {'kNN-Cons':>10} {'CrossDom':>10} {'COMPOSITE':>12}")
            print(f"  {'-'*64}")

            for method in chunk_methods:
                chunks = method.discover_chunks(corpus)
                if not chunks:
                    continue

                result = fitness.score(
                    chunks, tokens, embedder,
                    cross_chunks=genomics_chunks,
                    cross_tokens=genomics_tokens,
                )

                print(
                    f"  {method.name:<10} "
                    f"{result['projection_stability']:>10.4f} "
                    f"{result['orbit_stability']:>10.4f} "
                    f"{result['knn_consistency']:>10.4f} "
                    f"{result['cross_domain_persistence']:>10.4f} "
                    f"{result['composite']:>12.4f}"
                )

                record_run(
                    method=method.name,
                    dataset=f"{class_name}/{embedder.name}",
                    track="structural",
                    boundary_f1=result["projection_stability"],
                    compression=result["orbit_stability"],
                    reuse=result["knn_consistency"],
                    novelty=result["cross_domain_persistence"],
                    ci_95=[result["composite"], result["composite"]],
                )

    # Cross-domain structural test
    print(f"\n{'='*70}")
    print("  Cross-Domain Structural Test")
    print(f"  Source: A_cpython chunks → Target: genomics/math/music")
    print(f"{'='*70}")

    a_corpus = "\n\n".join(ALL_CODE["A_cpython"])
    a_tokens = a_corpus.split()

    for embedder in embedders:
        print(f"\n  Embedder: {embedder.name}")
        print(f"  {'Method':<10} {'→ genomics':>12} {'→ math':>12} {'→ music':>12}")
        print(f"  {'-'*48}")
        for method in [H1Method(), BPEMethod(), RandomMethod()]:
            chunks = method.discover_chunks(a_corpus)
            row = f"  {method.name:<10}"
            for domain_name, domain_data in ALL_DOMAINS.items():
                cross_corpus = " ".join(domain_data["structured"])
                cross_tokens = cross_corpus.split()
                cross_chunks = [s.split() for s in domain_data["structured"]]
                s3 = track_s3_cross_domain_persistence(
                    chunks, a_tokens, cross_chunks, cross_tokens, embedder
                )
                row += f" {s3['mean_cross_domain_persistence']:>12.4f}"
            print(row)

    print(f"\n{'='*90}")
    print("Structural Olympics complete.")
    print()
    print("Key interpretations:")
    print("  ProjStab > 0.5 → geometric structure is preserved under dimension reduction")
    print("  OrbitStab > 0.8 → vector is near-invariant under Weyl reflections (lattice point)")
    print("  kNN-Cons > 0.5 → chunks form coherent clusters in embedding space")
    print("  CrossDom > 0.3 → cross-domain relationships are stable under projection")
    print()
    print("If H1 ≈ Random on ALL embedders: the theory's chunking is irrelevant.")
    print("If H1 > Random on StructuralFeature but not RandomHash: the embedding is the problem.")
    print("If H1 > Random on ANY embedder: H1 discovers real structure.")
    print(f"{'='*90}")


if __name__ == "__main__":
    main()
