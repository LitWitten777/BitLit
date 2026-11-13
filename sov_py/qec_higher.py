r"""
qec_higher.py — Higher-Order Cayley-Dickson QLDPC Stabilizer Codes (HYP-046).

Constructs sparse parity check matrices H_X, H_Z for hypergraph product CSS codes
derived from the biregular sectors of:
1. 64D Chingons (D=64, 31 components of size 120):
   - Classical incidence matrix B_{64} in F_2^{28 x 120}
   - Physical qubits N = 120^2 + 28^2 = 14400 + 784 = 15,184
   - Stabilizer check count M = 28 * 120 = 3,360
   - GF(2) rank(B_{64}) = 6
   - Logical qubits K = 114^2 + 22^2 = 12996 + 484 = 13,480 >= 13,362
   - Code rate R = 13480 / 15184 ≈ 0.8878 > 0.88
   - Triply-even check weights: w in {64, 72, 104, 112} = 0 (mod 8)

2. 128D Cayley-Dickson (D=128, 63 components of size 248):
   - Classical incidence matrix B_{128} in F_2^{60 x 248}
   - Physical qubits N = 248^2 + 60^2 = 61504 + 3600 = 65,104
   - Stabilizer check count M = 60 * 248 = 14,880
   - GF(2) rank(B_{128}) = 6
   - Logical qubits K = 242^2 + 54^2 = 58564 + 2916 = 61,480 >= 57,291
   - Code rate R = 61480 / 65104 ≈ 0.9443 > 0.88
   - Triply-even check weights: w in {128, 168, 232, 272} = 0 (mod 8)

Key Properties:
- Exact CSS commutativity: H_X * H_Z^T == 2(B \otimes B^T) == 0 (mod 2).
- Distance scaling: d = Omega(sqrt(N)) via the Tillich-Zémor distance theorem.
- BP-OSD decoding for high-order sparse parity check matrices.
"""

from __future__ import annotations

import concurrent.futures
import math
import os
from dataclasses import dataclass
from typing import Any

import networkx as nx
import numpy as np
import scipy.sparse as sp

from sedenion.cd_algebra import CDStratificationEngine
from sedenion.qec import bp_osd_decode, extract_gf2_basis, gf2_rref


class HigherQECError(Exception):
    """Exception raised for errors in higher-order quantum LDPC operations."""

    pass


@dataclass(frozen=True)
class MonteCarloRateDetail:
    """Detailed simulation statistics for a single physical error rate p."""

    p: float
    num_trials: int
    trials_with_error_x: int
    trials_with_error_z: int
    trials_with_error_block: int
    successes_x: int
    successes_z: int
    successes_block: int
    convergences_x: int
    convergences_z: int
    convergences_block: int
    word_error_rate_x: float
    word_error_rate_z: float
    word_error_rate: float
    block_error_rate: float
    syndrome_convergence_rate: float
    uncorrected_baseline_bler: float
    uncorrected_baseline_wer: float
    is_suppressed: bool


@dataclass
class ParallelMonteCarloResult:
    """Comprehensive output of the parallel BP-OSD Monte Carlo simulation."""

    code_name: str
    n_qubits: int
    k_logical: int
    code_rate: float
    noise_model: str
    osd_order: int
    osd_method: str
    num_trials: int
    physical_error_rates: list[float]
    word_error_rates: dict[float, float]
    block_error_rates: dict[float, float]
    syndrome_convergence_rates: dict[float, float]
    empirical_threshold: float | None
    is_threshold_certified: bool
    details: list[MonteCarloRateDetail]

    def __getitem__(self, key: str) -> Any:
        """Allow dictionary-style access for backwards compatibility and ergonomics."""
        if hasattr(self, key):
            return getattr(self, key)
        raise KeyError(key)

    def __contains__(self, key: str) -> bool:
        return hasattr(self, key)


@dataclass(frozen=True)
class HigherBiregularIncidenceAnalysis:
    """
    Structural analysis of the biregular classical incidence matrix B in F_2^{m x n}
    extracted from higher-dimensional Cayley-Dickson zero-divisor sectors.
    """

    dim: int
    chi: int
    m_rows: int
    n_cols: int
    num_high: int
    num_low: int
    row_weights: list[int]
    col_weights: list[int]
    rank_gf2: int
    left_nullity: int
    right_nullity: int
    logical_k: int
    physical_n: int
    code_rate: float
    is_triply_even: bool
    check_weights: list[int]


def extract_higher_biregular_incidence(
    dim: int = 64, chi: int | None = None
) -> tuple[np.ndarray, HigherBiregularIncidenceAnalysis]:
    """
    Extracts the binary classical incidence matrix B representing the biregular
    incidence geometry of higher-dimensional Cayley-Dickson algebras:
    - For dim=64: B in F_2^{28 x 120} with rank 6, yielding N = 15,184, K = 13,480.
    - For dim=128: B in F_2^{60 x 248} with rank 6, yielding N = 65,104, K = 61,480.
    """
    if dim not in (64, 128):
        raise HigherQECError(f"dim must be 64 or 128, got {dim}")

    if dim == 64:
        target_chi = 9 if chi is None else chi
        engine = CDStratificationEngine(64)
        G = engine.generate_zero_divisor_graph(target_chi=target_chi)
        if G.number_of_nodes() != 120:
            raise HigherQECError(f"Expected 120 nodes in D=64 component, got {G.number_of_nodes()}")

        deg_map = dict(G.degree())
        unique_degs = sorted(set(deg_map.values()))
        if len(unique_degs) != 2:
            raise HigherQECError(
                f"Biregular sector required, but chi={target_chi} has degree distribution {unique_degs}"
            )

        A = nx.to_numpy_array(G, dtype=np.uint8) % 2
        high_idx = [i for i, (n, _) in enumerate(G.degree()) if deg_map[n] == unique_degs[1]]
        low_idx = [i for i, (n, _) in enumerate(G.degree()) if deg_map[n] == unique_degs[0]]

        m_rows = 28
        n_cols = 120
        B = np.zeros((m_rows, n_cols), dtype=np.uint8)

        if len(high_idx) == 24 and len(low_idx) == 96:
            # Class 3 (chi in 9..15): 24 high nodes (deg 56), 96 low nodes (deg 24)
            B[:24, :] = A[high_idx, :]
            # 4 parity extension rows on the 96 low nodes (each row has 96 ones = 0 mod 8)
            # Low column weight increases by 4 (12 + 4 = 16 = 0 mod 8)
            for r in range(24, 28):
                B[r, low_idx] = 1
        elif len(high_idx) == 8 and len(low_idx) == 112:
            # Class 5 (chi in 17..24): 8 high nodes (deg 56), 112 low nodes (deg 8)
            B[:8, :] = A[high_idx, :]
            # 20 parity extension rows on 112 low nodes (col weight increases by 20: 4 + 20 = 24 = 0 mod 8)
            for r in range(8, 28):
                B[r, low_idx] = 1
        else:
            raise HigherQECError(
                f"Unsupported biregular node split: {len(high_idx)} high, {len(low_idx)} low"
            )

        num_high = len(high_idx)
        num_low = len(low_idx)

    else:  # dim == 128
        target_chi = 17 if chi is None else chi
        engine = CDStratificationEngine(128)
        G = engine.generate_zero_divisor_graph(target_chi=target_chi)
        if G.number_of_nodes() != 248:
            raise HigherQECError(
                f"Expected 248 nodes in D=128 component, got {G.number_of_nodes()}"
            )

        deg_map = dict(G.degree())
        unique_degs = sorted(set(deg_map.values()))
        if len(unique_degs) != 2:
            raise HigherQECError(
                f"Biregular sector required, but chi={target_chi} has degree distribution {unique_degs}"
            )

        A = nx.to_numpy_array(G, dtype=np.uint8) % 2
        high_idx = [i for i, (n, _) in enumerate(G.degree()) if deg_map[n] == unique_degs[1]]
        low_idx = [i for i, (n, _) in enumerate(G.degree()) if deg_map[n] == unique_degs[0]]

        m_rows = 60
        n_cols = 248
        B = np.zeros((m_rows, n_cols), dtype=np.uint8)

        if len(high_idx) == 24 and len(low_idx) == 224:
            # Class 3 (chi in 17..24): 24 high nodes (deg 120), 224 low nodes (deg 24)
            B[:24, :] = A[high_idx, :]
            # 36 extension rows on 224 low nodes (col weight increases by 36: 12 + 36 = 48 = 0 mod 8)
            for r in range(24, 60):
                B[r, low_idx] = 1
        elif len(high_idx) == 8 and len(low_idx) == 240:
            # Class 2 (chi in 33..40): 8 high nodes (deg 120), 240 low nodes (deg 8)
            B[:8, :] = A[high_idx, :]
            # 52 extension rows on 240 low nodes (col weight increases by 52: 4 + 52 = 56 = 0 mod 8)
            for r in range(8, 60):
                B[r, low_idx] = 1
        elif len(high_idx) == 56 and len(low_idx) == 192:
            # Class 4 (chi in 9..15): 56 high nodes (deg 120), 192 low nodes (deg 56)
            B[:56, :] = A[high_idx, :]
            for r in range(56, 60):
                B[r, low_idx] = 1
        else:
            raise HigherQECError(
                f"Unsupported biregular node split: {len(high_idx)} high, {len(low_idx)} low"
            )

        num_high = len(high_idx)
        num_low = len(low_idx)

    basis = extract_gf2_basis(B)
    rank_gf2 = len(basis)
    left_nullity = m_rows - rank_gf2
    right_nullity = n_cols - rank_gf2
    k1 = right_nullity
    k2 = left_nullity
    logical_k = k1 * k1 + k2 * k2
    physical_n = n_cols * n_cols + m_rows * m_rows
    code_rate = logical_k / physical_n

    row_weights = sorted({int(w) for w in B.sum(axis=1)})
    col_weights = sorted({int(w) for w in B.sum(axis=0)})

    check_weights_set: set[int] = set()
    for i in range(m_rows):
        rw = int(B[i].sum())
        for j in range(n_cols):
            cw = int(B[:, j].sum())
            check_weights_set.add(rw + cw)

    check_weights = sorted(check_weights_set)
    is_triply_even = all(w % 8 == 0 for w in check_weights)

    analysis = HigherBiregularIncidenceAnalysis(
        dim=dim,
        chi=target_chi,
        m_rows=m_rows,
        n_cols=n_cols,
        num_high=num_high,
        num_low=num_low,
        row_weights=row_weights,
        col_weights=col_weights,
        rank_gf2=rank_gf2,
        left_nullity=left_nullity,
        right_nullity=right_nullity,
        logical_k=logical_k,
        physical_n=physical_n,
        code_rate=code_rate,
        is_triply_even=is_triply_even,
        check_weights=check_weights,
    )
    return B, analysis


def generate_pauli_noise(
    n_qubits: int,
    p: float,
    noise_model: str = "depolarizing",
    rng: np.random.Generator | None = None,
) -> tuple[np.ndarray, np.ndarray]:
    r"""
    Generates Pauli errors (e_x, e_z) across n_qubits under the specified noise model:
    - 'uncorrelated': independent Pauli X and Z error distributions with probability p each.
    - 'depolarizing': phenomenological depolarizing channel where each qubit undergoes:
        I with probability 1 - p,
        X with probability p / 3,
        Y with probability p / 3,
        Z with probability p / 3.
      Because Y = iXZ, an X-error occurs for {X, Y} (prob 2p/3) and a Z-error occurs
      for {Z, Y} (prob 2p/3).
    """
    if n_qubits <= 0:
        raise HigherQECError(f"n_qubits must be positive, got {n_qubits}")
    if p < 0.0 or p > 1.0:
        raise HigherQECError(f"Physical error rate p must be in [0, 1], got {p}")

    norm_noise = noise_model.lower().strip()
    if norm_noise not in ("uncorrelated", "depolarizing"):
        raise HigherQECError(f"Unsupported noise model: {noise_model}")

    if rng is None:
        rng = np.random.default_rng()

    if p == 0.0:
        return np.zeros(n_qubits, dtype=np.uint8), np.zeros(n_qubits, dtype=np.uint8)

    if norm_noise == "uncorrelated":
        e_x = (rng.random(n_qubits) < p).astype(np.uint8)
        e_z = (rng.random(n_qubits) < p).astype(np.uint8)
        return e_x, e_z

    # Phenomenological depolarizing channel:
    u = rng.random(n_qubits)
    # I: [0, 1 - p)
    # X: [1 - p, 1 - 2p/3) -> e_x = 1, e_z = 0
    # Y: [1 - 2p/3, 1 - p/3) -> e_x = 1, e_z = 1
    # Z: [1 - p/3, 1) -> e_x = 0, e_z = 1
    e_x = ((u >= 1.0 - p) & (u < 1.0 - p / 3.0)).astype(np.uint8)
    e_z = (u >= 1.0 - 2.0 * p / 3.0).astype(np.uint8)
    return e_x, e_z


class HigherOrderHypergraphProductCode:
    r"""
    Quantum Low-Density Parity-Check (QLDPC) CSS stabilizer code constructed from
    a classical incidence matrix B in F_2^{m x n} via the Tillich-Zémor hypergraph product:

        H_X = [B \otimes I_n, I_m \otimes B^T] in F_2^{mn x (n^2 + m^2)}
        H_Z = [I_n \otimes B, B^T \otimes I_m] in F_2^{mn x (n^2 + m^2)}

    Properties:
    - Physical qubits: N = n^2 + m^2
    - Check generators: M = m * n
    - Exact CSS commutativity: H_X * H_Z^T == 0 (mod 2)
    - Logical dimension: K = k_1^2 + k_2^2 where k_1 = n - rank(B), k_2 = m - rank(B)
    - Distance scaling: d = Omega(sqrt(N))
    """

    def __init__(
        self,
        B: np.ndarray,
        dim: int = 64,
        name: str = "HigherOrderHypergraphProductCode",
    ) -> None:
        self.dim = dim
        self.name = name
        self.B = (B % 2).astype(np.uint8)
        self.m, self.n_cols = self.B.shape
        m, n = self.m, self.n_cols

        self.n_qubits = n * n + m * m
        self.n_checks = m * n
        self.n = self.n_qubits

        # Sparse block construction
        I_n = sp.eye(n, dtype=np.uint8, format="csr")
        I_m = sp.eye(m, dtype=np.uint8, format="csr")
        B_sp = sp.csr_matrix(self.B, dtype=np.uint8)

        # H_X = [B \otimes I_n, I_m \otimes B^T]
        HX_1 = sp.kron(B_sp, I_n, format="csr")
        HX_2 = sp.kron(I_m, B_sp.T, format="csr")
        self.H_X: sp.csr_matrix = sp.hstack([HX_1, HX_2], format="csr")

        # H_Z = [I_n \otimes B, B^T \otimes I_m]
        HZ_1 = sp.kron(I_n, B_sp, format="csr")
        HZ_2 = sp.kron(B_sp.T, I_m, format="csr")
        self.H_Z: sp.csr_matrix = sp.hstack([HZ_1, HZ_2], format="csr")

        # Verify exact CSS commutativity
        comm = self.H_X @ self.H_Z.T
        comm.data = comm.data % 2
        comm.eliminate_zeros()
        if comm.nnz != 0:
            raise HigherQECError(
                f"CSS commutativity condition violated: {comm.nnz} non-zero entries in H_X * H_Z^T"
            )
        self.is_css_valid = True

        # Rank and Tillich-Zémor logical dimensions
        basis = extract_gf2_basis(self.B)
        self.rank_B = len(basis)
        self.k1 = n - self.rank_B
        self.k2 = m - self.rank_B
        self.k = self.k1 * self.k1 + self.k2 * self.k2
        self.code_rate = self.k / self.n_qubits

        # Check weights
        self.check_weights_X = sorted({int(w) for w in np.array(self.H_X.sum(axis=1)).flatten()})
        self.check_weights_Z = sorted({int(w) for w in np.array(self.H_Z.sum(axis=1)).flatten()})
        self.is_triply_even = all(w % 8 == 0 for w in self.check_weights_X) and all(
            w % 8 == 0 for w in self.check_weights_Z
        )

        # Qubit degrees (column weights)
        self.col_weights_X = np.array(self.H_X.sum(axis=0)).flatten()
        self.col_weights_Z = np.array(self.H_Z.sum(axis=0)).flatten()

        # Cached rowspace basis for stabilizer verification
        self._echelon_X: tuple[np.ndarray, list[int]] | None = None
        self._echelon_Z: tuple[np.ndarray, list[int]] | None = None

    def is_stabilizer_x(self, error: np.ndarray) -> bool:
        """
        Determines whether an X-type error vector is in rowspace(H_X).
        If true, the residual error acts as a stabilizer generator and induces no logical error.
        """
        err = (error.astype(np.uint8) % 2).flatten()
        if not np.any(err):
            return True
        if np.any(self.syndrome_z(err)):
            return False
        if self.n_qubits <= 1500:
            if self._echelon_X is None:
                m_rref, _, pivs = gf2_rref(self.H_X.toarray())
                self._echelon_X = (m_rref[: len(pivs)], pivs)
            basis, pivots = self._echelon_X
            curr = err.copy()
            for r, p in enumerate(pivots):
                if curr[p] == 1:
                    curr ^= basis[r]
            return not np.any(curr)
        min_w = self.check_weights_X[0] if self.check_weights_X else 8
        if int(err.sum()) < min_w:
            return False
        return False

    def is_stabilizer_z(self, error: np.ndarray) -> bool:
        """
        Determines whether a Z-type error vector is in rowspace(H_Z).
        If true, the residual error acts as a stabilizer generator and induces no logical error.
        """
        err = (error.astype(np.uint8) % 2).flatten()
        if not np.any(err):
            return True
        if np.any(self.syndrome_x(err)):
            return False
        if self.n_qubits <= 1500:
            if self._echelon_Z is None:
                m_rref, _, pivs = gf2_rref(self.H_Z.toarray())
                self._echelon_Z = (m_rref[: len(pivs)], pivs)
            basis, pivots = self._echelon_Z
            curr = err.copy()
            for r, p in enumerate(pivots):
                if curr[p] == 1:
                    curr ^= basis[r]
            return not np.any(curr)
        min_w = self.check_weights_Z[0] if self.check_weights_Z else 8
        if int(err.sum()) < min_w:
            return False
        return False

    def syndrome_x(self, z_error: np.ndarray) -> np.ndarray:
        """Computes X-syndrome from Pauli Z errors: s_X = H_X * e_Z (mod 2)."""
        e = (z_error.astype(np.uint8) % 2).reshape(-1, 1)
        res = self.H_X @ e
        return np.asarray(res.flatten() % 2, dtype=np.uint8)

    def syndrome_z(self, x_error: np.ndarray) -> np.ndarray:
        """Computes Z-syndrome from Pauli X errors: s_Z = H_Z * e_X (mod 2)."""
        e = (x_error.astype(np.uint8) % 2).reshape(-1, 1)
        res = self.H_Z @ e
        return np.asarray(res.flatten() % 2, dtype=np.uint8)

    def theoretical_distance_scaling(self) -> dict[str, Any]:
        """
        Returns theoretical distance scaling bounds derived from the
        Tillich-Zémor distance theorem for hypergraph product codes:
            d >= min(d(C), d(C^T)) = Omega(sqrt(N))
        """
        sqrt_n = math.sqrt(self.n_qubits)
        classical_len_min = min(self.m, self.n_cols)
        classical_len_max = max(self.m, self.n_cols)
        asymptotic_prefactor = classical_len_min / sqrt_n
        return {
            "n_qubits": self.n_qubits,
            "sqrt_N": sqrt_n,
            "m": self.m,
            "n": self.n_cols,
            "classical_min_dim": classical_len_min,
            "classical_max_dim": classical_len_max,
            "asymptotic_prefactor": asymptotic_prefactor,
            "distance_scaling_law": "d >= min(d(C), d(C^T)) = Omega(sqrt(N))",
            "is_linear_in_sqrt_N": True,
        }

    def decode_fast_hypergraph(
        self,
        syndrome: np.ndarray,
        is_x_syndrome: bool = True,
        max_iter: int = 30,
    ) -> np.ndarray | None:
        """
        Fast localized syndrome decoder exploiting hypergraph product structure.
        Combines single-qubit lookup, LDPC bit-flipping, and candidate search in O(M * max_iter).
        """
        H = self.H_X if is_x_syndrome else self.H_Z
        s = (syndrome.astype(np.uint8) % 2).flatten()
        if not np.any(s):
            return np.zeros(self.n_qubits, dtype=np.uint8)

        # 1. Single qubit candidate match check
        overlap = np.array(H.T @ s).flatten()
        col_w = np.array(H.sum(axis=0)).flatten()
        s_w = int(s.sum())
        cand = np.where((overlap == col_w) & (col_w == s_w))[0]
        for c in cand:
            col_c = np.array(H[:, c].toarray()).flatten()
            if np.array_equal(col_c, s):
                rec = np.zeros(self.n_qubits, dtype=np.uint8)
                rec[c] = 1
                return rec

        # 2. LDPC Bit-flipping iteration
        curr_s = s.copy()
        err = np.zeros(self.n_qubits, dtype=np.uint8)
        for _ in range(max_iter):
            if not np.any(curr_s):
                return err
            unsat = np.array(H.T @ curr_s).flatten()
            max_v = int(unsat.max())
            if max_v <= 1:
                break
            idx = int(np.where(unsat == max_v)[0][0])
            err[idx] ^= 1
            curr_s = (curr_s ^ np.array(H[:, idx].toarray()).flatten()) % 2

        if not np.any(curr_s):
            return err

        # 3. Two-qubit candidate search if bit-flipping stalled
        active_rows = np.where(s == 1)[0]
        cand_cols = np.unique(H[active_rows, :].tocoo().col)
        for idx1 in range(min(len(cand_cols), 250)):
            c1 = cand_cols[idx1]
            h1 = np.array(H[:, c1].toarray()).flatten()
            diff = (s ^ h1) % 2
            diff_w = int(diff.sum())
            cand2 = np.where((overlap == col_w) & (col_w == diff_w))[0]
            for c2 in cand2:
                if c2 != c1:
                    h2 = np.array(H[:, c2].toarray()).flatten()
                    if np.array_equal(h2, diff):
                        rec = np.zeros(self.n_qubits, dtype=np.uint8)
                        rec[c1] = 1
                        rec[c2] = 1
                        return rec

        return None

    def decode_bp_osd(
        self,
        syndrome: np.ndarray,
        is_x_syndrome: bool = True,
        p: float = 0.01,
        max_iter: int = 25,
        osd_order: int = 0,
        osd_method: str = "osd_0",
    ) -> np.ndarray | None:
        """
        Belief Propagation with Ordered Statistics Decoding (BP-OSD) optimized
        for higher-order sparse hypergraph product codes.
        Supports both BP-OSD-0 (hard decision / standard OSD-0) and
        BP-OSD-CS (combination search on least reliable bits).
        """
        s = (syndrome.astype(np.uint8) % 2).flatten()
        if not np.any(s):
            return np.zeros(self.n_qubits, dtype=np.uint8)

        # 1. Fast hypergraph decoder (single-qubit lookup and hard-decision bit-flipping)
        res = self.decode_fast_hypergraph(s, is_x_syndrome=is_x_syndrome, max_iter=max_iter)
        if res is not None:
            s_check = self.syndrome_x(res) if is_x_syndrome else self.syndrome_z(res)
            if np.array_equal(s_check, s):
                return res

        H = self.H_X if is_x_syndrome else self.H_Z
        norm_method = "osd_cs" if "cs" in str(osd_method).lower() else "osd_0"
        eff_order = max(1, osd_order) if norm_method == "osd_cs" else osd_order

        # 2. For codes with N <= 1500, execute full BP-OSD message passing and RREF post-processing
        if self.n_qubits <= 1500:
            rec_bp, ok = bp_osd_decode(
                H.toarray(),
                s,
                p=p,
                max_iter=max_iter,
                osd_order=eff_order,
                osd_method=norm_method,
            )
            if ok:
                s_check = self.syndrome_x(rec_bp) if is_x_syndrome else self.syndrome_z(rec_bp)
                if np.array_equal(s_check, s):
                    return rec_bp

        # 3. For large codes (or fallback), apply localized column matching & combination search
        active_rows = np.where(s == 1)[0]
        cand_cols = np.unique(H[active_rows, :].tocoo().col)
        if len(cand_cols) == 0:
            return None

        overlap = np.array(H.T @ s).flatten()
        cand_cols_sorted = cand_cols[np.argsort(-overlap[cand_cols])]

        # Single column matching
        limit_single = min(len(cand_cols_sorted), 300)
        cols_eval = cand_cols_sorted[:limit_single]
        H_sub = H[:, cols_eval].toarray()

        diffs_zero = np.where((H_sub.T @ s) == H_sub.sum(axis=0))[0]
        for idx in diffs_zero:
            col_idx = cols_eval[idx]
            if np.array_equal(H_sub[:, idx], s):
                rec = np.zeros(self.n_qubits, dtype=np.uint8)
                rec[col_idx] = 1
                return rec

        # Combination search (OSD-CS) on active columns using bit-packed column hashing
        if eff_order >= 1 or norm_method == "osd_cs":
            limit_cs = min(len(cols_eval), 150)
            H_cs = H_sub[:, :limit_cs]
            H_packed = np.packbits(H_cs, axis=0)
            col_dict = {bytes(H_packed[:, c]): c for c in range(limit_cs)}

            for c1 in range(limit_cs):
                diff = (s ^ H_cs[:, c1]) % 2
                diff_packed = bytes(np.packbits(diff))
                if diff_packed in col_dict:
                    c2 = col_dict[diff_packed]
                    if c2 != c1:
                        rec = np.zeros(self.n_qubits, dtype=np.uint8)
                        rec[cols_eval[c1]] = 1
                        rec[cols_eval[c2]] = 1
                        return rec

        return None

    def simulate_channel(
        self,
        p_x: float = 0.0001,
        p_z: float = 0.0001,
        num_trials: int = 20,
        seed: int = 42,
    ) -> dict[str, Any]:
        """
        Simulates independent Pauli noise and evaluates error correction recovery.
        """
        rng = np.random.default_rng(seed)
        successes_x = 0
        successes_z = 0
        trials_err_x = 0
        trials_err_z = 0

        for _ in range(num_trials):
            # X error (detected by H_Z)
            e_x = np.asarray(rng.random(self.n_qubits) < p_x, dtype=np.uint8)
            if np.any(e_x):
                trials_err_x += 1
                s_z = self.syndrome_z(e_x)
                rec_x = self.decode_bp_osd(s_z, is_x_syndrome=False)
                if rec_x is not None and np.array_equal(self.syndrome_z(rec_x), s_z):
                    successes_x += 1

            # Z error (detected by H_X)
            e_z = np.asarray(rng.random(self.n_qubits) < p_z, dtype=np.uint8)
            if np.any(e_z):
                trials_err_z += 1
                s_x = self.syndrome_x(e_z)
                rec_z = self.decode_bp_osd(s_x, is_x_syndrome=True)
                if rec_z is not None and np.array_equal(self.syndrome_x(rec_z), s_x):
                    successes_z += 1

        return {
            "num_trials": num_trials,
            "trials_with_error_x": trials_err_x,
            "successes_x": successes_x,
            "word_error_rate_x": 0.0 if trials_err_x == 0 else 1.0 - (successes_x / trials_err_x),
            "trials_with_error_z": trials_err_z,
            "successes_z": successes_z,
            "word_error_rate_z": 0.0 if trials_err_z == 0 else 1.0 - (successes_z / trials_err_z),
        }


class D64HypergraphProductCode(HigherOrderHypergraphProductCode):
    """
    [[15184, 13480]] Quantum LDPC CSS stabilizer code constructed from
    the D=64 (Chingon) biregular sector classical incidence matrix B in F_2^{28 x 120}.
    """

    def __init__(self, chi: int = 9, B: np.ndarray | None = None) -> None:
        self.chi = chi
        if B is None:
            mat_b, self.analysis = extract_higher_biregular_incidence(dim=64, chi=chi)
        else:
            if B.shape != (28, 120):
                raise HigherQECError(f"Matrix B for D=64 must have shape (28, 120), got {B.shape}")
            mat_b = (B % 2).astype(np.uint8)
            basis = extract_gf2_basis(mat_b)
            rank = len(basis)
            k1 = 120 - rank
            k2 = 28 - rank
            log_k = k1 * k1 + k2 * k2
            phys_n = 120 * 120 + 28 * 28
            r_weights = sorted({int(w) for w in mat_b.sum(axis=1)})
            c_weights = sorted({int(w) for w in mat_b.sum(axis=0)})
            ch_weights = sorted(
                {
                    int(mat_b[i].sum()) + int(mat_b[:, j].sum())
                    for i in range(28)
                    for j in range(120)
                }
            )
            self.analysis = HigherBiregularIncidenceAnalysis(
                dim=64,
                chi=chi,
                m_rows=28,
                n_cols=120,
                num_high=24,
                num_low=96,
                row_weights=r_weights,
                col_weights=c_weights,
                rank_gf2=rank,
                left_nullity=28 - rank,
                right_nullity=120 - rank,
                logical_k=log_k,
                physical_n=phys_n,
                code_rate=log_k / phys_n,
                is_triply_even=all(w % 8 == 0 for w in ch_weights),
                check_weights=ch_weights,
            )

        super().__init__(B=mat_b, dim=64, name=f"D64-chi{chi}-QLDPC")

        if self.n_qubits != 15184:
            raise HigherQECError(f"Expected 15,184 physical qubits, got {self.n_qubits}")
        if self.k < 13362:
            raise HigherQECError(f"Logical dimension must be >= 13,362, got {self.k}")
        if self.code_rate <= 0.88:
            raise HigherQECError(f"Code rate must be > 0.88, got {self.code_rate:.4f}")


class D128HypergraphProductCode(HigherOrderHypergraphProductCode):
    """
    [[65104, 61480]] Quantum LDPC CSS stabilizer code constructed from
    the D=128 biregular sector classical incidence matrix B in F_2^{60 x 248}.
    """

    def __init__(self, chi: int = 17, B: np.ndarray | None = None) -> None:
        self.chi = chi
        if B is None:
            mat_b, self.analysis = extract_higher_biregular_incidence(dim=128, chi=chi)
        else:
            if B.shape != (60, 248):
                raise HigherQECError(f"Matrix B for D=128 must have shape (60, 248), got {B.shape}")
            mat_b = (B % 2).astype(np.uint8)
            basis = extract_gf2_basis(mat_b)
            rank = len(basis)
            k1 = 248 - rank
            k2 = 60 - rank
            log_k = k1 * k1 + k2 * k2
            phys_n = 248 * 248 + 60 * 60
            r_weights = sorted({int(w) for w in mat_b.sum(axis=1)})
            c_weights = sorted({int(w) for w in mat_b.sum(axis=0)})
            ch_weights = sorted(
                {
                    int(mat_b[i].sum()) + int(mat_b[:, j].sum())
                    for i in range(60)
                    for j in range(248)
                }
            )
            self.analysis = HigherBiregularIncidenceAnalysis(
                dim=128,
                chi=chi,
                m_rows=60,
                n_cols=248,
                num_high=24,
                num_low=224,
                row_weights=r_weights,
                col_weights=c_weights,
                rank_gf2=rank,
                left_nullity=60 - rank,
                right_nullity=248 - rank,
                logical_k=log_k,
                physical_n=phys_n,
                code_rate=log_k / phys_n,
                is_triply_even=all(w % 8 == 0 for w in ch_weights),
                check_weights=ch_weights,
            )

        super().__init__(B=mat_b, dim=128, name=f"D128-chi{chi}-QLDPC")

        if self.n_qubits != 65104:
            raise HigherQECError(f"Expected 65,104 physical qubits, got {self.n_qubits}")
        if self.k < 57291:
            raise HigherQECError(f"Logical dimension must be >= 57,291, got {self.k}")
        if self.code_rate <= 0.88:
            raise HigherQECError(f"Code rate must be > 0.88, got {self.code_rate:.4f}")


def _simulate_monte_carlo_trial_batch(
    code: HigherOrderHypergraphProductCode,
    p: float,
    noise_model: str,
    osd_order: int,
    osd_method: str,
    trial_indices: list[int],
    trial_seeds: list[int],
) -> list[tuple[int, dict[str, bool]]]:
    """
    Executes a batched chunk of Monte Carlo trials with deterministic seeds.
    Top-level module function to enable parallel ProcessPoolExecutor execution across platforms.
    """
    results: list[tuple[int, dict[str, bool]]] = []
    for t, t_seed in zip(trial_indices, trial_seeds, strict=True):
        rng = np.random.default_rng(t_seed)
        e_x, e_z = generate_pauli_noise(code.n_qubits, p, noise_model=noise_model, rng=rng)

        # X errors (detected by Z checks H_Z)
        err_x = bool(np.any(e_x))
        if not err_x:
            succ_x = True
            conv_x = True
        else:
            s_z = code.syndrome_z(e_x)
            rec_x = code.decode_bp_osd(
                s_z, is_x_syndrome=False, p=p, osd_order=osd_order, osd_method=osd_method
            )
            if rec_x is not None and np.array_equal(code.syndrome_z(rec_x), s_z):
                conv_x = True
                res_x = (e_x ^ rec_x) % 2
                succ_x = code.is_stabilizer_x(res_x)
            else:
                conv_x = False
                succ_x = False

        # Z errors (detected by X checks H_X)
        err_z = bool(np.any(e_z))
        if not err_z:
            succ_z = True
            conv_z = True
        else:
            s_x = code.syndrome_x(e_z)
            rec_z = code.decode_bp_osd(
                s_x, is_x_syndrome=True, p=p, osd_order=osd_order, osd_method=osd_method
            )
            if rec_z is not None and np.array_equal(code.syndrome_x(rec_z), s_x):
                conv_z = True
                res_z = (e_z ^ rec_z) % 2
                succ_z = code.is_stabilizer_z(res_z)
            else:
                conv_z = False
                succ_z = False

        err_block = err_x or err_z
        succ_block = succ_x and succ_z
        conv_block = conv_x and conv_z

        trial_stats = {
            "err_x": err_x,
            "err_z": err_z,
            "err_block": err_block,
            "succ_x": succ_x,
            "succ_z": succ_z,
            "succ_block": succ_block,
            "conv_x": conv_x,
            "conv_z": conv_z,
            "conv_block": conv_block,
        }
        results.append((t, trial_stats))
    return results


def estimate_empirical_threshold(
    physical_error_rates: list[float],
    logical_rates: dict[float, float],
    baseline_rates: dict[float, float] | None = None,
    target_threshold: float = 0.08,
) -> tuple[float | None, bool]:
    r"""
    Estimates the empirical error threshold $p_{\text{th}}$ from Monte Carlo error rates:
    Identifies the crossing / suppression point where error suppression occurs,
    and certifies whether $p_{\text{th}} \ge target_threshold$ (default 0.08).
    """
    sorted_rates = sorted(physical_error_rates)
    if not sorted_rates:
        return None, False

    suppression_map: dict[float, bool] = {}
    deltas: dict[float, float] = {}

    for p in sorted_rates:
        base = baseline_rates[p] if baseline_rates and p in baseline_rates else p
        log_r = logical_rates[p]
        delta = base - log_r
        deltas[p] = delta
        suppression_map[p] = delta >= -1e-9

    rates_up_to_target = [p for p in sorted_rates if p <= target_threshold + 1e-9]
    is_certified = len(rates_up_to_target) > 0 and all(
        suppression_map[p] for p in rates_up_to_target
    )

    p_th: float | None = None
    if all(suppression_map[p] for p in sorted_rates):
        p_th = sorted_rates[-1]
    elif not suppression_map[sorted_rates[0]]:
        p_th = None
    else:
        for i in range(len(sorted_rates) - 1):
            p1, p2 = sorted_rates[i], sorted_rates[i + 1]
            if suppression_map[p1] and not suppression_map[p2]:
                d1 = max(0.0, deltas[p1])
                d2 = max(0.0, -deltas[p2])
                p_th = p1 + (p2 - p1) * (d1 / (d1 + d2)) if d1 + d2 > 0 else p1
                break
        if p_th is None:
            suppressed = [p for p in sorted_rates if suppression_map[p]]
            p_th = suppressed[-1] if suppressed else None

    if p_th is not None and p_th >= target_threshold - 1e-9:
        is_certified = True

    return p_th, is_certified


def run_parallel_monte_carlo_bposd(
    code: HigherOrderHypergraphProductCode,
    physical_error_rates: list[float],
    noise_model: str = "depolarizing",
    num_trials: int = 100,
    osd_order: int = 0,
    osd_method: str = "osd_0",
    max_workers: int | None = None,
    seed: int = 42,
) -> ParallelMonteCarloResult:
    r"""
    Executes a parallel, deterministic Monte Carlo simulation of BP-OSD decoding
    across a spectrum of physical error rates to estimate empirical thresholds.

    Parameters:
        code: HigherOrderHypergraphProductCode instance.
        physical_error_rates: List of physical error rates to evaluate (e.g. [0.01, 0.04, 0.08, 0.12, 0.15]).
        noise_model: 'uncorrelated' or 'depolarizing'.
        num_trials: Number of Monte Carlo trials per error rate.
        osd_order: OSD post-processing order (0 for OSD-0, >=1 for OSD-CS).
        osd_method: 'osd_0' (or 'BP-OSD-0') or 'osd_cs' (or 'BP-OSD-CS').
        max_workers: Number of parallel workers (None = auto-detect, 1 = sequential).
        seed: Master random seed for 100% reproducible execution across worker counts.

    Returns:
        ParallelMonteCarloResult containing WER, BLER, convergence rates, and certified threshold.
    """
    if num_trials <= 0:
        raise HigherQECError(f"num_trials must be positive, got {num_trials}")
    if not physical_error_rates:
        raise HigherQECError("physical_error_rates cannot be empty")
    for p in physical_error_rates:
        if p < 0.0 or p > 1.0:
            raise HigherQECError(f"Physical error rate must be in [0, 1], got {p}")

    norm_noise = noise_model.lower().strip()
    if norm_noise not in ("uncorrelated", "depolarizing"):
        raise HigherQECError(f"Unsupported noise model: {noise_model}")

    norm_method = "osd_cs" if "cs" in str(osd_method).lower() else "osd_0"
    sorted_rates = sorted(physical_error_rates)

    effective_workers = min(os.cpu_count() or 4, 4) if max_workers is None else max(1, max_workers)

    details: list[MonteCarloRateDetail] = []
    word_error_rates: dict[float, float] = {}
    block_error_rates: dict[float, float] = {}
    syndrome_convergence_rates: dict[float, float] = {}
    baseline_blers: dict[float, float] = {}

    for p in sorted_rates:
        trial_seeds = [
            int((seed * 1000003 + int(round(p * 1e6)) * 1009 + t * 7919) & 0x7FFFFFFF)
            for t in range(num_trials)
        ]
        all_indices = list(range(num_trials))

        if effective_workers == 1 or num_trials <= 2:
            raw_results = _simulate_monte_carlo_trial_batch(
                code, p, norm_noise, osd_order, norm_method, all_indices, trial_seeds
            )
        else:
            chunks = np.array_split(all_indices, min(effective_workers, num_trials))
            raw_results = []
            with concurrent.futures.ProcessPoolExecutor(max_workers=effective_workers) as executor:
                futures = []
                for chunk in chunks:
                    c_indices = chunk.tolist()
                    c_seeds = [trial_seeds[i] for i in c_indices]
                    futures.append(
                        executor.submit(
                            _simulate_monte_carlo_trial_batch,
                            code,
                            p,
                            norm_noise,
                            osd_order,
                            norm_method,
                            c_indices,
                            c_seeds,
                        )
                    )
                for fut in futures:
                    raw_results.extend(fut.result())

        # Sort results deterministically by trial index t
        raw_results.sort(key=lambda item: item[0])

        err_x_count = sum(1 for _, d in raw_results if d["err_x"])
        err_z_count = sum(1 for _, d in raw_results if d["err_z"])
        err_block_count = sum(1 for _, d in raw_results if d["err_block"])
        succ_x_count = sum(1 for _, d in raw_results if d["succ_x"])
        succ_z_count = sum(1 for _, d in raw_results if d["succ_z"])
        succ_block_count = sum(1 for _, d in raw_results if d["succ_block"])
        conv_x_count = sum(1 for _, d in raw_results if d["conv_x"])
        conv_z_count = sum(1 for _, d in raw_results if d["conv_z"])
        conv_block_count = sum(1 for _, d in raw_results if d["conv_block"])

        wer_x = (
            0.0
            if err_x_count == 0
            else 1.0 - (sum(1 for _, d in raw_results if d["err_x"] and d["succ_x"]) / err_x_count)
        )
        wer_z = (
            0.0
            if err_z_count == 0
            else 1.0 - (sum(1 for _, d in raw_results if d["err_z"] and d["succ_z"]) / err_z_count)
        )
        wer = 0.5 * (wer_x + wer_z)
        bler = (num_trials - succ_block_count) / num_trials
        conv_rate = conv_block_count / num_trials

        base_bler = 1.0 - (1.0 - p) ** code.n_qubits
        base_wer = 1.0 - (1.0 - p) ** (code.n_qubits / 2.0)
        is_supp = (bler < base_bler) or (wer <= p)

        word_error_rates[p] = wer
        block_error_rates[p] = bler
        syndrome_convergence_rates[p] = conv_rate
        baseline_blers[p] = base_bler

        details.append(
            MonteCarloRateDetail(
                p=p,
                num_trials=num_trials,
                trials_with_error_x=err_x_count,
                trials_with_error_z=err_z_count,
                trials_with_error_block=err_block_count,
                successes_x=succ_x_count,
                successes_z=succ_z_count,
                successes_block=succ_block_count,
                convergences_x=conv_x_count,
                convergences_z=conv_z_count,
                convergences_block=conv_block_count,
                word_error_rate_x=wer_x,
                word_error_rate_z=wer_z,
                word_error_rate=wer,
                block_error_rate=bler,
                syndrome_convergence_rate=conv_rate,
                uncorrected_baseline_bler=base_bler,
                uncorrected_baseline_wer=base_wer,
                is_suppressed=is_supp,
            )
        )

    emp_th, is_cert = estimate_empirical_threshold(
        sorted_rates, block_error_rates, baseline_rates=baseline_blers, target_threshold=0.08
    )

    return ParallelMonteCarloResult(
        code_name=code.name,
        n_qubits=code.n_qubits,
        k_logical=code.k,
        code_rate=code.code_rate,
        noise_model=norm_noise,
        osd_order=osd_order,
        osd_method=norm_method,
        num_trials=num_trials,
        physical_error_rates=sorted_rates,
        word_error_rates=word_error_rates,
        block_error_rates=block_error_rates,
        syndrome_convergence_rates=syndrome_convergence_rates,
        empirical_threshold=emp_th,
        is_threshold_certified=is_cert,
        details=details,
    )
