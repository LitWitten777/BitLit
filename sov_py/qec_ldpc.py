"""
Quantum LDPC Stabilizer Codes on 32D Biregular Sectors (HYP-042).

Constructs [[2368, 2152]] quantum Low-Density Parity-Check (QLDPC) CSS stabilizer codes
from the 7 biregular incidence subgraphs (degree split {24, 8}) of the 840-vertex
trigintaduonion (D=32) zero-divisor network under the Tillich-Zémor hypergraph product.

Key Properties:
- 56-vertex biregular sectors chi in {9..15} have 8 high-degree vertices (deg 24)
  and 48 low-degree vertices (deg 8).
- The incidence matrix B between high-degree and low-degree vertices is 8 x 48,
  with row weight 24, column weight 4, and GF(2) rank exactly 2.
- The quantum hypergraph product code yields:
  * N = 48^2 + 8^2 = 2304 + 64 = 2368 physical qubits.
  * M_X = M_Z = 8 * 48 = 384 stabilizer check generators.
  * Uniform check weight w_X = w_Z = 24 + 4 = 28.
  * Column weights: 2304 qubits with degree 4, 64 qubits with degree 24.
  * Exact GF(2) ranks: rank(H_X) = rank(H_Z) = 384 - 6 * 46 = 108.
  * Exact logical qubits: K = 2368 - 108 - 108 = 2152 (code rate R = 269/296 ≈ 0.9088).
  * Analytical Tillich-Zémor theorem: K = k^2 + (k^T)^2 = 46^2 + 6^2 = 2116 + 36 = 2152.
  * Exact CSS commutativity: H_X * H_Z^T == 0 (mod 2).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import numpy as np

from sedenion.cd_algebra import CDStratificationEngine
from sedenion.qec import bp_osd_decode, extract_gf2_basis


class QELDPCError(Exception):
    """Exception raised for errors in quantum LDPC operations."""

    pass


@dataclass(frozen=True)
class BiregularIncidenceAnalysis:
    """
    Structural analysis of the bipartite incidence between high-degree and low-degree
    vertices in a D=32 biregular zero-divisor sector.
    """

    chi: int
    num_high: int
    num_low: int
    row_weight: int
    col_weight: int
    edge_count: int
    rank_gf2: int
    left_nullity: int
    right_nullity: int
    unique_rows: int
    unique_cols: int


def extract_biregular_incidence(chi: int) -> tuple[np.ndarray, BiregularIncidenceAnalysis]:
    """
    Extracts the binary incidence matrix B in {0, 1}^{8 x 48} between high-degree (8)
    and low-degree (48) vertices for a biregular sector chi in {9..15}.
    """
    if chi < 9 or chi > 15:
        raise QELDPCError(f"Biregular sector requires chi in {{9..15}}, got {chi}")

    engine = CDStratificationEngine(32)
    G = engine.generate_zero_divisor_graph(target_chi=chi)
    deg_map = dict(G.degree())

    high_nodes = sorted([n for n, d in deg_map.items() if d == 24])
    low_nodes = sorted([n for n, d in deg_map.items() if d == 8])

    if len(high_nodes) != 8 or len(low_nodes) != 48:
        raise QELDPCError(
            f"Expected 8 high-degree and 48 low-degree nodes, found {len(high_nodes)} and {len(low_nodes)}"
        )

    B = np.zeros((8, 48), dtype=np.uint8)
    for i, h in enumerate(high_nodes):
        for j, low_node in enumerate(low_nodes):
            if G.has_edge(h, low_node):
                B[i, j] = 1

    row_weights = {int(w) for w in B.sum(axis=1)}
    col_weights = {int(w) for w in B.sum(axis=0)}

    if row_weights != {24}:
        raise QELDPCError(f"Expected uniform row weight 24, got {row_weights}")
    if col_weights != {4}:
        raise QELDPCError(f"Expected uniform col weight 4, got {col_weights}")

    basis = extract_gf2_basis(B)
    rank_gf2 = len(basis)
    left_nullity = 8 - rank_gf2
    right_nullity = 48 - rank_gf2

    unique_rows = int(np.unique(B, axis=0).shape[0])
    unique_cols = int(np.unique(B, axis=1).shape[1])

    analysis = BiregularIncidenceAnalysis(
        chi=chi,
        num_high=8,
        num_low=48,
        row_weight=24,
        col_weight=4,
        edge_count=int(B.sum()),
        rank_gf2=rank_gf2,
        left_nullity=left_nullity,
        right_nullity=right_nullity,
        unique_rows=unique_rows,
        unique_cols=unique_cols,
    )
    return B, analysis


class TrigintaduonionHypergraphProductCode:
    """
    [[2368, 2152]] Quantum LDPC CSS stabilizer code constructed from
    the D=32 biregular sector incidence matrix B in {0, 1}^{8 x 48}.
    """

    def __init__(self, chi: int = 9, B: np.ndarray | None = None) -> None:
        if B is None:
            self.B, self.analysis = extract_biregular_incidence(chi)
        else:
            if B.shape != (8, 48):
                raise QELDPCError(f"Matrix B must have shape (8, 48), got {B.shape}")
            self.B = (B % 2).astype(np.uint8)
            basis = extract_gf2_basis(self.B)
            rank = len(basis)
            self.analysis = BiregularIncidenceAnalysis(
                chi=chi,
                num_high=8,
                num_low=48,
                row_weight=int(self.B[0].sum()),
                col_weight=int(self.B[:, 0].sum()),
                edge_count=int(self.B.sum()),
                rank_gf2=rank,
                left_nullity=8 - rank,
                right_nullity=48 - rank,
                unique_rows=int(np.unique(self.B, axis=0).shape[0]),
                unique_cols=int(np.unique(self.B, axis=1).shape[1]),
            )

        self.chi = chi
        m, n = self.B.shape  # 8, 48

        # Block dimensions
        self.n_low_low = n * n  # 48 * 48 = 2304
        self.n_high_high = m * m  # 8 * 8 = 64
        self.n = self.n_low_low + self.n_high_high  # 2368
        self.m_checks = m * n  # 8 * 48 = 384

        I_n = np.eye(n, dtype=np.uint8)
        I_m = np.eye(m, dtype=np.uint8)

        # H_X = [B \otimes I_n, I_m \otimes B^T]
        HX_1 = np.kron(self.B, I_n)
        HX_2 = np.kron(I_m, self.B.T)
        self.H_X = np.hstack([HX_1, HX_2]) % 2

        # H_Z = [I_n \otimes B, B^T \otimes I_m]
        HZ_1 = np.kron(I_n, self.B)
        HZ_2 = np.kron(self.B.T, I_m)
        self.H_Z = np.hstack([HZ_1, HZ_2]) % 2

        # Verify CSS condition H_X * H_Z^T == 0 (mod 2)
        comm = (self.H_X @ self.H_Z.T) % 2
        if np.any(comm != 0):
            raise QELDPCError("CSS commutativity condition violated: H_X * H_Z^T != 0 (mod 2)")

        # Analytical ranks from Tillich-Zémor
        k_right = self.analysis.right_nullity  # 46
        k_left = self.analysis.left_nullity  # 6
        self.rank_X = self.m_checks - (k_left * k_right)  # 384 - 6 * 46 = 108
        self.rank_Z = self.m_checks - (k_right * k_left)  # 384 - 46 * 6 = 108

        # Logical qubits
        self.k = self.n - self.rank_X - self.rank_Z  # 2368 - 216 = 2152
        self.code_rate = self.k / self.n  # 2152 / 2368 = 269 / 296

        # Check weights
        self.check_weight_X = int(self.H_X[0].sum())
        self.check_weight_Z = int(self.H_Z[0].sum())

        # Qubit degrees
        self.qubit_degrees_X = [int(self.H_X[:, j].sum()) for j in range(self.n)]
        self.qubit_degrees_Z = [int(self.H_Z[:, j].sum()) for j in range(self.n)]

    def syndrome_x(self, z_error: np.ndarray) -> np.ndarray:
        """Computes X-syndrome from Pauli Z errors: s_X = H_X * e_Z (mod 2)."""
        return (self.H_X @ (z_error.astype(np.uint8) % 2)) % 2

    def syndrome_z(self, x_error: np.ndarray) -> np.ndarray:
        """Computes Z-syndrome from Pauli X errors: s_Z = H_Z * e_X (mod 2)."""
        return (self.H_Z @ (x_error.astype(np.uint8) % 2)) % 2

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
        if not np.any(syndrome):
            return np.zeros(self.n, dtype=np.uint8)

        # 1. Single qubit match check
        for j in range(self.n):
            if np.array_equal(H[:, j], syndrome):
                err = np.zeros(self.n, dtype=np.uint8)
                err[j] = 1
                return err

        # 2. LDPC Bit-flipping iteration
        curr_s = syndrome.copy().astype(np.uint8)
        err = np.zeros(self.n, dtype=np.uint8)
        for _ in range(max_iter):
            if not np.any(curr_s):
                return err
            unsat = H.T @ curr_s
            max_v = int(unsat.max())
            if max_v <= 1:
                break
            flip_indices = np.where(unsat == max_v)[0]
            idx = int(flip_indices[0])
            err[idx] ^= 1
            curr_s = (curr_s ^ H[:, idx]) % 2

        if not np.any(curr_s):
            return err

        # 3. Two-qubit candidate search if bit-flipping stalled
        active_rows = np.where(syndrome == 1)[0]
        candidate_cols = set()
        for r in active_rows:
            candidate_cols.update(np.where(H[r, :] == 1)[0])

        cand_list = sorted(candidate_cols)
        for idx1 in range(len(cand_list)):
            c1 = cand_list[idx1]
            h1 = H[:, c1]
            diff = (syndrome ^ h1) % 2
            for idx2 in range(idx1 + 1, len(cand_list)):
                c2 = cand_list[idx2]
                if np.array_equal(H[:, c2], diff):
                    rec = np.zeros(self.n, dtype=np.uint8)
                    rec[c1] = 1
                    rec[c2] = 1
                    return rec

        return None

    def decode_bposd(
        self,
        syndrome: np.ndarray,
        is_x_syndrome: bool = True,
        p: float = 0.01,
        max_iter: int = 25,
        osd_order: int = 0,
    ) -> np.ndarray | None:
        """
        Decodes syndrome via BP-OSD.
        """
        H = self.H_X if is_x_syndrome else self.H_Z
        rec, ok = bp_osd_decode(H, syndrome, p=p, max_iter=max_iter, osd_order=osd_order)
        if ok and rec is not None:
            return rec
        return None

    def simulate_channel(
        self,
        p_x: float = 0.001,
        p_z: float = 0.001,
        num_trials: int = 50,
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
            e_x = np.asarray(rng.random(self.n) < p_x, dtype=np.uint8)
            if np.any(e_x):
                trials_err_x += 1
                s_z = self.syndrome_z(e_x)
                rec_x = self.decode_fast_hypergraph(s_z, is_x_syndrome=False)
                if rec_x is not None:
                    res_x = (e_x ^ rec_x) % 2
                    if not np.any(self.syndrome_z(res_x)):
                        successes_x += 1

            # Z error (detected by H_X)
            e_z = np.asarray(rng.random(self.n) < p_z, dtype=np.uint8)
            if np.any(e_z):
                trials_err_z += 1
                s_x = self.syndrome_x(e_z)
                rec_z = self.decode_fast_hypergraph(s_x, is_x_syndrome=True)
                if rec_z is not None:
                    res_z = (e_z ^ rec_z) % 2
                    if not np.any(self.syndrome_x(res_z)):
                        successes_z += 1

        return {
            "n": self.n,
            "k": self.k,
            "trials": num_trials,
            "p_x": p_x,
            "p_z": p_z,
            "trials_err_x": trials_err_x,
            "successes_x": successes_x,
            "success_rate_x": successes_x / max(1, trials_err_x),
            "trials_err_z": trials_err_z,
            "successes_z": successes_z,
            "success_rate_z": successes_z / max(1, trials_err_z),
        }


def catalog_all_biregular_qldpc_codes() -> dict[int, dict[str, Any]]:
    """
    Catalogs the quantum LDPC hypergraph product codes across all 7 biregular sectors chi in {9..15}.
    """
    catalog: dict[int, dict[str, Any]] = {}
    for chi in range(9, 16):
        code = TrigintaduonionHypergraphProductCode(chi=chi)
        catalog[chi] = {
            "n": code.n,
            "k": code.k,
            "code_rate": code.code_rate,
            "rank_X": code.rank_X,
            "rank_Z": code.rank_Z,
            "check_weight_X": code.check_weight_X,
            "check_weight_Z": code.check_weight_Z,
            "num_checks_X": code.m_checks,
            "num_checks_Z": code.m_checks,
            "analysis": {
                "rank_gf2": code.analysis.rank_gf2,
                "left_nullity": code.analysis.left_nullity,
                "right_nullity": code.analysis.right_nullity,
                "edge_count": code.analysis.edge_count,
            },
        }
    return catalog
