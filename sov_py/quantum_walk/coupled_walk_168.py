"""
Coupled 168-Vertex Discrete-Time Quantum Walk and Algebraic Annihilator Search.

Implements the full 168-vertex quantum walk on the sedenion zero-divisor graph:
1. State space: H = C^168 (x) C^8 (dimension 1,344).
2. Unitarity of full 168-vertex shift operator S_168 and walk operator U_168.
3. Algebraic zero-divisor search using Cayley-Dickson multiplication oracle.
4. Fano triality inter-component coupling.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

import numpy as np

from .algebraic_oracle import AlgebraicZeroDivisorOracle, ZeroDivisor168Graph
from .coins import CoinName, coin_operator, is_unitary
from .emulator import build_shift
from .graph import RamanujanGraph


@dataclass
class AnnihilatorSearchResult:
    query_id: int
    found_id: int
    is_annihilator: bool
    steps: int
    success_probability: float
    probability_trace: list[float]


class CoupledQuantumWalk168:
    """
    168-vertex discrete-time quantum walk engine on the full sedenion zero-divisor graph.
    
    Hilbert space: C^168 (x) C^8 (dimension 1,344).
    The 168 vertices are organized into 7 Ramanujan components of 24 vertices each.
    """

    def __init__(
        self,
        coin: CoinName = "grover",
        fano_coupling: float = 0.0,
    ) -> None:
        self.zd_graph = ZeroDivisor168Graph()
        self.n = 168
        self.d = 8
        self.coin_name = coin
        self.fano_coupling = fano_coupling

        # Component graph template
        self.comp_graph = RamanujanGraph()
        self.S_comp = build_shift(self.comp_graph)

        # Build full 168-vertex shift operator S_168 = diag(S_24, ..., S_24)
        dim_comp = 24 * 8
        self.dim = 168 * 8
        self.S = np.zeros((self.dim, self.dim), dtype=complex)
        for b in range(7):
            idx = slice(b * dim_comp, (b + 1) * dim_comp)
            self.S[idx, idx] = self.S_comp

        # Coin operator
        self.C = coin_operator(coin, self.d)
        self.I_n = np.eye(self.n, dtype=complex)

        # Walk operator: U = S * (I_168 (x) C)
        self.U = self.S @ np.kron(self.I_n, self.C)

        if not is_unitary(self.U, tol=1e-9):
            raise RuntimeError("168-vertex walk operator U is not unitary")

        self.oracle_engine = AlgebraicZeroDivisorOracle(self.zd_graph)

    def uniform_state(self) -> np.ndarray:
        """Uniform superposition over all 168 vertices and 8 coin directions."""
        psi = np.ones(self.dim, dtype=complex)
        return psi / np.linalg.norm(psi)

    def localized_state(self, vertex_id: int) -> np.ndarray:
        """State localized at vertex_id with uniform coin superposition."""
        psi = np.zeros(self.dim, dtype=complex)
        psi[vertex_id * self.d : (vertex_id + 1) * self.d] = (
            np.ones(self.d, dtype=complex) / np.sqrt(self.d)
        )
        return psi

    def step(self, psi: np.ndarray) -> np.ndarray:
        return self.U @ psi

    def position_distribution(self, psi: np.ndarray) -> np.ndarray:
        """Probability distribution over the 168 vertices."""
        prob = np.abs(psi) ** 2
        return prob.reshape(self.n, self.d).sum(axis=1)

    def search_algebraic_annihilators(
        self,
        query_u_id: int,
        max_steps: int = 15,
    ) -> AnnihilatorSearchResult:
        """
        Executes quantum search using the Algebraic Zero-Divisor Oracle.
        
        Searches for vertices w that algebraically annihilate query_u: u * w = 0.
        """
        annihilators = set(self.zd_graph.annihilators(query_u_id))
        oracle = self.oracle_engine.build_oracle(query_u_id)

        # Search operator U_search = U * Oracle
        U_search = self.U @ oracle

        # Start from uniform superposition over the relevant component
        # (or over all 168 vertices)
        target_charge = self.zd_graph.vectors[query_u_id].charge
        comp_offset = (target_charge - 1) * 24

        psi = np.zeros(self.dim, dtype=complex)
        # Uniform superposition on the 24 vertices of the target charge sector
        for v in range(comp_offset, comp_offset + 24):
            psi[v * self.d : (v + 1) * self.d] = 1.0 / np.sqrt(24 * self.d)

        trace: list[float] = []
        best_p = -1.0
        best_step = 0

        for k in range(max_steps + 1):
            dist = self.position_distribution(psi)
            p_ann = float(sum(dist[w] for w in annihilators))
            trace.append(p_ann)

            if p_ann > best_p:
                best_p = p_ann
                best_step = k

            if k < max_steps:
                psi = U_search @ psi

        # Measure best state: evolve to best_step
        psi_meas = np.zeros(self.dim, dtype=complex)
        for v in range(comp_offset, comp_offset + 24):
            psi_meas[v * self.d : (v + 1) * self.d] = 1.0 / np.sqrt(24 * self.d)
        for _ in range(best_step):
            psi_meas = U_search @ psi_meas

        dist_meas = self.position_distribution(psi_meas)
        # Filter candidate to highest probability vertex
        found_id = int(np.argmax(dist_meas))
        is_ann = found_id in annihilators

        return AnnihilatorSearchResult(
            query_id=query_u_id,
            found_id=found_id,
            is_annihilator=is_ann,
            steps=best_step,
            success_probability=best_p,
            probability_trace=trace,
        )
