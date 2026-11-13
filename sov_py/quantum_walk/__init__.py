"""
Quantum-walk emulation on Cayley-Dickson zero-divisor Ramanujan expander graphs.
"""

from __future__ import annotations

from .algebraic_oracle import (
    AlgebraicZeroDivisorOracle,
    ZeroDivisor168Graph,
    ZeroDivisorVector,
)
from .algorithms import ElementDistinctness, GroverResult, GroverSearch
from .coins import (
    CoinName,
    coin_operator,
    dft_coin,
    grover_coin,
    hadamard_coin,
    is_unitary,
)
from .coupled_walk_168 import (
    AnnihilatorSearchResult,
    CoupledQuantumWalk168,
)
from .emulator import QuantumWalk, WalkStatistics, build_shift
from .graph import RamanujanGraph, build_full_annihilation_graph

__all__ = [
    "AlgebraicZeroDivisorOracle",
    "AnnihilatorSearchResult",
    "CoinName",
    "CoupledQuantumWalk168",
    "ElementDistinctness",
    "GroverResult",
    "GroverSearch",
    "QuantumWalk",
    "RamanujanGraph",
    "WalkStatistics",
    "ZeroDivisor168Graph",
    "ZeroDivisorVector",
    "build_full_annihilation_graph",
    "build_shift",
    "coin_operator",
    "dft_coin",
    "grover_coin",
    "hadamard_coin",
    "is_unitary",
]
