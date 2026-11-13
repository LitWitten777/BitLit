"""
Coin operators for the discrete-time quantum walk on Γ = C₆[K̄₄].

The coin acts on the 8-dimensional internal (direction) space at each vertex.
Three standard coins:

Hadamard — H₂^⊗3, the "democratic" coin with no marked direction.
Grover   — 2|s⟩⟨s| - I, the optimal coin for search on regular graphs.
DFT      — the 8×8 discrete Fourier transform, maximally mixing.

All coins are unitary. The walk operator U = S · (I ⊗ C) is unitary iff C is.
"""

from __future__ import annotations

from typing import Literal

import numpy as np

CoinName = Literal["hadamard", "grover", "dft", "identity"]


def hadamard_coin(d: int) -> np.ndarray:
    """H₂^⊗log₂(d) — the tensor-power Hadamard coin.

    For d = 8 this is H₂ ⊗ H₂ ⊗ H₂, which has entries ±1/√8.
    """
    if d <= 0 or (d & (d - 1)) != 0:
        raise ValueError(f"Hadamard coin requires d a power of 2, got {d}")
    H2 = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)
    C = H2.copy()
    for _ in range(int(np.log2(d)) - 1):
        C = np.kron(C, H2)
    return C


def grover_coin(d: int) -> np.ndarray:
    """G = 2|s⟩⟨s| - I where |s⟩ = (1/√d) Σ|c⟩ is the uniform superposition.

    This is the "diffusion" operator of Grover's algorithm. It is the
    optimal coin for quantum-walk search on regular graphs.
    """
    if d <= 0:
        raise ValueError(f"Grover coin requires d > 0, got {d}")
    return 2.0 * np.ones((d, d), dtype=complex) / d - np.eye(d, dtype=complex)


def dft_coin(d: int) -> np.ndarray:
    """The d-dimensional discrete Fourier transform:
    F[j, k] = ω^(jk) / √d,  ω = exp(2πi/d).
    """
    if d <= 0:
        raise ValueError(f"DFT coin requires d > 0, got {d}")
    omega = np.exp(2j * np.pi / d)
    j, k = np.meshgrid(np.arange(d), np.arange(d), indexing="ij")
    return (omega ** (j * k)) / np.sqrt(d)


def coin_operator(name: CoinName, d: int) -> np.ndarray:
    """Factory for coin operators."""
    if name == "hadamard":
        return hadamard_coin(d)
    if name == "grover":
        return grover_coin(d)
    if name == "dft":
        return dft_coin(d)
    if name == "identity":
        return np.eye(d, dtype=complex)
    raise ValueError(f"unknown coin '{name}'")


def is_unitary(C: np.ndarray, tol: float = 1e-10) -> bool:
    """Check C† C = I to numerical tolerance."""
    d = C.shape[0]
    return bool(np.allclose(C.conj().T @ C, np.eye(d), atol=tol))
