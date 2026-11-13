"""Fast Tensor Transforms and Ring-Valued Orthogonal Matrices for Cryptography.

Grounding:
    Jacques Peyrière (2026),
    "Fast Tensor Transforms and Ring-Valued Orthogonal Matrices: An Application to Cryptography",
    arXiv preprint.

Key Mathematical Invariants & Algorithmic Principles:
1. Ring-Valued Orthogonal Matrix Construction (Section 3.1 & 3.2):
   Let R = Z/256Z. Given b = (b_1, ..., b_{q-1}) with sum_{j=1}^{q-1} b_j^2 == 1 (mod 4).
   Let S = sum_{j=1}^{q-1} b_j^2. Writing S = 4k + 1:
     1 - S = -4k
     1 + S = 4k + 2 = 2(2k + 1)
   The reduced fractions define:
     a_0 = -2k / (2k + 1)  (mod 256)
     L_j = b_j / (2k + 1)   (mod 256)
   Both 2k + 1 and (1 + eps * a_0) are odd, hence invertible in Z/256Z for eps in {-1, 1}.
   The matrix:
     U_eps = [  a_0                      L              ]
             [ -eps L^T    I - (1 + eps a_0)^{-1} L^T L ]
   satisfies U_eps^T U_eps = I_q (mod 256) and U_eps U_eps^T = I_q (mod 256).

2. Number of Admissible Parameter Vectors nu(q):
   nu(q) = 2^{7(q-1)} * sum_{r equiv 1 mod 4, 0 <= r <= q-1} binom(q-1, r).
   Exact values for q = 2..13:
     nu(2) = 2^7
     nu(3) = 2^{15}
     nu(4) = 3 * 2^{21}
     nu(5) = 2^{30}
     nu(6) = 3 * 2^{36}
     nu(7) = 3 * 2^{44}
     nu(8) = 7 * 2^{51}
     nu(9) = 2^{62}
     nu(10) = 17 * 2^{66}
     nu(11) = 17 * 2^{74}
     nu(12) = 33 * 2^{81} = 3 * 11 * 2^{81}
     nu(13) = 2^{94}.

3. Fast Tensor Product Algorithm (Lemma 1):
   For a tensor product R = R_1 (x) ... (x) R_n of size q^n,
   evaluating R X takes n * q^n byte operations instead of q^{2n}.

4. Symmetric Cryptosystem:
   Block size: q^n bytes.
   Key: n tuples (eps_j, b^{(j)}) with size n(8q - 7) bits.
   Encryption: C = (R_1 (x) ... (x) R_n) X (mod 256).
   Decryption: X = (R_1^T (x) ... (x) R_n^T) C (mod 256).
   Exact involutory/orthogonal inversion: X = Decrypt(Encrypt(X)).
"""

from __future__ import annotations

import itertools
import math
from typing import List, Tuple
import numpy as np


def inv_mod_256(x: int) -> int:
    """Compute modular inverse in Z/256Z for odd integers."""
    x = x % 256
    if x % 2 == 0:
        raise ValueError(f"Integer {x} is not invertible modulo 256 (must be odd).")
    return pow(x, -1, 256)


def admissible_vector_count(q: int) -> int:
    """Compute exact number of admissible parameter vectors nu(q).

    nu(q) = 2^{7(q-1)} * sum_{r equiv 1 mod 4, 1 <= r <= q-1} binom(q-1, r).
    """
    if q < 2:
        raise ValueError(f"q must be >= 2, got {q}")
    m = q - 1
    odd_ways = sum(math.comb(m, r) for r in range(1, m + 1, 4))
    return (2 ** (7 * m)) * odd_ways


def construct_ring_orthogonal_matrix(b: List[int], eps: int = 1) -> np.ndarray:
    """Construct a q x q orthogonal matrix over Z/256Z from parameter vector b.

    Parameters:
        b: list of q - 1 integers in {0, ..., 255} such that sum(b_i^2) == 1 (mod 4).
        eps: +1 or -1.

    Returns:
        U: q x q numpy array with uint8/int entries satisfying U^T U == I (mod 256).
    """
    if eps not in (1, -1):
        raise ValueError(f"eps must be +1 or -1, got {eps}")

    b_arr = np.array(b, dtype=int) % 256
    q = len(b_arr) + 1
    S = int(np.sum(b_arr**2))
    if S % 4 != 1:
        raise ValueError(f"Sum of squares of b must be 1 mod 4, got {S} == {S % 4} mod 4")

    k = (S - 1) // 4
    denom = (2 * k + 1) % 256
    denom_inv = inv_mod_256(denom)

    a_0 = ((-2 * k) * denom_inv) % 256
    L = (b_arr * denom_inv) % 256

    # Invert (1 + eps * a_0) mod 256
    denom_U = (1 + eps * a_0) % 256
    denom_U_inv = inv_mod_256(denom_U)

    # Assemble U
    U = np.zeros((q, q), dtype=int)
    U[0, 0] = a_0
    U[0, 1:] = L
    U[1:, 0] = (-eps * L) % 256

    LtL = np.outer(L, L) % 256
    A = (np.eye(q - 1, dtype=int) - denom_U_inv * LtL) % 256
    U[1:, 1:] = A

    return U % 256


def apply_fast_tensor_product(
    matrices: List[np.ndarray],
    X: np.ndarray,
) -> np.ndarray:
    """Apply tensor product R_1 (x) ... (x) R_n to vector X of size q^n (mod 256).

    Implements Peyriere Lemma 1 in O(n * q^n) operations.
    """
    n = len(matrices)
    if n == 0:
        return X.copy()

    q = matrices[0].shape[0]
    for R in matrices:
        if R.shape != (q, q):
            raise ValueError(f"All matrices must be {q}x{q}")

    if X.size != q**n:
        raise ValueError(f"X must have size {q**n}, got {X.size}")

    # Reshape state as an n-dimensional tensor of shape (q, q, ..., q)
    tensor = X.reshape([q] * n).copy() % 256

    # Apply each matrix R_m along the corresponding axis
    for m in range(n):
        R = matrices[m] % 256
        # Contract along axis m: tensor_new[..., i, ...] = sum_j R[i, j] * tensor[..., j, ...]
        # Using numpy tensordot / rollaxis:
        tensor = np.moveaxis(tensor, m, 0)
        # Flatten remaining axes
        rest_shape = tensor.shape[1:]
        flat_tensor = tensor.reshape(q, -1)
        contracted = (R @ flat_tensor) % 256
        tensor = contracted.reshape((q,) + rest_shape)
        tensor = np.moveaxis(tensor, 0, m)

    return tensor.reshape(-1) % 256


class RingOrthogonalCryptosystem:
    """Symmetric block cryptosystem over Z/256Z using tensor products of orthogonal matrices."""

    def __init__(self, q: int, n: int, keys: List[Tuple[int, List[int]]]):
        """Initialize with q (matrix dimension), n (number of tensor factors), and keys.

        Each key is a tuple (eps_m, b^{(m)}) for m = 1..n.
        """
        self.q = q
        self.n = n
        self.block_size = q**n
        self.key_bits = n * (8 * q - 7)

        if len(keys) != n:
            raise ValueError(f"Expected {n} keys, got {len(keys)}")

        self.R_matrices = []
        self.R_inv_matrices = []

        for eps, b in keys:
            U = construct_ring_orthogonal_matrix(b, eps)
            self.R_matrices.append(U)
            # Inverse of orthogonal matrix is transpose!
            self.R_inv_matrices.append(U.T % 256)

    def encrypt_block(self, plaintext: np.ndarray) -> np.ndarray:
        """Encrypt a block of q^n bytes."""
        pt = np.asarray(plaintext, dtype=int) % 256
        if pt.size != self.block_size:
            raise ValueError(f"Block size must be {self.block_size}, got {pt.size}")
        return apply_fast_tensor_product(self.R_matrices, pt)

    def decrypt_block(self, ciphertext: np.ndarray) -> np.ndarray:
        """Decrypt a block of q^n bytes using transpose matrices."""
        ct = np.asarray(ciphertext, dtype=int) % 256
        if ct.size != self.block_size:
            raise ValueError(f"Block size must be {self.block_size}, got {ct.size}")
        return apply_fast_tensor_product(self.R_inv_matrices, ct)

    def encrypt_cbc_mode(self, plaintext_blocks: List[np.ndarray], iv: np.ndarray) -> Tuple[List[np.ndarray], np.ndarray]:
        """Encrypt multiple blocks using CBC-like chaining as described in Peyriere Section 4.1."""
        cipher_blocks = []
        current_feedback = (self.encrypt_block(iv)) % 256

        for block in plaintext_blocks:
            chained_input = (block ^ current_feedback) % 256
            c_block = self.encrypt_block(chained_input)
            cipher_blocks.append(c_block)
            current_feedback = c_block

        return cipher_blocks, current_feedback
