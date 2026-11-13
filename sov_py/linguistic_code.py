"""
src/sedenion/linguistic_code.py
=============================================================================
Alphabet Injective Feature Code in E_8 Root System
Resolving Claim 3 (Refinement Audit):
  Provides an explicit line-by-line injection of:
  - 22 Hebrew consonants -> D_8 integer roots (norm^2 = 2)
  - 24 Greek letters     -> E_8 \\ D_8 spinor roots (norm^2 = 2)

EPISTEMIC STATUS: [A] Injective Lattice Feature Code.
  NOT an algebraic ring or algebra homomorphism. E_8 carries no canonical
  bilinear associative multiplication. Word vectors are additive feature sums
  v(W) = sum_{c in W} iota(c).
=============================================================================
"""

import numpy as np
from typing import Dict, Tuple, List


# 22 Hebrew Consonants mapped explicitly to distinct D_8 integer roots (±e_i ± e_j)
HEBREW_ROOT_MAP: Dict[str, Tuple[int, ...]] = {
    "Aleph":  (1,  1,  0,  0,  0,  0,  0,  0),
    "Beth":   (1, -1,  0,  0,  0,  0,  0,  0),
    "Gimel":  (1,  0,  1,  0,  0,  0,  0,  0),
    "Daleth": (1,  0, -1,  0,  0,  0,  0,  0),
    "He":     (1,  0,  0,  1,  0,  0,  0,  0),
    "Vav":    (1,  0,  0, -1,  0,  0,  0,  0),
    "Zayin":  (1,  0,  0,  0,  1,  0,  0,  0),
    "Cheth":  (1,  0,  0,  0, -1,  0,  0,  0),
    "Teth":   (1,  0,  0,  0,  0,  1,  0,  0),
    "Yod":    (1,  0,  0,  0,  0, -1,  0,  0),
    "Kaph":   (1,  0,  0,  0,  0,  0,  1,  0),
    "Lamed":  (1,  0,  0,  0,  0,  0, -1,  0),
    "Mem":    (1,  0,  0,  0,  0,  0,  0,  1),
    "Nun":    (1,  0,  0,  0,  0,  0,  0, -1),
    "Samekh": (0,  1,  1,  0,  0,  0,  0,  0),
    "Ayin":   (0,  1, -1,  0,  0,  0,  0,  0),
    "Pe":     (0,  1,  0,  1,  0,  0,  0,  0),
    "Tsade":  (0,  1,  0, -1,  0,  0,  0,  0),
    "Qoph":   (0,  1,  0,  0,  1,  0,  0,  0),
    "Resh":   (0,  1,  0,  0, -1,  0,  0,  0),
    "Shin":   (0,  1,  0,  0,  0,  1,  0,  0),
    "Tav":    (0,  1,  0,  0,  0, -1,  0,  0),
}


# 24 Greek Letters mapped explicitly to distinct E_8 \ D_8 half-integer spinor roots
# Vectors with coords in {+1/2, -1/2}^8 having an even number of minus signs.
# Represented here scaled by 2 (all coords in {+1, -1}, sum = 0 mod 4, even neg count)
GREEK_SPINOR_SIGNS: List[Tuple[int, ...]] = [
    # 0 minus signs (1 vector)
    (1, 1, 1, 1, 1, 1, 1, 1),
    # 2 minus signs (first 23 of 28 vectors)
    (-1, -1,  1,  1,  1,  1,  1,  1),
    (-1,  1, -1,  1,  1,  1,  1,  1),
    (-1,  1,  1, -1,  1,  1,  1,  1),
    (-1,  1,  1,  1, -1,  1,  1,  1),
    (-1,  1,  1,  1,  1, -1,  1,  1),
    (-1,  1,  1,  1,  1,  1, -1,  1),
    (-1,  1,  1,  1,  1,  1,  1, -1),
    ( 1, -1, -1,  1,  1,  1,  1,  1),
    ( 1, -1,  1, -1,  1,  1,  1,  1),
    ( 1, -1,  1,  1, -1,  1,  1,  1),
    ( 1, -1,  1,  1,  1, -1,  1,  1),
    ( 1, -1,  1,  1,  1,  1, -1,  1),
    ( 1, -1,  1,  1,  1,  1,  1, -1),
    ( 1,  1, -1, -1,  1,  1,  1,  1),
    ( 1,  1, -1,  1, -1,  1,  1,  1),
    ( 1,  1, -1,  1,  1, -1,  1,  1),
    ( 1,  1, -1,  1,  1,  1, -1,  1),
    ( 1,  1, -1,  1,  1,  1,  1, -1),
    ( 1,  1,  1, -1, -1,  1,  1,  1),
    ( 1,  1,  1, -1,  1, -1,  1,  1),
    ( 1,  1,  1, -1,  1,  1, -1,  1),
    ( 1,  1,  1, -1,  1,  1,  1, -1),
    ( 1,  1,  1,  1, -1, -1,  1,  1),
]

GREEK_LETTERS = [
    "Alpha", "Beta", "Gamma", "Delta", "Epsilon", "Zeta",
    "Eta", "Theta", "Iota", "Kappa", "Lambda", "Mu",
    "Nu", "Xi", "Omicron", "Pi", "Rho", "Sigma",
    "Tau", "Upsilon", "Phi", "Chi", "Psi", "Omega"
]

GREEK_ROOT_MAP: Dict[str, Tuple[float, ...]] = {
    letter: tuple(x / 2.0 for x in signs)
    for letter, signs in zip(GREEK_LETTERS, GREEK_SPINOR_SIGNS)
}


class LinguisticFeatureCode:
    """
    Injective Feature Code interface for Chern-quantized linguistic tokens.
    """
    @staticmethod
    def hebrew_root(letter: str) -> np.ndarray:
        if letter not in HEBREW_ROOT_MAP:
            raise KeyError(f"Unknown Hebrew letter: {letter}")
        return np.array(HEBREW_ROOT_MAP[letter], dtype=np.float64)

    @staticmethod
    def greek_root(letter: str) -> np.ndarray:
        if letter not in GREEK_ROOT_MAP:
            raise KeyError(f"Unknown Greek letter: {letter}")
        return np.array(GREEK_ROOT_MAP[letter], dtype=np.float64)

    @staticmethod
    def embed_hebrew_word(letters: List[str]) -> np.ndarray:
        """Additive word embedding: v(W) = sum_c iota(c)."""
        roots = [LinguisticFeatureCode.hebrew_root(c) for c in letters]
        return np.sum(roots, axis=0)

    @staticmethod
    def antipodal_involution(v: np.ndarray) -> np.ndarray:
        """Weyl antipodal reflection across origin: v |-> -v."""
        return -v
