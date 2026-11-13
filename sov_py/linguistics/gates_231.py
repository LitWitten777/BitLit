"""
The 231 Gates Engine (Sefer Yetzirah Chordal Commutator Graph).

Mathematical Foundations:
1. The 22 Hebrew consonants form 231 undirected chords on the circle S¹:
   N_gates = C(22, 2) = (22 * 21) / 2 = 231.
2. Canonical division into:
   - 3 Mothers (Aleph, Mem, Shin): C(3, 2) = 3 gates
   - 7 Doubles (Bet, Gimel, Dalet, Kaf, Pe, Resh, Tav): C(7, 2) = 21 gates
   - 12 Elementals (He, Vav, Zayin, Het, Tet, Yod, Lamed, Nun, Samekh, Ayin, Tsadi, Qof): C(12, 2) = 66 gates
   - Cross-class pairs: 3*7 + 3*12 + 7*12 = 21 + 36 + 84 = 141 gates
   Total = 3 + 21 + 66 + 141 = 231 gates.
3. D₈ ⊂ E₈ integer root embedding:
   Each consonant embeds into the 112 integer roots of D₈: (±1, ±1, 0, ..., 0).
4. Sedenion commutator brackets and XOR charge:
   For gate (u, v), basis products satisfy e_u * e_v = -e_v * e_u = ε(u, v) e_{u ^ v}.
   Zero-divisor pairs annihilate across shared XOR charges χ.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, List, Optional, Set, Tuple

import numpy as np


class LetterClass(Enum):
    MOTHER = "MOTHER"
    DOUBLE = "DOUBLE"
    ELEMENTAL = "ELEMENTAL"


@dataclass(frozen=True)
class HebrewConsonant:
    index: int  # 1 to 22
    name: str
    symbol: str
    letter_class: LetterClass
    d8_root: Tuple[int, ...]  # 8D vector in D8


@dataclass(frozen=True)
class Gate231:
    gate_id: int  # 1 to 231
    letter1: HebrewConsonant
    letter2: HebrewConsonant
    gate_class: str  # "MOTHER-MOTHER", "DOUBLE-DOUBLE", "ELEMENTAL-ELEMENTAL", "CROSS"
    xor_charge: int
    chord_angle: float  # Angle subtended on S¹ in radians


class The231GatesEngine:
    """
    Engine for generating, classifying, and evaluating the 231 Gates of Sefer Yetzirah.
    """

    CONSONANT_DATA = [
        # 3 Mothers
        (1, "Aleph", "א", LetterClass.MOTHER, (1, 1, 0, 0, 0, 0, 0, 0)),
        (13, "Mem", "מ", LetterClass.MOTHER, (1, -1, 0, 0, 0, 0, 0, 0)),
        (21, "Shin", "ש", LetterClass.MOTHER, (-1, 1, 0, 0, 0, 0, 0, 0)),
        # 7 Doubles
        (2, "Bet", "ב", LetterClass.DOUBLE, (0, 0, 1, 1, 0, 0, 0, 0)),
        (3, "Gimel", "ג", LetterClass.DOUBLE, (0, 0, 1, -1, 0, 0, 0, 0)),
        (4, "Dalet", "ד", LetterClass.DOUBLE, (0, 0, -1, 1, 0, 0, 0, 0)),
        (11, "Kaf", "כ", LetterClass.DOUBLE, (0, 0, 0, 0, 1, 1, 0, 0)),
        (17, "Pe", "פ", LetterClass.DOUBLE, (0, 0, 0, 0, 1, -1, 0, 0)),
        (20, "Resh", "ר", LetterClass.DOUBLE, (0, 0, 0, 0, -1, 1, 0, 0)),
        (22, "Tav", "ת", LetterClass.DOUBLE, (-1, -1, 0, 0, 0, 0, 0, 0)),
        # 12 Elementals
        (5, "He", "ה", LetterClass.ELEMENTAL, (1, 0, 1, 0, 0, 0, 0, 0)),
        (6, "Vav", "ו", LetterClass.ELEMENTAL, (1, 0, -1, 0, 0, 0, 0, 0)),
        (7, "Zayin", "ז", LetterClass.ELEMENTAL, (-1, 0, 1, 0, 0, 0, 0, 0)),
        (8, "Het", "ח", LetterClass.ELEMENTAL, (0, 1, 0, 1, 0, 0, 0, 0)),
        (9, "Tet", "ט", LetterClass.ELEMENTAL, (0, 1, 0, -1, 0, 0, 0, 0)),
        (10, "Yod", "י", LetterClass.ELEMENTAL, (0, -1, 0, 1, 0, 0, 0, 0)),
        (12, "Lamed", "ל", LetterClass.ELEMENTAL, (0, 0, 0, 0, 0, 0, 1, 1)),
        (14, "Nun", "נ", LetterClass.ELEMENTAL, (0, 0, 0, 0, 0, 0, 1, -1)),
        (15, "Samekh", "ס", LetterClass.ELEMENTAL, (0, 0, 0, 0, 0, 0, -1, 1)),
        (16, "Ayin", "ע", LetterClass.ELEMENTAL, (0, 0, 0, 0, 0, 0, -1, -1)),
        (18, "Tsadi", "צ", LetterClass.ELEMENTAL, (0, 0, 1, 0, 1, 0, 0, 0)),
        (19, "Qof", "ק", LetterClass.ELEMENTAL, (0, 0, 1, 0, -1, 0, 0, 0)),
    ]

    def __init__(self) -> None:
        self.consonants: List[HebrewConsonant] = sorted(
            [
                HebrewConsonant(
                    index=idx,
                    name=name,
                    symbol=sym,
                    letter_class=lclass,
                    d8_root=root,
                )
                for idx, name, sym, lclass, root in self.CONSONANT_DATA
            ],
            key=lambda c: c.index,
        )
        assert len(self.consonants) == 22, f"Expected 22 consonants, got {len(self.consonants)}"
        self.gates: List[Gate231] = self._build_all_gates()
        assert len(self.gates) == 231, f"Expected 231 gates, got {len(self.gates)}"

    def _build_all_gates(self) -> List[Gate231]:
        gates: List[Gate231] = []
        gate_id = 1
        for c1, c2 in itertools.combinations(self.consonants, 2):
            # Class determination
            if c1.letter_class == c2.letter_class:
                g_class = f"{c1.letter_class.value}-{c2.letter_class.value}"
            else:
                g_class = "CROSS"

            # XOR charge in F₂⁵
            xor_charge = c1.index ^ c2.index

            # Angular chord distance on circle S¹: 22 nodes uniformly distributed
            theta1 = 2.0 * np.pi * (c1.index - 1) / 22.0
            theta2 = 2.0 * np.pi * (c2.index - 1) / 22.0
            d_theta = abs(theta1 - theta2)
            chord_angle = min(d_theta, 2.0 * np.pi - d_theta)

            gates.append(
                Gate231(
                    gate_id=gate_id,
                    letter1=c1,
                    letter2=c2,
                    gate_class=g_class,
                    xor_charge=xor_charge,
                    chord_angle=chord_angle,
                )
            )
            gate_id += 1
        return gates

    def get_partition_counts(self) -> Dict[str, int]:
        """Returns the count of gates in each structural category."""
        counts = {
            "MOTHER-MOTHER": 0,
            "DOUBLE-DOUBLE": 0,
            "ELEMENTAL-ELEMENTAL": 0,
            "CROSS": 0,
        }
        for g in self.gates:
            counts[g.gate_class] += 1
        return counts

    def evaluate_gate_commutator(self, gate: Gate231) -> Dict[str, Any]:
        """
        Computes the algebraic commutator and D8 root inner product for a gate.
        """
        v1 = np.array(gate.letter1.d8_root, dtype=np.int32)
        v2 = np.array(gate.letter2.d8_root, dtype=np.int32)
        inner_prod = int(np.dot(v1, v2))
        euclidean_dist = float(np.linalg.norm(v1 - v2))

        return {
            "gate_id": gate.gate_id,
            "pair": f"{gate.letter1.symbol}-{gate.letter2.symbol}",
            "names": f"{gate.letter1.name}-{gate.letter2.name}",
            "d8_inner_product": inner_prod,
            "d8_euclidean_distance": euclidean_dist,
            "xor_charge": gate.xor_charge,
            "anticommuting": True,  # Non-trivial basis elements in CD tower strictly anticommute
        }

    def total_gates_count(self) -> int:
        return len(self.gates)
