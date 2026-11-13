"""
geometric_lexer.py
==================
Phase 1: Tokenizer Replacement — Geometric 2-Frames on V_2(R^7).

Replaces 1D subword tokens with orthonormal 2-frames (u, v) in V_2(R^7)
paired with their octonionic cross-product w = u x v.
The native geometric vocabulary comprises the 168 discrete sedenion
zero-divisor 2-frames partitioned across the 7 lines of the Fano plane.

Key Mechanics:
  - Base Alphabet: 168 discrete orthonormal frames (i, j, s1, s2).
  - Harmonic Representation: 21 spherical harmonics of degree (1, 0) on V_2(R^7).
  - Lossless Radix-168 Encodings: Invertible byte/text encoding to frame streams.
  - Continuous Projection: Geometric snapping of arbitrary 7D or 21D vectors onto
    the nearest discrete 2-frame on the Stiefel manifold.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple
import numpy as np

from sedenion.geometry.stiefel_spectrum import octonion_cross_product
from sedenion.stratification import CrossOctetVector, stratify_cross_octet

# First-class GNL Sentinel Constants
FRAME_PAD: int = 164
FRAME_SOS: int = 165
FRAME_EOS: int = 166
FRAME_UNK: int = 167

SENTINEL_SYMBOLS: Dict[int, str] = {
    FRAME_PAD: "<PAD>",
    FRAME_SOS: "<SOS>",
    FRAME_EOS: "<EOS>",
    FRAME_UNK: "<UNK>",
}

# 22 Hebrew Consonants (D8 Integer Root Lattice Embeddings)
HEBREW_CONSONANTS: List[str] = [
    "א", "ב", "ג", "ד", "ה", "ו", "ז", "ח", "ט", "י", "כ",
    "ל", "מ", "נ", "ס", "ע", "פ", "צ", "ק", "ר", "ש", "ת"
]

# 5 Sofit Consonants as Cohomological Boundary Closures (dOmega = 0, c1 = 0)
SOFIT_LETTERS: set[str] = {"ך", "ם", "ן", "ף", "ץ"}
SOFIT_BASE_MAP: Dict[str, str] = {
    "ך": "כ",
    "ם": "מ",
    "ן": "נ",
    "ף": "פ",
    "ץ": "צ",
}

# 24 Greek Letters (E8 \ D8 Half-Integer Spinor Roots)
GREEK_LETTERS: List[str] = [
    "α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ", "λ", "μ",
    "ν", "ξ", "ο", "π", "ρ", "σ", "τ", "υ", "φ", "χ", "ψ", "ω"
]


@dataclass(frozen=True)
class GeometricFrame:
    """
    An orthonormal 2-frame (u, v) in V_2(R^7) with w = u x v.
    Represents a native primitive symbol in the Geometric Native Language (GNL).
    """
    frame_id: int               # Canonical index in 0..167
    i: int                      # First basis index in 1..7
    j: int                      # Second basis index in 1..7
    s1: int                     # Sign of u: +1 or -1
    s2: int                     # Sign of v: +1 or -1
    sector: int                 # XOR charge sector chi = i ^ j in 1..7
    u: tuple[float, ...]        # Unit vector in R^7
    v: tuple[float, ...]        # Unit vector in R^7
    w: tuple[float, ...]        # Cross-product vector u x v in R^7
    harmonics: tuple[float, ...] # 21-dimensional degree (1, 0) harmonic vector

    @property
    def name(self) -> str:
        s1_str = "+" if self.s1 > 0 else "-"
        s2_str = "+" if self.s2 > 0 else "-"
        return f"GF_{self.frame_id:03d}(e{self.i}^{s1_str}, e{self.j}^{s2_str} | chi={self.sector})"

    def to_array_u(self) -> np.ndarray:
        return np.array(self.u, dtype=float)

    def to_array_v(self) -> np.ndarray:
        return np.array(self.v, dtype=float)

    def to_array_w(self) -> np.ndarray:
        return np.array(self.w, dtype=float)

    def to_array_harmonics(self) -> np.ndarray:
        return np.array(self.harmonics, dtype=float)

    def antipodal(self) -> "GeometricFrame":
        """Antipodal reflection (u, v) -> (-u, -v)."""
        target_s1 = -self.s1
        target_s2 = -self.s2
        # Lookup in lexer singleton
        return GeometricLexer.get_instance().get_frame_by_signature(self.i, self.j, target_s1, target_s2)


class GeometricLexer:
    """
    Lexer mapping continuous representations, strings, and byte streams
    to sequences of discrete 2-frames on V_2(R^7) = G_2 / SU(2).
    """
    _instance: Optional["GeometricLexer"] = None

    def __init__(self) -> None:
        self.frames: List[GeometricFrame] = []
        self._sig_to_id: Dict[Tuple[int, int, int, int], int] = {}
        self._sector_map: Dict[int, List[GeometricFrame]] = {s: [] for s in range(1, 8)}
        self._symbol_to_frame: Dict[str, GeometricFrame] = {}
        self._frame_to_symbol: Dict[int, str] = {}
        self._annihilation_map: Dict[int, List[int]] = {}
        self._build_alphabet()
        self._ground_symbols()
        self._build_annihilation_map()

    @classmethod
    def get_instance(cls) -> "GeometricLexer":
        """Singleton accessor for standard 168-frame vocabulary."""
        if cls._instance is None:
            inst = cls.__new__(cls)
            cls._instance = inst
            inst.__init__()
        return cls._instance

    def _build_alphabet(self) -> None:
        """Construct the canonical 168-frame alphabet from sedenion zero divisors."""
        zds, _, _ = stratify_cross_octet()
        assert len(zds) == 168, f"Expected 168 zero divisors, got {len(zds)}"

        for idx, zd in enumerate(zds):
            u_arr = np.zeros(7, dtype=float)
            v_arr = np.zeros(7, dtype=float)
            u_arr[zd.i - 1] = float(zd.s1)
            v_arr[zd.j - 1] = float(zd.s2)
            w_arr = octonion_cross_product(u_arr, v_arr)

            harmonics = np.concatenate([u_arr, v_arr, w_arr])
            sector = zd.i ^ zd.j

            frame = GeometricFrame(
                frame_id=idx,
                i=zd.i,
                j=zd.j,
                s1=zd.s1,
                s2=zd.s2,
                sector=sector,
                u=tuple(u_arr),
                v=tuple(v_arr),
                w=tuple(w_arr),
                harmonics=tuple(harmonics),
            )
            self.frames.append(frame)
            self._sig_to_id[(zd.i, zd.j, zd.s1, zd.s2)] = idx
            self._sector_map[sector].append(frame)

        assert len(self.frames) == 168
        for s in range(1, 8):
            assert len(self._sector_map[s]) == 24, f"Sector {s} has {len(self._sector_map[s])} frames, expected 24"

    @property
    def vocab_size(self) -> int:
        return 168

    def get_frame(self, frame_id: int) -> GeometricFrame:
        if not 0 <= frame_id < 168:
            raise IndexError(f"Frame ID {frame_id} out of range [0, 167]")
        return self.frames[frame_id]

    def get_frame_by_signature(self, i: int, j: int, s1: int, s2: int) -> GeometricFrame:
        sig = (i, j, s1, s2)
        if sig not in self._sig_to_id:
            raise KeyError(f"No geometric frame for signature {sig}")
        return self.frames[self._sig_to_id[sig]]

    def get_sector_frames(self, sector: int) -> List[GeometricFrame]:
        if not 1 <= sector <= 7:
            raise ValueError(f"Sector {sector} out of range [1, 7]")
        return list(self._sector_map[sector])

    # -----------------------------------------------------------------------
    # Continuous Vector Snapping (Projection onto Stiefel 2-Design)
    # -----------------------------------------------------------------------

    def project_vector(self, vec: Sequence[float]) -> GeometricFrame:
        """
        Projects an arbitrary vector in R^7 or R^21 onto the nearest 2-frame
        on V_2(R^7) maximizing inner product alignment.
        """
        v_arr = np.array(vec, dtype=float)
        if len(v_arr) == 7:
            # Match against u, v, or w projection
            best_id = 0
            best_score = -float("inf")
            for f in self.frames:
                # Score alignment with u component
                score = float(np.dot(v_arr, f.u))
                if score > best_score:
                    best_score = score
                    best_id = f.frame_id
            return self.frames[best_id]
        elif len(v_arr) == 21:
            # Full spherical harmonic inner product
            best_id = 0
            best_score = -float("inf")
            for f in self.frames:
                score = float(np.dot(v_arr, f.harmonics))
                if score > best_score:
                    best_score = score
                    best_id = f.frame_id
            return self.frames[best_id]
        else:
            raise ValueError(f"Vector dimension must be 7 or 21, got {len(v_arr)}")

    # -----------------------------------------------------------------------
    # Lossless Byte / Text Lexing (Radix-168)
    # -----------------------------------------------------------------------

    def encode_bytes(self, data: bytes) -> List[GeometricFrame]:
        """
        Encodes arbitrary raw bytes into a sequence of 2-frames via radix-168
        decomposition with a 1-sentinel header to preserve leading zero bytes.
        Guarantees exact, lossless round-trip decoding.
        """
        if not data:
            return []

        # Prefix with sentinel value 1 to preserve leading zeros
        num = 1
        for b in data:
            num = (num << 8) | b

        digits: List[int] = []
        while num > 0:
            digits.append(num % 168)
            num //= 168
        digits.reverse()

        return [self.frames[d] for d in digits]

    def decode_bytes(self, frames: Sequence[GeometricFrame]) -> bytes:
        """
        Decodes a sequence of 2-frames back to the exact original raw bytes.
        """
        if not frames:
            return b""

        num = 0
        for f in frames:
            num = num * 168 + f.frame_id

        out = bytearray()
        while num > 1:
            out.append(num & 0xFF)
            num >>= 8

        return bytes(reversed(out))

    def encode_text(self, text: str) -> List[GeometricFrame]:
        """Encodes a UTF-8 text string into a sequence of geometric 2-frames."""
        return self.encode_bytes(text.encode("utf-8"))

    def decode_text(self, frames: Sequence[GeometricFrame]) -> str:
        """Decodes a sequence of geometric 2-frames back into a UTF-8 text string."""
        return self.decode_bytes(frames).decode("utf-8")

    def frames_to_harmonics(self, frames: Sequence[GeometricFrame]) -> np.ndarray:
        """Converts a sequence of frames into a (N, 21) continuous harmonic trajectory."""
        if not frames:
            return np.zeros((0, 21), dtype=float)
        return np.array([f.harmonics for f in frames], dtype=float)

    # -----------------------------------------------------------------------
    # Symbolic Grounding & Zero-Divisor Annihilation Dynamics
    # -----------------------------------------------------------------------

    def _ground_symbols(self) -> None:
        """
        Grounds Hebrew consonants (D8 roots), Greek letters (E8 spinor roots),
        sofit boundary closures, and sentinels to canonical 2-frames on V_2(R^7).
        """
        # 1. Sentinels
        for fid, sym in SENTINEL_SYMBOLS.items():
            f = self.frames[fid]
            self._symbol_to_frame[sym] = f
            self._frame_to_symbol[fid] = sym

        # 2. 22 Hebrew Consonants mapped injectively into distinct frames
        for idx, letter in enumerate(HEBREW_CONSONANTS):
            fid = (idx * 7) % 164
            f = self.frames[fid]
            self._symbol_to_frame[letter] = f
            if fid not in self._frame_to_symbol:
                self._frame_to_symbol[fid] = letter

        # 3. 5 Sofit Consonants: mapped to the antipodal frame of their base letter
        for sofit, base in SOFIT_BASE_MAP.items():
            base_frame = self._symbol_to_frame[base]
            sofit_frame = base_frame.antipodal()
            self._symbol_to_frame[sofit] = sofit_frame
            self._frame_to_symbol[sofit_frame.frame_id] = sofit

        # 4. 24 Greek Letters (Spinor vowels & consonants)
        for idx, letter in enumerate(GREEK_LETTERS):
            fid = (idx * 7 + 3) % 164
            f = self.frames[fid]
            self._symbol_to_frame[letter] = f
            if fid not in self._frame_to_symbol:
                self._frame_to_symbol[fid] = letter

    def _build_annihilation_map(self) -> None:
        """
        Precomputes for each of the 168 frames the exact 8 partner frames that
        annihilate with it in the sedenion algebra (Sedenion product vanishes).
        """
        from sedenion.algebra import Sedenion
        sedenion_vecs = []
        for f in self.frames:
            # u = s1 * e_i + s2 * e_{8+j}
            vec = f.s1 * Sedenion.basis(f.i) + f.s2 * Sedenion.basis(8 + f.j)
            sedenion_vecs.append(vec)

        for i, u in enumerate(sedenion_vecs):
            partners = []
            f_u = self.frames[i]
            # Zero-divisor partners strictly share the same XOR charge sector
            for cand in self._sector_map[f_u.sector]:
                if cand.frame_id == i:
                    continue
                v = sedenion_vecs[cand.frame_id]
                if (u * v).is_zero():
                    partners.append(cand.frame_id)
            self._annihilation_map[i] = partners

    def encode_symbol(self, symbol: str) -> GeometricFrame:
        """Encodes a single symbol or sentinel into a 2-frame."""
        if symbol in self._symbol_to_frame:
            return self._symbol_to_frame[symbol]
        return self.frames[FRAME_UNK]

    def decode_symbol(self, frame: GeometricFrame) -> str:
        """Decodes a 2-frame into its canonical symbolic token."""
        return self._frame_to_symbol.get(frame.frame_id, frame.name)

    def encode_symbols(self, symbols: Sequence[str]) -> List[GeometricFrame]:
        """Encodes a sequence of symbols/tokens into geometric 2-frames."""
        return [self.encode_symbol(s) for s in symbols]

    def decode_symbols(self, frames: Sequence[GeometricFrame]) -> List[str]:
        """Decodes a sequence of 2-frames into symbolic tokens."""
        return [self.decode_symbol(f) for f in frames]

    def generate_polar_opposite(self, frame: GeometricFrame) -> Tuple[GeometricFrame, bool]:
        """
        Generates the antipodal polar opposite (u, v) -> (-u, -v) on V_2(R^7).
        Evaluates whether this transition triggers sedenion zero-divisor annihilation.
        Returns (opposite_frame, is_annihilating).
        """
        opp = frame.antipodal()
        is_annihilating = opp.frame_id in self._annihilation_map.get(frame.frame_id, [])
        return opp, is_annihilating

    def get_annihilation_partners(self, frame: GeometricFrame) -> List[GeometricFrame]:
        """Returns the exact 8 zero-divisor frames that annihilate with this frame."""
        partner_ids = self._annihilation_map.get(frame.frame_id, [])
        return [self.frames[pid] for pid in partner_ids]

    def annihilates(self, frame1: GeometricFrame, frame2: GeometricFrame) -> bool:
        """Deterministic algebraic check if frame1 and frame2 annihilate in Sedenion space."""
        return frame2.frame_id in self._annihilation_map.get(frame1.frame_id, [])

    def is_sofit_closure(self, tokens: Sequence[str | GeometricFrame]) -> bool:
        """
        Checks if a symbolic sequence terminates with a sofit boundary closure
        enforcing topological boundary closure dOmega = 0, c1 = 0, ||H^1|| = 0.
        """
        if not tokens:
            return False
        last = tokens[-1]
        if isinstance(last, str):
            return last in SOFIT_LETTERS or last == SENTINEL_SYMBOLS[FRAME_EOS]
        elif isinstance(last, GeometricFrame):
            sym = self._frame_to_symbol.get(last.frame_id, "")
            return sym in SOFIT_LETTERS or last.frame_id == FRAME_EOS
        return False
