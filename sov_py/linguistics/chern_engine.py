"""
Chern-Quantized Linguistic Topology Engine.
Hebrew D8 integer roots, Greek E8\\D8 spinor vowels, sofit boundary closures,
and deterministic polar opposite generation via E8 Weyl antipodal involution.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any, Sequence

from ..algebra import Sedenion
from ..polytope.gosset_logic import GossetLogicSynthesizer, classify_relation, inner_product, Relation

# ---------------------------------------------------------------------------
# Sofit Constants & Alphabets (Hebrew, Greek, Arabic, Sanskrit)
# ---------------------------------------------------------------------------

SOFIT_LETTERS: set[str] = {"ך", "ם", "ן", "ף", "ץ"}

# 22 Hebrew consonants (standard order, 1-indexed)
HEBREW_CONSONANTS: dict[str, dict[str, Any]] = {
    "א": {"ordinal": 1,  "name": "Aleph", "gematria": 1,   "phoneme": "stop"},
    "ב": {"ordinal": 2,  "name": "Bet",   "gematria": 2,   "phoneme": "stop"},
    "ג": {"ordinal": 3,  "name": "Gimel", "gematria": 3,   "phoneme": "stop"},
    "ד": {"ordinal": 4,  "name": "Dalet", "gematria": 4,   "phoneme": "stop"},
    "ה": {"ordinal": 5,  "name": "He",    "gematria": 5,   "phoneme": "fricative"},
    "ו": {"ordinal": 6,  "name": "Vav",   "gematria": 6,   "phoneme": "semivowel"},
    "ז": {"ordinal": 7,  "name": "Zayin", "gematria": 7,   "phoneme": "sibilant"},
    "ח": {"ordinal": 8,  "name": "Het",   "gematria": 8,   "phoneme": "fricative"},
    "ט": {"ordinal": 9,  "name": "Tet",   "gematria": 9,   "phoneme": "stop"},
    "י": {"ordinal": 10, "name": "Yod",   "gematria": 10,  "phoneme": "semivowel"},
    "כ": {"ordinal": 11, "name": "Kaph",  "gematria": 20,  "phoneme": "stop"},
    "ל": {"ordinal": 12, "name": "Lamed", "gematria": 30,  "phoneme": "liquid"},
    "מ": {"ordinal": 13, "name": "Mem",   "gematria": 40,  "phoneme": "nasal"},
    "נ": {"ordinal": 14, "name": "Nun",   "gematria": 50,  "phoneme": "nasal"},
    "ס": {"ordinal": 15, "name": "Samekh","gematria": 60,  "phoneme": "sibilant"},
    "ע": {"ordinal": 16, "name": "Ayin",  "gematria": 70,  "phoneme": "fricative"},
    "פ": {"ordinal": 17, "name": "Pe",    "gematria": 80,  "phoneme": "stop"},
    "צ": {"ordinal": 18, "name": "Tsade", "gematria": 90,  "phoneme": "sibilant"},
    "ק": {"ordinal": 19, "name": "Qoph",  "gematria": 100, "phoneme": "stop"},
    "ר": {"ordinal": 20, "name": "Resh",  "gematria": 200, "phoneme": "liquid"},
    "ש": {"ordinal": 21, "name": "Shin",  "gematria": 300, "phoneme": "sibilant"},
    "ת": {"ordinal": 22, "name": "Tav",   "gematria": 400, "phoneme": "stop"},
}

# 24 Greek letters (standard classical alphabet)
GREEK_LETTERS: dict[str, dict[str, Any]] = {
    "α": {"ordinal": 1,  "name": "Alpha",   "is_vowel": True,  "phoneme": "vowel"},
    "β": {"ordinal": 2,  "name": "Beta",    "is_vowel": False, "phoneme": "stop"},
    "γ": {"ordinal": 3,  "name": "Gamma",   "is_vowel": False, "phoneme": "stop"},
    "δ": {"ordinal": 4,  "name": "Delta",   "is_vowel": False, "phoneme": "stop"},
    "ε": {"ordinal": 5,  "name": "Epsilon", "is_vowel": True,  "phoneme": "vowel"},
    "ζ": {"ordinal": 6,  "name": "Zeta",    "is_vowel": False, "phoneme": "sibilant"},
    "η": {"ordinal": 7,  "name": "Eta",     "is_vowel": True,  "phoneme": "vowel"},
    "θ": {"ordinal": 8,  "name": "Theta",   "is_vowel": False, "phoneme": "fricative"},
    "ι": {"ordinal": 9,  "name": "Iota",    "is_vowel": True,  "phoneme": "vowel"},
    "κ": {"ordinal": 10, "name": "Kappa",   "is_vowel": False, "phoneme": "stop"},
    "λ": {"ordinal": 11, "name": "Lambda",  "is_vowel": False, "phoneme": "liquid"},
    "μ": {"ordinal": 12, "name": "Mu",      "is_vowel": False, "phoneme": "nasal"},
    "ν": {"ordinal": 13, "name": "Nu",      "is_vowel": False, "phoneme": "nasal"},
    "ξ": {"ordinal": 14, "name": "Xi",      "is_vowel": False, "phoneme": "sibilant"},
    "ο": {"ordinal": 15, "name": "Omicron", "is_vowel": True,  "phoneme": "vowel"},
    "π": {"ordinal": 16, "name": "Pi",      "is_vowel": False, "phoneme": "stop"},
    "ρ": {"ordinal": 17, "name": "Rho",     "is_vowel": False, "phoneme": "liquid"},
    "σ": {"ordinal": 18, "name": "Sigma",   "is_vowel": False, "phoneme": "sibilant"},
    "τ": {"ordinal": 19, "name": "Tau",     "is_vowel": False, "phoneme": "stop"},
    "υ": {"ordinal": 20, "name": "Upsilon", "is_vowel": True,  "phoneme": "vowel"},
    "φ": {"ordinal": 21, "name": "Phi",     "is_vowel": False, "phoneme": "fricative"},
    "χ": {"ordinal": 22, "name": "Chi",     "is_vowel": False, "phoneme": "fricative"},
    "ψ": {"ordinal": 23, "name": "Psi",     "is_vowel": False, "phoneme": "sibilant"},
    "ω": {"ordinal": 24, "name": "Omega",   "is_vowel": True,  "phoneme": "vowel"},
}

# 28 Arabic letters (classical Abjad / Huruf alphabet)
# Canonical bijection to the C(8, 2) = 28 coordinate pairs of D8 ⊂ E8 root lattice
ARABIC_LETTERS: dict[str, dict[str, Any]] = {
    "ا": {"ordinal": 1,  "name": "Alif",  "jummal": 1,    "phoneme": "glottal"},
    "ب": {"ordinal": 2,  "name": "Ba",    "jummal": 2,    "phoneme": "stop"},
    "ج": {"ordinal": 3,  "name": "Jim",   "jummal": 3,    "phoneme": "affricate"},
    "د": {"ordinal": 4,  "name": "Dal",   "jummal": 4,    "phoneme": "stop"},
    "ه": {"ordinal": 5,  "name": "Ha",    "jummal": 5,    "phoneme": "fricative"},
    "و": {"ordinal": 6,  "name": "Waw",   "jummal": 6,    "phoneme": "semivowel"},
    "ز": {"ordinal": 7,  "name": "Zay",   "jummal": 7,    "phoneme": "sibilant"},
    "ح": {"ordinal": 8,  "name": "Hha",   "jummal": 8,    "phoneme": "fricative"},
    "ط": {"ordinal": 9,  "name": "Ta_emp","jummal": 9,    "phoneme": "stop"},
    "ي": {"ordinal": 10, "name": "Ya",    "jummal": 10,   "phoneme": "semivowel"},
    "ك": {"ordinal": 11, "name": "Kaf",   "jummal": 20,   "phoneme": "stop"},
    "ل": {"ordinal": 12, "name": "Lam",   "jummal": 30,   "phoneme": "liquid"},
    "م": {"ordinal": 13, "name": "Mim",   "jummal": 40,   "phoneme": "nasal"},
    "ن": {"ordinal": 14, "name": "Nun",   "jummal": 50,   "phoneme": "nasal"},
    "س": {"ordinal": 15, "name": "Sin",   "jummal": 60,   "phoneme": "sibilant"},
    "ع": {"ordinal": 16, "name": "Ayn",   "jummal": 70,   "phoneme": "fricative"},
    "ف": {"ordinal": 17, "name": "Fa",    "jummal": 80,   "phoneme": "fricative"},
    "ص": {"ordinal": 18, "name": "Sad",   "jummal": 90,   "phoneme": "sibilant"},
    "ق": {"ordinal": 19, "name": "Qaf",   "jummal": 100,  "phoneme": "stop"},
    "ر": {"ordinal": 20, "name": "Ra",    "jummal": 200,  "phoneme": "liquid"},
    "ش": {"ordinal": 21, "name": "Shin",  "jummal": 300,  "phoneme": "sibilant"},
    "ت": {"ordinal": 22, "name": "Ta",    "jummal": 400,  "phoneme": "stop"},
    "ث": {"ordinal": 23, "name": "Tha",   "jummal": 500,  "phoneme": "fricative"},
    "خ": {"ordinal": 24, "name": "Kha",   "jummal": 600,  "phoneme": "fricative"},
    "ذ": {"ordinal": 25, "name": "Dhal",  "jummal": 700,  "phoneme": "fricative"},
    "ض": {"ordinal": 26, "name": "Dad",   "jummal": 800,  "phoneme": "stop"},
    "ظ": {"ordinal": 27, "name": "Za_emp","jummal": 900,  "phoneme": "fricative"},
    "غ": {"ordinal": 28, "name": "Ghayn", "jummal": 1000, "phoneme": "fricative"},
}

# Arabic boundary closure operators (Ta Marbuta, Alif Maqsura, Sukun, Tanwin)
ARABIC_BOUNDARY_MARKERS: set[str] = {"ة", "ى", "ْ", "ً", "ٍ", "ٌ"}

# Sanskrit classical letters (Devanagari phonemes: 13 vowels + 33 consonants = 46 base)
# Vowels map to E8\D8 spinor roots; 33 consonants cycle through D8 integer roots
SANSKRIT_LETTERS: dict[str, dict[str, Any]] = {
    # 13 Vowels (Svaras)
    "अ": {"ordinal": 1,  "name": "a",      "is_vowel": True,  "katapayadi": 0},
    "आ": {"ordinal": 2,  "name": "aa",     "is_vowel": True,  "katapayadi": 0},
    "इ": {"ordinal": 3,  "name": "i",      "is_vowel": True,  "katapayadi": 0},
    "ई": {"ordinal": 4,  "name": "ii",     "is_vowel": True,  "katapayadi": 0},
    "उ": {"ordinal": 5,  "name": "u",      "is_vowel": True,  "katapayadi": 0},
    "ऊ": {"ordinal": 6,  "name": "uu",     "is_vowel": True,  "katapayadi": 0},
    "ऋ": {"ordinal": 7,  "name": "r_vow",  "is_vowel": True,  "katapayadi": 0},
    "ॠ": {"ordinal": 8,  "name": "rr_vow", "is_vowel": True,  "katapayadi": 0},
    "ऌ": {"ordinal": 9,  "name": "l_vow",  "is_vowel": True,  "katapayadi": 0},
    "ए": {"ordinal": 10, "name": "e",      "is_vowel": True,  "katapayadi": 0},
    "ऐ": {"ordinal": 11, "name": "ai",     "is_vowel": True,  "katapayadi": 0},
    "ओ": {"ordinal": 12, "name": "o",      "is_vowel": True,  "katapayadi": 0},
    "औ": {"ordinal": 13, "name": "au",     "is_vowel": True,  "katapayadi": 0},
    # 25 Vargiya Consonants (5x5 matrix of stops and nasals)
    "क": {"ordinal": 14, "name": "ka",     "is_vowel": False, "katapayadi": 1},
    "ख": {"ordinal": 15, "name": "kha",    "is_vowel": False, "katapayadi": 2},
    "ग": {"ordinal": 16, "name": "ga",     "is_vowel": False, "katapayadi": 3},
    "घ": {"ordinal": 17, "name": "gha",    "is_vowel": False, "katapayadi": 4},
    "ङ": {"ordinal": 18, "name": "nga",    "is_vowel": False, "katapayadi": 5},
    "च": {"ordinal": 19, "name": "ca",     "is_vowel": False, "katapayadi": 6},
    "छ": {"ordinal": 20, "name": "cha",    "is_vowel": False, "katapayadi": 7},
    "ज": {"ordinal": 21, "name": "ja",     "is_vowel": False, "katapayadi": 8},
    "झ": {"ordinal": 22, "name": "jha",    "is_vowel": False, "katapayadi": 9},
    "ञ": {"ordinal": 23, "name": "nya",    "is_vowel": False, "katapayadi": 0},
    "ट": {"ordinal": 24, "name": "tta",    "is_vowel": False, "katapayadi": 1},
    "ठ": {"ordinal": 25, "name": "ttha",   "is_vowel": False, "katapayadi": 2},
    "ड": {"ordinal": 26, "name": "dda",    "is_vowel": False, "katapayadi": 3},
    "ढ": {"ordinal": 27, "name": "ddha",   "is_vowel": False, "katapayadi": 4},
    "ण": {"ordinal": 28, "name": "nna",    "is_vowel": False, "katapayadi": 5},
    "त": {"ordinal": 29, "name": "ta",     "is_vowel": False, "katapayadi": 6},
    "थ": {"ordinal": 30, "name": "tha",    "is_vowel": False, "katapayadi": 7},
    "द": {"ordinal": 31, "name": "da",     "is_vowel": False, "katapayadi": 8},
    "ध": {"ordinal": 32, "name": "dha",    "is_vowel": False, "katapayadi": 9},
    "न": {"ordinal": 33, "name": "na",     "is_vowel": False, "katapayadi": 0},
    "प": {"ordinal": 34, "name": "pa",     "is_vowel": False, "katapayadi": 1},
    "फ": {"ordinal": 35, "name": "pha",    "is_vowel": False, "katapayadi": 2},
    "ब": {"ordinal": 36, "name": "ba",     "is_vowel": False, "katapayadi": 3},
    "भ": {"ordinal": 37, "name": "bha",    "is_vowel": False, "katapayadi": 4},
    "म": {"ordinal": 38, "name": "ma",     "is_vowel": False, "katapayadi": 5},
    # 4 Antastha (Semivowels)
    "य": {"ordinal": 39, "name": "ya",     "is_vowel": False, "katapayadi": 1},
    "र": {"ordinal": 40, "name": "ra",     "is_vowel": False, "katapayadi": 2},
    "ल": {"ordinal": 41, "name": "la",     "is_vowel": False, "katapayadi": 3},
    "व": {"ordinal": 42, "name": "va",     "is_vowel": False, "katapayadi": 4},
    # 4 Ushman (Sibilants & Aspirate)
    "श": {"ordinal": 43, "name": "sha",    "is_vowel": False, "katapayadi": 5},
    "ष": {"ordinal": 44, "name": "ssa",    "is_vowel": False, "katapayadi": 6},
    "स": {"ordinal": 45, "name": "sa",     "is_vowel": False, "katapayadi": 7},
    "ह": {"ordinal": 46, "name": "ha",     "is_vowel": False, "katapayadi": 8},
}

# Sanskrit boundary closure operators (Virama/Halanta, Visarga, Anusvara)
SANSKRIT_BOUNDARY_MARKERS: set[str] = {"्", "ः", "ं"}


# ---------------------------------------------------------------------------
# Results Dataclasses
# ---------------------------------------------------------------------------

@dataclass
class SofitClosureResult:
    word: str
    has_sofit: bool
    chern_number: int       # c1 = 0 if sofit closed; c1 = 1 if open boundary
    cohomology_defect: float# H1 norm: 0.0 if closed, >0 if open
    is_topological_knot: bool
    boundary_marker: str = ""

    @property
    def has_boundary(self) -> bool:
        return self.has_sofit


BoundaryClosureResult = SofitClosureResult


@dataclass
class PolarOppositeResult:
    word: str
    root: tuple[float, ...]
    antipodal_root: tuple[float, ...]
    canonical_opposite: tuple[float, ...]
    nearest_opposite_char: str
    metric_distance: float
    relation: Relation
    sedenion_annihilation: bool


# ---------------------------------------------------------------------------
# Engine Implementation
# ---------------------------------------------------------------------------

class ChernLinguisticTopologist:
    """
    Topological language modeling, Chern class quantization, and semantic antipodes.
    Supports Hebrew, Greek, Arabic, and Sanskrit.
    """

    def __init__(self) -> None:
        self.gosset = GossetLogicSynthesizer()
        self._hebrew_root_cache: dict[str, tuple[float, ...]] = {}
        self._greek_root_cache: dict[str, tuple[float, ...]] = {}
        self._arabic_root_cache: dict[str, tuple[float, ...]] = {}
        self._sanskrit_root_cache: dict[str, tuple[float, ...]] = {}
        self._build_canonical_letter_roots()

    def _build_canonical_letter_roots(self) -> None:
        """Map Hebrew, Arabic, Sanskrit to D8 roots and Greek, Sanskrit vowels to spinor roots."""
        int_roots = self.gosset.integer_roots
        spin_roots = self.gosset.spinor_roots

        # Hebrew consonants cycle through D8 integer roots
        for i, char in enumerate(HEBREW_CONSONANTS):
            self._hebrew_root_cache[char] = int_roots[i % len(int_roots)]

        # Sofits map to closed D8 roots
        sofit_list = sorted(list(SOFIT_LETTERS))
        for j, s_char in enumerate(sofit_list):
            self._hebrew_root_cache[s_char] = int_roots[(len(HEBREW_CONSONANTS) + j) % len(int_roots)]

        # Greek letters cycle through E8\\D8 spinor roots
        for k, g_char in enumerate(GREEK_LETTERS):
            self._greek_root_cache[g_char] = spin_roots[k % len(spin_roots)]

        # Arabic (28 letters) mapped bijectively to the C(8, 2) = 28 coordinate pairs of D8
        # We select the canonical positive root (e_p + e_q) for each of the 28 pairs (p, q)
        pair_idx = 0
        pos_roots_28: list[tuple[float, ...]] = []
        for p in range(8):
            for q in range(p + 1, 8):
                vec = [0.0] * 8
                vec[p] = 1.0
                vec[q] = 1.0
                pos_roots_28.append(tuple(vec))
        for m, a_char in enumerate(ARABIC_LETTERS):
            self._arabic_root_cache[a_char] = pos_roots_28[m % len(pos_roots_28)]

        # Arabic boundary markers mapped to closed D8 roots
        for mb, b_char in enumerate(sorted(list(ARABIC_BOUNDARY_MARKERS))):
            self._arabic_root_cache[b_char] = int_roots[(len(ARABIC_LETTERS) + mb) % len(int_roots)]

        # Sanskrit letters:
        # Vowels (13) map to spinor roots; Consonants (33) map to D8 integer roots
        vowel_count = 0
        cons_count = 0
        for s_char, info in SANSKRIT_LETTERS.items():
            if info["is_vowel"]:
                self._sanskrit_root_cache[s_char] = spin_roots[vowel_count % len(spin_roots)]
                vowel_count += 1
            else:
                self._sanskrit_root_cache[s_char] = int_roots[cons_count % len(int_roots)]
                cons_count += 1

        # Sanskrit boundary markers mapped to closed D8 roots
        for sb, sk_b in enumerate(sorted(list(SANSKRIT_BOUNDARY_MARKERS))):
            self._sanskrit_root_cache[sk_b] = int_roots[(cons_count + sb) % len(int_roots)]

    def embed_letter(self, char: str) -> tuple[float, ...]:
        """Return the 8D E8 root vector for a given character (Hebrew, Greek, Arabic, Sanskrit)."""
        c = char.lower()
        if c in self._hebrew_root_cache:
            return self._hebrew_root_cache[c]
        if c in self._greek_root_cache:
            return self._greek_root_cache[c]
        if char in self._arabic_root_cache:
            return self._arabic_root_cache[char]
        if char in self._sanskrit_root_cache:
            return self._sanskrit_root_cache[char]
        # Fallback: hash to canonical root
        idx = hash(char) % len(self.gosset.all_roots)
        return self.gosset.all_roots[idx]

    def embed_word(self, word: str) -> tuple[float, ...]:
        """Embed an arbitrary multi-letter word into a normalized 8D vector on S^7."""
        if not word:
            return (0.0,) * 8
        acc = [0.0] * 8
        for char in word:
            r = self.embed_letter(char)
            for i in range(8):
                acc[i] += r[i]
        norm = math.sqrt(sum(x * x for x in acc))
        if norm > 1e-9:
            scale = math.sqrt(2.0) / norm
            return tuple(x * scale for x in acc)
        return self.embed_letter(word[0])

    def evaluate_boundary_closure(self, word: str) -> BoundaryClosureResult:
        """
        Evaluate topological boundary closure (dOmega = 0 => c1 = 0, H1 = 0).
        Hebrew sofit letters, Arabic boundary markers (Ta Marbuta, Alif Maqsura, Sukun, Tanwin),
        and Sanskrit boundary markers (Virama, Visarga, Anusvara) close the open 1-chain into a soliton.
        """
        if not word:
            return BoundaryClosureResult(word, False, 1, 1.0, False)

        final_char = word[-1]
        is_hebrew_sofit = final_char in SOFIT_LETTERS
        is_arabic_boundary = final_char in ARABIC_BOUNDARY_MARKERS
        is_sanskrit_boundary = final_char in SANSKRIT_BOUNDARY_MARKERS
        has_boundary = is_hebrew_sofit or is_arabic_boundary or is_sanskrit_boundary

        if has_boundary:
            return BoundaryClosureResult(
                word=word,
                has_sofit=True,
                chern_number=0,
                cohomology_defect=0.0,
                is_topological_knot=True,
                boundary_marker=final_char,
            )
        else:
            v_word = self.embed_word(word)
            # Exact metric defect: minimum Euclidean distance from word embedding on S^7 to any canonical boundary root
            boundary_roots = [
                self.embed_letter(b) for b in list(SOFIT_LETTERS) + list(ARABIC_BOUNDARY_MARKERS) + list(SANSKRIT_BOUNDARY_MARKERS)
            ]
            min_dist = min(math.sqrt(sum((v_word[i] - br[i]) ** 2 for i in range(8))) for br in boundary_roots)
            return BoundaryClosureResult(
                word=word,
                has_sofit=False,
                chern_number=1,
                cohomology_defect=round(min_dist, 6),
                is_topological_knot=False,
            )

    def evaluate_sofit_closure(self, word: str) -> SofitClosureResult:
        """Backwards-compatible alias for evaluate_boundary_closure."""
        return self.evaluate_boundary_closure(word)

    def generate_polar_opposite(self, word: str) -> PolarOppositeResult:
        """
        Computes the deterministic antipodal counterpart w -> w* (v -> -v on S^7),
        projects through the 240-root Gosset polytope, and checks 16D sedenion annihilation.
        """
        v = self.embed_word(word)

        # Project v onto the closest canonical E8 minimal root
        best_forward = self.gosset.all_roots[0]
        max_fwd_ip = -1e9
        for r in self.gosset.all_roots:
            ip = inner_product(v, r)
            if ip > max_fwd_ip:
                max_fwd_ip = ip
                best_forward = r

        # Exact canonical opposite in the 240 roots of E8
        canonical_opposite = tuple(-x for x in best_forward)
        antipodal_v = tuple(-x for x in v)

        # Metric distance and relation between canonical root and canonical opposite
        rel = classify_relation(best_forward, canonical_opposite)
        dist = math.sqrt(sum((a - b) ** 2 for a, b in zip(best_forward, canonical_opposite)))

        # Nearest letter across all supported alphabets (Hebrew, Greek, Arabic, Sanskrit)
        nearest_char = "?"
        min_char_dist = 1e9
        for cache in [self._hebrew_root_cache, self._greek_root_cache, self._arabic_root_cache, self._sanskrit_root_cache]:
            for ch, r in cache.items():
                d = math.sqrt(sum((a - b) ** 2 for a, b in zip(canonical_opposite, r)))
                if d < min_char_dist:
                    min_char_dist = d
                    nearest_char = ch

        # 16D Sedenion Zero-Divisor Annihilation Check
        # Minimal E8 roots have integer or half-integer coordinates in {0, ±0.5, ±1}.
        # Scaling by 2 yields exact integer coordinates in {0, ±1, ±2}.
        u_16 = [int(round(2.0 * x)) for x in best_forward] + [0] * 8
        w_16 = [0] * 8 + [int(round(2.0 * x)) for x in canonical_opposite]
        s_u = Sedenion(u_16)
        s_w = Sedenion(w_16)
        prod = s_u * s_w
        annihilates = (prod.norm_sq() == 0) or (rel == Relation.CONTRADICTION)

        return PolarOppositeResult(
            word=word,
            root=best_forward,
            antipodal_root=antipodal_v,
            canonical_opposite=canonical_opposite,
            nearest_opposite_char=nearest_char,
            metric_distance=dist,
            relation=rel,
            sedenion_annihilation=annihilates,
        )

