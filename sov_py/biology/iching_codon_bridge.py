"""
Universal Tetrachromatic Splitter and 64 I Ching Codon Bridge.

Mathematical & Biological Foundations:
1. Tetrachromatic Splitter (4-spinor decomposition):
   Maps 4 nucleotides {A, C, G, T} to the 4 vertices of the tetrahedron K₄:
   A -> (0, 0), C -> (0, 1), G -> (1, 0), T -> (1, 1).
2. 64 Codons = 4³ = 2⁶ isomorphic to the 64 I Ching hexagrams:
   Each triplet (b₁, b₂, b₃) maps to a 6-bit integer c ∈ {0, ..., 63}.
3. Chingon (D=64) basis element embedding:
   Codon index c corresponds to basis unit e_c in the 64-dimensional Cayley-Dickson algebra.
4. Standard Genetic Code Translation:
   Translates all 64 codons into 20 amino acids + Stop signals.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

from ..grammar.classical_chinese_bridge import Trigram, Hexagram


@dataclass(frozen=True)
class CodonInfo:
    codon: str
    hexagram_index: int  # 0 to 63
    bitstring: str  # 6-bit binary string
    amino_acid: str  # 1-letter amino acid symbol
    amino_acid_name: str
    is_stop: bool
    hydrophobicity: float  # Kyte-Doolittle scale
    hexagram: Optional[Hexagram] = None


class TetrachromaticSplitter:
    """
    4-state spinor decomposition on F₂²:
    A: 00, C: 01, G: 10, T: 11.
    """

    NUCLEOTIDE_BITS = {
        "A": (0, 0),
        "C": (0, 1),
        "G": (1, 0),
        "T": (1, 1),
        "U": (1, 1),  # RNA support
    }

    @classmethod
    def split_nucleotide(cls, nuc: str) -> Tuple[int, int]:
        nuc_clean = nuc.upper()
        if nuc_clean not in cls.NUCLEOTIDE_BITS:
            raise ValueError(f"Invalid nucleotide: {nuc}")
        return cls.NUCLEOTIDE_BITS[nuc_clean]

    @classmethod
    def encode_triplet(cls, triplet: str) -> Tuple[int, str]:
        """Encodes 3-nucleotide codon into 6-bit integer and bitstring."""
        if len(triplet) != 3:
            raise ValueError(f"Codon must be of length 3, got: {triplet}")
        bits = []
        for nuc in triplet.upper():
            b1, b2 = cls.split_nucleotide(nuc)
            bits.extend([b1, b2])

        val = 0
        for bit in bits:
            val = (val << 1) | bit
        bitstr = "".join(str(b) for b in bits)
        return val, bitstr


class IChingCodonBridge:
    """
    Bridges the 64 Genetic Codons, 64 I Ching Hexagrams, and D=64 Chingon algebra.
    """

    # Standard genetic code dictionary
    GENETIC_CODE: Dict[str, Tuple[str, str, float]] = {
        # Codon: (1-letter, Name, Kyte-Doolittle Hydrophobicity)
        "TTT": ("F", "Phenylalanine", 2.8), "TTC": ("F", "Phenylalanine", 2.8),
        "TTA": ("L", "Leucine", 3.8), "TTG": ("L", "Leucine", 3.8),
        "CTT": ("L", "Leucine", 3.8), "CTC": ("L", "Leucine", 3.8),
        "CTA": ("L", "Leucine", 3.8), "CTG": ("L", "Leucine", 3.8),
        "ATT": ("I", "Isoleucine", 4.5), "ATC": ("I", "Isoleucine", 4.5),
        "ATA": ("I", "Isoleucine", 4.5), "ATG": ("M", "Methionine", 1.9),
        "GTT": ("V", "Valine", 4.2), "GTC": ("V", "Valine", 4.2),
        "GTA": ("V", "Valine", 4.2), "GTG": ("V", "Valine", 4.2),
        "TCT": ("S", "Serine", -0.8), "TCC": ("S", "Serine", -0.8),
        "TCA": ("S", "Serine", -0.8), "TCG": ("S", "Serine", -0.8),
        "CCT": ("P", "Proline", -1.6), "CCC": ("P", "Proline", -1.6),
        "CCA": ("P", "Proline", -1.6), "CCG": ("P", "Proline", -1.6),
        "ACT": ("T", "Threonine", -0.7), "ACC": ("T", "Threonine", -0.7),
        "ACA": ("T", "Threonine", -0.7), "ACG": ("T", "Threonine", -0.7),
        "GCT": ("A", "Alanine", 1.8), "GCC": ("A", "Alanine", 1.8),
        "GCA": ("A", "Alanine", 1.8), "GCG": ("A", "Alanine", 1.8),
        "TAT": ("Y", "Tyrosine", -1.3), "TAC": ("Y", "Tyrosine", -1.3),
        "TAA": ("*", "Stop", 0.0), "TAG": ("*", "Stop", 0.0),
        "CAT": ("H", "Histidine", -3.2), "CAC": ("H", "Histidine", -3.2),
        "CAA": ("Q", "Glutamine", -3.5), "CAG": ("Q", "Glutamine", -3.5),
        "AAT": ("N", "Asparagine", -3.5), "AAC": ("N", "Asparagine", -3.5),
        "AAA": ("K", "Lysine", -3.9), "AAG": ("K", "Lysine", -3.9),
        "GAT": ("D", "Aspartate", -3.5), "GAC": ("D", "Aspartate", -3.5),
        "GAA": ("E", "Glutamate", -3.5), "GAG": ("E", "Glutamate", -3.5),
        "TGT": ("C", "Cysteine", 2.5), "TGC": ("C", "Cysteine", 2.5),
        "TGA": ("*", "Stop", 0.0), "TGG": ("W", "Tryptophan", -0.9),
        "CGT": ("R", "Arginine", -4.5), "CGC": ("R", "Arginine", -4.5),
        "CGA": ("R", "Arginine", -4.5), "CGG": ("R", "Arginine", -4.5),
        "AGT": ("S", "Serine", -0.8), "AGC": ("S", "Serine", -0.8),
        "AGA": ("R", "Arginine", -4.5), "AGG": ("R", "Arginine", -4.5),
        "GGT": ("G", "Glycine", -0.4), "GGC": ("G", "Glycine", -0.4),
        "GGA": ("G", "Glycine", -0.4), "GGG": ("G", "Glycine", -0.4),
    }

    def __init__(self) -> None:
        self.codons_map: Dict[str, CodonInfo] = {}
        self.hexagram_to_codon: Dict[int, CodonInfo] = {}

        bases = ["T", "C", "A", "G"]
        for b1 in bases:
            for b2 in bases:
                for b3 in bases:
                    triplet = f"{b1}{b2}{b3}"
                    hex_idx, bitstr = TetrachromaticSplitter.encode_triplet(triplet)
                    aa, name, hydro = self.GENETIC_CODE[triplet]
                    hex_obj = Hexagram.from_index(hex_idx)
                    c_info = CodonInfo(
                        codon=triplet,
                        hexagram_index=hex_idx,
                        bitstring=bitstr,
                        amino_acid=aa,
                        amino_acid_name=name,
                        is_stop=(aa == "*"),
                        hydrophobicity=hydro,
                        hexagram=hex_obj,
                    )
                    self.codons_map[triplet] = c_info
                    self.hexagram_to_codon[hex_idx] = c_info

        assert len(self.codons_map) == 64, f"Expected 64 codons, got {len(self.codons_map)}"

    def translate_dna(self, dna_sequence: str) -> Tuple[str, List[CodonInfo]]:
        """Translates a DNA sequence into amino acid string and codon metadata."""
        clean_dna = dna_sequence.upper().replace(" ", "").replace("\n", "").replace("U", "T")
        n = len(clean_dna) - (len(clean_dna) % 3)
        amino_acids: List[str] = []
        infos: List[CodonInfo] = []

        for i in range(0, n, 3):
            triplet = clean_dna[i : i + 3]
            info = self.codons_map[triplet]
            infos.append(info)
            amino_acids.append(info.amino_acid)

        return "".join(amino_acids), infos

    def get_chingon_basis_index(self, codon: str) -> int:
        """Returns the D=64 basis index e_c for this codon."""
        clean = codon.upper().replace("U", "T")
        return self.codons_map[clean].hexagram_index

    def total_codons(self) -> int:
        return len(self.codons_map)

    def get_codon_by_hexagram_index(self, hex_idx: int) -> CodonInfo:
        """Returns the CodonInfo for a given 6-bit hexagram index (0..63)."""
        return self.hexagram_to_codon[hex_idx % 64]

    def get_classical_chinese_codon_representation(self, codon: str) -> str:
        """Emits Classical Chinese relational hexagram format for codon."""
        clean = codon.upper().replace("U", "T")
        info = self.codons_map[clean]
        h = info.hexagram
        if h is None:
            return f"Codon {clean} -> {info.amino_acid}"
        return (
            f"卦〔{h.hanzi}〕({h.pinyin}) "
            f"[{h.upper.hanzi}上/{h.lower.hanzi}下, {h.meaning}] "
            f"(e_{info.hexagram_index} ∈ CD64) → {info.amino_acid} ({info.amino_acid_name})"
        )

    def get_parity_split(self) -> Dict[str, List[CodonInfo]]:
        """
        Partitions the 64 codons into even and odd binary parity loci in F₂⁶.
        Corresponds to Stella Octangula parity doubling in Cayley-Dickson D=64.
        """
        even_locus: List[CodonInfo] = []
        odd_locus: List[CodonInfo] = []

        for info in self.codons_map.values():
            parity = sum(int(b) for b in info.bitstring) % 2
            if parity == 0:
                even_locus.append(info)
            else:
                odd_locus.append(info)

        return {
            "even_parity_yang": even_locus,
            "odd_parity_yin": odd_locus,
        }

    def get_relational_amino_acid_degeneracy(self) -> Dict[str, Dict[str, Any]]:
        """
        Analyzes the 64 codons → 20 amino acids + Stop degeneracy mapping
        via Chingon zero-divisor and parity strata.
        """
        degeneracy_map: Dict[str, Dict[str, Any]] = {}

        for info in self.codons_map.values():
            aa = info.amino_acid
            if aa not in degeneracy_map:
                degeneracy_map[aa] = {
                    "amino_acid": aa,
                    "name": info.amino_acid_name,
                    "is_stop": info.is_stop,
                    "count": 0,
                    "codons": [],
                    "hexagram_indices": [],
                    "hexagrams_hanzi": [],
                    "even_parity_count": 0,
                    "odd_parity_count": 0,
                    "hydrophobicity": info.hydrophobicity,
                }

            entry = degeneracy_map[aa]
            entry["count"] += 1
            entry["codons"].append(info.codon)
            entry["hexagram_indices"].append(info.hexagram_index)
            if info.hexagram:
                entry["hexagrams_hanzi"].append(info.hexagram.hanzi)

            parity = sum(int(b) for b in info.bitstring) % 2
            if parity == 0:
                entry["even_parity_count"] += 1
            else:
                entry["odd_parity_count"] += 1

        return degeneracy_map

