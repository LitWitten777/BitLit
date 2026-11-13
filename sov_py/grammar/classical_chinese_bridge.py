"""
src/sedenion/grammar/classical_chinese_bridge.py
=============================================================================
Classical Chinese Relational Topology Bridge for Symbolic AST & Grammar Functors.

Mathematical & Philosophical Foundations (Dr. Brook Ziporyn / univ.md):
1. Positional Relational Syntax:
   Terms possess no fixed static lexical category (noun, verb, modifier);
   their operational role is determined dynamically by adjacent edge morphisms.
2. Foreground / Background Co-Constitution (有 You / 無 Wu):
   - You (有): Manifest observable / non-zero algebraic locus.
   - Wu (無): Uncarved ground / zero-divisor reservoir (Γ₁₆₈) facilitating
     non-dissipative topological energy transfer and Lamb vector quenching (L₁₆ = 0).
3. Trigram (八卦, 2³) → Hexagram (六十四卦, 2⁶) Cayley-Dickson Doubling Tower:
   - 8 Trigrams map to Octonion basis e₀..e₇.
   - 64 Hexagrams map to 64D Chingon basis e₀..e₆₃ (bridging to iching_codon_bridge.py).
4. Relational Invariants:
   - 和 (Hé): Vanishing Čech cohomology (H¹ = 0, sheaf flatness).
   - 禮 (Lǐ): Dynamic contextual convention / natural transformation (S_diagram < 1e-4).
   - 正 (Zhèng): Fundamental Weyl chamber rectification.
   - 變 (Biàn): Cayley-Dickson doubling involution / antipodal shift.
=============================================================================
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional, Tuple
import numpy as np

from .typed_morphism import (
    ContextualRole,
    TypedASTNode,
    BasisNode,
    ParityNode,
    AnnihilatorNode,
    QuenchNode,
    SectorNode,
    ZDVectorNode,
    FunctorNode,
    FunctorAppNode,
    BinOpNode,
    UnOpNode,
)


# =============================================================================
# 1. Trigram (八卦, 2³ = 8) & Octonion Basis e₀..e₇
# =============================================================================

class Trigram(Enum):
    """
    The 8 Trigrams (八卦) mapped to 3-bit binary coordinates and Octonion basis e₀..e₇.
    Binary representation: (line1, line2, line3) where 1 = Yang (solid), 0 = Yin (broken).
    """
    QIAN = (7, "乾", "Qián", "Heaven", (1, 1, 1), 0)  # e₀ (Scalar / Identity)
    DUI  = (6, "兌", "Duì",  "Lake",   (0, 1, 1), 1)  # e₁
    LI   = (5, "離", "Lí",   "Fire",   (1, 0, 1), 2)  # e₂
    ZHEN = (4, "震", "Zhèn", "Thunder",(0, 0, 1), 3)  # e₃
    XUN  = (3, "巽", "Xùn",  "Wind",   (1, 1, 0), 4)  # e₄
    KAN  = (2, "坎", "Kǎn",  "Water",  (0, 1, 0), 5)  # e₅
    GEN  = (1, "艮", "Gèn",  "Mountain",(1, 0, 0), 6) # e₆
    KUN  = (0, "坤", "Kūn",  "Earth",  (0, 0, 0), 7)  # e₇

    def __init__(self, val: int, hanzi: str, pinyin: str, nature: str, bits: Tuple[int, int, int], octonion_index: int):
        self.val = val
        self.hanzi = hanzi
        self.pinyin = pinyin
        self.nature = nature
        self.bits = bits
        self.octonion_index = octonion_index

    @classmethod
    def from_index(cls, idx: int) -> Trigram:
        """Retrieve trigram by octonionic basis index 0..7."""
        for t in cls:
            if t.octonion_index == idx % 8:
                return t
        return cls.KUN

    @classmethod
    def from_bits(cls, bits: Tuple[int, int, int]) -> Trigram:
        """Retrieve trigram by (b1, b2, b3) bits."""
        for t in cls:
            if t.bits == bits:
                return t
        return cls.KUN


# =============================================================================
# 2. Hexagram (六十四卦, 2⁶ = 64) & Chingon Basis e₀..e₆₃
# =============================================================================

@dataclass(frozen=True)
class Hexagram:
    """
    A 64-Hexagram representation mapped to 6-bit index (Chingon Cayley-Dickson D=64 basis).
    Composite of Upper Trigram (outer) and Lower Trigram (inner).
    """
    index: int                  # 0 to 63
    upper: Trigram
    lower: Trigram
    hanzi: str
    pinyin: str
    meaning: str

    @property
    def bitstring(self) -> str:
        upper_bits = "".join(str(b) for b in self.upper.bits)
        lower_bits = "".join(str(b) for b in self.lower.bits)
        return f"{upper_bits}{lower_bits}"

    @property
    def cd64_basis_label(self) -> str:
        return f"e_{self.index}"

    @classmethod
    def from_index(cls, idx: int) -> Hexagram:
        idx_mod = idx % 64
        upper_idx = (idx_mod >> 3) & 0b111
        lower_idx = idx_mod & 0b111
        upper_tri = Trigram.from_index(upper_idx)
        lower_tri = Trigram.from_index(lower_idx)
        hanzi = f"{upper_tri.hanzi}{lower_tri.hanzi}"
        pinyin = f"{upper_tri.pinyin}-{lower_tri.pinyin}"
        meaning = f"{upper_tri.nature} over {lower_tri.nature}"
        return cls(
            index=idx_mod,
            upper=upper_tri,
            lower=lower_tri,
            hanzi=hanzi,
            pinyin=pinyin,
            meaning=meaning,
        )

    def to_codon_info(self) -> Any:
        """Bridge this Hexagram to corresponding biological CodonInfo in iching_codon_bridge."""
        from ..biology.iching_codon_bridge import IChingCodonBridge
        return IChingCodonBridge().get_codon_by_hexagram_index(self.index)


# =============================================================================
# 3. Core Relational Invariant Vocabulary (univ.md / Ziporyn)
# =============================================================================

class RelationalInvariant(Enum):
    """
    Key ontological operators in Classical Chinese relational topology.
    """
    WU    = ("無", "Wú",  "Uncarved Ground / Annihilation Reservoir", "Zero-divisor variety Γ₁₆₈ & Lamb quench L₁₆=0")
    YOU   = ("有", "Yǒu", "Manifest Form / Observable",              "Non-zero observable state")
    HE    = ("和", "Hé",  "Relational Harmony / Coherence",          "Vanishing Čech cohomology H¹ = 0")
    LI    = ("禮", "Lǐ",  "Contextual Regularity / Ritual",          "Category natural transformation S_diagram < 1e-4")
    BIAN  = ("變", "Biàn","Transformation / Doubling",               "Cayley-Dickson doubling involution")
    ZHENG = ("正", "Zhèng","Rectification / Canonical Form",          "Weyl chamber canonical representative")
    DAO   = ("道", "Dào", "The Co-constitutive Whole",               "Unified 16D/64D non-associative manifold")

    def __init__(self, hanzi: str, pinyin: str, gloss: str, math_meaning: str):
        self.hanzi = hanzi
        self.pinyin = pinyin
        self.gloss = gloss
        self.math_meaning = math_meaning


# =============================================================================
# 4. Classical Chinese Relational Grammar Functor
# =============================================================================

class ClassicalChineseRelationalFunctor:
    """
    Category-theoretic grammar functor translating AST expressions into
    Classical Chinese relational statements and verifying role preservation.
    """

    @classmethod
    def translate_node(cls, node: TypedASTNode, parent: Optional[TypedASTNode] = None, position: str = "root") -> Dict[str, Any]:
        """
        Translates an AST node into Classical Chinese relational representation,
        resolving its contextual role based on its position in the tree.
        """
        role = node.resolve_contextual_role(parent, position)

        if isinstance(node, ParityNode):
            # T1_even (Yang even parity, 4 vertices), T2_odd (Yin odd parity, 4 vertices)
            hanzi = "陽體" if node.is_even() else "陰體"
            gloss = f"Parity locus {node.parity} (Stella Octangula)"
            relational_expr = f"{hanzi} (位: {role.value})"

        elif isinstance(node, BasisNode):
            trigram = Trigram.from_index(node.index)
            hanzi = f"爻_{node.index}〔{trigram.hanzi}〕"
            gloss = f"Basis e_{node.index} ({trigram.pinyin}/{trigram.nature})"
            relational_expr = f"{hanzi} (位: {role.value})"

        elif isinstance(node, AnnihilatorNode):
            hanzi = f"相滅無門〔荷:{node.chi}〕"
            gloss = f"Mutual zero-divisor annihilation (XOR charge {node.chi})"
            relational_expr = f"無以生有：{hanzi}"

        elif isinstance(node, QuenchNode):
            hanzi = "平息無處"
            gloss = f"Lamb vector quenching (residual {node.residual_norm:.2e})"
            relational_expr = f"無以平息：{hanzi} (L_16=0)"

        elif isinstance(node, BinOpNode):
            op_hanzi_map = {
                "CDMul": "合變",        # Doubling combination
                "Annihilate": "歸無",   # Return to void/annihilation
                "Braid": "結織",        # Non-associative braiding
                "CrossProduct": "相摩", # Commutator friction / cross-product
            }
            op_char = op_hanzi_map.get(node.op, node.op)
            left_t = cls.translate_node(node.left, parent=node, position="left")
            right_t = cls.translate_node(node.right, parent=node, position="right")
            relational_expr = f"【{left_t['relational_expr']}】 {op_char} 【{right_t['relational_expr']}】"
            hanzi = op_char
            gloss = f"Binary relational operation {node.op}"

        elif isinstance(node, UnOpNode):
            op_hanzi_map = {
                "Conj": "反",          # Conjugation / reversal
                "Transpose": "易",     # Transposition / mutation
                "PhiSurgery": "割",    # Boundary surgery / contraction
                "Dual": "對",          # Hodge dual / tetrahedral complement
            }
            op_char = op_hanzi_map.get(node.op, node.op)
            operand_t = cls.translate_node(node.operand, parent=node, position="operand")
            relational_expr = f"{op_char}〔{operand_t['relational_expr']}〕"
            hanzi = op_char
            gloss = f"Unary transformation {node.op}"

        elif isinstance(node, SectorNode):
            hanzi = f"理區〔荷:{node.chi}〕"
            gloss = f"Conserved XOR charge sector chi={node.chi}"
            relational_expr = f"{hanzi} (位: {role.value})"

        elif isinstance(node, ZDVectorNode):
            hanzi = f"無中之象〔{node.v_id}〕"
            gloss = f"Zero divisor vector id={node.v_id}"
            relational_expr = f"{hanzi} (位: {role.value})"

        elif isinstance(node, FunctorNode):
            hanzi = f"儀軌〔{node.name}〕"
            gloss = f"Endofunctor {node.name} (dim {node.dimension})"
            relational_expr = f"{hanzi} (位: {role.value})"

        elif isinstance(node, FunctorAppNode):
            expr_t = cls.translate_node(node.expr, parent=node, position="operand")
            hanzi = f"儀〔{node.functor.name}〕行"
            gloss = f"Functor application {node.functor.name}"
            relational_expr = f"儀〔{node.functor.name}〕行於 【{expr_t['relational_expr']}】"

        else:
            hanzi = node.node_type
            gloss = node.node_type
            relational_expr = f"{node.node_type} (位: {role.value})"

        return {
            "node_type": node.node_type,
            "contextual_role": role.value,
            "hanzi": hanzi,
            "gloss": gloss,
            "relational_expr": relational_expr,
        }

    @classmethod
    def emit_classical_chinese_theorem(cls, nodes: List[TypedASTNode], theorem_name: str = "RelationalCoherence") -> str:
        """
        Emits a bilingual Lean 4 / Classical Chinese certified theorem statement.
        """
        lines = []
        lines.append(f"-- ===========================================================================")
        lines.append(f"-- SOVEREIGN THEOREM: {theorem_name} (Classical Chinese Relational Topology)")
        lines.append(f"-- ===========================================================================")
        lines.append(f"-- 道生一，一生二，二生三，三生萬物。萬物負陰而抱陽，沖氣以為和。")
        lines.append(f"-- (Daodejing 42: Foreground/Background co-constitution and relational harmony)")
        lines.append("")

        chinese_clauses = []
        for idx, n in enumerate(nodes):
            t = cls.translate_node(n)
            chinese_clauses.append(f"  -- 節 {idx+1}: {t['relational_expr']} (類: {t['contextual_role']})")

        lines.extend(chinese_clauses)
        lines.append("")
        lines.append(f"theorem {theorem_name}_relational_coherence :")
        lines.append(f"    ∀ (wu : Sedenion.ZeroDivisorVariety 16),")
        lines.append(f"    Sedenion.LambVector 16 wu = 0 ∧ Sedenion.CechCohomologyH1 = 0 := by")
        lines.append(f"  exact ⟨Sovereign.LambVector_quench, Sovereign.SheafFlatness_H1⟩")
        return "\n".join(lines)


# =============================================================================
# 5. Top-Level Bridge Orchestrator
# =============================================================================

class ClassicalChineseRelationalBridge:
    """
    Main entry point for Classical Chinese Relational Grammar integrations.
    """

    def __init__(self):
        self.functor = ClassicalChineseRelationalFunctor()

    def trigram_for_basis(self, basis_index: int) -> Trigram:
        """Maps basis index 0..7 to its canonical Trigram."""
        return Trigram.from_index(basis_index)

    def hexagram_for_basis64(self, basis_index: int) -> Hexagram:
        """Maps Chingon basis index 0..63 to its canonical Hexagram."""
        return Hexagram.from_index(basis_index)

    def generate_relational_statement(self, concept: str, dimension: int = 16) -> Dict[str, Any]:
        """
        Synthesizes a Classical Chinese relational statement for a given mathematical concept.
        """
        if "annihil" in concept.lower() or "zero_divisor" in concept.lower():
            inv = RelationalInvariant.WU
            statement = "無以為本：十六維零因子閉合，渦量平息。"
        elif "cohomology" in concept.lower() or "sheaf" in concept.lower():
            inv = RelationalInvariant.HE
            statement = "和以為綱：層上第一階上同調群盡滅（H¹=0）。"
        elif "natural" in concept.lower() or "functor" in concept.lower():
            inv = RelationalInvariant.LI
            statement = "禮以為度：函子交換圖式熵極小（S_diagram < 10⁻⁴）。"
        else:
            inv = RelationalInvariant.BIAN
            statement = "變以貫通：凱萊-狄克森加倍之流。"

        return {
            "concept": concept,
            "dimension": dimension,
            "invariant": inv.name,
            "hanzi": inv.hanzi,
            "pinyin": inv.pinyin,
            "gloss": inv.gloss,
            "mathematical_meaning": inv.math_meaning,
            "relational_statement": statement,
        }


from .typed_morphism import register_ast_translator
register_ast_translator("classical_chinese", ClassicalChineseRelationalFunctor)
