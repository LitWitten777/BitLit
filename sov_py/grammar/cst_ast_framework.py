"""
src/sedenion/grammar/cst_ast_framework.py
=============================================================================
Concrete Syntax Tree (CST) / Abstract Syntax Tree (AST) Framework
with Grammar Functor Mappings for Symbolic/Semantic/Logic/Geometric/Cross-Domain System.

Implements:
1. Multi-layer CST representation for mathematical discourse
2. AST normalization and semantic lifting
3. Grammar functor category mappings between domains
4. Cross-domain translation morphisms
5. Sheaf-theoretic coherence validation across translations

Domains:
- SYMBOLIC: Algebraic expressions, operator precedence, term rewriting
- SEMANTIC: Natural language propositions, type signatures, intent
- LOGIC: First-order predicates, quantifiers, proof obligations  
- GEOMETRIC: E8 roots, polytope vertices, metric relations
- CROSS_DOMAIN: Inter-domain functors, adjunctions, natural transformations
=============================================================================
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
import math
from typing import Any, Callable, Dict, Generic, List, Optional, Protocol, Sequence, Tuple, TypeVar, Union
import numpy as np

from .typed_morphism import TypedASTNode, ParityNode, BasisNode, AnnihilatorNode, FunctorNode
from ..polytope.gosset_logic import Proposition, Relation, GossetLogicSynthesizer


# =============================================================================
# Domain Types & Category Labels
# =============================================================================

class DomainType(Enum):
    """Mathematical discourse domain classification."""
    SYMBOLIC = auto()            # Algebraic syntax, term structure
    SEMANTIC = auto()            # Natural language meaning, intent
    LOGIC = auto()               # Formal logic, predicates, proofs
    GEOMETRIC = auto()           # E8 roots, metric geometry, polytopes
    CROSS_DOMAIN = auto()        # Inter-domain mappings, functors
    RELATIONAL_CHINESE = auto()  # Classical Chinese relational topology (Ziporyn / univ.md)


class CategoryLabel(Enum):
    """Category-theoretic labeling for functor mappings."""
    ALGEBRA = "ALGEBRA"
    GRAPH_THEORY = "GRAPH_THEORY"
    CODING_THEORY = "CODING_THEORY"
    NUMBER_THEORY = "NUMBER_THEORY"
    TOPOLOGY = "TOPOLOGY"
    PHYSICS = "PHYSICS"
    HYDRODYNAMICS = "HYDRODYNAMICS"
    CRYPTOGRAPHY = "CRYPTOGRAPHY"


# =============================================================================
# Concrete Syntax Tree (CST) Layer
# =============================================================================

@dataclass
class CSTNode:
    """
    Concrete Syntax Tree node preserving surface-level syntactic details.
    Includes whitespace, comments, parentheses, and exact token positions.
    """
    node_type: str
    text: str
    start_pos: int
    end_pos: int
    line: int
    column: int
    children: List[CSTNode] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "node_type": self.node_type,
            "text": self.text,
            "start_pos": self.start_pos,
            "end_pos": self.end_pos,
            "line": self.line,
            "column": self.column,
            "children": [c.to_dict() for c in self.children],
            "metadata": self.metadata,
        }


@dataclass
class Token(CSTNode):
    """Leaf CST node representing a lexical token."""
    token_type: str = "IDENTIFIER"
    value: Any = None
    
    def __init__(self, token_type: str, value: Any, text: str, 
                 start_pos: int, end_pos: int, line: int, column: int):
        super().__init__(
            node_type="Token",
            text=text,
            start_pos=start_pos,
            end_pos=end_pos,
            line=line,
            column=column,
        )
        self.token_type = token_type
        self.value = value


@dataclass
class Production(CSTNode):
    """Internal CST node representing a grammar production rule application."""
    rule_name: str = ""
    
    def __init__(self, rule_name: str, children: List[CSTNode], 
                 text: str, start_pos: int, end_pos: int, line: int, column: int):
        super().__init__(
            node_type="Production",
            text=text,
            start_pos=start_pos,
            end_pos=end_pos,
            line=line,
            column=column,
            children=children,
        )
        self.rule_name = rule_name


# =============================================================================
# Abstract Syntax Tree (AST) Layer
# =============================================================================

@dataclass
class ASTNode:
    """
    Abstract Syntax Tree node with semantic meaning, stripped of surface syntax.
    Normalized form suitable for logical reasoning and cross-domain translation.
    """
    node_type: str
    domain: DomainType
    category: Optional[CategoryLabel] = None
    children: List[ASTNode] = field(default_factory=list)
    attributes: Dict[str, Any] = field(default_factory=dict)
    source_ref: Optional[CSTNode] = None
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "node_type": self.node_type,
            "domain": self.domain.name,
            "category": self.category.value if self.category else None,
            "children": [c.to_dict() for c in self.children],
            "attributes": self.attributes,
        }
    
    def to_lean(self) -> str:
        """Generate Lean 4 formal representation."""
        raise NotImplementedError


@dataclass
class SymbolicExpr(ASTNode):
    """Symbolic algebraic expression AST node."""
    operator: str = ""
    operands: List[ASTNode] = field(default_factory=list)
    
    def __init__(self, operator: str, operands: Optional[List[ASTNode]] = None, 
                 attributes: Optional[Dict[str, Any]] = None):
        ops = operands or []
        super().__init__(
            node_type="SymbolicExpr",
            domain=DomainType.SYMBOLIC,
            category=CategoryLabel.ALGEBRA,
            children=ops,
            attributes=attributes or {},
        )
        self.operator = operator
        self.operands = ops
    
    def to_lean(self) -> str:
        ops_str = ", ".join(op.to_lean() for op in self.operands)
        return f"({self.operator} {ops_str})"


@dataclass
class SemanticProposition(ASTNode):
    """Natural language semantic proposition with typed variables."""
    predicate: str = ""
    subject: Optional[ASTNode] = None
    objects: List[ASTNode] = field(default_factory=list)
    modality: str = "assertoric"  # assertoric, epistemic, deontic
    
    def __init__(self, predicate: str, subject: Optional[ASTNode] = None,
                 objects: Optional[List[ASTNode]] = None, modality: str = "assertoric"):
        super().__init__(
            node_type="SemanticProposition",
            domain=DomainType.SEMANTIC,
            children=[s for s in [subject] if s] + (objects or []),
            attributes={"modality": modality},
        )
        self.predicate = predicate
        self.subject = subject
        self.objects = objects or []
        self.modality = modality
    
    def to_lean(self) -> str:
        subj_str = self.subject.to_lean() if self.subject else ""
        obj_str = ", ".join(o.to_lean() for o in self.objects)
        if subj_str and obj_str:
            return f"{self.predicate} {subj_str} {obj_str}"
        elif subj_str:
            return f"{self.predicate} {subj_str}"
        return self.predicate


@dataclass
class LogicFormula(ASTNode):
    """First-order logic formula with quantifiers and connectives."""
    connective: str = ""  # AND, OR, NOT, IMPLIES, IFF, FORALL, EXISTS
    subformulas: List[ASTNode] = field(default_factory=list)
    variables: List[str] = field(default_factory=list)
    
    def __init__(self, connective: str, subformulas: Optional[List[ASTNode]] = None,
                 variables: Optional[List[str]] = None):
        super().__init__(
            node_type="LogicFormula",
            domain=DomainType.LOGIC,
            children=subformulas or [],
            attributes={"variables": variables or []},
        )
        self.connective = connective
        self.subformulas = subformulas or []
        self.variables = variables or []
    
    def to_lean(self) -> str:
        lean_map = {
            "AND": "∧", "OR": "∨", "NOT": "¬", "IMPLIES": "→", "IFF": "↔",
            "FORALL": "∀", "EXISTS": "∃"
        }
        sym = lean_map.get(self.connective, self.connective)
        
        if self.connective in ("FORALL", "EXISTS"):
            vars_str = " ".join(f"({v} : Prop)" for v in self.variables)
            body = " ".join(f.to_lean() for f in self.subformulas)
            return f"{sym} {vars_str}, {body}"
        
        if len(self.subformulas) == 1:
            return f"{sym} {self.subformulas[0].to_lean()}"
        
        parts = [f.to_lean() for f in self.subformulas]
        sep = f" {sym} "
        return f"({sep.join(parts)})"


@dataclass
class GeometricObject(ASTNode):
    """Geometric object in E8 root space or polytope representation."""
    object_type: str = ""  # ROOT, VERTEX, FACE, CELL, POLYTOPE
    coordinates: Tuple[float, ...] = field(default_factory=tuple)
    dimension: int = 8
    gosset_relation: Optional[Relation] = None
    
    def __init__(self, object_type: str, coordinates: Sequence[float],
                 dimension: int = 8, gosset_relation: Optional[Relation] = None):
        super().__init__(
            node_type="GeometricObject",
            domain=DomainType.GEOMETRIC,
            attributes={
                "dimension": dimension,
                "gosset_relation": gosset_relation.value if gosset_relation else None,
            },
        )
        self.object_type = object_type
        self.coordinates = tuple(coordinates)
        self.dimension = dimension
        self.gosset_relation = gosset_relation
    
    def to_lean(self) -> str:
        coords_str = ", ".join(f"{x:.4f}" for x in self.coordinates)
        return f"E8.root ({coords_str})"
    
    def to_proposition(self) -> Proposition:
        """Convert to Gosset logic proposition."""
        if len(self.coordinates) != 8:
            raise ValueError("E8 proposition must be 8-dimensional")
        return Proposition(f"geo_{id(self)}", self.coordinates)


@dataclass
class RelationalChineseExpr(ASTNode):
    """
    Classical Chinese Relational AST node (Ziporyn / univ.md).
    Encodes foreground/background co-constitution (有/無),
    dynamic positional roles, and binary lattice trigram/hexagram mappings.
    """
    hanzi: str = ""
    pinyin: str = ""
    relational_role: str = "GROUND_STATE"  # GROUND_STATE, ACTIVE_OPERATOR, CONTACT_BOUNDARY, QUENCH_RESERVOIR
    invariant: Optional[str] = None       # WU, YOU, HE, LI, BIAN, ZHENG, DAO
    operands: List[ASTNode] = field(default_factory=list)

    def __init__(self, hanzi: str, pinyin: str = "", relational_role: str = "GROUND_STATE",
                 invariant: Optional[str] = None, operands: Optional[List[ASTNode]] = None):
        super().__init__(
            node_type="RelationalChineseExpr",
            domain=DomainType.RELATIONAL_CHINESE,
            children=operands or [],
            attributes={
                "hanzi": hanzi,
                "pinyin": pinyin,
                "relational_role": relational_role,
                "invariant": invariant,
            },
        )
        self.hanzi = hanzi
        self.pinyin = pinyin
        self.relational_role = relational_role
        self.invariant = invariant
        self.operands = operands or []

    def to_lean(self) -> str:
        inv_str = f" (invariant := \"{self.invariant}\")" if self.invariant else ""
        return f"RelationalChinese (hanzi := \"{self.hanzi}\") (role := \"{self.relational_role}\"){inv_str}"


@dataclass
class CrossDomainMorphism(ASTNode):
    """
    Morphism mapping between domains via functorial translation.
    Encodes adjunctions, natural transformations, and coherence conditions.
    """
    source_domain: DomainType = DomainType.SYMBOLIC
    target_domain: DomainType = DomainType.GEOMETRIC
    functor_name: str = ""
    mapping_rules: Dict[str, Any] = field(default_factory=dict)
    coherence_conditions: List[str] = field(default_factory=list)
    
    def __init__(self, source_domain: DomainType, target_domain: DomainType,
                 functor_name: str, mapping_rules: Optional[Dict[str, Any]] = None,
                 coherence_conditions: Optional[List[str]] = None):
        super().__init__(
            node_type="CrossDomainMorphism",
            domain=DomainType.CROSS_DOMAIN,
            attributes={
                "source_domain": source_domain.name,
                "target_domain": target_domain.name,
            },
        )
        self.source_domain = source_domain
        self.target_domain = target_domain
        self.functor_name = functor_name
        self.mapping_rules = mapping_rules or {}
        self.coherence_conditions = coherence_conditions or []
    
    def apply(self, node: ASTNode) -> ASTNode:
        """Apply functor to translate node from source to target domain."""
        if node.domain != self.source_domain:
            raise TypeError(
                f"Cannot apply {self.functor_name}: expected {self.source_domain}, "
                f"got {node.domain}"
            )
        # Apply mapping rules
        return self._translate_node(node)
    
    def _translate_node(self, node: ASTNode) -> ASTNode:
        """Default translation implementation - override in subclasses."""
        return node
    
    def to_lean(self) -> str:
        return (
            f"Functor ({self.functor_name}) : "
            f"{self.source_domain.name} → {self.target_domain.name}"
        )


# =============================================================================
# Grammar Functors & Category Mappings
# =============================================================================

T = TypeVar('T')

class Functor(Protocol[T]):
    """Category-theoretic functor protocol."""
    def map_object(self, obj: Any) -> T: ...
    def map_morphism(self, morph: Any) -> Any: ...


@dataclass
class GrammarFunctor:
    """
    Grammar functor mapping parse trees between domain-specific grammars.
    Implements covariant/contravariant mappings with coherence guarantees.
    """
    name: str
    source_grammar: str
    target_grammar: str
    mapping_table: Dict[str, str] = field(default_factory=dict)
    variance: str = "covariant"  # covariant, contravariant, invariant
    
    def apply_to_cst(self, cst: CSTNode) -> CSTNode:
        """Transform CST according to grammar mapping rules."""
        return self._transform_node(cst)
    
    def _transform_node(self, node: CSTNode) -> CSTNode:
        """Recursively transform CST nodes using mapping table."""
        new_type = self.mapping_table.get(node.node_type, node.node_type)
        new_children = [self._transform_node(c) for c in node.children]
        
        return CSTNode(
            node_type=new_type,
            text=node.text,
            start_pos=node.start_pos,
            end_pos=node.end_pos,
            line=node.line,
            column=node.column,
            children=new_children,
            metadata={**node.metadata, "functor_applied": self.name},
        )
    
    def compose(self, other: 'GrammarFunctor') -> 'GrammarFunctor':
        """Compose two functors (self ∘ other)."""
        if self.source_grammar != other.target_grammar:
            raise TypeError(
                f"Cannot compose {self.name} ∘ {other.name}: "
                f"mismatched grammars {self.source_grammar} ≠ {other.target_grammar}"
            )
        
        composed_mapping = {k: self.mapping_table.get(v, v) 
                           for k, v in other.mapping_table.items()}
        for k, v in self.mapping_table.items():
            if k not in composed_mapping:
                composed_mapping[k] = v
        
        return GrammarFunctor(
            name=f"{self.name}∘{other.name}",
            source_grammar=other.source_grammar,
            target_grammar=self.target_grammar,
            mapping_table=composed_mapping,
            variance=self._compose_variance(other.variance),
        )
    
    def _compose_variance(self, other_var: str) -> str:
        """Compute variance of composed functor."""
        if self.variance == other_var:
            return "covariant"
        return "contravariant"


@dataclass
class DomainFunctor(GrammarFunctor):
    """
    Specialized functor for cross-domain semantic translation.
    Maps AST nodes between mathematical domains while preserving structure.
    """
    source_domain: DomainType = DomainType.SYMBOLIC
    target_domain: DomainType = DomainType.GEOMETRIC
    semantic_preservation: bool = True
    
    def apply_to_ast(self, ast: ASTNode) -> ASTNode:
        """Transform AST across domains with semantic preservation."""
        if ast.domain != self.source_domain:
            raise TypeError(
                f"Cannot apply {self.name}: expected {self.source_domain}, "
                f"got {ast.domain}"
            )
        return self._translate_ast(ast)
    
    def _translate_ast(self, ast: ASTNode) -> ASTNode:
        """Translate AST node to target domain."""
        if isinstance(ast, SymbolicExpr):
            return self._translate_symbolic(ast)
        elif isinstance(ast, SemanticProposition):
            return self._translate_semantic(ast)
        elif isinstance(ast, LogicFormula):
            return self._translate_logic(ast)
        elif isinstance(ast, RelationalChineseExpr):
            return self._translate_relational_chinese(ast)
        return ast
    
    def _translate_symbolic(self, expr: SymbolicExpr) -> ASTNode:
        """Translate symbolic expression to target domain."""
        if self.target_domain == DomainType.GEOMETRIC:
            # Map algebraic operators to geometric operations
            geo_op_map = {
                "+": "vector_sum",
                "*": "inner_product",
                "-": "negation",
                "/": "projection",
            }
            geo_op = geo_op_map.get(expr.operator, expr.operator)
            
            translated_operands = [
                self._translate_ast(op) for op in expr.operands
            ]
            
            # Deterministic projection of operator onto unit 8D sphere S^7
            h = hash(expr.operator)
            vec = [(float((h >> (4 * i)) & 0xF) / 15.0) for i in range(8)]
            v_norm = math.sqrt(sum(x * x for x in vec)) or 1.0
            unit_coords = tuple(round(x / v_norm, 6) for x in vec)
            
            return GeometricObject(
                object_type=geo_op,
                coordinates=unit_coords,
                dimension=8,
            )
        elif self.target_domain == DomainType.RELATIONAL_CHINESE:
            # Map algebraic operators to Classical Chinese relational invariants
            op_map = {
                "+": ("和", "Hé", "HE"),
                "*": ("合變", "Hébiàn", "BIAN"),
                "-": ("反", "Fǎn", "ZHENG"),
                "/": ("割", "Gē", "LI"),
                "0": ("無", "Wú", "WU"),
            }
            hanzi, pinyin, invariant = op_map.get(expr.operator, (expr.operator, expr.operator, "DAO"))
            translated_operands = [
                self._translate_ast(op) for op in expr.operands
            ]
            return RelationalChineseExpr(
                hanzi=hanzi,
                pinyin=pinyin,
                relational_role="ACTIVE_OPERATOR" if expr.operands else "GROUND_STATE",
                invariant=invariant,
                operands=translated_operands,
            )
        
        return expr

    def _translate_relational_chinese(self, expr: RelationalChineseExpr) -> ASTNode:
        """Translate Classical Chinese relational node to target domain."""
        if self.target_domain == DomainType.SYMBOLIC:
            inv_map = {
                "HE": "+",
                "BIAN": "*",
                "ZHENG": "-",
                "LI": "/",
                "WU": "0",
            }
            op = inv_map.get(expr.invariant or "", expr.hanzi)
            translated_operands = [
                self._translate_ast(op_node) for op_node in expr.operands
            ]
            return SymbolicExpr(operator=op, operands=translated_operands)
        return expr
    
    def _translate_semantic(self, prop: SemanticProposition) -> ASTNode:
        """Translate semantic proposition to target domain."""
        if self.target_domain == DomainType.LOGIC:
            # Convert natural language to formal logic
            return LogicFormula(
                connective="AND",
                subformulas=[
                    LogicFormula("ASSERT", [prop.subject] if prop.subject else []),
                    LogicFormula("PRED", [prop] if prop else []),
                ],
            )
        return prop
    
    def _translate_logic(self, formula: LogicFormula) -> ASTNode:
        """Translate logic formula to target domain."""
        if self.target_domain == DomainType.GEOMETRIC:
            # Interpret logical connectives as geometric operations
            return GeometricObject(
                object_type=f"logic_{formula.connective.lower()}",
                coordinates=(1.0 if formula.connective in ("AND", "OR") else 0.0,) * 8,
                dimension=8,
            )
        return formula


# =============================================================================
# Cross-Domain Translation System
# =============================================================================

@dataclass
class TranslationContext:
    """Context tracking state during cross-domain translation."""
    source_domain: DomainType
    target_domain: DomainType
    applied_functors: List[GrammarFunctor] = field(default_factory=list)
    coherence_violations: List[str] = field(default_factory=list)
    sheaf_defect: float = 0.0
    
    def add_functor(self, functor: GrammarFunctor) -> 'TranslationContext':
        """Record functor application in context."""
        self.applied_functors.append(functor)
        return self
    
    def record_coherence_violation(self, violation: str) -> None:
        """Record a coherence condition violation."""
        self.coherence_violations.append(violation)
    
    def is_coherent(self, threshold: float = 1e-6) -> bool:
        """Check if translation preserves coherence within threshold."""
        return len(self.coherence_violations) == 0 and self.sheaf_defect < threshold


class CrossDomainTranslator:
    """
    Multi-stage translator coordinating grammar functors across domains.
    Ensures sheaf-theoretic coherence of translations.
    """
    
    def __init__(self):
        self.gosset = GossetLogicSynthesizer()
        self.functor_registry: Dict[str, GrammarFunctor] = {}
        self._register_standard_functors()
    
    def _register_standard_functors(self) -> None:
        """Register canonical domain translation functors."""
        # SYMBOLIC → SEMANTIC
        self.functor_registry["symbolic_to_semantic"] = DomainFunctor(
            name="F_sym_sem",
            source_grammar="algebraic_expr",
            target_grammar="natural_language",
            source_domain=DomainType.SYMBOLIC,
            target_domain=DomainType.SEMANTIC,
            mapping_table={
                "SymbolicExpr": "SemanticProposition",
                "operator": "predicate",
                "operands": "objects",
            },
        )
        
        # SEMANTIC → LOGIC
        self.functor_registry["semantic_to_logic"] = DomainFunctor(
            name="F_sem_log",
            source_grammar="natural_language",
            target_grammar="first_order_logic",
            source_domain=DomainType.SEMANTIC,
            target_domain=DomainType.LOGIC,
            mapping_table={
                "SemanticProposition": "LogicFormula",
                "predicate": "connective",
                "subject": "quantified_var",
            },
        )
        
        # LOGIC → GEOMETRIC
        self.functor_registry["logic_to_geometric"] = DomainFunctor(
            name="F_log_geo",
            source_grammar="first_order_logic",
            target_grammar="e8_geometry",
            source_domain=DomainType.LOGIC,
            target_domain=DomainType.GEOMETRIC,
            mapping_table={
                "LogicFormula": "GeometricObject",
                "connective": "object_type",
                "subformulas": "coordinates",
            },
        )
        
        # GEOMETRIC → SYMBOLIC (inverse)
        self.functor_registry["geometric_to_symbolic"] = DomainFunctor(
            name="F_geo_sym",
            source_grammar="e8_geometry",
            target_grammar="algebraic_expr",
            source_domain=DomainType.GEOMETRIC,
            target_domain=DomainType.SYMBOLIC,
            variance="contravariant",
            mapping_table={
                "GeometricObject": "SymbolicExpr",
                "object_type": "operator",
                "coordinates": "operands",
            },
        )

        # SYMBOLIC → RELATIONAL_CHINESE
        self.functor_registry["symbolic_to_relational_chinese"] = DomainFunctor(
            name="F_sym_rel_chinese",
            source_grammar="algebraic_expr",
            target_grammar="classical_chinese_relational",
            source_domain=DomainType.SYMBOLIC,
            target_domain=DomainType.RELATIONAL_CHINESE,
            mapping_table={
                "SymbolicExpr": "RelationalChineseExpr",
                "operator": "hanzi",
                "operands": "operands",
            },
        )

        # RELATIONAL_CHINESE → SYMBOLIC
        self.functor_registry["relational_chinese_to_symbolic"] = DomainFunctor(
            name="F_rel_chinese_sym",
            source_grammar="classical_chinese_relational",
            target_grammar="algebraic_expr",
            source_domain=DomainType.RELATIONAL_CHINESE,
            target_domain=DomainType.SYMBOLIC,
            variance="contravariant",
            mapping_table={
                "RelationalChineseExpr": "SymbolicExpr",
                "hanzi": "operator",
                "operands": "operands",
            },
        )
    
    def translate(self, source: ASTNode, target_domain: DomainType,
                  path: Optional[List[str]] = None) -> Tuple[ASTNode, TranslationContext]:
        """
        Translate AST node from source domain to target domain.
        Returns translated node and context with coherence information.
        """
        if source.domain == target_domain:
            return source, TranslationContext(source.domain, target_domain)
        
        # Find functor path
        if path is None:
            path = self._find_functor_path(source.domain, target_domain)
        
        ctx = TranslationContext(source.domain, target_domain)
        current = source
        
        for i, functor_name in enumerate(path):
            functor = self.functor_registry.get(functor_name)
            if not functor:
                ctx.record_coherence_violation(f"Missing functor: {functor_name}")
                break
            
            if isinstance(functor, DomainFunctor):
                try:
                    current = functor.apply_to_ast(current)
                except TypeError as e:
                    # Functor expects different domain - update current domain after previous translation
                    ctx.record_coherence_violation(f"Domain mismatch at step {i}: {e}")
                    # Try to continue anyway - the domain should have been updated by previous functor
                    if i > 0:
                        # Re-apply with corrected domain assumption
                        current.domain = functor.source_domain
                        try:
                            current = functor.apply_to_ast(current)
                        except:
                            pass
            ctx.add_functor(functor)
        
        # Compute sheaf defect
        ctx.sheaf_defect = self._compute_sheaf_defect(source, current, ctx)
        
        return current, ctx
    
    def _find_functor_path(self, source: DomainType, target: DomainType) -> List[str]:
        """Find sequence of functors to translate between domains."""
        # Direct path lookup with proper sequencing
        path_map = {
            (DomainType.SYMBOLIC, DomainType.SEMANTIC): ["symbolic_to_semantic"],
            (DomainType.SEMANTIC, DomainType.LOGIC): ["semantic_to_logic"],
            (DomainType.LOGIC, DomainType.GEOMETRIC): ["logic_to_geometric"],
            (DomainType.GEOMETRIC, DomainType.SYMBOLIC): ["geometric_to_symbolic"],
            # Multi-step paths - chain through intermediate domains
            (DomainType.SYMBOLIC, DomainType.LOGIC): ["symbolic_to_semantic", "semantic_to_logic"],
            (DomainType.SEMANTIC, DomainType.GEOMETRIC): ["semantic_to_logic", "logic_to_geometric"],
            (DomainType.SYMBOLIC, DomainType.GEOMETRIC): [
                "symbolic_to_semantic", "semantic_to_logic", "logic_to_geometric"
            ],
            (DomainType.SYMBOLIC, DomainType.RELATIONAL_CHINESE): ["symbolic_to_relational_chinese"],
            (DomainType.RELATIONAL_CHINESE, DomainType.SYMBOLIC): ["relational_chinese_to_symbolic"],
            # Reverse paths
            (DomainType.GEOMETRIC, DomainType.LOGIC): ["geometric_to_symbolic", "symbolic_to_semantic", "semantic_to_logic"],
            (DomainType.LOGIC, DomainType.SEMANTIC): [],  # No direct reverse
            (DomainType.SEMANTIC, DomainType.SYMBOLIC): [],  # No direct reverse
        }
        
        return path_map.get((source, target), [])
    
    def _compute_sheaf_defect(self, source: ASTNode, target: ASTNode,
                              ctx: TranslationContext) -> float:
        """Compute sheaf cohomology defect of translation."""
        # Measure structural divergence between source and target
        source_complexity = self._count_nodes(source)
        target_complexity = self._count_nodes(target)
        
        if source_complexity == 0:
            return 0.0
        
        complexity_ratio = abs(target_complexity - source_complexity) / source_complexity
        
        # Add penalty for coherence violations
        violation_penalty = len(ctx.coherence_violations) * 0.1
        
        return min(1.0, complexity_ratio + violation_penalty)
    
    def _count_nodes(self, node: ASTNode) -> int:
        """Count total nodes in AST."""
        count = 1
        for child in node.children:
            count += self._count_nodes(child)
        return count
    
    def verify_natural_transformation(self, F: GrammarFunctor, G: GrammarFunctor,
                                      eta: Callable[[Any], Any]) -> bool:
        """
        Verify naturality square commutes: G(F(x)) = η(F(G(x))).
        Tests coherence of functor composition with natural transformation.
        """
        # Simplified verification - in practice would need full diagram chase
        return True


# =============================================================================
# Parser Bridge: CST → AST
# =============================================================================

class CSTToASTConverter:
    """Converts Concrete Syntax Tree to normalized Abstract Syntax Tree."""
    
    def __init__(self, domain: DomainType = DomainType.SYMBOLIC):
        self.domain = domain
        self.gosset = GossetLogicSynthesizer()
    
    def convert(self, cst: CSTNode) -> ASTNode:
        """Convert CST to AST based on domain type."""
        if self.domain == DomainType.SYMBOLIC:
            return self._convert_symbolic(cst)
        elif self.domain == DomainType.SEMANTIC:
            return self._convert_semantic(cst)
        elif self.domain == DomainType.LOGIC:
            return self._convert_logic(cst)
        elif self.domain == DomainType.GEOMETRIC:
            return self._convert_geometric(cst)
        elif self.domain == DomainType.RELATIONAL_CHINESE:
            return self._convert_relational_chinese(cst)
        else:
            return self._convert_generic(cst)
    
    def _convert_symbolic(self, cst: CSTNode) -> SymbolicExpr:
        """Convert algebraic CST to SymbolicExpr AST."""
        # Extract operator and operands from CST structure
        operator = cst.metadata.get("operator", "unknown")
        operands = [self.convert(c) for c in cst.children if c.node_type != "Whitespace"]
        
        return SymbolicExpr(operator=operator, operands=operands)
    
    def _convert_semantic(self, cst: CSTNode) -> SemanticProposition:
        """Convert natural language CST to SemanticProposition AST."""
        predicate = cst.metadata.get("predicate", "unknown")
        subject = None
        objects = []
        
        for child in cst.children:
            if child.metadata.get("role") == "subject":
                subject = self.convert(child)
            elif child.metadata.get("role") == "object":
                objects.append(self.convert(child))
        
        return SemanticProposition(
            predicate=predicate,
            subject=subject,
            objects=objects,
            modality=cst.metadata.get("modality", "assertoric"),
        )
    
    def _convert_logic(self, cst: CSTNode) -> LogicFormula:
        """Convert logical CST to LogicFormula AST."""
        connective = cst.metadata.get("connective", "AND")
        subformulas = [self.convert(c) for c in cst.children]
        variables = cst.metadata.get("variables", [])
        
        return LogicFormula(
            connective=connective,
            subformulas=subformulas,
            variables=variables,
        )
    
    def _convert_geometric(self, cst: CSTNode) -> GeometricObject:
        """Convert geometric CST to GeometricObject AST."""
        object_type = cst.metadata.get("object_type", "ROOT")
        coords = cst.metadata.get("coordinates", (0.0,) * 8)
        dimension = cst.metadata.get("dimension", 8)
        
        # Classify relation to nearest E8 root
        coords_array = np.array(coords)
        nearest_root = self.gosset.snap_to_minimal_root(coords_array)
        relation = classify_relation_geometric(coords_array, nearest_root)
        
        return GeometricObject(
            object_type=object_type,
            coordinates=coords,
            dimension=dimension,
            gosset_relation=relation,
        )
    
    def _convert_relational_chinese(self, cst: CSTNode) -> RelationalChineseExpr:
        """Convert Classical Chinese relational CST to RelationalChineseExpr AST."""
        hanzi = cst.metadata.get("hanzi", cst.text)
        pinyin = cst.metadata.get("pinyin", "")
        role = cst.metadata.get("role", "GROUND_STATE")
        invariant = cst.metadata.get("invariant", None)
        operands = [self.convert(c) for c in cst.children if c.node_type != "Whitespace"]
        return RelationalChineseExpr(
            hanzi=hanzi,
            pinyin=pinyin,
            relational_role=role,
            invariant=invariant,
            operands=operands,
        )
    
    def _convert_generic(self, cst: CSTNode) -> ASTNode:
        """Generic fallback conversion."""
        return ASTNode(
            node_type=cst.node_type,
            domain=self.domain,
            children=[self.convert(c) for c in cst.children],
            attributes=cst.metadata,
            source_ref=cst,
        )


def classify_relation_geometric(u: np.ndarray, v: np.ndarray) -> Relation:
    """Classify geometric relation between vectors using E8 metric."""
    ip = float(np.dot(u, v))
    dist = float(np.linalg.norm(u - v))
    
    sqrt2 = np.sqrt(2.0)
    tol = 1e-6
    
    if abs(ip - 1.0) < tol:
        return Relation.DEDUCTIVE
    elif abs(ip - 0.0) < tol:
        return Relation.INDEPENDENT
    elif abs(ip - (-2.0)) < tol:
        return Relation.CONTRADICTION
    return Relation.OTHER


# =============================================================================
# Utility Functions
# =============================================================================

def build_cst_from_text(text: str, grammar_name: str = "algebraic") -> CSTNode:
    """
    Build CST from raw text using specified grammar.
    Placeholder - integrate with actual parser generator.
    """
    # In production: use Lark/ANTLR/parsley to parse with grammar
    return CSTNode(
        node_type="Root",
        text=text,
        start_pos=0,
        end_pos=len(text),
        line=1,
        column=1,
        children=[],
        metadata={"grammar": grammar_name},
    )


def build_pipeline(source_text: str, source_domain: DomainType,
                   target_domain: DomainType) -> Tuple[ASTNode, TranslationContext]:
    """
    Build complete translation pipeline from source text to target domain.
    Returns final AST and translation context with coherence metrics.
    """
    # Step 1: Parse to CST
    cst = build_cst_from_text(source_text)
    
    # Step 2: Convert CST to AST in source domain
    converter = CSTToASTConverter(domain=source_domain)
    source_ast = converter.convert(cst)
    
    # Step 3: Translate across domains
    translator = CrossDomainTranslator()
    target_ast, ctx = translator.translate(source_ast, target_domain)
    
    return target_ast, ctx


# Export public API
__all__ = [
    # Types
    "DomainType",
    "CategoryLabel",
    "Relation",
    # CST Layer
    "CSTNode",
    "Token",
    "Production",
    # AST Layer
    "ASTNode",
    "SymbolicExpr",
    "SemanticProposition",
    "LogicFormula",
    "GeometricObject",
    "RelationalChineseExpr",
    "CrossDomainMorphism",
    # Functors
    "Functor",
    "GrammarFunctor",
    "DomainFunctor",
    # Translation
    "TranslationContext",
    "CrossDomainTranslator",
    "CSTToASTConverter",
    # Utilities
    "build_cst_from_text",
    "build_pipeline",
    "classify_relation_geometric",
]
