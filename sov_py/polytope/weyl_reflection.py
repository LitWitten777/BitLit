"""
src/sedenion/polytope/weyl_reflection.py
=============================================================================
E8 Weyl Root Reflections, Fundamental Chamber Folding, and AST Operator Duality.

Implements:
1. E8 simple root system (8 roots, norm² = 2.0).
2. Weyl reflection s_α(x) = x - ⟨x, α⟩ α (exact Euclidean isometry).
3. Fundamental Weyl chamber folding: ⟨x_fund, α_i⟩ ≥ 0 for all i ∈ {1..8}.
4. Point inversion (antipodal reflection x ↦ -x).
5. AST operator reflection: comparison (< ↔ >), Boolean (And ↔ Or),
   and arithmetic (+ ↔ -) duality inversion.
=============================================================================
"""

from __future__ import annotations

import ast
import math
from dataclasses import dataclass
from typing import Any, Sequence, Tuple

import numpy as np


# ---------------------------------------------------------------------------
# E8 Simple Roots (Standard Bourbaki Basis, norm² = 2.0)
# ---------------------------------------------------------------------------

E8_SIMPLE_ROOTS: tuple[tuple[float, ...], ...] = (
    (1.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0),
    (0.0, 1.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0),
    (0.0, 0.0, 1.0, -1.0, 0.0, 0.0, 0.0, 0.0),
    (0.0, 0.0, 0.0, 1.0, -1.0, 0.0, 0.0, 0.0),
    (0.0, 0.0, 0.0, 0.0, 1.0, -1.0, 0.0, 0.0),
    (0.0, 0.0, 0.0, 0.0, 0.0, 1.0, -1.0, 0.0),
    (0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 0.0),
    (-0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5),
)


def inner_product(u: Sequence[float], v: Sequence[float]) -> float:
    return float(sum(a * b for a, b in zip(u, v)))


def weyl_reflect(x: Sequence[float], alpha: Sequence[float]) -> tuple[float, ...]:
    """
    Computes elementary Weyl reflection across hyperplane orthogonal to root alpha:
    s_alpha(x) = x - 2 * (⟨x, alpha⟩ / ⟨alpha, alpha⟩) * alpha.
    Since ⟨alpha, alpha⟩ = 2 for E8 simple roots, this simplifies to:
    s_alpha(x) = x - ⟨x, alpha⟩ * alpha.
    """
    ip = inner_product(x, alpha)
    norm_alpha_sq = inner_product(alpha, alpha)
    factor = 2.0 * ip / norm_alpha_sq
    return tuple(xi - factor * ai for xi, ai in zip(x, alpha))


def point_inversion(x: Sequence[float]) -> tuple[float, ...]:
    """Computes polar antipodal negation: x ↦ -x."""
    return tuple(-xi for xi in x)


def fold_into_fundamental_chamber(
    x: Sequence[float],
    max_steps: int = 200,
    tol: float = 1e-9,
) -> tuple[tuple[float, ...], int]:
    """
    Folds an arbitrary vector x in R^8 into the closed Fundamental Weyl Chamber
    by iteratively reflecting across any simple root with negative inner product.
    """
    current = tuple(float(xi) for xi in x)
    steps = 0

    for _ in range(max_steps):
        reflected = False
        for alpha in E8_SIMPLE_ROOTS:
            if inner_product(current, alpha) < -tol:
                current = weyl_reflect(current, alpha)
                steps += 1
                reflected = True
                break
        if not reflected:
            break

    return current, steps


# ---------------------------------------------------------------------------
# AST Operator Reflection (Duality Transformations)
# ---------------------------------------------------------------------------

class ASTOperatorReflector(ast.NodeTransformer):
    """
    Inverts comparison, Boolean, and arithmetic operators to generate dual AST.
    """

    def visit_Compare(self, node: ast.Compare) -> ast.Compare:
        self.generic_visit(node)
        new_ops = []
        for op in node.ops:
            if isinstance(op, ast.Lt):
                new_ops.append(ast.Gt())
            elif isinstance(op, ast.Gt):
                new_ops.append(ast.Lt())
            elif isinstance(op, ast.LtE):
                new_ops.append(ast.GtE())
            elif isinstance(op, ast.GtE):
                new_ops.append(ast.LtE())
            elif isinstance(op, ast.Eq):
                new_ops.append(ast.NotEq())
            elif isinstance(op, ast.NotEq):
                new_ops.append(ast.Eq())
            elif isinstance(op, ast.In):
                new_ops.append(ast.NotIn())
            elif isinstance(op, ast.NotIn):
                new_ops.append(ast.In())
            elif isinstance(op, ast.Is):
                new_ops.append(ast.IsNot())
            elif isinstance(op, ast.IsNot):
                new_ops.append(ast.Is())
            else:
                new_ops.append(op)
        node.ops = new_ops
        return node

    def visit_BoolOp(self, node: ast.BoolOp) -> ast.BoolOp:
        self.generic_visit(node)
        if isinstance(node.op, ast.And):
            node.op = ast.Or()
        elif isinstance(node.op, ast.Or):
            node.op = ast.And()
        return node

    def visit_BinOp(self, node: ast.BinOp) -> ast.BinOp:
        self.generic_visit(node)
        if isinstance(node.op, ast.Add):
            node.op = ast.Sub()
        elif isinstance(node.op, ast.Sub):
            node.op = ast.Add()
        elif isinstance(node.op, ast.Mult):
            node.op = ast.Div()
        elif isinstance(node.op, ast.Div):
            node.op = ast.Mult()
        return node


def reflect_ast_code(code_str: str) -> str:
    """
    Parses Python source code, applies AST operator reflection, and returns unparsed source.
    """
    tree = ast.parse(code_str)
    reflector = ASTOperatorReflector()
    transformed = reflector.visit(tree)
    ast.fix_missing_locations(transformed)
    return ast.unparse(transformed)


# ---------------------------------------------------------------------------
# Verification Helpers
# ---------------------------------------------------------------------------

def verify_reflection_invariants(x: Sequence[float]) -> dict[str, Any]:
    """
    Verifies that Weyl reflections are exact isometries and point inversion produces
    antipodal vectors.
    """
    norm_x = math.sqrt(inner_product(x, x))
    refl_norms_match = True
    for alpha in E8_SIMPLE_ROOTS:
        s_x = weyl_reflect(x, alpha)
        norm_s = math.sqrt(inner_product(s_x, s_x))
        if not math.isclose(norm_x, norm_s, rel_tol=1e-7):
            refl_norms_match = False
            break

    x_neg = point_inversion(x)
    norm_neg = math.sqrt(inner_product(x_neg, x_neg))
    neg_norm_matches = math.isclose(norm_x, norm_neg, rel_tol=1e-7)

    x_fund, steps = fold_into_fundamental_chamber(x)
    in_chamber = all(inner_product(x_fund, alpha) >= -1e-8 for alpha in E8_SIMPLE_ROOTS)

    return {
        "norm_x": norm_x,
        "refl_norms_match": refl_norms_match,
        "neg_norm_matches": neg_norm_matches,
        "chamber_steps": steps,
        "in_chamber": in_chamber,
    }


# ---------------------------------------------------------------------------
# Geometric Logic & Weyl Orbit Tracing
# ---------------------------------------------------------------------------

class GeometricInferenceRelation:
    DEDUCTIVE = "deductive"           # d = √2, <u, v> = 1
    ORTHOGONAL = "orthogonal"         # d = 2,  <u, v> = 0
    DUAL = "dual"                     # d = √6, <u, v> = -1
    CONTRADICTION = "contradiction"   # d = 2√2, <u, v> = -2
    IDENTICAL = "identical"           # d = 0,  <u, v> = 2
    NON_ROOT = "non_root"


def euclidean_distance(u: Sequence[float], v: Sequence[float]) -> float:
    """Computes standard Euclidean metric distance."""
    return math.sqrt(sum((a - b) ** 2 for a, b in zip(u, v)))


def classify_geometric_relation(u: Sequence[float], v: Sequence[float], tol: float = 1e-5) -> str:
    """
    Classifies non-propositional geometric inference relations over E8 root vectors:
    - Deductive inference: d = √2 (⟨u, v⟩ = 1)
    - Logical orthogonality: d = 2 (⟨u, v⟩ = 0)
    - Duality: d = √6 (⟨u, v⟩ = -1)
    - Antipodal contradiction: d = 2√2 (⟨u, v⟩ = -2)
    - Identical: d = 0 (⟨u, v⟩ = 2)
    """
    ip = inner_product(u, v)
    if math.isclose(ip, 2.0, abs_tol=tol):
        return GeometricInferenceRelation.IDENTICAL
    elif math.isclose(ip, 1.0, abs_tol=tol):
        return GeometricInferenceRelation.DEDUCTIVE
    elif math.isclose(ip, 0.0, abs_tol=tol):
        return GeometricInferenceRelation.ORTHOGONAL
    elif math.isclose(ip, -1.0, abs_tol=tol):
        return GeometricInferenceRelation.DUAL
    elif math.isclose(ip, -2.0, abs_tol=tol):
        return GeometricInferenceRelation.CONTRADICTION
    return GeometricInferenceRelation.NON_ROOT


def trace_weyl_orbit(
    x: Sequence[float],
    max_depth: int = 3,
    simple_roots: Sequence[Sequence[float]] = E8_SIMPLE_ROOTS,
    tol: float = 1e-6,
) -> list[tuple[float, ...]]:
    """
    Traces the discrete orbit of vector x under the action of the E8 Weyl group
    generated by reflections across simple roots up to a specified depth.
    """
    start = tuple(round(coord, 8) for coord in x)
    orbit = [start]
    seen = {start}
    current_level = [start]
    for _ in range(max_depth):
        next_level = []
        for vec in current_level:
            for root in simple_roots:
                refl = weyl_reflect(vec, root)
                canonical = tuple(round(coord, 8) for coord in refl)
                if canonical not in seen:
                    seen.add(canonical)
                    orbit.append(canonical)
                    next_level.append(canonical)
        current_level = next_level
        if not current_level:
            break
    return orbit

