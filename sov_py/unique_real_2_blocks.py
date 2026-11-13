"""Finite Groups with a Unique Real 2-Block.

Grounding:
    Yu Zeng, Fuming Jiang (2026),
    "Finite groups with a unique real 2-block",
    arXiv preprint.

Key Theorems & Structural Invariants:
1. Quasi-Simple Classification (Theorem 3.1 & McHugh–Schaeffer Fry 2026):
   A finite quasi-simple group G has a unique real 2-block if and only if
   G/Z(G) in {M_11, M_22, M_23, M_24, PSL(3, 3), PSU(3, 3)}.

2. General Finite Group Classification (Theorem A):
   Let G be a finite group, and let N = O^{2'}(G).
   G has a unique real 2-block if and only if:
     (1) Every N-conjugacy class contained in O_{2'}(N) has odd size.
     (2) Set T = N / O_{2'}(N). Then T = E x H where:
         (i) E is trivial or a direct product of simple groups in {M_11, M_23, PSL(3, 3), PSU(3, 3)}.
         (ii) H is either 2-constrained, or every component of H is of type M_22 or M_24.

3. Rational Ordinary Characters in Principal 2-Block (Corollary B):
   Every irreducible ordinary character afforded by a rational representation lies
   in the principal 2-block B_0(G) if and only if (1) and (2) hold.

4. 2-Constrained Criterion:
   A group H is 2-constrained if C_H(O_{2', 2}(H) / O_{2'}(H)) <= O_{2', 2}(H).
   For 2-groups or solvable groups with trivial odd core, this is automatically satisfied.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple


# The 6 sporadic/Lie-type simple groups admitting a unique real 2-block
QUASI_SIMPLE_UNIQUE_REAL_2_BLOCK: Set[str] = {
    "M11",
    "M22",
    "M23",
    "M24",
    "PSL(3,3)",
    "PSU(3,3)",
}

# The direct product E factor simple group components
E_FACTOR_SIMPLE_COMPONENTS: Set[str] = {
    "M11",
    "M23",
    "PSL(3,3)",
    "PSU(3,3)",
}

# Allowed H factor simple components if not 2-constrained
H_FACTOR_ALLOWED_COMPONENTS: Set[str] = {
    "M22",
    "M24",
}

# Group orders
SIMPLE_GROUP_ORDERS: Dict[str, int] = {
    "M11": 7920,        # 2^4 * 3^2 * 5 * 11
    "M22": 443520,      # 2^7 * 3^2 * 5 * 7 * 11
    "M23": 10200960,    # 2^7 * 3^2 * 5 * 7 * 11 * 23
    "M24": 244823040,   # 2^10 * 3^3 * 5 * 7 * 11 * 23
    "PSL(3,3)": 5616,   # 2^4 * 3^3 * 13
    "PSU(3,3)": 6048,   # 2^5 * 3^3 * 7
}

# Outer automorphism group orders
OUTER_AUTOMORPHISM_ORDERS: Dict[str, int] = {
    "M11": 1,
    "M22": 2,
    "M23": 1,
    "M24": 1,
    "PSL(3,3)": 2,
    "PSU(3,3)": 2,
}

# Schur multiplier orders
SCHUR_MULTIPLIER_ORDERS: Dict[str, int] = {
    "M11": 1,
    "M22": 12,
    "M23": 1,
    "M24": 1,
    "PSL(3,3)": 1,
    "PSU(3,3)": 1,
}


@dataclass(frozen=True)
class GroupBlockProfile:
    """Structural profile of a finite group G for real 2-block classification."""
    name: str
    order: int
    n_classes_in_o2prime_n: List[int]  # Sizes of N-conjugacy classes in O_{2'}(N)
    e_components: List[str]            # Simple components of E
    h_is_2_constrained: bool           # True if H is 2-constrained
    h_components: List[str]            # Components of H (if not 2-constrained)

    def check_odd_class_sizes_in_odd_core(self) -> bool:
        """Condition (1): Every N-conjugacy class in O_{2'}(N) has odd size."""
        return all(size % 2 == 1 for size in self.n_classes_in_o2prime_n)

    def check_e_factor(self) -> bool:
        """Condition (2)(i): E is trivial or product of {M11, M23, PSL(3,3), PSU(3,3)}."""
        return all(c in E_FACTOR_SIMPLE_COMPONENTS for c in self.e_components)

    def check_h_factor(self) -> bool:
        """Condition (2)(ii): H is 2-constrained, or every component is of type M22 or M24."""
        if self.h_is_2_constrained:
            return True
        return len(self.h_components) > 0 and all(c in H_FACTOR_ALLOWED_COMPONENTS for c in self.h_components)

    def has_unique_real_2_block(self) -> bool:
        """Evaluate Theorem A necessary and sufficient condition."""
        return (
            self.check_odd_class_sizes_in_odd_core()
            and self.check_e_factor()
            and self.check_h_factor()
        )


def verify_quasisimple_group(name: str) -> bool:
    """Verify whether a quasi-simple group has a unique real 2-block (Theorem 3.1)."""
    return name in QUASI_SIMPLE_UNIQUE_REAL_2_BLOCK


def build_standard_test_cases() -> Dict[str, GroupBlockProfile]:
    """Build structural profiles for standard test groups."""
    return {
        "A4": GroupBlockProfile(
            name="A4",
            order=12,
            n_classes_in_o2prime_n=[1],  # O_{2'}(V_4) = {1}
            e_components=[],
            h_is_2_constrained=True,     # V_4 is 2-constrained
            h_components=[],
        ),
        "S3": GroupBlockProfile(
            name="S3",
            order=6,
            n_classes_in_o2prime_n=[1, 2],  # Class of 3-cycles has size 2 (EVEN!)
            e_components=[],
            h_is_2_constrained=True,
            h_components=[],
        ),
        "A5": GroupBlockProfile(
            name="A5",
            order=60,
            n_classes_in_o2prime_n=[1],  # O_{2'}(A5) = 1
            e_components=[],
            h_is_2_constrained=False,
            h_components=["A5"],        # Component A5 not in {M22, M24}
        ),
        "M11": GroupBlockProfile(
            name="M11",
            order=7920,
            n_classes_in_o2prime_n=[1],
            e_components=["M11"],
            h_is_2_constrained=True,     # H = 1 is 2-constrained
            h_components=[],
        ),
        "M22": GroupBlockProfile(
            name="M22",
            order=443520,
            n_classes_in_o2prime_n=[1],
            e_components=[],
            h_is_2_constrained=False,
            h_components=["M22"],        # M22 allowed in H
        ),
        "M23": GroupBlockProfile(
            name="M23",
            order=10200960,
            n_classes_in_o2prime_n=[1],
            e_components=["M23"],
            h_is_2_constrained=True,
            h_components=[],
        ),
        "M24": GroupBlockProfile(
            name="M24",
            order=244823040,
            n_classes_in_o2prime_n=[1],
            e_components=[],
            h_is_2_constrained=False,
            h_components=["M24"],        # M24 allowed in H
        ),
        "PSL(3,3)": GroupBlockProfile(
            name="PSL(3,3)",
            order=5616,
            n_classes_in_o2prime_n=[1],
            e_components=["PSL(3,3)"],
            h_is_2_constrained=True,
            h_components=[],
        ),
        "PSU(3,3)": GroupBlockProfile(
            name="PSU(3,3)",
            order=6048,
            n_classes_in_o2prime_n=[1],
            e_components=["PSU(3,3)"],
            h_is_2_constrained=True,
            h_components=[],
        ),
        "DirectProduct_M11_M23": GroupBlockProfile(
            name="M11_x_M23",
            order=7920 * 10200960,
            n_classes_in_o2prime_n=[1],
            e_components=["M11", "M23"],
            h_is_2_constrained=True,
            h_components=[],
        ),
    }
