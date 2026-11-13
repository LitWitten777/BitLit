"""Symplectic Surface Summing and Negative Spheres (Anar Akhmedov 2026).

Implements:
1. Relative Surface-Summing Invariants (Theorem 2.2):
   Given relative surfaces C_1, ..., C_r in X meeting Sigma transversely in d_i > 0 points
   (total m = sum d_i), and connector F in Z meeting Sigma' in m points:
   - Self-intersection additive law: C^2 = F^2 + sum_{i=1}^r C_i^2
   - Genus formula: g(C) = g(F) + sum_{i=1}^r g(C_i) + m - r
   - Euler characteristic conservation: chi(C) = chi(F) + sum_{i=1}^r chi(C_i) - 2m.
2. Connected Gluing Graph Formulation (Proposition 3.1):
   Let Gamma = (V, E) be the gluing graph where V = {F, C_1, ..., C_r} (|V| = r + 1)
   and E = {matched circles} (|E| = m).
   - First Betti number: b_1(Gamma) = |E| - |V| + 1 = m - r.
   - Graph genus formula: g(C_Gamma) = sum_{v in V} g(C_v) + b_1(Gamma).
3. Sphere-Summing Consolidation (Section 4, Corollary 4.1):
   When g(F) = 0, g(C_i) = 0, and d_i = 1 for all i:
   - m = r = p
   - g(C) = 0 + 0 + p - p = 0 (output is a symplectic sphere!)
   - C^2 = F^2 + sum_{i=1}^p C_i^2 = 0 + sum_{i=1}^p C_i^2.
   - For p exceptional (-1)-spheres: C^2 = -p.
4. Higher-Genus Generalization via Smith Braids (Proposition 6.1):
   For class 2k[Sigma_h] in Sigma_h x S^2, genus r = 1 + 2k(h - 1),
   with sphere connector F = {x} x S^2 (F^2 = 0, g(F) = 0, meeting in 2k points).
   Summing 2k sphere sections of square S_i^2 gives sphere of square sum S_i^2.
   If each S_i^2 = -1, output is a (-2k)-sphere.
"""

from dataclasses import dataclass
from typing import List, Tuple, Dict


@dataclass(frozen=True)
class RelativeSurface:
    name: str
    genus: int
    self_intersection: int
    intersection_points: int  # d_i with summing surface


@dataclass(frozen=True)
class ConnectorSurface:
    name: str
    genus: int
    self_intersection: int
    intersection_points: int  # m = sum d_i


def compute_summed_surface_invariants(
    rel_surfaces: List[RelativeSurface],
    connector: ConnectorSurface,
) -> Tuple[int, int, int]:
    """Compute (genus, self_intersection, euler_char) of C = C_1 # ... # C_r # F.
    Returns: (g(C), C^2, chi(C))
    """
    r = len(rel_surfaces)
    m = sum(s.intersection_points for s in rel_surfaces)
    assert m == connector.intersection_points, f"Mismatch: sum d_i = {m} != connector m = {connector.intersection_points}"

    # Genus formula: g(C) = g(F) + sum g(C_i) + m - r
    genus_c = connector.genus + sum(s.genus for s in rel_surfaces) + (m - r)

    # Self-intersection formula: C^2 = F^2 + sum C_i^2
    square_c = connector.self_intersection + sum(s.self_intersection for s in rel_surfaces)

    # Euler characteristic: chi(C) = 2 - 2 * g(C)
    chi_c = 2 - 2 * genus_c

    # Direct Euler characteristic calculation via punctured surfaces:
    # chi(F \ m disks) = (2 - 2 g(F)) - m
    # chi(C_i \ d_i disks) = (2 - 2 g(C_i)) - d_i
    # Summing punctured pieces gives identical chi
    chi_punctured_sum = (
        (2 - 2 * connector.genus - m)
        + sum((2 - 2 * s.genus - s.intersection_points) for s in rel_surfaces)
    )
    assert chi_c == chi_punctured_sum, f"Euler characteristic mismatch: {chi_c} != {chi_punctured_sum}"

    return genus_c, square_c, chi_c


def verify_graph_genus_formula(
    rel_surfaces: List[RelativeSurface],
    connector: ConnectorSurface,
) -> Tuple[bool, Dict[str, int]]:
    """Verify g(C_Gamma) = sum_{v in V} g(C_v) + b_1(Gamma)
    where |V| = r + 1, |E| = m, b_1(Gamma) = m - r.
    """
    r = len(rel_surfaces)
    m = sum(s.intersection_points for s in rel_surfaces)
    v_count = r + 1
    e_count = m
    b1_gamma = e_count - v_count + 1  # m - r

    sum_vertex_genus = connector.genus + sum(s.genus for s in rel_surfaces)
    g_graph = sum_vertex_genus + b1_gamma

    g_formula, c2, chi = compute_summed_surface_invariants(rel_surfaces, connector)
    ok = (g_graph == g_formula)

    return ok, {
        "V": v_count,
        "E": e_count,
        "b1": b1_gamma,
        "sum_vertex_genus": sum_vertex_genus,
        "g_total": g_graph,
        "c_squared": c2,
    }


def sphere_summing_consolidation(p: int, square_per_section: int = -1) -> Tuple[int, int]:
    """Recover the sphere-summing construction of Akhmedov-Zhang (2012):
    p disjoint spheres (g=0) each with square s, meeting torus T once (d_i = 1).
    Connector F = {pt} x S^2 in T^2 x S^2 (g(F)=0, F^2 = 0, m = p).
    Returns (g(C), C^2).
    """
    surfaces = [
        RelativeSurface(name=f"S_{i}", genus=0, self_intersection=square_per_section, intersection_points=1)
        for i in range(p)
    ]
    connector = ConnectorSurface(name="F", genus=0, self_intersection=0, intersection_points=p)
    g_c, c2, _ = compute_summed_surface_invariants(surfaces, connector)
    return g_c, c2


def smith_higher_genus_summing(h: int, k: int, square_per_section: int = -1) -> Tuple[int, int, int]:
    """Proposition 6.1 (Smith higher-genus summing):
    h >= 1, k >= 2.
    Summing surface genus r = 1 + 2k(h - 1).
    2k sphere sections S_i (g=0, square s, d_i = 1).
    Connector sphere F in Sigma_h x S^2 meets B_{h,k,a} in 2k points (F^2 = 0, g(F) = 0).
    Returns (r, g(C), C^2).
    """
    r = 1 + 2 * k * (h - 1)
    surfaces = [
        RelativeSurface(name=f"S_{i}", genus=0, self_intersection=square_per_section, intersection_points=1)
        for i in range(2 * k)
    ]
    connector = ConnectorSurface(name="F", genus=0, self_intersection=0, intersection_points=2 * k)
    g_c, c2, _ = compute_summed_surface_invariants(surfaces, connector)
    return r, g_c, c2


def hyp284_master_verification() -> bool:
    """Master verification function for HYP-284."""
    # 1. Sphere summing for p = 4, 5, 6
    for p in [4, 5, 6]:
        g, c2 = sphere_summing_consolidation(p, -1)
        if g != 0 or c2 != -p:
            return False

    # 2. Smith higher genus summing for h = 2, k = 2
    # r = 1 + 4(1) = 5. Output sphere has square -4.
    r, g, c2 = smith_higher_genus_summing(h=2, k=2, square_per_section=-1)
    if r != 5 or g != 0 or c2 != -4:
        return False

    # 3. General positive genus surfaces with multiple intersections
    # C_1 (g=1, C^2=2, d_1=2), C_2 (g=2, C^2=-1, d_2=3), F (g=1, F^2=4, m=5)
    # r = 2, m = 5
    # b1(Gamma) = 5 - 2 = 3
    # g(C) = 1 + (1 + 2) + (5 - 2) = 1 + 3 + 3 = 7
    # C^2 = 4 + 2 - 1 = 5
    s1 = RelativeSurface("C1", genus=1, self_intersection=2, intersection_points=2)
    s2 = RelativeSurface("C2", genus=2, self_intersection=-1, intersection_points=3)
    conn = ConnectorSurface("F", genus=1, self_intersection=4, intersection_points=5)
    ok, data = verify_graph_genus_formula([s1, s2], conn)
    if not ok or data["g_total"] != 7 or data["c_squared"] != 5 or data["b1"] != 3:
        return False

    return True
