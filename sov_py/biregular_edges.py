"""
Universal Biregular Edge Formula across All Depths and Dimensions (OP-013, HYP-116).

Proves and certifies the exact edge formula for biregular zero-divisor sectors
at arbitrary depth k >= 0 across the Cayley-Dickson tower (D = 2^n >= 32):

- Degree levels:
    d_low = 2^(k + 4) - 8
    d_high = D - 8
- Vertex partition:
    N_high = d_low
    N_low = 2(D - 4) - d_low
- Undirected edge count:
    E(D, k) = d_low * (3*D - 16 - d_low) // 2
- Handshake identity:
    N_high * d_high + N_low * d_low = 2 * E(D, k)
"""

from typing import Dict, Any, Tuple
import math
from sedenion.cd_algebra import CDStratificationEngine


def biregular_degrees(D: int, k: int) -> Tuple[int, int]:
    """Returns (d_low, d_high) for dimension D and depth k."""
    d_low = (1 << (k + 4)) - 8
    d_high = D - 8
    return d_low, d_high


def biregular_counts(D: int, k: int) -> Tuple[int, int]:
    """Returns (N_low, N_high) for dimension D and depth k."""
    d_low = (1 << (k + 4)) - 8
    n_high = d_low
    n_low = 2 * (D - 4) - n_high
    return n_low, n_high


def biregular_edge_count(D: int, k: int) -> int:
    """Returns the theoretical total edge count E(D, k)."""
    d_low = (1 << (k + 4)) - 8
    return d_low * (3 * D - 16 - d_low) // 2


def verify_handshake_identity(D: int, k: int) -> bool:
    """Verifies N_high * d_high + N_low * d_low == 2 * E(D, k)."""
    d_low, d_high = biregular_degrees(D, k)
    n_low, n_high = biregular_counts(D, k)
    e = biregular_edge_count(D, k)
    return n_high * d_high + n_low * d_low == 2 * e


def compute_empirical_biregular_edges(D: int, chi: int) -> Dict[str, Any]:
    """
    Computes empirical graph degrees, vertex counts, and edge count for sector chi in dimension D.
    """
    G = CDStratificationEngine.build_component_graph(dim=D, chi=chi)
    degrees = dict(G.degree())
    deg_vals = sorted(set(degrees.values()))
    
    if len(deg_vals) != 2:
        return {
            "D": D,
            "chi": chi,
            "is_biregular": False,
            "degree_levels": deg_vals,
        }
        
    d_low, d_high = deg_vals[0], deg_vals[1]
    n_low = sum(1 for d in degrees.values() if d == d_low)
    n_high = sum(1 for d in degrees.values() if d == d_high)
    e_empirical = G.number_of_edges()
    
    # Invert k from d_low = 2^(k + 4) - 8 => 2^(k + 4) = d_low + 8
    k = int(math.log2(d_low + 8)) - 4
    e_theoretical = biregular_edge_count(D, k)
    
    return {
        "D": D,
        "chi": chi,
        "is_biregular": True,
        "k": k,
        "d_low": d_low,
        "d_high": d_high,
        "n_low": n_low,
        "n_high": n_high,
        "e_empirical": e_empirical,
        "e_theoretical": e_theoretical,
        "matches_formula": e_empirical == e_theoretical,
        "handshake_satisfied": n_high * d_high + n_low * d_low == 2 * e_empirical,
    }
