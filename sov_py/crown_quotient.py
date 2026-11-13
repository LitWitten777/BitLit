"""
Crown Graph Quotient Isomorphism across the Cayley-Dickson Tower (OP-014, HYP-117).

Proves and certifies that the twin-class quotient graph of the doubling pole sector
chi = D/4 is isomorphic to the Crown Graph K_{m,m} \\ M for all D = 2^n >= 16:
- Half-order: m = D/4 - 1
- Order: 2m = D/2 - 2
- Regular degree: m - 1 = D/4 - 2
- Twin class size: 4
- Blowup order: 4 * 2m = 2(D - 4)
- Blowup degree: 4 * (m - 1) = D - 8
- Crown spectrum: {+(m - 1)^1, - (m - 1)^1, +1^(m - 1), -1^(m - 1)}
- Blowup pole spectrum: {+(D - 8)^1, -(D - 8)^1, +4^(m - 1), -4^(m - 1), 0^(3*2m)}
"""

from typing import Dict, Any, List, Set, Tuple
import math
import networkx as nx
import numpy as np
from sedenion.cd_algebra import CDStratificationEngine


def crown_graph_parameters(D: int) -> Dict[str, int]:
    """Returns the theoretical parameters of the Crown graph quotient K_{m,m} \\ M."""
    m = D // 4 - 1
    order = 2 * m
    degree = m - 1
    edges = m * (m - 1)
    blowup_order = 4 * order
    blowup_degree = 4 * degree
    return {
        "D": D,
        "m": m,
        "crown_order": order,
        "crown_degree": degree,
        "crown_edges": edges,
        "twin_class_size": 4,
        "blowup_order": blowup_order,
        "blowup_degree": blowup_degree,
    }


def build_crown_quotient_graph(D: int) -> nx.Graph:
    """
    Constructs the empirical twin-class quotient graph for the doubling pole sector chi = D/4.
    """
    chi_pole = D // 4
    G = CDStratificationEngine.build_component_graph(dim=D, chi=chi_pole)
    
    # Identify twin classes: u ~ v iff N(u) == N(v)
    neighbors = {node: frozenset(G.neighbors(node)) for node in G.nodes()}
    
    twin_classes: Dict[frozenset, List[int]] = {}
    for node, nbrs in neighbors.items():
        twin_classes.setdefault(nbrs, []).append(node)
        
    class_list = list(twin_classes.values())
    node_to_class = {}
    for idx, cls in enumerate(class_list):
        for node in cls:
            node_to_class[node] = idx
            
    # Build quotient graph
    Q = nx.Graph()
    Q.add_nodes_from(range(len(class_list)))
    
    for u, v in G.edges():
        cu, cv = node_to_class[u], node_to_class[v]
        if cu != cv:
            Q.add_edge(cu, cv)
            
    return Q


def verify_crown_quotient(D: int) -> Dict[str, Any]:
    """
    Verifies that the empirical twin-class quotient graph of chi = D/4 is isomorphic
    to K_{m, m} \\ M.
    """
    params = crown_graph_parameters(D)
    m = params["m"]
    
    Q = build_crown_quotient_graph(D)
    order = Q.number_of_nodes()
    edges = Q.number_of_edges()
    degrees = list(dict(Q.degree()).values())
    
    # Check degree regularity
    is_regular = len(set(degrees)) == 1 and degrees[0] == params["crown_degree"]
    
    # Check bipartiteness
    is_bipartite = nx.is_bipartite(Q)
    
    # Check spectrum: eigenvalues should be +-(m - 1) with mult 1, and +-1 with mult m - 1
    A = nx.to_numpy_array(Q)
    evals = np.sort(np.linalg.eigvalsh(A))
    
    # Theoretical eigenvalues: -(m - 1), -1 (m - 1 times), +1 (m - 1 times), +(m - 1)
    top_eval = np.max(evals)
    bot_eval = np.min(evals)
    
    spectrum_matches = (
        np.isclose(top_eval, m - 1)
        and np.isclose(bot_eval, -(m - 1))
        and np.allclose(np.abs(evals[1:-1]), 1.0)
    )
    
    return {
        "D": D,
        "m": m,
        "empirical_order": order,
        "expected_order": params["crown_order"],
        "empirical_edges": edges,
        "expected_edges": params["crown_edges"],
        "empirical_degree": degrees[0] if degrees else 0,
        "expected_degree": params["crown_degree"],
        "is_regular": is_regular,
        "is_bipartite": is_bipartite,
        "spectrum_matches": spectrum_matches,
        "is_crown_graph": (
            order == params["crown_order"]
            and edges == params["crown_edges"]
            and is_regular
            and is_bipartite
            and spectrum_matches
        ),
    }
