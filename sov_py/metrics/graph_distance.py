"""
src/metrics/graph_distance.py
Graph edit distance (GED) approximation metric between two IR semantic graphs.

Uses a greedy node-matching heuristic (not exact GED, which is NP-hard).
Exact GED via networkx is available as a fallback for small graphs (≤8 nodes).

Author: EngB
Version: 0.1.0
"""
from __future__ import annotations

from typing import Any

from ..hypergraph import RepresentationObject
from .base import BaseMetric

try:
    import networkx as nx
    HAS_NX = True
except ImportError:
    HAS_NX = False


def _build_nx_graph(ir: dict) -> "nx.Graph":
    """Build a networkx Graph from an IR content.graph dict."""
    G = nx.Graph()
    graph = ir.get("content", {}).get("graph", {})
    for node in graph.get("nodes", []):
        G.add_node(node["node_id"], label=node.get("label", ""), node_type=node.get("node_type", ""))
    for edge in graph.get("edges", []):
        for src in edge.get("sources", []):
            for tgt in edge.get("targets", []):
                G.add_edge(src, tgt, relation=edge.get("relation", ""))
    return G


def _greedy_ged(G1: "nx.Graph", G2: "nx.Graph") -> float:
    """
    Greedy approximation of Graph Edit Distance.
    Cost model: node substitution=1, node insertion/deletion=1, edge insertion/deletion=1.
    """
    n1, n2 = G1.number_of_nodes(), G2.number_of_nodes()
    e1, e2 = G1.number_of_edges(), G2.number_of_edges()

    # Unmatched nodes cost 1 each (insertion/deletion)
    node_cost = abs(n1 - n2)
    # Unmatched edges cost 1 each
    edge_cost = abs(e1 - e2)
    # Shared nodes with different labels cost 0.5 each (substitution heuristic)
    labels1 = sorted(G1.nodes[n].get("label", "") for n in G1.nodes)
    labels2 = sorted(G2.nodes[n].get("label", "") for n in G2.nodes)
    label_matches = sum(a == b for a, b in zip(labels1, labels2))
    substitution_cost = min(n1, n2) - label_matches

    return float(node_cost + edge_cost + substitution_cost)


def _normalize_ged(ged: float, G1: "nx.Graph", G2: "nx.Graph") -> float:
    """Normalize GED to [0,1]; 0=identical, 1=maximally different."""
    max_cost = G1.number_of_nodes() + G2.number_of_nodes() + G1.number_of_edges() + G2.number_of_edges()
    if max_cost == 0:
        return 0.0
    return min(ged / max_cost, 1.0)


class GraphDistance(BaseMetric):
    """
    Graph-edit-distance-based similarity between two IR semantic graphs.
    Score = 1 - normalized_GED, so 1.0 = identical, 0.0 = maximally different.

    Falls back to structural feature comparison if networkx is unavailable.
    """

    metric_name = "graph_distance_similarity"
    bounded = True
    NX_EXACT_THRESHOLD = 8   # use exact GED only for graphs with ≤ this many nodes

    def _compute(
        self,
        a: RepresentationObject,
        b: RepresentationObject,
        use_exact: bool = False,
        **kwargs: Any,
    ) -> tuple[float, dict[str, Any]]:

        if not HAS_NX:
            return self._fallback_compute(a, b)

        G1 = _build_nx_graph(a.ir)
        G2 = _build_nx_graph(b.ir)

        n_nodes = max(G1.number_of_nodes(), G2.number_of_nodes())

        # For small graphs use exact GED (networkx optimize_graph_edit_distance)
        if use_exact and n_nodes <= self.NX_EXACT_THRESHOLD:
            try:
                ged = next(nx.optimize_graph_edit_distance(G1, G2))
                method = "exact"
            except Exception:
                ged = _greedy_ged(G1, G2)
                method = "greedy_fallback"
        else:
            ged = _greedy_ged(G1, G2)
            method = "greedy"

        norm_ged = _normalize_ged(ged, G1, G2)
        score = 1.0 - norm_ged

        return score, {
            "ged": round(ged, 4),
            "normalized_ged": round(norm_ged, 4),
            "method": method,
            "nodes_a": G1.number_of_nodes(),
            "edges_a": G1.number_of_edges(),
            "nodes_b": G2.number_of_nodes(),
            "edges_b": G2.number_of_edges(),
        }

    def _fallback_compute(
        self,
        a: RepresentationObject,
        b: RepresentationObject,
    ) -> tuple[float, dict[str, Any]]:
        """Structural feature fallback (no networkx)."""
        def graph_features(ir: dict) -> dict[str, int]:
            g = ir.get("content", {}).get("graph", {})
            return {
                "nodes": len(g.get("nodes", [])),
                "edges": len(g.get("edges", [])),
            }

        fa = graph_features(a.ir)
        fb = graph_features(b.ir)
        diffs = sum(abs(fa[k] - fb[k]) for k in fa)
        total = sum(fa[k] + fb[k] for k in fa)
        norm = diffs / total if total > 0 else 0.0
        return 1.0 - norm, {
            "method": "structural_fallback",
            "nodes_a": fa["nodes"],
            "nodes_b": fb["nodes"],
            "edges_a": fa["edges"],
            "edges_b": fb["edges"],
        }
