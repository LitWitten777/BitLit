"""
src/sedenion/kernel/symbol_graph.py
=============================================================================
Persistent Symbol Graph with Invariant Geometric Addressing.
Provides directed relational property graph traversal, topological path finding,
and metric-space geometric neighborhood queries.
=============================================================================
"""

import math
from collections import deque
from typing import Any, Dict, List, Optional, Tuple, Set

from .storage import KernelStorage


class SymbolGraph:
    """
    Relational property graph anchored in geometric coordinate representations.
    Backed by durable SQLite WAL storage.
    """

    def __init__(self, storage: KernelStorage):
        self.storage = storage

    def add_node(
        self,
        node_id: str,
        label: str,
        coordinates: Optional[List[float]] = None,
        attributes: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """
        Insert or update a node in the symbol graph.
        """
        self.storage.put_node(
            node_id=node_id,
            label=label,
            coordinates=coordinates,
            attributes=attributes
        )
        return {
            "node_id": node_id,
            "label": label,
            "coordinates": coordinates,
            "attributes": attributes or {}
        }

    def get_node(self, node_id: str) -> Optional[Dict[str, Any]]:
        """Retrieve node attributes and coordinates by node ID."""
        return self.storage.get_node(node_id)

    def add_edge(
        self,
        source_id: str,
        target_id: str,
        relation: str,
        weight: float = 1.0,
        attributes: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """
        Create a directed relation between source and target nodes.
        Requires both nodes to exist in the graph.
        """
        if not self.get_node(source_id):
            raise ValueError(f"Source node '{source_id}' does not exist in graph.")
        if not self.get_node(target_id):
            raise ValueError(f"Target node '{target_id}' does not exist in graph.")

        self.storage.put_edge(
            source_id=source_id,
            target_id=target_id,
            relation=relation,
            weight=weight,
            attributes=attributes
        )
        return {
            "source_id": source_id,
            "target_id": target_id,
            "relation": relation,
            "weight": weight,
            "attributes": attributes or {}
        }

    def get_neighbors(self, node_id: str, relation: Optional[str] = None) -> List[Dict[str, Any]]:
        """
        Get all outgoing neighbors of a node, optionally filtered by relation type.
        """
        neighbors = self.storage.get_neighbors(node_id)
        if relation is not None:
            return [n for n in neighbors if n.get("relation") == relation]
        return neighbors

    def get_nodes_by_label(self, label: str) -> List[Dict[str, Any]]:
        """Find all nodes matching a specific categorical label."""
        return self.storage.get_all_nodes(label=label)

    def find_path(self, source_id: str, target_id: str, max_depth: int = 6) -> Optional[List[str]]:
        """
        Find shortest path from source to target using Breadth-First Search (BFS).
        Returns list of node IDs forming the path, or None if unreachable within max_depth.
        """
        if source_id == target_id:
            return [source_id]

        queue = deque([(source_id, [source_id])])
        visited: Set[str] = {source_id}

        while queue:
            curr, path = queue.popleft()
            if len(path) - 1 >= max_depth:
                continue

            for neighbor in self.storage.get_neighbors(curr):
                nid = neighbor["node_id"]
                if nid == target_id:
                    return path + [nid]
                if nid not in visited:
                    visited.add(nid)
                    queue.append((nid, path + [nid]))

        return None

    def geometric_nearest(
        self,
        target_coords: List[float],
        top_k: int = 5,
        metric: str = "euclidean"
    ) -> List[Tuple[Dict[str, Any], float]]:
        """
        Find nodes closest to target coordinates in metric space.
        Supports 'euclidean' and 'cosine' distance metrics.
        """
        all_nodes = self.storage.get_all_nodes()
        candidates: List[Tuple[Dict[str, Any], float]] = []

        dim = len(target_coords)

        for node in all_nodes:
            coords = node.get("coordinates")
            if coords is None or len(coords) != dim:
                continue

            if metric == "euclidean":
                dist = math.sqrt(sum((a - b) ** 2 for a, b in zip(target_coords, coords)))
            elif metric == "cosine":
                norm_a = math.sqrt(sum(a ** 2 for a in target_coords))
                norm_b = math.sqrt(sum(b ** 2 for b in coords))
                if norm_a == 0 or norm_b == 0:
                    dist = 1.0
                else:
                    dot = sum(a * b for a, b in zip(target_coords, coords))
                    sim = dot / (norm_a * norm_b)
                    dist = 1.0 - max(-1.0, min(1.0, sim))
            else:
                raise ValueError(f"Unsupported metric: {metric}")

            candidates.append((node, dist))

        candidates.sort(key=lambda x: x[1])
        return candidates[:top_k]

    def count_nodes(self) -> int:
        """Total number of nodes in graph."""
        return len(self.storage.get_all_nodes())

    def count_edges(self) -> int:
        """Total number of edges in graph."""
        return len(self.storage.get_all_edges())

    def get_all_symbols(self) -> List[Dict[str, Any]]:
        """Return all nodes in the symbol graph."""
        return self.storage.get_all_nodes()
