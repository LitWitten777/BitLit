"""
src/sedenion/kernel/memory_kernel.py
=============================================================================
Sovereign Universal Memory Kernel v1.0.
Coordinates immutable content addressing, geometric coordinate indexing,
first-class symbol graph relations, strict invariant validation, and plugin lifecycle.
=============================================================================
"""

import hashlib
import json
import math
from typing import Any, Dict, List, Optional, Tuple

from .storage import KernelStorage
from .symbol_graph import SymbolGraph
from .plugin import KernelPlugin


class UniversalMemoryKernel:
    """
    Core invariant memory substrate providing:
    1. Content-addressable object storage (CID).
    2. Geometric addressing and metric space queries.
    3. First-class relational symbol graph.
    4. Deterministic mathematical invariant validation.
    5. Modular plugin extension architecture.
    """

    def __init__(self, db_path: str = ":memory:"):
        self.db_path = db_path
        self.storage = KernelStorage(db_path=db_path)
        self.graph = SymbolGraph(self.storage)
        self._plugins: List[KernelPlugin] = []

    def __enter__(self) -> "UniversalMemoryKernel":
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        self.close()

    def close(self) -> None:
        """Close storage connections and release resources."""
        self.storage.close()

    @staticmethod
    def compute_cid(content: Any) -> str:
        """
        Compute deterministic SHA-256 Content Identifier (CID).
        """
        if isinstance(content, str):
            payload = content.encode("utf-8")
        elif isinstance(content, (bytes, bytearray)):
            payload = bytes(content)
        else:
            payload = json.dumps(content, sort_keys=True).encode("utf-8")
        return f"cid:sha256:{hashlib.sha256(payload).hexdigest()}"

    def register_plugin(self, plugin: KernelPlugin) -> None:
        """Register a domain plugin and trigger its lifecycle hook."""
        self._plugins.append(plugin)
        plugin.on_attach(self)

    def list_plugins(self) -> List[str]:
        """Return names of registered plugins."""
        return [p.name for p in self._plugins]

    # -------------------------------------------------------------------------
    # Invariant Validation
    # -------------------------------------------------------------------------

    def _validate_coordinates(self, coords: Optional[List[float]]) -> None:
        if coords is None:
            return
        if not isinstance(coords, (list, tuple)) or len(coords) == 0:
            raise ValueError("Coordinates must be a non-empty sequence of numbers.")
        for val in coords:
            if not isinstance(val, (int, float)) or math.isnan(val) or math.isinf(val):
                raise ValueError(f"Invalid coordinate value: {val}. Must be finite float.")

    def _validate_metadata_invariants(self, metadata: Dict[str, Any]) -> None:
        # Probability & confidence invariant: p in [0.0, 1.0]
        for key in ("probability", "confidence", "weight"):
            if key in metadata:
                val = metadata[key]
                if not isinstance(val, (int, float)) or math.isnan(val):
                    raise ValueError(f"Field '{key}' must be numeric, got {val}.")
                if key in ("probability", "confidence") and not (0.0 <= val <= 1.0):
                    raise ValueError(f"Probability invariant violated: {key}={val} not in [0.0, 1.0].")

    # -------------------------------------------------------------------------
    # Record Storage & Retrieval
    # -------------------------------------------------------------------------

    def store(
        self,
        content: Any,
        key: Optional[str] = None,
        coordinates: Optional[List[float]] = None,
        metadata: Optional[Dict[str, Any]] = None
    ) -> str:
        """
        Store an object into memory.
        If key is omitted, a cryptographic CID is automatically generated.
        Applies invariant validation and plugin transformations.
        """
        if key is None:
            key = self.compute_cid(content)

        meta = dict(metadata or {})
        self._validate_coordinates(coordinates)
        self._validate_metadata_invariants(meta)

        record: Dict[str, Any] = {
            "key": key,
            "content": content,
            "coordinates": coordinates,
            "metadata": meta
        }

        # Plugin validation and transformations
        for plugin in self._plugins:
            valid, err = plugin.validate_record(record)
            if not valid:
                raise ValueError(f"Plugin '{plugin.name}' rejected record: {err}")
            record = plugin.transform_record(record)

        self.storage.put_record(
            key=record["key"],
            content=record["content"],
            coordinates=record["coordinates"],
            metadata=record["metadata"]
        )
        return record["key"]

    def retrieve(self, key: str) -> Optional[Dict[str, Any]]:
        """Retrieve a record by key or CID."""
        return self.storage.get_record(key)

    # -------------------------------------------------------------------------
    # Symbol Graph Operations
    # -------------------------------------------------------------------------

    def register_symbol(
        self,
        node_id: str,
        label: str,
        coordinates: Optional[List[float]] = None,
        attributes: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """
        Register a concept or entity into the symbol graph with invariant checks.
        """
        self._validate_coordinates(coordinates)
        attrs = dict(attributes or {})
        self._validate_metadata_invariants(attrs)

        node_data = {
            "node_id": node_id,
            "label": label,
            "coordinates": coordinates,
            "attributes": attrs
        }

        for plugin in self._plugins:
            valid, err = plugin.validate_node(node_data)
            if not valid:
                raise ValueError(f"Plugin '{plugin.name}' rejected symbol node: {err}")

        return self.graph.add_node(
            node_id=node_id,
            label=label,
            coordinates=coordinates,
            attributes=attrs
        )

    def link_symbols(
        self,
        source_id: str,
        target_id: str,
        relation: str,
        weight: float = 1.0,
        attributes: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """
        Establish a directed semantic/mathematical relation between two symbols.
        """
        attrs = dict(attributes or {})
        self._validate_metadata_invariants(attrs)
        if not (0.0 <= weight <= 1.0) and "probability" in relation.lower():
            raise ValueError(f"Relation weight must be in [0.0, 1.0] for probabilistic links, got {weight}.")

        edge_data = {
            "source_id": source_id,
            "target_id": target_id,
            "relation": relation,
            "weight": weight,
            "attributes": attrs
        }

        for plugin in self._plugins:
            valid, err = plugin.validate_edge(edge_data)
            if not valid:
                raise ValueError(f"Plugin '{plugin.name}' rejected symbol edge: {err}")

        return self.graph.add_edge(
            source_id=source_id,
            target_id=target_id,
            relation=relation,
            weight=weight,
            attributes=attrs
        )

    def connect_symbols(
        self,
        source_id: str,
        target_id: str,
        relation: str,
        weight: float = 1.0,
        attributes: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """Alias for link_symbols."""
        return self.link_symbols(
            source_id=source_id,
            target_id=target_id,
            relation=relation,
            weight=weight,
            attributes=attributes
        )

    def get_neighbors(self, node_id: str, relation: Optional[str] = None) -> List[Dict[str, Any]]:
        """Return outgoing neighbors of node in the symbol graph."""
        return self.graph.get_neighbors(node_id, relation=relation)

    def find_path(self, source_id: str, target_id: str, max_depth: int = 6) -> Optional[List[str]]:
        """Find shortest path between symbols using breadth-first search."""
        return self.graph.find_path(source_id, target_id, max_depth=max_depth)

    def query_geometric(
        self,
        coordinates: List[float],
        top_k: int = 5,
        metric: str = "euclidean"
    ) -> List[Tuple[Dict[str, Any], float]]:
        """
        Query nearest symbols in metric coordinate space.
        """
        self._validate_coordinates(coordinates)
        return self.graph.geometric_nearest(target_coords=coordinates, top_k=top_k, metric=metric)

    # -------------------------------------------------------------------------
    # Integrity Audit
    # -------------------------------------------------------------------------

    def verify_integrity(self) -> Dict[str, Any]:
        """
        Perform exhaustive audit on storage and graph invariants.
        Checks for orphan edges, corrupted coordinates, or out-of-bound probabilities.
        """
        violations: List[str] = []
        nodes = self.storage.get_all_nodes()
        edges = self.storage.get_all_edges()

        node_ids = {n["node_id"] for n in nodes}

        # Check edge referential integrity
        for edge in edges:
            if edge["source_id"] not in node_ids:
                violations.append(f"Orphan edge {edge['edge_id']}: missing source {edge['source_id']}")
            if edge["target_id"] not in node_ids:
                violations.append(f"Orphan edge {edge['edge_id']}: missing target {edge['target_id']}")

        # Check node coordinate validity
        for n in nodes:
            coords = n.get("coordinates")
            if coords is not None:
                for c in coords:
                    if math.isnan(c) or math.isinf(c):
                        violations.append(f"Node {n['node_id']} has non-finite coordinate {c}")

        return {
            "healthy": len(violations) == 0,
            "nodes_count": len(nodes),
            "edges_count": len(edges),
            "violations": violations
        }
