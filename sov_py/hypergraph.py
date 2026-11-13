"""
src/hypergraph.py
Typed Hypergraph runtime — RepresentationObject, first-class HyperEdge,
and provenance enforcement for all nodes and edges.

Author: EngA
Version: 0.1.0
Provenance: {
  source: manual_construction_v0.1,
  derivation: Sprint 1 hypergraph skeleton — typed RepresentationObject + HyperEdge,
  confidence: 0.9, validation_status: validated
}

Design notes
------------
- Every node is a RepresentationObject (a thin wrapper over an IR dict).
- Every edge is a HyperEdge connecting ≥1 source nodes to ≥1 target nodes.
- Provenance is required on both; validation raises ProvenanceError if missing.
- Uses networkx DiGraph internally; HyperNetX support is an optional extension.
- contextID links nodes/edges to a Crucible execution context.
"""
from __future__ import annotations

import uuid
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any, Iterator, Optional

try:
    import networkx as nx
    HAS_NX = True
except ImportError:  # pragma: no cover
    HAS_NX = False
    nx = None  # type: ignore

# ---------------------------------------------------------------------------
# Provenance enforcement
# ---------------------------------------------------------------------------

PROVENANCE_REQUIRED = {
    "source", "derivation", "evidence",
    "confidence", "validation_status", "version", "timestamp",
}


class ProvenanceError(ValueError):
    """Raised when a node or edge is missing required provenance fields."""


def validate_provenance(prov: dict, label: str = "object") -> None:
    if not isinstance(prov, dict):
        raise ProvenanceError(f"{label}: provenance must be a dict, got {type(prov)}")
    missing = PROVENANCE_REQUIRED - set(prov.keys())
    if missing:
        raise ProvenanceError(
            f"{label}: provenance missing required fields: {sorted(missing)}"
        )
    conf = prov.get("confidence")
    if not isinstance(conf, (int, float)) or not (0.0 <= float(conf) <= 1.0):
        raise ProvenanceError(f"{label}: provenance.confidence must be float in [0,1]")


def make_provenance(
    source: str,
    derivation: str,
    *,
    confidence: float = 1.0,
    validation_status: str = "unvalidated",
    version: str = "0.1.0",
    evidence: Optional[list[str]] = None,
    author: Optional[str] = None,
) -> dict[str, Any]:
    """Convenience constructor for a valid provenance dict."""
    return {
        "source": source,
        "derivation": derivation,
        "evidence": evidence or [],
        "confidence": confidence,
        "validation_status": validation_status,
        "version": version,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        **({"author": author} if author else {}),
    }


# ---------------------------------------------------------------------------
# RepresentationObject (Hypergraph Node)
# ---------------------------------------------------------------------------

@dataclass
class RepresentationObject:
    """
    A typed node in the Crucible Hypergraph.
    Wraps a Representation Kernel IR dict and adds hypergraph metadata.
    """
    node_id: str
    context_id: str
    ir: dict[str, Any]                # Must be a valid Representation Kernel IR dict
    provenance: dict[str, Any]
    label: str = ""
    node_type: str = "representation_object"
    attributes: dict[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        validate_provenance(self.provenance, label=f"RepresentationObject({self.node_id})")
        if not self.label:
            self.label = self.ir.get("object_type", self.node_id)

    @classmethod
    def from_ir(
        cls,
        ir: dict[str, Any],
        context_id: str,
        *,
        node_id: Optional[str] = None,
        provenance: Optional[dict] = None,
        **kwargs: Any,
    ) -> "RepresentationObject":
        """Create a RepresentationObject directly from an IR dict."""
        nid = node_id or ir.get("ir_id") or str(uuid.uuid4())
        prov = provenance or ir.get("provenance")
        if prov is None:
            raise ProvenanceError(
                f"IR object {nid!r} has no provenance; cannot create RepresentationObject"
            )
        return cls(
            node_id=nid,
            context_id=context_id,
            ir=ir,
            provenance=prov,
            **kwargs,
        )

    @property
    def representation_level(self) -> int:
        return self.ir.get("representation_level", -1)

    @property
    def object_type(self) -> str:
        return self.ir.get("object_type", "unknown")

    @property
    def ir_id(self) -> str:
        return self.ir.get("ir_id", self.node_id)

    def to_dict(self) -> dict[str, Any]:
        return {
            "node_id": self.node_id,
            "context_id": self.context_id,
            "label": self.label,
            "node_type": self.node_type,
            "ir_id": self.ir_id,
            "object_type": self.object_type,
            "representation_level": self.representation_level,
            "provenance": self.provenance,
            "attributes": self.attributes,
        }


# ---------------------------------------------------------------------------
# HyperEdge (first-class)
# ---------------------------------------------------------------------------

@dataclass
class HyperEdge:
    """
    A first-class hyperedge connecting one or more source nodes to one or more
    target nodes. Can represent n-ary relations.

    Unlike a simple graph edge, a HyperEdge is itself a first-class object
    with its own provenance, label, and attributes — it may be used as a
    source/target of other hyperedges (reification).
    """
    edge_id: str
    context_id: str
    relation: str
    sources: list[str]       # node_ids or edge_ids
    targets: list[str]       # node_ids or edge_ids
    provenance: dict[str, Any]
    weight: float = 1.0
    edge_type: str = "hyperedge"
    attributes: dict[str, Any] = field(default_factory=dict)
    reified_node_id: Optional[str] = None  # if this edge is reified as a node

    def __post_init__(self) -> None:
        if not self.sources:
            raise ValueError(f"HyperEdge {self.edge_id!r}: sources must be non-empty")
        if not self.targets:
            raise ValueError(f"HyperEdge {self.edge_id!r}: targets must be non-empty")
        validate_provenance(self.provenance, label=f"HyperEdge({self.edge_id})")

    def to_dict(self) -> dict[str, Any]:
        return {
            "edge_id": self.edge_id,
            "context_id": self.context_id,
            "relation": self.relation,
            "sources": self.sources,
            "targets": self.targets,
            "weight": self.weight,
            "edge_type": self.edge_type,
            "provenance": self.provenance,
            "attributes": self.attributes,
            "reified_node_id": self.reified_node_id,
        }


# ---------------------------------------------------------------------------
# RepresentationHypergraph
# ---------------------------------------------------------------------------

class RepresentationHypergraph:
    """
    The Crucible Hypergraph: a typed, provenance-enforced hypergraph of
    RepresentationObjects and HyperEdges.

    Internally uses a networkx DiGraph for efficient traversal; hyperedges
    that connect >2 nodes are represented via a reified "edge node".
    """

    def __init__(self, graph_id: Optional[str] = None, context_id: str = "default") -> None:
        self.graph_id = graph_id or str(uuid.uuid4())
        self.context_id = context_id
        self._nodes: dict[str, RepresentationObject] = {}
        self._edges: dict[str, HyperEdge] = {}
        if HAS_NX:
            self._nx_graph: nx.DiGraph = nx.DiGraph(
                graph_id=self.graph_id, context_id=self.context_id
            )

    # ------------------------------------------------------------------
    # Node operations
    # ------------------------------------------------------------------

    def add_node(self, obj: RepresentationObject) -> None:
        """Add a RepresentationObject node. Raises ProvenanceError if invalid."""
        if obj.context_id != self.context_id:
            raise ValueError(
                f"Node {obj.node_id!r} contextID {obj.context_id!r} "
                f"does not match graph contextID {self.context_id!r}"
            )
        self._nodes[obj.node_id] = obj
        if HAS_NX:
            self._nx_graph.add_node(obj.node_id, **obj.to_dict())

    def get_node(self, node_id: str) -> RepresentationObject:
        if node_id not in self._nodes:
            raise KeyError(f"Node {node_id!r} not in hypergraph")
        return self._nodes[node_id]

    def nodes(self) -> Iterator[RepresentationObject]:
        yield from self._nodes.values()

    def node_count(self) -> int:
        return len(self._nodes)

    def __contains__(self, node_id: str) -> bool:
        return node_id in self._nodes

    # ------------------------------------------------------------------
    # Edge operations
    # ------------------------------------------------------------------

    def add_edge(self, edge: HyperEdge) -> None:
        """Add a HyperEdge. All source/target node_ids must already exist."""
        for nid in edge.sources + edge.targets:
            # Nodes may be reified edge nodes — check both dicts
            if nid not in self._nodes and nid not in self._edges:
                raise KeyError(
                    f"HyperEdge {edge.edge_id!r}: node/edge {nid!r} not found in graph"
                )
        self._edges[edge.edge_id] = edge
        if HAS_NX:
            # For n-ary edges, add a reified "edge node" and connect sources→edge→targets
            if len(edge.sources) > 1 or len(edge.targets) > 1:
                eid_node = f"__edge__{edge.edge_id}"
                self._nx_graph.add_node(eid_node, edge_id=edge.edge_id, reified=True)
                for src in edge.sources:
                    self._nx_graph.add_edge(src, eid_node, **edge.to_dict())
                for tgt in edge.targets:
                    self._nx_graph.add_edge(eid_node, tgt, **edge.to_dict())
            else:
                self._nx_graph.add_edge(
                    edge.sources[0], edge.targets[0], **edge.to_dict()
                )

    def get_edge(self, edge_id: str) -> HyperEdge:
        if edge_id not in self._edges:
            raise KeyError(f"Edge {edge_id!r} not in hypergraph")
        return self._edges[edge_id]

    def edges(self) -> Iterator[HyperEdge]:
        yield from self._edges.values()

    def edge_count(self) -> int:
        return len(self._edges)

    # ------------------------------------------------------------------
    # Queries
    # ------------------------------------------------------------------

    def outgoing_edges(self, node_id: str) -> list[HyperEdge]:
        return [e for e in self._edges.values() if node_id in e.sources]

    def incoming_edges(self, node_id: str) -> list[HyperEdge]:
        return [e for e in self._edges.values() if node_id in e.targets]

    def neighbors(self, node_id: str) -> list[str]:
        """Return all node_ids reachable from node_id via any outgoing edge."""
        result: list[str] = []
        for e in self.outgoing_edges(node_id):
            result.extend(e.targets)
        return list(set(result))

    def nodes_by_level(self, level: int) -> list[RepresentationObject]:
        return [n for n in self._nodes.values() if n.representation_level == level]

    def nodes_by_type(self, object_type: str) -> list[RepresentationObject]:
        return [n for n in self._nodes.values() if n.object_type == object_type]

    def validate_all_provenance(self) -> list[str]:
        """Return list of provenance error messages (empty = all OK)."""
        errors: list[str] = []
        for nid, node in self._nodes.items():
            try:
                validate_provenance(node.provenance, label=f"node:{nid}")
            except ProvenanceError as exc:
                errors.append(str(exc))
        for eid, edge in self._edges.items():
            try:
                validate_provenance(edge.provenance, label=f"edge:{eid}")
            except ProvenanceError as exc:
                errors.append(str(exc))
        return errors

    # ------------------------------------------------------------------
    # Serialisation
    # ------------------------------------------------------------------

    def to_dict(self) -> dict[str, Any]:
        return {
            "graph_id": self.graph_id,
            "context_id": self.context_id,
            "nodes": [n.to_dict() for n in self._nodes.values()],
            "edges": [e.to_dict() for e in self._edges.values()],
        }

    def summary(self) -> str:
        return (
            f"RepresentationHypergraph(id={self.graph_id!r}, "
            f"context={self.context_id!r}, "
            f"nodes={self.node_count()}, edges={self.edge_count()})"
        )


# Canonical alias
Hypergraph = RepresentationHypergraph

