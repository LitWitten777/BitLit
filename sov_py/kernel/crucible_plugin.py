"""
src/sedenion/kernel/crucible_plugin.py
=============================================================================
Crucible Hypergraph Plugin for Sovereign Universal Memory Kernel.
Bridges RepresentationObjects, HyperEdges, and the 7 canonical Crucible operators
into the invariant KernelStorage and SymbolGraph.
=============================================================================
"""

from typing import Any, Dict, List, Optional, Tuple, TYPE_CHECKING
from .plugin import KernelPlugin
from ..crucible import HyperEdge, Hypergraph, RepresentationObject, validate_provenance

if TYPE_CHECKING:
    from .memory_kernel import UniversalMemoryKernel


class CrucibleKernelPlugin(KernelPlugin):
    """
    Bridge plugin connecting Crucible Hypergraph runtime to UniversalMemoryKernel.
    Guarantees that RepresentationObjects and HyperEdges are indexed with cryptographic
    CIDs, geometric coordinates, and relational edges in SymbolGraph.
    """

    def __init__(self, hypergraph: Optional[Hypergraph] = None, context_id: str = "default"):
        self.hypergraph = hypergraph or Hypergraph(context_id=context_id)
        self._kernel: Optional["UniversalMemoryKernel"] = None

    @property
    def name(self) -> str:
        return "CrucibleKernelPlugin"

    def on_attach(self, kernel: "UniversalMemoryKernel") -> None:
        self._kernel = kernel

    def validate_record(self, record: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """
        If the record represents an IR representation object, enforce provenance fields.
        """
        meta = record.get("metadata", {})
        if "ir_type" in meta or "provenance" in meta:
            prov = meta.get("provenance")
            if not prov or not isinstance(prov, dict):
                return False, "Crucible IR records require a valid 'provenance' dict in metadata."
            try:
                validate_provenance(prov, label=record.get("key", "record"))
            except Exception as e:
                return False, str(e)
        return True, None

    def ingest_representation(self, obj: RepresentationObject) -> str:
        """
        Store a RepresentationObject into the UniversalMemoryKernel and register
        it as a SymbolGraph node.
        """
        if self._kernel is None:
            raise RuntimeError("CrucibleKernelPlugin must be attached to a UniversalMemoryKernel before ingestion.")

        # Extract coordinates if present in IR data
        coords: Optional[List[float]] = None
        content = obj.ir.get("content", {})
        payload = content.get("payload", {}) if isinstance(content, dict) else {}
        raw_coords = (
            payload.get("coordinates")
            or payload.get("vector")
            or obj.attributes.get("coordinates")
        )
        if isinstance(raw_coords, (list, tuple)):
            coords = [float(x) for x in raw_coords]

        metadata = {
            "ir_type": obj.object_type,
            "node_id": obj.node_id,
            "provenance": obj.provenance,
            "confidence": float(obj.provenance.get("confidence", 1.0)),
        }

        # Store in kernel
        cid = self._kernel.store(
            content=obj.to_dict(),
            key=f"rep:{obj.node_id}",
            coordinates=coords,
            metadata=metadata
        )

        # Register in symbol graph
        self._kernel.register_symbol(
            node_id=obj.node_id,
            label=obj.object_type,
            coordinates=coords,
            attributes={"cid": cid, **metadata}
        )

        # Also track in local hypergraph
        if obj.node_id not in self.hypergraph:
            self.hypergraph.add_node(obj)

        return cid

    def ingest_hyperedge(self, edge: HyperEdge) -> None:
        """
        Ingest a Crucible HyperEdge, establishing pairwise relations across all
        source-target pairs in the SymbolGraph.
        """
        if self._kernel is None:
            raise RuntimeError("CrucibleKernelPlugin must be attached to a UniversalMemoryKernel before ingestion.")

        # Ensure all source and target nodes are in hypergraph
        for src_id in edge.sources:
            if src_id not in self.hypergraph:
                raise ValueError(f"Edge source '{src_id}' not found in hypergraph.")
        for tgt_id in edge.targets:
            if tgt_id not in self.hypergraph:
                raise ValueError(f"Edge target '{tgt_id}' not found in hypergraph.")

        self.hypergraph.add_edge(edge)

        # Link in kernel SymbolGraph
        for src_id in edge.sources:
            for tgt_id in edge.targets:
                self._kernel.link_symbols(
                    source_id=src_id,
                    target_id=tgt_id,
                    relation=edge.relation,
                    weight=float(edge.provenance.get("confidence", 1.0)),
                    attributes={
                        "edge_id": edge.edge_id,
                        "provenance": edge.provenance,
                        "weight": edge.weight
                    }
                )

    def sync_hypergraph(self, hg: Hypergraph) -> Dict[str, int]:
        """
        Synchronize an entire Hypergraph into the attached UniversalMemoryKernel.
        """
        if self.hypergraph.node_count() == 0:
            self.hypergraph.context_id = hg.context_id

        nodes_synced = 0
        edges_synced = 0

        for node in hg.nodes():
            self.ingest_representation(node)
            nodes_synced += 1

        for edge in hg.edges():
            self.ingest_hyperedge(edge)
            edges_synced += 1

        return {"nodes_synced": nodes_synced, "edges_synced": edges_synced}
