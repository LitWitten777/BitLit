"""
src/crucible/context.py
CrucibleContext — execution context for a single Crucible run.

Carries: hypergraph reference, registry, adversary, TTF instrumentation,
justification log, decomposed sub-objects, and contextID.

Author: EngA
Version: 0.1.0
"""
from __future__ import annotations

import uuid
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any, Optional

if TYPE_CHECKING:
    from ..atlas.registry import AtlasRegistry
    from ..hypergraph import RepresentationHypergraph
    from .justification import Justification
    from .ttf import TTFInstrumentation
    from .adversary import AdversaryEngine


@dataclass
class CrucibleContext:
    """
    Shared execution context passed to every Crucible operator call.

    All mutable state accumulated during a pipeline run (justifications,
    decomposed fragments, TTF metrics) lives here, keeping operators pure.
    """

    context_id: str = field(default_factory=lambda: f"ctx-{str(uuid.uuid4())[:8]}")
    hypergraph: Optional["RepresentationHypergraph"] = None
    registry: Optional["AtlasRegistry"] = None
    adversary: Optional["AdversaryEngine"] = None
    ttf: Optional["TTFInstrumentation"] = None

    # Accumulated during execution
    justifications: list["Justification"] = field(default_factory=list)
    decomposed: list[Any] = field(default_factory=list)
    metadata: dict[str, Any] = field(default_factory=dict)

    def record_justification(self, j: "Justification") -> None:
        self.justifications.append(j)

    def justification_summary(self) -> list[dict]:
        return [j.to_dict() for j in self.justifications]

    def summary(self) -> dict:
        return {
            "context_id": self.context_id,
            "justifications": len(self.justifications),
            "decomposed_fragments": len(self.decomposed),
            "hypergraph_nodes": (
                self.hypergraph.node_count() if self.hypergraph else 0
            ),
            "hypergraph_edges": (
                self.hypergraph.edge_count() if self.hypergraph else 0
            ),
            "ttf_metrics": self.ttf.summary() if self.ttf else {},
        }
