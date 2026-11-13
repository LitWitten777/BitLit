"""
src/melchizidek/atlas_adapter.py
AtlasAdapter — Registry bridge for Melchizidek.

Translates Melchizidek routing requests into AtlasRegistry API calls.

Atlas registration: chart_id = "melchizidek-atlas-adapter-v1"
Melchizidek level: L2
Author: EngB
Version: 0.1.0
"""
from __future__ import annotations

import logging
from typing import Any, Optional

from ..atlas.registry import AtlasChart, AtlasRegistry, get_registry
from ..hypergraph import RepresentationObject

logger = logging.getLogger(__name__)

ATLAS_ADAPTER_METADATA = {
    "chart_id": "melchizidek-atlas-adapter-v1",
    "chart_name": "Melchizidek Atlas Adapter",
    "chart_version": "0.1.0",
    "description": "Bridges Melchizidek orchestration calls to AtlasRegistry queries.",
    "representation_level": 2,
    "melchizidek_level": 2,
    "capability_tags": ["atlas", "adapter", "bridge", "melchizidek"],
    "provenance": {
        "source": "manual_construction_v0.1",
        "derivation": "Sprint 1 AtlasAdapter skeleton",
        "evidence": [],
        "confidence": 0.85,
        "validation_status": "validated",
        "version": "0.1.0",
        "timestamp": "2026-07-01T07:00:00Z",
        "author": "EngB",
    },
}


class AtlasAdapter:
    """
    Wraps AtlasRegistry with Melchizidek-specific query helpers.

    Usage:
        adapter = AtlasAdapter()
        charts = adapter.charts_for_ir(ir_object)
        chart  = adapter.best_chart_for_ir(ir_object)
    """

    def __init__(self, registry: Optional[AtlasRegistry] = None) -> None:
        self._registry = registry or get_registry()

    # ------------------------------------------------------------------
    # Level-based queries
    # ------------------------------------------------------------------

    def charts_for_level(self, level: int) -> list[AtlasChart]:
        """Return all validated charts at the given representation level."""
        return [
            c for c in self._registry.validated_charts()
            if c.representation_level == level
        ]

    def charts_for_level_range(self, min_level: int, max_level: int) -> list[AtlasChart]:
        return [
            c for c in self._registry.validated_charts()
            if min_level <= c.representation_level <= max_level
        ]

    # ------------------------------------------------------------------
    # IR-based queries
    # ------------------------------------------------------------------

    def charts_for_ir(self, ir_object: RepresentationObject) -> list[AtlasChart]:
        """Return charts whose representation_level matches or is adjacent to the IR."""
        level = ir_object.representation_level
        return self.charts_for_level_range(max(0, level - 1), min(5, level + 1))

    def best_chart_for_ir(self, ir_object: RepresentationObject) -> Optional[AtlasChart]:
        """Return the single best chart (highest confidence × coverage) for an IR."""
        candidates = self.charts_for_ir(ir_object)
        if not candidates:
            return None
        return max(
            candidates,
            key=lambda c: c.provenance.confidence * c.metrics.coverage,
        )

    def charts_by_tags(self, *tags: str) -> list[AtlasChart]:
        return self._registry.by_tag(*tags)

    # ------------------------------------------------------------------
    # Dependency resolution
    # ------------------------------------------------------------------

    def resolve_dependencies(self, chart_id: str) -> list[AtlasChart]:
        """Return the dependency chain for a chart (topological order, deps first)."""
        resolved: list[str] = []
        visited: set[str] = set()

        def dfs(cid: str) -> None:
            if cid in visited:
                return
            visited.add(cid)
            try:
                chart = self._registry.get(cid)
                for dep in chart.dependencies:
                    dfs(dep)
                resolved.append(cid)
            except KeyError:
                logger.warning("AtlasAdapter: dependency %r not found in registry", cid)

        dfs(chart_id)
        return [self._registry.get(cid) for cid in resolved if cid in {
            c.chart_id for c in self._registry.all_charts()
        }]

    # ------------------------------------------------------------------
    # Registry pass-through
    # ------------------------------------------------------------------

    def get_chart(self, chart_id: str) -> AtlasChart:
        return self._registry.get(chart_id)

    def summary(self) -> dict[str, Any]:
        return self._registry.summary()
