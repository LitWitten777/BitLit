"""
src/melchizidek/conductor.py
Conductor — Pipeline Orchestrator for Melchizidek.

Sequences Logos → Hermes → Operator calls for a complete IR processing run.
Replaces orchestrator.py.

Atlas registration: chart_id = "melchizidek-conductor-v1"
Melchizidek level: L3
Author: EngA
Version: 0.1.0
Provenance: {
  source: manual_construction_v0.1,
  derivation: Sprint 1 Conductor skeleton per melchizidek_refactor.md §7,
  confidence: 0.85, validation_status: validated
}
"""
from __future__ import annotations

import logging
from typing import Any, Optional

from ..crucible.context import CrucibleContext
from ..hypergraph import RepresentationObject
from .atlas_adapter import AtlasAdapter
from .hermes import Hermes
from .logos import Logos

logger = logging.getLogger(__name__)

CONDUCTOR_ATLAS_METADATA = {
    "chart_id": "melchizidek-conductor-v1",
    "chart_name": "Melchizidek Conductor",
    "chart_version": "0.1.0",
    "description": "Sequences Logos → Hermes → Operator pipeline for IR processing.",
    "representation_level": 3,
    "melchizidek_level": 3,
    "capability_tags": ["pipeline", "orchestration", "conductor", "melchizidek"],
    "provenance": {
        "source": "manual_construction_v0.1",
        "derivation": "Sprint 1 Conductor skeleton",
        "evidence": [],
        "confidence": 0.85,
        "validation_status": "validated",
        "version": "0.1.0",
        "timestamp": "2026-07-01T07:00:00Z",
        "author": "EngA",
    },
}

# All Melchizidek modules registered as Atlas objects
MELCHIZIDEK_ATLAS_OBJECTS = [
    "melchizidek-hermes-v1",
    "melchizidek-logos-v1",
    "melchizidek-atlas-adapter-v1",
    "melchizidek-conductor-v1",
]


class Conductor:
    """
    Orchestrates a full Melchizidek pipeline pass on a RepresentationObject.

    Pipeline:
      1. Logos.interpret(ir_object)  → (level, chart_ids)
      2. AtlasAdapter.charts_for_ir  → candidate charts
      3. Hermes.route(ir_object)     → operator
      4. operator(ir_object, ctx)    → result RepresentationObject

    Usage:
        ctx = CrucibleContext(context_id="ctx-001", hypergraph=graph)
        conductor = Conductor(context=ctx)
        result = conductor.process(ir_object)
    """

    def __init__(
        self,
        context: CrucibleContext,
        logos: Optional[Logos] = None,
        hermes: Optional[Hermes] = None,
        adapter: Optional[AtlasAdapter] = None,
    ) -> None:
        self.context = context
        self._logos  = logos  or Logos(registry=context.registry)
        self._hermes = hermes or Hermes(registry=context.registry)
        self._adapter = adapter or AtlasAdapter(
            registry=context.registry
        ) if context.registry else None

    def process(
        self,
        ir_object: RepresentationObject,
        **operator_kwargs: Any,
    ) -> RepresentationObject:
        """
        Run the full Melchizidek pipeline on a single IR object.

        Returns the output RepresentationObject from the selected operator.
        """
        # Step 1: Logos — interpret level and chart recommendations
        level, chart_ids = self._logos.interpret(ir_object)
        logger.info(
            "Conductor.process: node=%s level=%d charts=%s",
            ir_object.node_id, level, chart_ids,
        )

        # Step 2: Atlas adapter — resolve best chart
        best_chart_id = chart_ids[0] if chart_ids else None

        # Step 3: Hermes — select operator
        operator = self._hermes.route(ir_object)
        logger.info(
            "Conductor.process: selected operator=%s for node=%s",
            operator.operator_name, ir_object.node_id,
        )

        # Step 4: Execute operator
        result = operator(
            ir_object,
            context=self.context,
            chart_id=best_chart_id,
            **operator_kwargs,
        )

        logger.info(
            "Conductor.process: produced node=%s (type=%s, conf=%.3f)",
            result.node_id,
            result.object_type,
            result.provenance.get("confidence", 0),
        )
        return result

    def process_batch(
        self,
        ir_objects: list[RepresentationObject],
        **operator_kwargs: Any,
    ) -> list[RepresentationObject]:
        """Process a list of IR objects sequentially."""
        return [self.process(obj, **operator_kwargs) for obj in ir_objects]

    def pipeline_summary(self) -> dict[str, Any]:
        return {
            "conductor_version": "0.1.0",
            "context_summary": self.context.summary(),
            "logos_level_rules": "see src/melchizidek/logos.py LEVEL_INFERENCE",
            "hermes_routing_table": "see src/melchizidek/hermes.py DEFAULT_ROUTING_TABLE",
            "registered_atlas_objects": MELCHIZIDEK_ATLAS_OBJECTS,
        }
