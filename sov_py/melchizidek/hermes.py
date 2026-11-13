"""
src/melchizidek/hermes.py
Hermes — Message Router for the Melchizidek orchestration layer.

Routes IR objects to the appropriate Crucible operator based on
representation_level and object_type.

Atlas registration: chart_id = "melchizidek-hermes-v1"
Melchizidek level: L3
Author: EngA
Version: 0.1.0
Provenance: {
  source: manual_construction_v0.1,
  derivation: Sprint 1 Hermes skeleton per melchizidek_refactor.md §4,
  confidence: 0.85, validation_status: validated
}
"""
from __future__ import annotations

import logging
from typing import Any, Optional, Type

from ..crucible.operators import (
    Associate, Compose, CrucibleOperator, Decompose,
    Generate, Integrate, Reflect, Verify,
)
from ..hypergraph import RepresentationObject

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Atlas metadata for this module (registered as an Atlas object)
# ---------------------------------------------------------------------------

HERMES_ATLAS_METADATA = {
    "chart_id": "melchizidek-hermes-v1",
    "chart_name": "Melchizidek Hermes Router",
    "chart_version": "0.1.0",
    "description": "Routes IR objects to Crucible operators based on representation level.",
    "representation_level": 3,
    "melchizidek_level": 3,
    "capability_tags": ["routing", "orchestration", "melchizidek"],
    "provenance": {
        "source": "manual_construction_v0.1",
        "derivation": "Sprint 1 Hermes skeleton",
        "evidence": [],
        "confidence": 0.85,
        "validation_status": "validated",
        "version": "0.1.0",
        "timestamp": "2026-07-01T07:00:00Z",
        "author": "EngA",
    },
}

# ---------------------------------------------------------------------------
# Routing table: (level_min, level_max, object_type_or_None) → operator_class
# ---------------------------------------------------------------------------

RoutingKey = tuple[int, int, Optional[str]]

DEFAULT_ROUTING_TABLE: list[tuple[RoutingKey, Type[CrucibleOperator]]] = [
    # Raw signal and lexical → Generate (parse from raw)
    ((0, 1, None), Generate),
    # Morphological → Generate then Associate (handled in two steps by Conductor)
    ((2, 2, None), Generate),
    # Syntactic/Semantic → Associate + Reflect (Conductor chains these)
    ((3, 3, "semantic_graph"), Reflect),
    ((3, 3, None), Associate),
    # Categorical → Compose
    ((4, 4, None), Compose),
    # Abstract → Verify
    ((5, 5, None), Verify),
    # Counterexample → Verify
    ((0, 5, "counterexample"), Verify),
    # Metric result → Integrate
    ((0, 5, "metric_result"), Integrate),
]


class Hermes:
    """
    Routes a RepresentationObject to the appropriate CrucibleOperator.

    Rules are evaluated in order; first match wins.
    Custom rules can be prepended via hermes.add_rule().
    """

    def __init__(
        self,
        routing_table: Optional[list] = None,
        registry: Optional[Any] = None,
    ) -> None:
        self._routing_table: list[tuple[RoutingKey, Type[CrucibleOperator]]] = (
            list(routing_table) if routing_table is not None
            else list(DEFAULT_ROUTING_TABLE)
        )
        self.registry = registry

    def add_rule(
        self,
        level_min: int,
        level_max: int,
        operator_class: Type[CrucibleOperator],
        object_type: Optional[str] = None,
        prepend: bool = True,
    ) -> None:
        """Add a routing rule. prepend=True means it takes priority over defaults."""
        rule = ((level_min, level_max, object_type), operator_class)
        if prepend:
            self._routing_table.insert(0, rule)
        else:
            self._routing_table.append(rule)

    def route(self, ir_object: RepresentationObject) -> CrucibleOperator:
        """
        Return the appropriate CrucibleOperator instance for ir_object.
        Falls back to Generate if no rule matches.
        """
        level = ir_object.representation_level
        obj_type = ir_object.object_type

        for (level_min, level_max, rule_type), op_class in self._routing_table:
            level_match = level_min <= level <= level_max
            type_match = rule_type is None or rule_type == obj_type
            if level_match and type_match:
                logger.debug(
                    "Hermes: routing level=%d type=%s → %s",
                    level, obj_type, op_class.__name__,
                )
                return op_class()

        logger.warning(
            "Hermes: no rule matched level=%d type=%s; defaulting to Generate",
            level, obj_type,
        )
        return Generate()

    def route_name(self, ir_object: RepresentationObject) -> str:
        """Return the operator name that would be selected (for logging/testing)."""
        return self.route(ir_object).operator_name
