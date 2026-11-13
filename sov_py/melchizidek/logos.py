"""
src/melchizidek/logos.py
Logos — Semantic Interpreter for the Melchizidek orchestration layer.

Assigns a representation level (L0–L5) to an IR object and recommends
Atlas charts. Replaces sefirot_router.py level assignment logic.

Identity Derivation: produces a stable logos_id from (ir_id, object_type,
representation_level) without cryptographic operations.

Atlas registration: chart_id = "melchizidek-logos-v1"
Melchizidek level: L4
Author: EngA
Version: 0.1.0
"""
from __future__ import annotations

import hashlib
import logging
from typing import Any, Optional

from ..hypergraph import RepresentationObject

logger = logging.getLogger(__name__)

LOGOS_ATLAS_METADATA = {
    "chart_id": "melchizidek-logos-v1",
    "chart_name": "Melchizidek Logos Interpreter",
    "chart_version": "0.1.0",
    "description": "Assigns L0–L5 level and chart recommendations to IR objects.",
    "representation_level": 4,
    "melchizidek_level": 4,
    "capability_tags": ["interpretation", "level_assignment", "melchizidek"],
    "provenance": {
        "source": "manual_construction_v0.1",
        "derivation": "Sprint 1 Logos skeleton",
        "evidence": [],
        "confidence": 0.85,
        "validation_status": "validated",
        "version": "0.1.0",
        "timestamp": "2026-07-01T07:00:00Z",
        "author": "EngA",
    },
}

# Level inference rules: (object_type, language_tag_prefix) → level
LEVEL_INFERENCE: list[tuple[tuple[str, ...], Optional[str], int]] = [
    # (object_types, language_prefix, level)
    (("token_sequence",),           None,    1),
    (("sentence",),                 "he",    2),
    (("sentence",),                 None,    1),
    (("code_snippet", "ast_node"),  None,    3),
    (("semantic_graph",),           None,    3),
    (("morphism", "hyperedge"),     None,    4),
    (("category_definition",),      None,    4),
    (("counterexample",),           None,    1),
    (("metric_result",),            None,    3),
    (("hypothesis",),               None,    4),
    (("atlas_chart",),              None,    5),
    (("corpus_fragment",),          None,    1),
]

# Chart recommendations by level
CHART_RECOMMENDATIONS: dict[int, list[str]] = {
    0: [],
    1: ["chart-sample-lang-v1"],
    2: ["chart-hebrew-morphology-v1"],
    3: ["chart-sample-lang-v1", "chart-category-theory-v1"],
    4: ["chart-category-theory-v1", "chart-hopf-s7-v1"],
    5: ["chart-e8-cartan-v1", "chart-category-theory-v1"],
}


def derive_logos_id(ir_id: str, object_type: str, level: int) -> str:
    """
    Identity Derivation: produce a stable, deterministic logos_id.
    Uses SHA-256 truncated to 16 hex chars — not for security, only for
    stable identity mapping. No secret keys involved.
    """
    payload = f"{ir_id}:{object_type}:{level}"
    return "logos-" + hashlib.sha256(payload.encode()).hexdigest()[:16]


class Logos:
    """
    Semantic interpreter: infers representation level and chart recommendations
    for a given RepresentationObject.
    """

    def __init__(self, registry: Optional[Any] = None) -> None:
        self.registry = registry

    def interpret(
        self, ir_object: RepresentationObject
    ) -> tuple[int, list[str]]:
        """
        Return (level, chart_ids) for the given IR object.

        Level comes from IR's explicit representation_level field first;
        falls back to inference rules if level is -1 or missing.
        """
        level = ir_object.representation_level
        if level < 0:
            level = self._infer_level(ir_object)

        chart_ids = CHART_RECOMMENDATIONS.get(level, [])

        # Filter to validated charts if registry is available
        if self.registry:
            valid_ids = {c.chart_id for c in self.registry.validated_charts()}
            chart_ids = [cid for cid in chart_ids if cid in valid_ids]

        logos_id = derive_logos_id(
            ir_object.ir_id, ir_object.object_type, level
        )
        logger.debug(
            "Logos: %s → level=%d, logos_id=%s, charts=%s",
            ir_object.node_id, level, logos_id, chart_ids,
        )
        return level, chart_ids

    def _infer_level(self, ir_object: RepresentationObject) -> int:
        obj_type = ir_object.object_type
        lang = ir_object.ir.get("language_tag", "")

        for obj_types, lang_prefix, lvl in LEVEL_INFERENCE:
            type_match = obj_type in obj_types
            lang_match = lang_prefix is None or lang.startswith(lang_prefix)
            if type_match and lang_match:
                return lvl

        # Default to L1 if no rule matches
        logger.warning(
            "Logos: no level rule for object_type=%r lang=%r; defaulting to L1",
            obj_type, lang,
        )
        return 1

    def logos_id(self, ir_object: RepresentationObject) -> str:
        level, _ = self.interpret(ir_object)
        return derive_logos_id(ir_object.ir_id, ir_object.object_type, level)
