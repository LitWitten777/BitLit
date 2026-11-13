"""
src/metrics/base.py
Base metric interface for the Crucible Atlas pipeline.

All metric implementations inherit from BaseMetric and implement compute().
Metrics receive RepresentationObject pairs (or lists) and return a float in [0,1]
(or an unbounded float for distance metrics) plus a provenance dict.

Author: EngB
Version: 0.1.0
Provenance: {
  source: manual_construction_v0.1,
  derivation: Sprint 1 metrics framework skeleton,
  confidence: 0.9, validation_status: validated
}
"""
from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any, Optional

from ..hypergraph import RepresentationObject


# ---------------------------------------------------------------------------
# Result container
# ---------------------------------------------------------------------------

@dataclass
class MetricResult:
    """
    Encapsulates the result of a metric computation.

    score      : Primary numeric result.
    metric_name: Name of the metric that produced this result.
    bounded    : True if score is in [0,1].
    provenance : Standard Crucible provenance block.
    details    : Optional metric-specific breakdown.
    """
    score: float
    metric_name: str
    bounded: bool = True
    provenance: dict[str, Any] = field(default_factory=dict)
    details: dict[str, Any] = field(default_factory=dict)

    def to_ir_metrics(self) -> dict[str, float]:
        """Compact form suitable for IR 'metrics' field."""
        return {self.metric_name: round(self.score, 6)}

    def to_dict(self) -> dict[str, Any]:
        return {
            "metric_name": self.metric_name,
            "score": round(self.score, 6),
            "bounded": self.bounded,
            "provenance": self.provenance,
            "details": self.details,
        }


# ---------------------------------------------------------------------------
# Base Metric
# ---------------------------------------------------------------------------

class BaseMetric(ABC):
    """
    Abstract base for all Crucible metrics.

    Subclasses implement _compute() and set metric_name / bounded.
    The base class handles provenance construction.
    """

    metric_name: str = "base_metric"
    metric_version: str = "0.1.0"
    bounded: bool = True               # True = result in [0,1]

    def __call__(
        self,
        a: RepresentationObject,
        b: RepresentationObject,
        **kwargs: Any,
    ) -> MetricResult:
        score, details = self._compute(a, b, **kwargs)
        prov = self._make_provenance(a, b, score)
        return MetricResult(
            score=score,
            metric_name=self.metric_name,
            bounded=self.bounded,
            provenance=prov,
            details=details,
        )

    @abstractmethod
    def _compute(
        self,
        a: RepresentationObject,
        b: RepresentationObject,
        **kwargs: Any,
    ) -> tuple[float, dict[str, Any]]:
        """
        Compute the metric between a and b.
        Returns (score, details_dict).
        """
        ...

    def _make_provenance(
        self,
        a: RepresentationObject,
        b: RepresentationObject,
        score: float,
    ) -> dict[str, Any]:
        return {
            "source": f"{self.metric_name}_v{self.metric_version}",
            "derivation": (
                f"{self.metric_name} between nodes "
                f"{a.node_id!r} and {b.node_id!r}; score={score:.4f}"
            ),
            "evidence": [a.node_id, b.node_id],
            "confidence": min(
                a.provenance.get("confidence", 0.5),
                b.provenance.get("confidence", 0.5),
            ),
            "validation_status": "unvalidated",
            "version": self.metric_version,
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "author": "automated",
        }


# ---------------------------------------------------------------------------
# Batch metric helper
# ---------------------------------------------------------------------------

def pairwise_metric(
    metric: BaseMetric,
    nodes: list[RepresentationObject],
) -> list[MetricResult]:
    """Compute metric for all consecutive pairs in nodes."""
    results = []
    for i in range(len(nodes) - 1):
        results.append(metric(nodes[i], nodes[i + 1]))
    return results


def all_pairs_metric(
    metric: BaseMetric,
    nodes: list[RepresentationObject],
) -> dict[tuple[str, str], MetricResult]:
    """Compute metric for all (i, j) pairs, i < j."""
    results: dict[tuple[str, str], MetricResult] = {}
    for i, a in enumerate(nodes):
        for j, b in enumerate(nodes):
            if i < j:
                results[(a.node_id, b.node_id)] = metric(a, b)
    return results
