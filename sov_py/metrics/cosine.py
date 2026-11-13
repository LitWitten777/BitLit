"""
src/metrics/cosine.py
Cosine similarity metric between IR object feature vectors.

Author: EngB
Version: 0.1.0
"""
from __future__ import annotations

import math
from typing import Any

from ..hypergraph import RepresentationObject
from .base import BaseMetric


def _extract_vector(obj: RepresentationObject) -> list[float]:
    """
    Extract a numeric feature vector from an IR object.

    Priority:
      1. obj.ir["metrics"] dict values (sorted by key for determinism)
      2. node attribute "vector" if present
      3. Fallback: [confidence, representation_level / 5.0]
    """
    # Option 1: pre-computed metrics
    metrics = obj.ir.get("metrics")
    if metrics and isinstance(metrics, dict):
        vec = [float(v) for v in sorted(metrics.values()) if isinstance(v, (int, float))]
        if vec:
            return vec

    # Option 2: explicit vector attribute
    vec_attr = obj.attributes.get("vector")
    if vec_attr and isinstance(vec_attr, list):
        return [float(x) for x in vec_attr]

    # Option 3: minimal fallback
    conf = float(obj.provenance.get("confidence", 0.5))
    lvl = float(obj.ir.get("representation_level", 0)) / 5.0
    return [conf, lvl]


def _cosine(a: list[float], b: list[float]) -> float:
    """Compute cosine similarity; pad shorter vector with zeros."""
    n = max(len(a), len(b))
    a = a + [0.0] * (n - len(a))
    b = b + [0.0] * (n - len(b))
    dot = sum(x * y for x, y in zip(a, b))
    mag_a = math.sqrt(sum(x * x for x in a))
    mag_b = math.sqrt(sum(y * y for y in b))
    if mag_a == 0.0 or mag_b == 0.0:
        return 0.0
    return dot / (mag_a * mag_b)


class CosineSimilarity(BaseMetric):
    """
    Cosine similarity between the feature vectors of two RepresentationObjects.
    Result is in [-1, 1]; clipped to [0, 1] for use as a confidence-compatible score.
    """

    metric_name = "cosine_similarity"
    bounded = True

    def _compute(
        self,
        a: RepresentationObject,
        b: RepresentationObject,
        **kwargs: Any,
    ) -> tuple[float, dict[str, Any]]:
        vec_a = _extract_vector(a)
        vec_b = _extract_vector(b)
        raw = _cosine(vec_a, vec_b)
        score = max(0.0, raw)   # clip to [0,1]
        return score, {
            "raw_cosine": round(raw, 6),
            "vec_a_len": len(vec_a),
            "vec_b_len": len(vec_b),
            "vec_a": vec_a,
            "vec_b": vec_b,
        }
