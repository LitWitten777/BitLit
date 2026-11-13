"""
src/crucible/verify.py
Standalone verification utilities — confidence aggregation, threshold
policies, and batch verification helpers used by the Verify operator.

Author: EngA
Version: 0.1.0
"""
from __future__ import annotations

from typing import Callable, Optional

from ..hypergraph import RepresentationObject


# ---------------------------------------------------------------------------
# Confidence aggregation strategies
# ---------------------------------------------------------------------------

def aggregate_mean(nodes: list[RepresentationObject]) -> float:
    if not nodes:
        return 0.0
    return sum(n.provenance.get("confidence", 0.5) for n in nodes) / len(nodes)


def aggregate_min(nodes: list[RepresentationObject]) -> float:
    if not nodes:
        return 0.0
    return min(n.provenance.get("confidence", 0.5) for n in nodes)


def aggregate_product(nodes: list[RepresentationObject]) -> float:
    result = 1.0
    for n in nodes:
        result *= n.provenance.get("confidence", 0.5)
    return result


AGGREGATORS: dict[str, Callable[[list[RepresentationObject]], float]] = {
    "mean": aggregate_mean,
    "min": aggregate_min,
    "product": aggregate_product,
}


# ---------------------------------------------------------------------------
# Verification decision
# ---------------------------------------------------------------------------

def decide_status(
    confidence: float,
    threshold: float = 0.7,
    counterexample_found: bool = False,
) -> str:
    """
    Map confidence + counterexample flag to a validation_status string.

    Returns one of: 'validated', 'contested', 'refuted', 'pending'
    """
    if counterexample_found:
        return "refuted"
    if confidence >= threshold:
        return "validated"
    if confidence >= threshold * 0.5:
        return "contested"
    return "pending"


# ---------------------------------------------------------------------------
# Batch verification
# ---------------------------------------------------------------------------

def batch_verify(
    hypotheses: list[RepresentationObject],
    evidence_map: dict[str, list[RepresentationObject]],
    threshold: float = 0.7,
    aggregation: str = "mean",
) -> list[dict]:
    """
    Verify a list of hypothesis nodes against evidence.

    Parameters
    ----------
    hypotheses   : List of hypothesis IR nodes.
    evidence_map : Maps hypothesis.node_id → list of evidence nodes.
    threshold    : Confidence threshold for "validated".
    aggregation  : "mean" | "min" | "product".

    Returns
    -------
    List of result dicts with keys: node_id, confidence, status.
    """
    agg_fn = AGGREGATORS.get(aggregation, aggregate_mean)
    results = []
    for hyp in hypotheses:
        evidence = evidence_map.get(hyp.node_id, [])
        conf = agg_fn(evidence) if evidence else hyp.provenance.get("confidence", 0.5)
        status = decide_status(conf, threshold)
        results.append({
            "node_id": hyp.node_id,
            "confidence": round(conf, 4),
            "status": status,
            "evidence_count": len(evidence),
        })
    return results
