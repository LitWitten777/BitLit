"""
src/metrics/policy.py
Decision Policy — selects an action or representation based on metric scores.

Replaces any "admin vector" usage with a transparent, auditable scoring policy.
All policy decisions are recorded with provenance.

Author: EngB
Version: 0.1.0
Provenance: {
  source: manual_construction_v0.1,
  derivation: Sprint 1 policy skeleton replacing admin vector usage,
  confidence: 0.85, validation_status: validated
}
"""
from __future__ import annotations

from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any, Callable, Optional

from ..hypergraph import RepresentationObject
from .base import BaseMetric, MetricResult


# ---------------------------------------------------------------------------
# Policy Rule
# ---------------------------------------------------------------------------

@dataclass
class PolicyRule:
    """
    A single rule: if metric.score satisfies predicate, recommend action.

    name      : Human-readable label.
    metric    : Which metric to evaluate.
    predicate : (score: float) -> bool
    action    : String label for the recommended action.
    priority  : Higher = evaluated first (rules are evaluated in priority order).
    """
    name: str
    metric: BaseMetric
    predicate: Callable[[float], bool]
    action: str
    priority: int = 0
    description: str = ""


# ---------------------------------------------------------------------------
# Policy Decision
# ---------------------------------------------------------------------------

@dataclass
class PolicyDecision:
    """Result of a policy evaluation."""
    action: str
    rule_name: str
    score: float
    metric_name: str
    node_ids: list[str]
    reasoning: str
    provenance: dict[str, Any] = field(default_factory=dict)


# ---------------------------------------------------------------------------
# Decision Policy
# ---------------------------------------------------------------------------

class DecisionPolicy:
    """
    Evaluates a ranked list of PolicyRules against a pair of RepresentationObjects
    and returns the first matching PolicyDecision.

    This replaces any hardcoded "admin vector" threshold with an explicit,
    auditable rule set. Metrics are computed lazily (only until first match).

    Example usage:
        from src.metrics.cosine import CosineSimilarity
        from src.metrics.policy import DecisionPolicy, PolicyRule

        policy = DecisionPolicy(rules=[
            PolicyRule(
                name="high_similarity",
                metric=CosineSimilarity(),
                predicate=lambda s: s >= 0.85,
                action="accept",
                priority=10,
            ),
            PolicyRule(
                name="low_similarity",
                metric=CosineSimilarity(),
                predicate=lambda s: s < 0.4,
                action="reject",
                priority=5,
            ),
        ])
        decision = policy.evaluate(node_a, node_b, fallback_action="review")
    """

    def __init__(
        self,
        rules: Optional[list[PolicyRule]] = None,
        policy_name: str = "default_policy",
        policy_version: str = "0.1.0",
    ) -> None:
        self._rules = sorted(rules or [], key=lambda r: -r.priority)
        self.policy_name = policy_name
        self.policy_version = policy_version

    def add_rule(self, rule: PolicyRule) -> None:
        self._rules.append(rule)
        self._rules.sort(key=lambda r: -r.priority)

    def evaluate(
        self,
        a: RepresentationObject,
        b: RepresentationObject,
        fallback_action: str = "review",
    ) -> PolicyDecision:
        """
        Evaluate rules in priority order.
        Returns the first matching decision, or a fallback decision.
        """
        for rule in self._rules:
            result: MetricResult = rule.metric(a, b)
            if rule.predicate(result.score):
                prov = {
                    "source": f"{self.policy_name}_v{self.policy_version}",
                    "derivation": (
                        f"Rule '{rule.name}' matched: "
                        f"{rule.metric.metric_name}={result.score:.4f} "
                        f"→ action='{rule.action}'"
                    ),
                    "evidence": [a.node_id, b.node_id],
                    "confidence": result.provenance.get("confidence", 0.5),
                    "validation_status": "unvalidated",
                    "version": self.policy_version,
                    "timestamp": datetime.now(timezone.utc).isoformat(),
                    "author": "automated",
                }
                return PolicyDecision(
                    action=rule.action,
                    rule_name=rule.name,
                    score=result.score,
                    metric_name=rule.metric.metric_name,
                    node_ids=[a.node_id, b.node_id],
                    reasoning=(
                        f"{rule.description or rule.name}: "
                        f"{rule.metric.metric_name}={result.score:.4f}"
                    ),
                    provenance=prov,
                )

        # Fallback
        return PolicyDecision(
            action=fallback_action,
            rule_name="__fallback__",
            score=0.0,
            metric_name="none",
            node_ids=[a.node_id, b.node_id],
            reasoning=f"No rule matched; using fallback action '{fallback_action}'",
            provenance={
                "source": f"{self.policy_name}_v{self.policy_version}",
                "derivation": "Fallback: no rules matched",
                "evidence": [a.node_id, b.node_id],
                "confidence": 0.0,
                "validation_status": "unvalidated",
                "version": self.policy_version,
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "author": "automated",
            },
        )

    def rule_names(self) -> list[str]:
        return [r.name for r in self._rules]


# ---------------------------------------------------------------------------
# Pre-built example policy (replaces admin vector)
# ---------------------------------------------------------------------------

def make_default_representation_policy() -> DecisionPolicy:
    """
    Returns a default policy that decides whether to accept, review, or
    reject a pair of representation objects based on cosine similarity.

    Replaces any hardcoded admin-vector threshold.
    """
    from .cosine import CosineSimilarity

    sim = CosineSimilarity()
    return DecisionPolicy(
        policy_name="representation_acceptance_policy",
        rules=[
            PolicyRule(
                name="high_similarity_accept",
                metric=sim,
                predicate=lambda s: s >= 0.85,
                action="accept",
                priority=10,
                description="Cosine similarity ≥ 0.85: accept as equivalent representations",
            ),
            PolicyRule(
                name="medium_similarity_review",
                metric=sim,
                predicate=lambda s: 0.4 <= s < 0.85,
                action="review",
                priority=5,
                description="Cosine similarity in [0.4, 0.85): send for human review",
            ),
            PolicyRule(
                name="low_similarity_reject",
                metric=sim,
                predicate=lambda s: s < 0.4,
                action="reject",
                priority=1,
                description="Cosine similarity < 0.4: reject as incompatible representations",
            ),
        ],
    )
