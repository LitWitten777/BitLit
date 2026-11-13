"""
src/crucible/adversary.py
Adversary / Counterexample Engine.

Generates simple counterexamples for numeric and structural hypotheses
and feeds the Verify operator.

Author: EngB
Version: 0.1.0
Provenance: {
  source: manual_construction_v0.1,
  derivation: Sprint 1 adversary engine skeleton,
  confidence: 0.8, validation_status: validated
}

Design
------
- AdversaryEngine wraps a set of CounterexampleStrategy objects.
- Each strategy targets a specific hypothesis type (numeric, structural, categorical).
- try_counterexample() runs all applicable strategies and returns the first
  counterexample found (or None if the hypothesis survives all attacks).
- New strategies are registered via AdversaryEngine.register_strategy().
"""
from __future__ import annotations

import uuid
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any, Optional

from ..hypergraph import RepresentationObject, make_provenance


# ---------------------------------------------------------------------------
# Counterexample data class
# ---------------------------------------------------------------------------

@dataclass
class Counterexample:
    ce_id: str
    strategy_name: str
    hypothesis_id: str
    witness: Any                    # The concrete refuting instance
    description: str
    confidence: float               # How confident we are this is a valid CE
    provenance: dict[str, Any] = field(default_factory=dict)

    def to_ir(self, context_id: str) -> dict[str, Any]:
        """Convert this counterexample to a Representation Kernel IR dict."""
        return {
            "ir_id": self.ce_id,
            "ir_version": "0.1.0",
            "object_type": "counterexample",
            "representation_level": 1,
            "language_tag": "math",
            "content": {
                "payload": {
                    "strategy": self.strategy_name,
                    "hypothesis_id": self.hypothesis_id,
                    "witness": self.witness,
                    "description": self.description,
                },
                "surface_form": self.description,
            },
            "provenance": self.provenance or make_provenance(
                source=f"adversary_{self.strategy_name}",
                derivation=f"Counterexample to hypothesis {self.hypothesis_id}",
                confidence=self.confidence,
                validation_status="unvalidated",
            ),
            "context_id": context_id,
        }


# ---------------------------------------------------------------------------
# Strategy base class
# ---------------------------------------------------------------------------

class CounterexampleStrategy(ABC):
    """Abstract base for counterexample strategies."""

    name: str = "base"

    @abstractmethod
    def applies_to(self, hypothesis: RepresentationObject) -> bool:
        """Return True if this strategy can attack the given hypothesis."""
        ...

    @abstractmethod
    def generate(self, hypothesis: RepresentationObject) -> Optional[Counterexample]:
        """
        Attempt to generate a counterexample.
        Return None if no counterexample found (hypothesis survives this strategy).
        """
        ...


# ---------------------------------------------------------------------------
# Numeric counterexample strategies
# ---------------------------------------------------------------------------

class NumericBoundaryStrategy(CounterexampleStrategy):
    """
    Attacks hypotheses that assert a numeric value is within [lower, upper].
    Generates a witness just outside the claimed bounds.
    """
    name = "numeric_boundary"

    def applies_to(self, hypothesis: RepresentationObject) -> bool:
        payload = hypothesis.ir.get("content", {}).get("payload", {})
        return (
            "numeric_claim" in payload
            and "lower_bound" in payload
            and "upper_bound" in payload
        )

    def generate(self, hypothesis: RepresentationObject) -> Optional[Counterexample]:
        payload = hypothesis.ir.get("content", {}).get("payload", {})
        lower = payload.get("lower_bound")
        upper = payload.get("upper_bound")
        value = payload.get("numeric_claim")

        if lower is None or upper is None or value is None:
            return None

        # Check if the claim is actually out of bounds
        if value < lower:
            witness = value
            desc = f"Value {value} < lower bound {lower}"
        elif value > upper:
            witness = value
            desc = f"Value {value} > upper bound {upper}"
        else:
            # Construct a witness outside bounds (adversarial injection)
            witness = upper + 1.0
            desc = f"Witness {witness} exceeds upper bound {upper}"

        return Counterexample(
            ce_id=str(uuid.uuid4()),
            strategy_name=self.name,
            hypothesis_id=hypothesis.node_id,
            witness=witness,
            description=desc,
            confidence=0.9,
            provenance=make_provenance(
                source=f"adversary_{self.name}",
                derivation=desc,
                confidence=0.9,
                evidence=[hypothesis.node_id],
            ),
        )


class NumericMonotonicityStrategy(CounterexampleStrategy):
    """
    Attacks hypotheses that claim a function is monotonically increasing.
    Generates a pair (x, y) where x < y but f(x) > f(y).
    """
    name = "numeric_monotonicity"

    def applies_to(self, hypothesis: RepresentationObject) -> bool:
        payload = hypothesis.ir.get("content", {}).get("payload", {})
        return payload.get("claim_type") == "monotonic_increasing"

    def generate(self, hypothesis: RepresentationObject) -> Optional[Counterexample]:
        payload = hypothesis.ir.get("content", {}).get("payload", {})
        sample_values = payload.get("sample_values", [])

        # Look for a violation in the provided sample
        for i in range(len(sample_values) - 1):
            x, fx = sample_values[i]
            y, fy = sample_values[i + 1]
            if x < y and fx > fy:
                desc = f"Monotonicity violated: f({x})={fx} > f({y})={fy} but {x}<{y}"
                return Counterexample(
                    ce_id=str(uuid.uuid4()),
                    strategy_name=self.name,
                    hypothesis_id=hypothesis.node_id,
                    witness={"x": x, "fx": fx, "y": y, "fy": fy},
                    description=desc,
                    confidence=0.95,
                    provenance=make_provenance(
                        source=f"adversary_{self.name}",
                        derivation=desc,
                        confidence=0.95,
                        evidence=[hypothesis.node_id],
                    ),
                )
        return None


# ---------------------------------------------------------------------------
# Structural counterexample strategies
# ---------------------------------------------------------------------------

class StructuralMissingFieldStrategy(CounterexampleStrategy):
    """
    Attacks structural hypotheses that claim all IR objects in a set
    have a specific field. Generates a witness IR missing that field.
    """
    name = "structural_missing_field"

    def applies_to(self, hypothesis: RepresentationObject) -> bool:
        payload = hypothesis.ir.get("content", {}).get("payload", {})
        return payload.get("claim_type") == "all_have_field"

    def generate(self, hypothesis: RepresentationObject) -> Optional[Counterexample]:
        payload = hypothesis.ir.get("content", {}).get("payload", {})
        required_field = payload.get("required_field")
        sample_irs = payload.get("sample_irs", [])

        if not required_field:
            return None

        for ir in sample_irs:
            if required_field not in ir:
                witness = {"ir_id": ir.get("ir_id", "unknown"), "missing_field": required_field}
                desc = f"IR object {ir.get('ir_id', '?')!r} missing required field '{required_field}'"
                return Counterexample(
                    ce_id=str(uuid.uuid4()),
                    strategy_name=self.name,
                    hypothesis_id=hypothesis.node_id,
                    witness=witness,
                    description=desc,
                    confidence=1.0,
                    provenance=make_provenance(
                        source=f"adversary_{self.name}",
                        derivation=desc,
                        confidence=1.0,
                        evidence=[hypothesis.node_id],
                    ),
                )

        # Synthesize a minimal counterexample by removing the field
        synthetic = {"ir_id": str(uuid.uuid4()), "_note": f"Missing {required_field}"}
        desc = f"Synthetic witness: IR missing '{required_field}'"
        return Counterexample(
            ce_id=str(uuid.uuid4()),
            strategy_name=self.name,
            hypothesis_id=hypothesis.node_id,
            witness=synthetic,
            description=desc,
            confidence=0.7,
            provenance=make_provenance(
                source=f"adversary_{self.name}",
                derivation=desc,
                confidence=0.7,
                evidence=[hypothesis.node_id],
            ),
        )


class StructuralCycleStrategy(CounterexampleStrategy):
    """
    Attacks hypotheses that claim a semantic graph is a DAG.
    Detects cycles in the graph's edges.
    """
    name = "structural_cycle"

    def applies_to(self, hypothesis: RepresentationObject) -> bool:
        payload = hypothesis.ir.get("content", {}).get("payload", {})
        return payload.get("claim_type") == "is_dag"

    def generate(self, hypothesis: RepresentationObject) -> Optional[Counterexample]:
        graph = hypothesis.ir.get("content", {}).get("graph", {})
        edges = graph.get("edges", [])

        # Build adjacency for cycle detection (DFS)
        adj: dict[str, list[str]] = {}
        for e in edges:
            for src in e.get("sources", []):
                adj.setdefault(src, [])
                adj[src].extend(e.get("targets", []))

        visited: set[str] = set()
        path: set[str] = set()

        def has_cycle(node: str) -> Optional[list[str]]:
            if node in path:
                return [node]
            if node in visited:
                return None
            visited.add(node)
            path.add(node)
            for nbr in adj.get(node, []):
                result = has_cycle(nbr)
                if result is not None:
                    return [node] + result
            path.discard(node)
            return None

        for start in adj:
            cycle_path = has_cycle(start)
            if cycle_path:
                desc = f"Cycle detected: {' → '.join(cycle_path)}"
                return Counterexample(
                    ce_id=str(uuid.uuid4()),
                    strategy_name=self.name,
                    hypothesis_id=hypothesis.node_id,
                    witness=cycle_path,
                    description=desc,
                    confidence=1.0,
                    provenance=make_provenance(
                        source=f"adversary_{self.name}",
                        derivation=desc,
                        confidence=1.0,
                        evidence=[hypothesis.node_id],
                    ),
                )
        return None


# ---------------------------------------------------------------------------
# Adversary Engine
# ---------------------------------------------------------------------------

class AdversaryEngine:
    """
    Aggregates counterexample strategies and routes hypotheses to
    applicable strategies.

    Usage:
        adv = AdversaryEngine()
        ce = adv.try_counterexample(hypothesis_node)
        if ce:
            print(f"Counterexample: {ce.description}")
    """

    DEFAULT_STRATEGIES: list[CounterexampleStrategy] = [
        NumericBoundaryStrategy(),
        NumericMonotonicityStrategy(),
        StructuralMissingFieldStrategy(),
        StructuralCycleStrategy(),
    ]

    def __init__(
        self,
        strategies: Optional[list[CounterexampleStrategy]] = None,
    ) -> None:
        self._strategies: list[CounterexampleStrategy] = (
            strategies if strategies is not None else list(self.DEFAULT_STRATEGIES)
        )

    def register_strategy(self, strategy: CounterexampleStrategy) -> None:
        self._strategies.append(strategy)

    def try_counterexample(
        self, hypothesis: RepresentationObject
    ) -> Optional[Counterexample]:
        """
        Run all applicable strategies. Return the first counterexample found,
        or None if the hypothesis survives all attacks.
        """
        for strategy in self._strategies:
            if strategy.applies_to(hypothesis):
                ce = strategy.generate(hypothesis)
                if ce is not None:
                    return ce
        return None

    def try_all(
        self, hypothesis: RepresentationObject
    ) -> list[Counterexample]:
        """Run all applicable strategies and return all found counterexamples."""
        results: list[Counterexample] = []
        for strategy in self._strategies:
            if strategy.applies_to(hypothesis):
                ce = strategy.generate(hypothesis)
                if ce is not None:
                    results.append(ce)
        return results

    def strategy_names(self) -> list[str]:
        return [s.name for s in self._strategies]
