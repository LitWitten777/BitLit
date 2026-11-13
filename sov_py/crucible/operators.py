"""
src/crucible/operators.py
Crucible Operator suite: Generate, Associate, Reflect, Verify, Compose,
Integrate, Decompose.

Each operator is a callable class that accepts RepresentationObject(s) and
a CrucibleContext, transforms them, and returns a new RepresentationObject
with full provenance.

Author: EngA
Version: 0.1.0
Provenance: {
  source: manual_construction_v0.1,
  derivation: Sprint 1 Crucible operator skeleton,
  confidence: 0.85, validation_status: validated
}
"""
from __future__ import annotations

import uuid
from abc import ABC, abstractmethod
from datetime import datetime, timezone
from typing import Any, Optional

from ..hypergraph import (
    HyperEdge,
    ProvenanceError,
    RepresentationObject,
    make_provenance,
    validate_provenance,
)
from .context import CrucibleContext
from .justification import Justification, JustificationStatus


# ---------------------------------------------------------------------------
# Base Operator
# ---------------------------------------------------------------------------

class CrucibleOperator(ABC):
    """
    Abstract base class for all Crucible operators.

    Subclasses implement _execute() and declare their operator_name.
    The base class handles:
      - Provenance construction
      - TTF instrumentation hooks (via context.ttf)
      - Justification recording
    """

    operator_name: str = "base"
    operator_version: str = "0.1.0"

    def __call__(
        self,
        *inputs: RepresentationObject,
        context: CrucibleContext,
        **kwargs: Any,
    ) -> RepresentationObject:
        ts_start = datetime.now(timezone.utc)

        # TTF: record operation start
        if context.ttf:
            context.ttf.record_start(self.operator_name, context.context_id)

        try:
            result = self._execute(*inputs, context=context, **kwargs)
        except Exception as exc:
            if context.ttf:
                context.ttf.record_failure(self.operator_name, context.context_id, str(exc))
            raise

        ts_end = datetime.now(timezone.utc)
        elapsed_ms = (ts_end - ts_start).total_seconds() * 1000

        # Ensure provenance is present and valid
        validate_provenance(result.provenance, label=f"{self.operator_name}.output")

        # Record justification
        j = Justification(
            justification_id=str(uuid.uuid4()),
            operator=self.operator_name,
            input_ids=[inp.node_id for inp in inputs],
            output_id=result.node_id,
            context_id=context.context_id,
            elapsed_ms=elapsed_ms,
            status=JustificationStatus.SUPPORTED,
        )
        context.record_justification(j)

        # TTF: record success
        if context.ttf:
            context.ttf.record_success(
                self.operator_name, context.context_id, elapsed_ms
            )

        return result

    @abstractmethod
    def _execute(
        self,
        *inputs: RepresentationObject,
        context: CrucibleContext,
        **kwargs: Any,
    ) -> RepresentationObject:
        ...

    def _new_ir(
        self,
        base_ir: dict,
        context: CrucibleContext,
        *,
        derivation: str,
        confidence: float,
        parent_ids: list[str],
        extra_content: Optional[dict] = None,
    ) -> dict:
        """Build a new IR dict derived from base_ir."""
        new_ir = {
            **base_ir,
            "ir_id": str(uuid.uuid4()),
            "provenance": make_provenance(
                source=f"{self.operator_name}_v{self.operator_version}",
                derivation=derivation,
                confidence=confidence,
                validation_status="unvalidated",
                version=self.operator_version,
                evidence=parent_ids,
                author="automated",
            ),
            "context_id": context.context_id,
        }
        if extra_content:
            new_ir.setdefault("content", {})
            new_ir["content"].update(extra_content)
        return new_ir


# ---------------------------------------------------------------------------
# Generate
# ---------------------------------------------------------------------------

class Generate(CrucibleOperator):
    """
    Generate a new RepresentationObject from a seed IR dict or an existing node.

    Usage:
        gen = Generate()
        result = gen(seed_node, context=ctx, chart_id="chart-sample-lang-v1")
    """
    operator_name = "Generate"

    def _execute(
        self,
        *inputs: RepresentationObject,
        context: CrucibleContext,
        chart_id: Optional[str] = None,
        seed_ir: Optional[dict] = None,
        **kwargs: Any,
    ) -> RepresentationObject:
        if seed_ir is None and inputs:
            seed_ir = inputs[0].ir
        elif seed_ir is None:
            raise ValueError("Generate requires at least one input node or seed_ir=")

        parent_ids = [inp.node_id for inp in inputs]
        new_ir = self._new_ir(
            seed_ir, context,
            derivation=f"Generated by {self.operator_name} from {parent_ids}; chart={chart_id}",
            confidence=0.75,
            parent_ids=parent_ids,
            extra_content={"payload": {
                **seed_ir.get("content", {}).get("payload", {}),
                "_generated_by": self.operator_name,
                "_chart_id": chart_id,
            }},
        )
        if chart_id:
            new_ir["chart_ids"] = [chart_id]

        return RepresentationObject(
            node_id=new_ir["ir_id"],
            context_id=context.context_id,
            ir=new_ir,
            provenance=new_ir["provenance"],
            label=f"Generated({seed_ir.get('object_type','?')})",
        )


# ---------------------------------------------------------------------------
# Associate
# ---------------------------------------------------------------------------

class Associate(CrucibleOperator):
    """
    Associate two RepresentationObjects by creating a HyperEdge between them
    and returning a synthetic IR representing the association.

    Also registers the edge on the hypergraph if context.hypergraph is set.
    """
    operator_name = "Associate"

    def _execute(
        self,
        *inputs: RepresentationObject,
        context: CrucibleContext,
        relation: str = "associated_with",
        weight: float = 1.0,
        **kwargs: Any,
    ) -> RepresentationObject:
        if len(inputs) < 2:
            raise ValueError("Associate requires at least 2 input nodes")

        source_ids = [inp.node_id for inp in inputs[:-1]]
        target_ids = [inputs[-1].node_id]
        edge_id = str(uuid.uuid4())
        prov = make_provenance(
            source=f"{self.operator_name}_v{self.operator_version}",
            derivation=f"Association [{relation}] between {source_ids} → {target_ids}",
            confidence=0.8,
            evidence=source_ids + target_ids,
            author="automated",
        )

        edge = HyperEdge(
            edge_id=edge_id,
            context_id=context.context_id,
            relation=relation,
            sources=source_ids,
            targets=target_ids,
            provenance=prov,
            weight=weight,
        )

        if context.hypergraph is not None:
            context.hypergraph.add_edge(edge)

        assoc_ir = self._new_ir(
            inputs[0].ir, context,
            derivation=f"Association IR for edge {edge_id} [{relation}]",
            confidence=0.8,
            parent_ids=[inp.node_id for inp in inputs],
            extra_content={"payload": {
                "association_edge_id": edge_id,
                "relation": relation,
                "source_ids": source_ids,
                "target_ids": target_ids,
            }},
        )
        assoc_ir["object_type"] = "hyperedge"

        return RepresentationObject(
            node_id=assoc_ir["ir_id"],
            context_id=context.context_id,
            ir=assoc_ir,
            provenance=assoc_ir["provenance"],
            label=f"Association({relation})",
        )


# ---------------------------------------------------------------------------
# Reflect
# ---------------------------------------------------------------------------

class Reflect(CrucibleOperator):
    """
    Reflect an IR object against an Atlas chart, checking structural
    consistency and returning a scored reflection result.
    """
    operator_name = "Reflect"

    def _execute(
        self,
        *inputs: RepresentationObject,
        context: CrucibleContext,
        chart_id: Optional[str] = None,
        **kwargs: Any,
    ) -> RepresentationObject:
        if not inputs:
            raise ValueError("Reflect requires at least 1 input")

        target = inputs[0]
        chart = None
        if chart_id and context.registry:
            try:
                chart = context.registry.get(chart_id)
            except KeyError:
                pass

        score = self._compute_reflection_score(target, chart)
        reflect_ir = self._new_ir(
            target.ir, context,
            derivation=(
                f"Reflection of {target.node_id} against chart={chart_id}; "
                f"score={score:.3f}"
            ),
            confidence=score,
            parent_ids=[target.node_id],
            extra_content={"payload": {
                "reflected_node_id": target.node_id,
                "chart_id": chart_id,
                "reflection_score": score,
                "chart_name": chart.chart_name if chart else "unknown",
            }},
        )
        reflect_ir["object_type"] = "metric_result"

        return RepresentationObject(
            node_id=reflect_ir["ir_id"],
            context_id=context.context_id,
            ir=reflect_ir,
            provenance=reflect_ir["provenance"],
            label=f"Reflect(score={score:.3f})",
        )

    def _compute_reflection_score(
        self,
        target: RepresentationObject,
        chart: Any,
    ) -> float:
        """Lean scoring: coverage * confidence. Extend with metric framework later."""
        if chart is None:
            return 0.5
        base = chart.metrics.coverage * chart.provenance.confidence
        return round(min(max(base, 0.0), 1.0), 4)


# ---------------------------------------------------------------------------
# Verify
# ---------------------------------------------------------------------------

class Verify(CrucibleOperator):
    """
    Verify a hypothesis IR against evidence nodes. Returns a verification
    result IR with confidence update and validation_status assignment.

    Integrates with adversary.py: if context.adversary is set, it will
    attempt to generate a counterexample first.
    """
    operator_name = "Verify"

    def _execute(
        self,
        *inputs: RepresentationObject,
        context: CrucibleContext,
        hypothesis: Optional[RepresentationObject] = None,
        threshold: float = 0.7,
        **kwargs: Any,
    ) -> RepresentationObject:
        if hypothesis is not None:
            hyp = hypothesis
            evidence_nodes = list(inputs)
        elif inputs:
            hyp = inputs[0]
            evidence_nodes = list(inputs[1:])
        else:
            raise ValueError("Verify requires a hypothesis node")

        # Try adversarial counterexample if adversary is available
        counterexample = None
        if context.adversary is not None:
            counterexample = context.adversary.try_counterexample(hyp)

        # Aggregate confidence from evidence
        if evidence_nodes:
            avg_conf = sum(
                n.provenance.get("confidence", 0.5) for n in evidence_nodes
            ) / len(evidence_nodes)
        else:
            avg_conf = hyp.provenance.get("confidence", 0.5)

        # Penalize if counterexample found
        if counterexample is not None:
            avg_conf = avg_conf * 0.5

        status = "validated" if avg_conf >= threshold else (
            "refuted" if counterexample is not None else "contested"
        )

        verify_ir = self._new_ir(
            hyp.ir, context,
            derivation=(
                f"Verification of {hyp.node_id} with {len(evidence_nodes)} evidence node(s); "
                f"counterexample={'yes' if counterexample else 'no'}; "
                f"confidence={avg_conf:.3f}; status={status}"
            ),
            confidence=avg_conf,
            parent_ids=[hyp.node_id] + [n.node_id for n in evidence_nodes],
        )
        verify_ir["provenance"]["validation_status"] = status
        verify_ir["object_type"] = "metric_result"

        return RepresentationObject(
            node_id=verify_ir["ir_id"],
            context_id=context.context_id,
            ir=verify_ir,
            provenance=verify_ir["provenance"],
            label=f"Verify(status={status}, conf={avg_conf:.3f})",
        )


# ---------------------------------------------------------------------------
# Compose
# ---------------------------------------------------------------------------

class Compose(CrucibleOperator):
    """
    Compose two or more RepresentationObjects by functor composition.
    The output IR is a new object whose semantic graph merges the inputs'.
    """
    operator_name = "Compose"

    def _execute(
        self,
        *inputs: RepresentationObject,
        context: CrucibleContext,
        composition_label: str = "composed",
        **kwargs: Any,
    ) -> RepresentationObject:
        if len(inputs) < 2:
            raise ValueError("Compose requires at least 2 inputs")

        merged_nodes: list[dict] = []
        merged_edges: list[dict] = []
        min_conf = 1.0

        for inp in inputs:
            graph = inp.ir.get("content", {}).get("graph", {})
            merged_nodes.extend(graph.get("nodes", []))
            merged_edges.extend(graph.get("edges", []))
            min_conf = min(min_conf, inp.provenance.get("confidence", 0.5))

        base_ir = inputs[0].ir.copy()
        base_ir.setdefault("content", {})
        base_ir["content"]["graph"] = {"nodes": merged_nodes, "edges": merged_edges}

        compose_ir = self._new_ir(
            base_ir, context,
            derivation=f"Composition of {[i.node_id for i in inputs]} as '{composition_label}'",
            confidence=min_conf,
            parent_ids=[inp.node_id for inp in inputs],
            extra_content={"payload": {
                "_composed_from": [inp.node_id for inp in inputs],
                "_composition_label": composition_label,
            }},
        )

        return RepresentationObject(
            node_id=compose_ir["ir_id"],
            context_id=context.context_id,
            ir=compose_ir,
            provenance=compose_ir["provenance"],
            label=f"Compose({composition_label})",
        )


# ---------------------------------------------------------------------------
# Integrate
# ---------------------------------------------------------------------------

class Integrate(CrucibleOperator):
    """
    Integrate an IR object into the hypergraph: adds the node and links it
    to existing nodes via Association edges.
    """
    operator_name = "Integrate"

    def _execute(
        self,
        *inputs: RepresentationObject,
        context: CrucibleContext,
        target_node_ids: Optional[list[str]] = None,
        relation: str = "integrated_with",
        **kwargs: Any,
    ) -> RepresentationObject:
        if not inputs:
            raise ValueError("Integrate requires at least 1 input")

        primary = inputs[0]

        if context.hypergraph is not None:
            # Add node to hypergraph if not already present
            if primary.node_id not in {n.node_id for n in context.hypergraph.nodes()}:
                context.hypergraph.add_node(primary)

            # Associate with target nodes
            if target_node_ids:
                for tid in target_node_ids:
                    try:
                        target_node = context.hypergraph.get_node(tid)
                        assoc = Associate()
                        assoc(primary, target_node, context=context, relation=relation)
                    except KeyError:
                        pass  # target not yet in graph — skip silently

        integrate_ir = self._new_ir(
            primary.ir, context,
            derivation=(
                f"Integrated {primary.node_id} into hypergraph; "
                f"linked to {target_node_ids or []}"
            ),
            confidence=primary.provenance.get("confidence", 0.8),
            parent_ids=[primary.node_id],
            extra_content={"payload": {
                "_integrated_node_id": primary.node_id,
                "_linked_to": target_node_ids or [],
            }},
        )

        return RepresentationObject(
            node_id=integrate_ir["ir_id"],
            context_id=context.context_id,
            ir=integrate_ir,
            provenance=integrate_ir["provenance"],
            label=f"Integrate({primary.node_id})",
        )


# ---------------------------------------------------------------------------
# Decompose
# ---------------------------------------------------------------------------

class Decompose(CrucibleOperator):
    """
    Decompose a composite IR object into its constituent sub-objects.
    Returns the first sub-object; all sub-objects are added to context.decomposed.
    """
    operator_name = "Decompose"

    def _execute(
        self,
        *inputs: RepresentationObject,
        context: CrucibleContext,
        decompose_key: str = "nodes",
        **kwargs: Any,
    ) -> RepresentationObject:
        if not inputs:
            raise ValueError("Decompose requires 1 input")

        source = inputs[0]
        graph = source.ir.get("content", {}).get("graph", {})
        parts = graph.get(decompose_key, [])

        sub_objects: list[RepresentationObject] = []
        for i, part in enumerate(parts):
            part_ir = {
                "ir_id": str(uuid.uuid4()),
                "ir_version": "0.1.0",
                "object_type": source.ir.get("object_type", "code_snippet"),
                "representation_level": source.ir.get("representation_level", 1),
                "content": {"payload": part},
                "provenance": make_provenance(
                    source=f"{self.operator_name}_v{self.operator_version}",
                    derivation=f"Decomposed from {source.node_id}[{decompose_key}][{i}]",
                    confidence=source.provenance.get("confidence", 0.8),
                    evidence=[source.node_id],
                    author="automated",
                ),
                "context_id": context.context_id,
            }
            sub_obj = RepresentationObject(
                node_id=part_ir["ir_id"],
                context_id=context.context_id,
                ir=part_ir,
                provenance=part_ir["provenance"],
                label=f"Decomposed({source.node_id}[{i}])",
            )
            sub_objects.append(sub_obj)

        if hasattr(context, "decomposed"):
            context.decomposed.extend(sub_objects)

        primary = sub_objects[0] if sub_objects else RepresentationObject(
            node_id=str(uuid.uuid4()),
            context_id=context.context_id,
            ir={
                **source.ir,
                "ir_id": str(uuid.uuid4()),
                "provenance": make_provenance(
                    source=f"{self.operator_name}_v{self.operator_version}",
                    derivation=f"Decompose of {source.node_id}: no parts found",
                    confidence=0.0,
                    author="automated",
                ),
            },
            provenance=make_provenance(
                source=f"{self.operator_name}_v{self.operator_version}",
                derivation="Empty decomposition",
                confidence=0.0,
            ),
            label="Decompose(empty)",
        )
        return primary
