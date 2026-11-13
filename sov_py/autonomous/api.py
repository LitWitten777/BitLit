"""
FastAPI REST & Telemetry Control API for the Autonomous Reasoning Engine.
Provides clean, standardized HTTP endpoints for:
1. Monitoring system telemetry, uptime, and database metrics.
2. Querying confirmed vs. falsified hypotheses and minimal counterexamples.
3. Live streaming of learned topological manifold coordinates and Betti barcodes.
4. Manually commanding reasoning ticks or submitting custom conjectures.
"""

from __future__ import annotations

import time
from typing import Any

from fastapi import FastAPI, Query
from pydantic import BaseModel

from .engine import AutonomousReasoningEngine
from .persistence import HypothesisRecord

app = FastAPI(
    title="Sovereign Autonomous Reasoning Engine API",
    description="Real-time control and telemetry interface for progressive self-organizing mathematical intelligence.",
    version="2.0.0",
)

# Global engine instance
_engine: AutonomousReasoningEngine | None = None


def get_engine() -> AutonomousReasoningEngine:
    global _engine
    if _engine is None:
        _engine = AutonomousReasoningEngine()
    return _engine


class HypothesisSubmission(BaseModel):
    id: str
    statement: str
    category: str
    falsification_criteria: str
    parameters: dict[str, Any] | None = None


class TickRequest(BaseModel):
    count: int = 1


@app.get("/api/status")
async def get_status() -> dict[str, Any]:
    """Returns real-time engine telemetry, worker status, and persistent database counts."""
    engine = get_engine()
    return engine.get_status()


@app.get("/api/hypotheses")
async def list_hypotheses(
    status: str | None = Query(None, description="Filter by OPEN, CONFIRMED, or FALSIFIED"),
    category: str | None = Query(None, description="Filter by category"),
) -> list[dict[str, Any]]:
    """Returns persisted hypotheses with their verification proofs and summaries."""
    engine = get_engine()
    hyps = engine.store.list_hypotheses(status=status, category=category)
    return [
        {
            "id": h.id,
            "statement": h.statement,
            "category": h.category,
            "status": h.status,
            "proof_summary": h.proof_summary,
            "details": h.details,
            "created_at": h.created_at,
            "updated_at": h.updated_at,
        }
        for h in hyps
    ]


@app.get("/api/verifications")
async def list_verifications(
    hypothesis_id: str | None = Query(None, description="Filter by specific hypothesis ID"),
) -> list[dict[str, Any]]:
    """Returns recent verification runs, execution times, and counterexamples."""
    engine = get_engine()
    runs = engine.store.list_verifications(hypothesis_id=hypothesis_id)
    return [
        {
            "id": r.id,
            "hypothesis_id": r.hypothesis_id,
            "engine": r.engine,
            "status": r.status,
            "duration_ms": r.duration_ms,
            "counterexample": r.counterexample,
            "logs": r.logs,
            "timestamp": r.timestamp,
        }
        for r in runs
    ]


@app.get("/api/manifold")
async def get_manifold() -> dict[str, Any]:
    """Returns current topological embeddings, 2D coordinates, Betti barcodes, and persistent entropy."""
    engine = get_engine()
    return engine.learner.get_manifold_state()


@app.post("/api/tick")
async def trigger_ticks(req: TickRequest) -> dict[str, Any]:
    """Manually triggers one or more reasoning cycles."""
    engine = get_engine()
    results = []
    for _ in range(max(1, min(req.count, 50))):
        res = engine.tick()
        results.append(res)
    return {"executed_ticks": len(results), "last_tick": results[-1] if results else None}


@app.post("/api/control/pause")
async def pause_daemon() -> dict[str, str]:
    """Pauses continuous autonomous ticks."""
    engine = get_engine()
    engine.is_paused = True
    return {"status": "PAUSED"}


@app.post("/api/control/resume")
async def resume_daemon() -> dict[str, str]:
    """Resumes continuous autonomous ticks."""
    engine = get_engine()
    engine.is_paused = False
    return {"status": "RESUMED"}


@app.post("/api/hypotheses")
async def submit_hypothesis(sub: HypothesisSubmission) -> dict[str, Any]:
    """Submits a new candidate hypothesis for autonomous verification."""
    engine = get_engine()
    rec = HypothesisRecord(
        id=sub.id,
        statement=sub.statement,
        category=sub.category,
        status="OPEN",
        details=sub.parameters or {},
        created_at=time.time(),
        updated_at=time.time(),
    )
    engine.store.save_hypothesis(rec)
    return {"status": "REGISTERED", "hypothesis_id": sub.id}


class OrganismEvaluationRequest(BaseModel):
    proposition_id: str
    linguistic_phrase: str = ""
    vector_params: list[float] | None = None
    operator: str = "=="
    dimension: int = 16
    functor_epochs: int = 120
    enable_topological_learner: bool = False


@app.post("/api/organism/evaluate")
async def evaluate_organism(req: OrganismEvaluationRequest) -> dict[str, Any]:
    """Executes the full 5-pillar Tower Organism cross-domain evaluation pipeline."""
    engine = get_engine()
    report = engine.evaluate_tower_organism(
        prop_id=req.proposition_id,
        linguistic_phrase=req.linguistic_phrase,
        vector_params=req.vector_params,
        operator=req.operator,
        dimension=req.dimension,
        functor_epochs=req.functor_epochs,
        enable_topological_learner=req.enable_topological_learner,
    )
    return {
        "proposition_id": report.proposition_id,
        "is_sofit_closed": report.is_sofit_closed,
        "cech_h1_defect": report.cech_h1_defect,
        "stella_parity_valid": report.stella_parity_valid,
        "annihilation_residual": report.annihilation_residual,
        "canonical_parameters": report.canonical_parameters,
        "s_diagram": report.s_diagram,
        "functor_converged": report.functor_converged,
        "pre_surgery_curvature": report.pre_surgery_curvature,
        "post_surgery_curvature": report.post_surgery_curvature,
        "surgeries_count": report.surgeries_count,
        "final_h1_flat": report.final_h1_flat,
        "system_sound": report.system_sound,
        "lean_receipt": report.lean_receipt,
        "execution_time_ms": report.execution_time_ms,
        "dominant_mog_partition": report.dominant_mog_partition,
        "mog_energy_ratio": report.mog_energy_ratio,
        "persistent_entropy": report.persistent_entropy,
        "topological_betti_0": report.topological_betti_0,
        "topological_betti_1": report.topological_betti_1,
        "topological_max_persistence": report.topological_max_persistence,
        "entropy_barrier_satisfied": report.entropy_barrier_satisfied,
        "polar_opposite": (
            {
                "nearest_char": report.polar_result.nearest_opposite_char,
                "metric_distance": report.polar_result.metric_distance,
                "annihilates": report.polar_result.sedenion_annihilation,
            }
            if report.polar_result
            else None
        ),
    }


class GrandTourRequest(BaseModel):
    ambient_dim: int = 16
    steps_per_segment: int = 12
    interpolation_mode: str = "stiefel"
    custom_points: list[list[float]] | None = None


@app.post("/api/v1/grand_tour")
async def compute_grand_tour(req: GrandTourRequest) -> dict[str, Any]:
    """Generates an Asimov-Buja geodesic Grand Tour projection sequence."""
    from ..grand_tour_stiefel import StiefelGrandTour
    import numpy as np

    dim = req.ambient_dim
    # Generate canonical key frames along orthogonal planes
    f0 = np.zeros((dim, 2), dtype=float)
    f0[0, 0] = 1.0
    f0[1, 1] = 1.0

    f1 = np.zeros((dim, 2), dtype=float)
    f1[2 % dim, 0] = 1.0
    f1[3 % dim, 1] = 1.0

    f2 = np.zeros((dim, 2), dtype=float)
    f2[4 % dim, 0] = 1.0
    f2[5 % dim, 1] = 1.0

    key_frames = [f0, f1, f2, f0]
    tour = StiefelGrandTour.generate_grand_tour_path(
        key_frames,
        steps_per_segment=req.steps_per_segment,
        interpolation_mode=req.interpolation_mode,
    )

    # If points provided or default canonical basis
    if req.custom_points is not None and len(req.custom_points) > 0:
        pts = np.array(req.custom_points, dtype=float)
    else:
        # Canonical standard basis points
        pts = np.eye(dim, dtype=float)

    projected_sequence = [
        StiefelGrandTour.project_point_cloud(pts, frame).tolist() for frame in tour
    ]

    svg_snapshot = StiefelGrandTour.render_tour_svg(
        np.array(projected_sequence[0]),
        point_labels=[f"v{i}" for i in range(len(pts))],
    )

    return {
        "ambient_dim": dim,
        "total_frames": len(tour),
        "interpolation_mode": req.interpolation_mode,
        "projected_sequence": projected_sequence,
        "svg_snapshot": svg_snapshot,
    }


