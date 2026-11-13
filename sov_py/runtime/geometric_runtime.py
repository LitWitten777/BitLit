"""
geometric_runtime.py
====================
Unified Geometric Cognitive Runtime for Geometric Native Language (GNL).

Orchestrates the end-to-end topological cognitive architecture:
  Perceptual Ingestion
    -> Conway-Sloane E_8 / D_8 CVP Snapping
    -> Ramanujan Expander Geodesic Router (D <= 3)
    -> Cech Cohomology Gate (||H^1|| = 0 Sheaf) + Curtis 35 MOG Basins
    -> Multiplierless Integer Shift Kernel (Zero GPU)
    -> Online Data-to-Weights Hypernetwork (Bayesian Updates)
    -> Certified Negentropy State
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence, Tuple, Union
import numpy as np

from .geometric_lexer import GeometricFrame, GeometricLexer
from .pencil_grammar import (
    ExpanderGeodesicRouter,
    GrammarValidationResult,
    PencilGrammarValidator,
)
from .cohomology_gate import CohomologyGate, CohomologyReport
from .multiplierless_kernel import MultiplierlessKernel
from .adaptive_engine import (
    AdaptationReceipt,
    AdaptiveHypernetworkEngine,
    ConwaySloaneCVP,
    MOGSemanticBasins,
)


@dataclass(frozen=True)
class CognitiveStepResult:
    step: int
    current_frame: GeometricFrame
    next_frame: GeometricFrame
    is_sound: bool
    h1_norm: float
    hallucination_risk: float
    hop_distance: int
    dominant_mog_basin: int
    basin_energy_ratio: float
    total_negentropy: float
    backtrack_triggered: bool
    status: str


@dataclass(frozen=True)
class CognitiveTrajectory:
    frames: Tuple[GeometricFrame, ...]
    grammar_result: GrammarValidationResult
    cohomology_report: CohomologyReport
    final_negentropy: float
    is_certified: bool
    state_vector: Tuple[int, ...]


class GeometricCognitiveRuntime:
    """
    Unified Geometric Cognitive Runtime replacing probabilistic autoregressive
    transformers with topological invariant navigation.
    """

    def __init__(
        self,
        cohomology_tol: float = 1e-4,
        learning_rate: float = 0.05,
    ) -> None:
        self.lexer = GeometricLexer.get_instance()
        self.router = ExpanderGeodesicRouter(self.lexer)
        self.grammar = PencilGrammarValidator(self.router)
        self.gate = CohomologyGate(tolerance=cohomology_tol)
        self.kernel = MultiplierlessKernel(self.router)
        self.adaptive = AdaptiveHypernetworkEngine(learning_rate=learning_rate)
        self.mog = MOGSemanticBasins()

        # Discrete 168-node integer state register
        self.state_register = [0] * 168

    def ingest(self, input_data: Union[str, bytes, np.ndarray, Sequence[float]]) -> List[GeometricFrame]:
        """
        Perceptual Ingestion: maps strings, bytes, or continuous vectors into GNL 2-frames.
        """
        if isinstance(input_data, str):
            return self.lexer.encode_text(input_data)
        elif isinstance(input_data, bytes):
            return self.lexer.encode_bytes(input_data)
        elif isinstance(input_data, (np.ndarray, list, tuple)):
            arr = np.array(input_data, dtype=float)
            if arr.ndim == 1 and len(arr) in (7, 21):
                return [self.lexer.project_vector(arr)]
            elif arr.ndim == 2 and arr.shape[1] in (7, 21):
                return [self.lexer.project_vector(row) for row in arr]
            else:
                # Quantize 8D slices via Conway-Sloane E8
                snapped = ConwaySloaneCVP.snap_to_e8(arr.flatten()[:8])
                return [self.lexer.project_vector(snapped[:7])]
        else:
            raise TypeError(f"Unsupported perceptual input type: {type(input_data)}")

    def step(
        self,
        current_frame: GeometricFrame,
        target_frame: GeometricFrame,
        history: Optional[Sequence[GeometricFrame]] = None,
    ) -> CognitiveStepResult:
        """
        Executes a single validated cognitive transition from current_frame to target_frame.
        """
        hist = list(history or [current_frame])
        test_chain = hist + [target_frame]

        # 1. Grammar validation (Pencil incidence & geodesic distance <= 3)
        dist = self.router.geodesic_distance(current_frame, target_frame)
        is_grammar_valid = self.grammar.is_valid_transition(current_frame, target_frame)

        # 2. Cech Cohomology Gate evaluation
        cohomology = self.gate.evaluate_chain(test_chain)

        # 3. MOG Basin Analysis
        sub8 = list(target_frame.harmonics[:7]) + [float(np.linalg.norm(target_frame.harmonics))]
        basin_k, basin_ratio = self.mog.classify_basin(sub8)

        # Check for sedenion zero-divisor annihilation: L_S(u) * v = 0
        is_annihilating = self.lexer.annihilates(current_frame, target_frame)
        if is_annihilating:
            # Annihilation collapses into empty zero-state; rejected by semantic conservation
            return CognitiveStepResult(
                step=self.adaptive.step_count + 1,
                current_frame=current_frame,
                next_frame=current_frame,  # Collapse / backtrack
                is_sound=False,
                h1_norm=float("inf"),
                hallucination_risk=1.0,
                hop_distance=dist,
                dominant_mog_basin=basin_k,
                basin_energy_ratio=basin_ratio,
                total_negentropy=self.adaptive.total_negentropy,
                backtrack_triggered=True,
                status="REJECTED_BY_SEDENION_ZERO_DIVISOR_ANNIHILATION",
            )

        if not is_grammar_valid or cohomology.backtrack_triggered:
            return CognitiveStepResult(
                step=self.adaptive.step_count + 1,
                current_frame=current_frame,
                next_frame=current_frame,  # Freeze / backtrack
                is_sound=False,
                h1_norm=cohomology.h1_norm,
                hallucination_risk=cohomology.hallucination_bound,
                hop_distance=dist,
                dominant_mog_basin=basin_k,
                basin_energy_ratio=basin_ratio,
                total_negentropy=self.adaptive.total_negentropy,
                backtrack_triggered=True,
                status="REJECTED_BY_COHOMOLOGY_OR_GRAMMAR_GATE",
            )

        # 4. Multiplierless integer register activation
        self.state_register[target_frame.frame_id] += 1
        self.state_register = self.kernel.convolve_step(self.state_register)

        # 5. Online Bayesian Data-to-Weights adaptation
        receipt = self.adaptive.update_from_transition(current_frame, target_frame)

        return CognitiveStepResult(
            step=receipt.step,
            current_frame=current_frame,
            next_frame=target_frame,
            is_sound=True,
            h1_norm=cohomology.h1_norm,
            hallucination_risk=cohomology.hallucination_bound,
            hop_distance=dist,
            dominant_mog_basin=receipt.dominant_mog_basin,
            basin_energy_ratio=receipt.basin_energy_ratio,
            total_negentropy=receipt.total_negentropy,
            backtrack_triggered=False,
            status="CERTIFIED_SOUND_TRANSITION",
        )

    def route_reasoning(self, start: GeometricFrame, goal: GeometricFrame) -> List[GeometricFrame]:
        """
        Synthesizes an unbroken geodesic reasoning path on the Ramanujan expander (D <= 3).
        """
        return self.router.shortest_geodesic(start, goal)

    def run_trajectory(
        self,
        key_frames: Sequence[GeometricFrame],
    ) -> CognitiveTrajectory:
        """
        Interpolates and certifies an entire reasoning trajectory across key frames.
        """
        complete_path = self.grammar.complete_sentence_geodesic(key_frames)
        grammar_eval = self.grammar.validate_sentence(complete_path)
        cohomology_eval = self.gate.evaluate_chain(complete_path)

        # Run adaptive learning along the complete path
        for i in range(len(complete_path) - 1):
            f_curr = complete_path[i]
            f_next = complete_path[i + 1]
            self.state_register[f_next.frame_id] += 1
            self.state_register = self.kernel.convolve_step(self.state_register)
            self.adaptive.update_from_transition(f_curr, f_next)

        is_certified = grammar_eval.is_valid and cohomology_eval.is_sound

        return CognitiveTrajectory(
            frames=tuple(complete_path),
            grammar_result=grammar_eval,
            cohomology_report=cohomology_eval,
            final_negentropy=self.adaptive.total_negentropy,
            is_certified=is_certified,
            state_vector=tuple(self.state_register),
        )

    def polar_step(self, current_frame: GeometricFrame) -> CognitiveStepResult:
        """
        Attempts a transition to the antipodal polar opposite (u, v) -> (-u, -v).
        Evaluates whether this triggers zero-divisor annihilation or sound reflection.
        """
        opposite, _ = self.lexer.generate_polar_opposite(current_frame)
        return self.step(current_frame, opposite)

    def evaluate_symbolic_closure(self, symbols: Sequence[str]) -> Tuple[bool, CohomologyReport]:
        """
        Encodes a sequence of symbolic tokens into 2-frames and certifies topological boundary closure.
        """
        frames = self.lexer.encode_symbols(symbols)
        report = self.gate.evaluate_chain(frames)
        return report.is_boundary_closed and report.is_sound, report
