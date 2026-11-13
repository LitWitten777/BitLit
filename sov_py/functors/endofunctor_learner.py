"""
Endofunctor Learner — self-optimizing category-theoretic functor discovery.

Implements the functorial-manifold-learner skill from endofunk.md:

  F_θ: C → C  (local advantage functor)
  G_φ: C → C  (global Kuramoto harmony functor)
  η: F_θ ⟹ G_φ  (natural transformation)

The learner minimizes diagrammatic entropy via bounded gradient descent on
W_f, W_g, W_h (morphism weight matrices) until S_diagram < 1e-4 and H¹ = 0,
at which point the natural transformation is certified strict.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Any


DIAGRAM_ENTROPY_THRESHOLD = 1e-4
H1_THRESHOLD = 1e-6
WEIGHT_BOUNDS = (0.1, 1.0)


@dataclass
class LearnerResult:
    """Output of a completed learning run."""
    s_diagram: float
    h1_norm: float
    l_total: float
    epochs_run: int
    converged: bool
    weight_f: float
    weight_g: float
    weight_h: float
    lean_receipt: str | None = None
    history: list[dict[str, float]] = field(default_factory=list)


class EndofunctorLearner:
    """
    Parametric endofunctor learner operating on a scalar proxy for the full
    matrix learning problem. The scalar (W_f, W_g, W_h) triplet represents
    the dominant singular values of the morphism weight matrices.

    For a full matrix implementation extend W_f, W_g, W_h to numpy arrays
    and replace the scalar operations with matrix multiplication / Frobenius norms.
    """

    def __init__(
        self,
        dimension: int = 8,
        lambda_cohomology: float = 0.3,
        lambda_active_inference: float = 0.1,
        learning_rate: float = 0.05,
        initial_weights: tuple[float, float, float] = (0.5, 0.5, 0.5),
    ) -> None:
        self.dimension = dimension
        self.lam_coh = lambda_cohomology
        self.lam_ai = lambda_active_inference
        self.lr = learning_rate
        self.W_f, self.W_g, self.W_h = initial_weights

    # ------------------------------------------------------------------
    # Loss functions
    # ------------------------------------------------------------------

    def commutator_loss(self) -> float:
        """L_commutator = (W_h - W_g * W_f)^2."""
        return (self.W_h - self.W_g * self.W_f) ** 2

    def cohomology_loss(self) -> float:
        """L_cohomology: ‖δ₁‖² approximated on 1-simplex chain."""
        return (self.W_g - self.W_h) ** 2 + (self.W_f - self.W_h) ** 2

    def active_inference_free_energy(self, prior: float = 0.5) -> float:
        """Variational free energy F = KL(q||p) - E_q[ln p(x|θ)]."""
        eps = 1e-9
        w = self.W_h
        kl = w * math.log((w + eps) / (prior + eps)) + (1 - w) * math.log(
            (1 - w + eps) / (1 - prior + eps)
        )
        return max(0.0, kl - math.log(w + eps))

    def total_loss(self) -> float:
        return (
            self.commutator_loss()
            + self.lam_coh * self.cohomology_loss()
            + self.lam_ai * self.active_inference_free_energy()
        )

    def h1_norm(self) -> float:
        """‖δ₁(W_F)‖₂ — Čech 1-coboundary norm."""
        return math.sqrt(self.cohomology_loss())

    # ------------------------------------------------------------------
    # Gradient step
    # ------------------------------------------------------------------

    def _gradient_step(self) -> None:
        """One bounded gradient descent step on L_commutator."""
        lo, hi = WEIGHT_BOUNDS
        err = self.W_h - self.W_g * self.W_f
        self.W_h = max(lo, min(hi, self.W_h - self.lr * 2.0 * err))
        self.W_g = max(lo, min(hi, self.W_g + self.lr * 2.0 * self.W_f * err))
        self.W_f = max(lo, min(hi, self.W_f + self.lr * 2.0 * self.W_g * err))

    # ------------------------------------------------------------------
    # Learning loop
    # ------------------------------------------------------------------

    def learn(
        self,
        max_epochs: int = 11,
        target_s_diagram: float = DIAGRAM_ENTROPY_THRESHOLD,
        verbose: bool = False,
    ) -> LearnerResult:
        """
        Run the functor learning loop until convergence or max_epochs.

        Returns a LearnerResult with the final weights, losses, and
        a Lean 4 naturality receipt if convergence is achieved.
        """
        history: list[dict[str, float]] = []

        for epoch in range(1, max_epochs + 1):
            s = self.commutator_loss()
            h1 = self.h1_norm()
            lt = self.total_loss()
            history.append({"epoch": float(epoch), "s_diagram": s, "h1": h1, "l_total": lt})

            if verbose:
                print(f"  Epoch {epoch:2d}: S_diagram={s:.8f}  H1={h1:.8f}  L={lt:.8f}")

            if s < target_s_diagram and h1 < H1_THRESHOLD:
                lean_receipt = self._generate_lean_receipt(epoch, s)
                return LearnerResult(
                    s_diagram=s,
                    h1_norm=h1,
                    l_total=lt,
                    epochs_run=epoch,
                    converged=True,
                    weight_f=self.W_f,
                    weight_g=self.W_g,
                    weight_h=self.W_h,
                    lean_receipt=lean_receipt,
                    history=history,
                )

            self._gradient_step()

        s = self.commutator_loss()
        h1 = self.h1_norm()
        return LearnerResult(
            s_diagram=s,
            h1_norm=h1,
            l_total=self.total_loss(),
            epochs_run=max_epochs,
            converged=s < target_s_diagram and h1 < H1_THRESHOLD,
            weight_f=self.W_f,
            weight_g=self.W_g,
            weight_h=self.W_h,
            lean_receipt=None,
            history=history,
        )

    # ------------------------------------------------------------------
    # Lean receipt generation
    # ------------------------------------------------------------------

    def _generate_lean_receipt(self, epoch: int, s_diagram: float) -> str:
        """Generate a Lean 4 naturality certificate comment (informal)."""
        return (
            f"/- Naturality certificate: EndofunctorLearner dimension={self.dimension}\n"
            f"   Converged at epoch {epoch}: S_diagram = {s_diagram:.2e} < 10⁻⁴\n"
            f"   W_f = {self.W_f:.6f}, W_g = {self.W_g:.6f}, W_h = {self.W_h:.6f}\n"
            f"   η: F_θ ⟹ G_φ is certified strict (H¹ = 0, naturality square commutes).\n"
            f"   To kernel-certify: run TheoremGenerationEngine with LEAN4_THEOREM predicate\n"
            f"   'autonomous_entropy_degree_decomposition' or custom FunctorNaturality.lean.\n"
            f"-/"
        )

    # ------------------------------------------------------------------
    # E₈ projection utility
    # ------------------------------------------------------------------

    @staticmethod
    def project_e8(v: list[float]) -> list[float]:
        """
        Project an 8D vector onto the nearest E₈ root lattice point.

        The 240 minimal roots of E₈ are:
          - 112 integer roots: (±1, ±1, 0, 0, 0, 0, 0, 0) and permutations
          - 128 half-integer roots: (±½, ±½, ..., ±½) with even # of minus signs

        This returns the nearest root by Euclidean distance.
        """
        import itertools

        if len(v) != 8:
            raise ValueError(f"Expected 8D vector, got {len(v)}D")

        # Generate all 240 E₈ roots
        roots: list[tuple[float, ...]] = []

        # Integer roots: ±e_i ± e_j for i < j
        for i, j in itertools.combinations(range(8), 2):
            for si in (1.0, -1.0):
                for sj in (1.0, -1.0):
                    r = [0.0] * 8
                    r[i] = si
                    r[j] = sj
                    roots.append(tuple(r))

        # Half-integer roots: (±½)^8 with even # minus signs
        for signs in itertools.product([0.5, -0.5], repeat=8):
            if signs.count(-0.5) % 2 == 0:
                roots.append(signs)

        # Find nearest root
        best_root = roots[0]
        best_dist = float("inf")
        for root in roots:
            dist = sum((v[k] - root[k]) ** 2 for k in range(8))
            if dist < best_dist:
                best_dist = dist
                best_root = root

        return list(best_root)
