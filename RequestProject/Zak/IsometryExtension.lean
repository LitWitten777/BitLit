import Mathlib

open scoped Classical BigOperators
open MeasureTheory

set_option maxHeartbeats 1000000

/-!
# Abstract linear-isometry extension from a dense subspace

This module provides the reusable Hilbert-space completion tool requested by the
`L²` Zak completion run (TASK B): a densely-defined linear isometry into a
complete space extends **uniquely** to a linear isometry of the whole space.

The proof is a thin wrapper around Mathlib's `ContinuousLinearMap.extend`
(extension of a continuous linear map along a dense uniform-inducing embedding):
the inclusion of a dense submodule is such an embedding, the extension is
continuous and agrees with the original map on the (dense) subspace, hence it
preserves the norm everywhere by continuity, upgrading the extended continuous
linear map to a `LinearIsometry`.

These are exactly the abstract analytic ingredient behind extending the densely
defined Zak transform `concreteZakDense` to all of `L²(ℝ)`.
-/

namespace CriticalMixedHRT

variable {𝕜 H E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-
**Dense linear-isometry extension (existence).**

If `D` is a dense subspace of an inner-product space `H` and `T₀ : D →ₗᵢ[𝕜] E`
is a linear isometry into a complete inner-product space `E`, then there is a
linear isometry `T : H →ₗᵢ[𝕜] E` agreeing with `T₀` on `D`.
-/
theorem linear_isometry_extends_from_dense_subspace
    (D : Submodule 𝕜 H) (hD : Dense (D : Set H))
    (T₀ : D →ₗᵢ[𝕜] E) :
    ∃ T : H →ₗᵢ[𝕜] E, ∀ x : D, T x = T₀ x := by
  obtain ⟨T₁, hT₁⟩ : ∃ (T₁ : H →L[𝕜] E), ∀ x : D, T₁ x = T₀ x := by
    have h_ext : ∀ (f : D →L[𝕜] E), ∃ T₁ : H →L[𝕜] E, ∀ x : D, T₁ x = f x := by
      intro f
      have h_ext : ∃ T₁ : H →L[𝕜] E, ∀ x : D, T₁ x = f x := by
        have h_dense : DenseRange (D.subtypeL : D →L[𝕜] H) := by
          convert hD using 1;
          simp +decide [ DenseRange, Set.range ]
        have h_unif : IsUniformInducing (D.subtypeL : D →L[𝕜] H) := by
          convert ( isUniformEmbedding_subtype_val.isUniformInducing ) using 1
        exact ⟨ f.extend ( D.subtypeL ), fun x => f.extend_eq h_dense h_unif x ⟩
      exact h_ext;
    convert h_ext ( T₀.toContinuousLinearMap );
  refine' ⟨ { toFun := T₁, map_add' := _, map_smul' := _, norm_map' := _ }, hT₁ ⟩;
  intro x
  have h_eq : ∀ y : D, ‖T₁ y‖ = ‖y‖ := by
    aesop;
  -- By the density of $D$, for any $x \in H$, there exists a sequence $\{y_n\}$ in $D$ such that $y_n \to x$.
  obtain ⟨y_n, hy_n⟩ : ∃ y_n : ℕ → D, Filter.Tendsto (fun n => (y_n n : H)) Filter.atTop (nhds x) := by
    have := hD x;
    rw [ mem_closure_iff_seq_limit ] at this;
    exact ⟨ fun n => ⟨ this.choose n, this.choose_spec.1 n ⟩, this.choose_spec.2 ⟩;
  exact tendsto_nhds_unique ( T₁.continuous.continuousAt.tendsto.comp hy_n |> Filter.Tendsto.norm ) ( hy_n.norm.congr ( by aesop ) )

/-
**Dense linear-isometry extension (uniqueness of the extending map).**

Any two continuous linear maps `H → E` that agree on a dense subspace `D` are
equal.  Together with `linear_isometry_extends_from_dense_subspace` this gives
existence and uniqueness of the densely-defined-isometry extension.
-/
omit [CompleteSpace E] in
theorem continuous_linear_map_eq_of_eq_on_dense_subspace
    (D : Submodule 𝕜 H) (hD : Dense (D : Set H))
    (S T : H →L[𝕜] E) (h : ∀ x : D, S x = T x) :
    S = T := by
  apply ContinuousLinearMap.ext
  intro x
  by_contra h_neq;
  -- Since $S(x) \neq T(x)$, there exists a neighborhood $U$ of $x$ such that $S(y) \neq T(y)$ for all $y \in U$.
  obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ y, dist y x < ε → S y ≠ T y := by
    exact Metric.mem_nhds_iff.mp ( IsOpen.mem_nhds ( isOpen_compl_iff.mpr <| isClosed_eq S.continuous T.continuous ) h_neq );
  rcases hD.inter_nhds_nonempty ( Metric.ball_mem_nhds x hε.1 ) with ⟨ y, hyD, hyx ⟩ ; exact hε.2 y hyx ( h ⟨ y, hyD ⟩ )

end CriticalMixedHRT