import Mathlib
import RequestProject.Rotation.ReturnData
import RequestProject.Rotation.FourierReturnSums
import RequestProject.Rotation.DenjoyKoksmaInterface

open scoped Classical BigOperators Real
open Filter Topology

/-!
# C¹ zero-mean uniform return sums via Denjoy–Koksma (Stage 2B)

Given Denjoy–Koksma return data `D : DenjoyKoksmaReturnData θ`, we upgrade the
finite trigonometric-polynomial return-sum theorem of Stage 2A to general
functions that can be approximated, *in variation*, by mean-zero trigonometric
polynomials.

The variation-approximation hypothesis is recorded by the predicate
`TrigApproxInVariation`.  The mathematical content is the standard route:

1. Given `ε > 0`, pick a mean-zero trigonometric polynomial `P` with
   `variation (φ - P) < ε/2`.
2. The Denjoy–Koksma bound (`D.dk_bound`) gives
   `‖∑_{j<qₙ} (φ - P)(· - jθ)‖ ≤ variation (φ - P) < ε/2`, uniformly in `x`.
3. The Stage 2A theorem `trigPoly_return_tendstoUniformly` gives
   `‖∑_{j<qₙ} P(· - jθ)‖ → 0` uniformly.
4. Adding the two estimates yields uniform convergence of the return sums of `φ`.

Because `φ = (φ - P) + P` pointwise, the return sum of `φ` splits as the sum of
the two return sums, so the two estimates combine directly.

For an actual `C¹` mean-zero function the hypothesis `TrigApproxInVariation` is
exactly what the classical antiderivative-of-a-Fejér-approximation argument
supplies; proving it against the *abstract* variation functional carried by the
interface is deferred to a later module that fixes a concrete variation API.
-/

namespace CriticalMixedHRT

/-- A function `φ` can be approximated, in the (abstract) variation functional of
`D`, by mean-zero trigonometric polynomials: for every `ε > 0` there is a
mean-zero trigonometric polynomial `P = trigPoly a s` (`0 ∉ s`) such that the
remainder `φ - P` has bounded variation, zero mean, and
`variation (φ - P) < ε`. -/
def TrigApproxInVariation {θ : ℝ} (D : DenjoyKoksmaReturnData θ) (φ : ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (a : ℤ → ℂ) (s : Finset ℤ),
      (0 : ℤ) ∉ s ∧
      D.HasBV (fun x => φ x - trigPoly a s x) ∧
      D.mean (fun x => φ x - trigPoly a s x) = 0 ∧
      D.variation (fun x => φ x - trigPoly a s x) < ε

/-- **Uniform return sums from a Denjoy–Koksma interface and a variation
approximation.**

If `φ` can be approximated in variation by mean-zero trigonometric polynomials
(hypothesis `happrox`), then its continued-fraction return sums converge to `0`
uniformly:
`‖∑_{j<qₙ} φ(· - jθ)‖∞ → 0`. -/
theorem uniformReturn_of_trigApprox_DK
    {θ : ℝ} (D : DenjoyKoksmaReturnData θ) (hθ : Irrational θ)
    (φ : ℝ → ℂ) (happrox : TrigApproxInVariation D φ) :
    TendstoUniformly
      (fun n (x : ℝ) => ∑ j ∈ Finset.range (D.q n), φ ((x : ℝ) - j * θ))
      (fun _ => (0 : ℂ)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  -- Approximate φ by a mean-zero trig polynomial P with variation (φ - P) < ε/2.
  obtain ⟨a, s, hs, hBV, hmean, hvar⟩ := happrox (ε / 2) (by positivity)
  set P : ℝ → ℂ := fun x => trigPoly a s x with hP
  set g : ℝ → ℂ := fun x => φ x - P x with hg
  -- Stage 2A: the return sums of P converge to 0 uniformly.
  have hPtu := trigPoly_return_tendstoUniformly D.toRotationReturnData hθ a s hs
  rw [Metric.tendstoUniformly_iff] at hPtu
  -- Eventually, ‖∑ P(· - jθ)‖ < ε/2.
  filter_upwards [hPtu (ε / 2) (by positivity)] with n hn x
  -- The Denjoy–Koksma bound controls the remainder g = φ - P.
  have hdk := D.dk_bound g hBV hmean n x
  have hsplit :
      (∑ j ∈ Finset.range (D.q n), φ ((x : ℝ) - j * θ))
        = (∑ j ∈ Finset.range (D.q n), g ((x : ℝ) - j * θ))
          + ∑ j ∈ Finset.range (D.q n), P ((x : ℝ) - j * θ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [hg]
  have hPbound : ‖∑ j ∈ Finset.range (D.q n), P ((x : ℝ) - j * θ)‖ < ε / 2 := by
    have := hn x
    simpa [P, dist_eq_norm, zero_sub, norm_neg] using this
  have hgbound : ‖∑ j ∈ Finset.range (D.q n), g ((x : ℝ) - j * θ)‖ < ε / 2 :=
    lt_of_le_of_lt hdk hvar
  rw [dist_eq_norm, zero_sub, norm_neg, hsplit]
  calc
    ‖(∑ j ∈ Finset.range (D.q n), g ((x : ℝ) - j * θ))
        + ∑ j ∈ Finset.range (D.q n), P ((x : ℝ) - j * θ)‖
        ≤ ‖∑ j ∈ Finset.range (D.q n), g ((x : ℝ) - j * θ)‖
          + ‖∑ j ∈ Finset.range (D.q n), P ((x : ℝ) - j * θ)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hgbound hPbound
    _ = ε := by ring

/-- **C¹ zero-mean uniform return sums (conditional on variation approximation).**

This is the Stage 2B target in interface-complete form: for `φ` admitting a
mean-zero trigonometric-polynomial approximation in variation, the
continued-fraction return sums converge to `0` uniformly. For an actual C¹
mean-zero `φ` the approximation hypothesis is supplied by the classical Fejér /
antiderivative argument (deferred). -/
theorem c1_zeroMean_returnSum_tendstoUniformly
    {θ : ℝ} (D : DenjoyKoksmaReturnData θ) (hθ : Irrational θ)
    (φ : ℝ → ℂ) (happrox : TrigApproxInVariation D φ) :
    TendstoUniformly
      (fun n (x : ℝ) => ∑ j ∈ Finset.range (D.q n), φ ((x : ℝ) - j * θ))
      (fun _ => (0 : ℂ)) atTop :=
  uniformReturn_of_trigApprox_DK D hθ φ happrox

end CriticalMixedHRT
