import Mathlib
import RequestProject.Rotation.HolonomyQuantization
import RequestProject.Rotation.PeriodicL2Translation
import RequestProject.Rotation.HolonomyZeroMeanBridge

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

/-!
# Part C: unconditional Stage 3A (modulo the Denjoy–Koksma interface)

We remove the explicit `htrans` (L² translation continuity) and `hRe` (zero real
holonomy mean) hypotheses from Stage 3A, deriving them from periodicity via the
Part A strong-continuity theorem and the Part B zero-mean bridge.

The only remaining conditional input is the existing Denjoy–Koksma /
variation-approximation interface (`DenjoyKoksmaReturnData` and
`TrigApproxInVariation`).
-/

namespace CriticalMixedHRT

/-- **Stage 3A, periodic form.**

Same conclusion as `measurable_cocycle_holonomy_quantized_of_periodic_log`, but
with the `htrans` and `hRe` hypotheses replaced by periodicity of `h`, `b`,
`ell`, measurability and periodic-`L²` of `h`, the cocycle relation, the
periodic logarithm, and the Stage 2B variation-approximation hypothesis.
The auxiliary facts that `b` is `1`-periodic and non-vanishing are derived from
`exp (ell x) = b x` together with periodicity of `ell`. -/
theorem measurable_cocycle_holonomy_quantized_periodic
    {θ : ℝ} (hθ : Irrational θ) (D : DenjoyKoksmaReturnData θ)
    (h b ell : ℝ → ℂ)
    (hh_meas : Measurable h) (hh_per : Function.Periodic h 1)
    (hell_meas : Measurable ell) (hell_per : Function.Periodic ell 1)
    (hell_int : Integrable ell (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hmem : MemLp h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hpos : eLpNorm h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ 0)
    (hcocycle : ∀ x, h (x - θ) = b x * h x)
    (hlog : ∀ x, Complex.exp (ell x) = b x)
    (happrox : TrigApproxInVariation D
        (fun x => ell x - ∫ y in Set.Ioc (0 : ℝ) 1, ell y)) :
    Tendsto (fun n => Complex.exp (∫ y in Set.Ioc (0 : ℝ) 1, ell y) ^ (D.q n))
        atTop (𝓝 1) := by
  have hb_ne : ∀ x, b x ≠ 0 := fun x => by rw [← hlog x]; exact Complex.exp_ne_zero _
  have hb_per : Function.Periodic b 1 := by
    intro x; rw [← hlog (x + 1), ← hlog x, hell_per x]
  have hRe : (∫ y in Set.Ioc (0 : ℝ) 1, ell y).re = 0 :=
    periodic_log_integral_re_eq_zero_of_cocycle hθ h b ell hh_meas hh_per hpos
      hb_per hb_ne hell_meas hell_per hell_int hlog hcocycle
  have htrans := periodic_eLpNorm_return_translation_tendsto D h hh_per hh_meas hmem
  exact measurable_cocycle_holonomy_quantized_of_periodic_log hθ D h b ell hell_meas
    hmem hpos hcocycle hlog hRe happrox htrans

/-- **Resonance-group corollary, periodic form.**

Under the hypotheses of `measurable_cocycle_holonomy_quantized_periodic`, the
holonomy `H = exp (∫₀¹ ell)` lies in the resonance group `resonanceGroupC D.q`. -/
theorem measurable_cocycle_holonomy_resonant_periodic
    {θ : ℝ} (hθ : Irrational θ) (D : DenjoyKoksmaReturnData θ)
    (h b ell : ℝ → ℂ)
    (hh_meas : Measurable h) (hh_per : Function.Periodic h 1)
    (hell_meas : Measurable ell) (hell_per : Function.Periodic ell 1)
    (hell_int : Integrable ell (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hmem : MemLp h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hpos : eLpNorm h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ 0)
    (hcocycle : ∀ x, h (x - θ) = b x * h x)
    (hlog : ∀ x, Complex.exp (ell x) = b x)
    (happrox : TrigApproxInVariation D
        (fun x => ell x - ∫ y in Set.Ioc (0 : ℝ) 1, ell y)) :
    Complex.exp (∫ y in Set.Ioc (0 : ℝ) 1, ell y) ∈ resonanceGroupC D.q := by
  have hRe : (∫ y in Set.Ioc (0 : ℝ) 1, ell y).re = 0 := by
    have hb_ne : ∀ x, b x ≠ 0 := fun x => by rw [← hlog x]; exact Complex.exp_ne_zero _
    have hb_per : Function.Periodic b 1 := by
      intro x; rw [← hlog (x + 1), ← hlog x, hell_per x]
    exact periodic_log_integral_re_eq_zero_of_cocycle hθ h b ell hh_meas hh_per hpos
      hb_per hb_ne hell_meas hell_per hell_int hlog hcocycle
  refine ⟨by norm_num [Complex.norm_exp, hRe], ?_⟩
  exact measurable_cocycle_holonomy_quantized_periodic hθ D h b ell hh_meas hh_per
    hell_meas hell_per hell_int hmem hpos hcocycle hlog happrox

end CriticalMixedHRT
