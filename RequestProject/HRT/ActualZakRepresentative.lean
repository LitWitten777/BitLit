import Mathlib
import RequestProject.Zak.ConcreteZakDense
import RequestProject.Zak.ConcreteZakPlancherel
import RequestProject.Zak.ZakFubiniRegularity
import RequestProject.HRT.FiberOperator

open scoped Classical BigOperators Real ENNReal
open Complex MeasureTheory

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the actual concrete Zak representative (Tasks B / D)

This module records, for the **actual** concrete dense-class Zak transform
`concreteZakDense f` (the genuine Zak transform `Zf(x,s) = ∑' k, f(x+k) e^{-2πiks}`
of a bounded measurable window `f` supported in `[0,N)`), the representative-level
facts requested by Tasks B and D.  These are the honest, *non-zero-fibre* analytic
ingredients of a `NontrivialAEFiberExtraction`:

* `actual_zak_representative_periodic_s` — `1`-periodicity in the frequency
  variable `s` (Task B);
* `actual_zak_representative_fiberDensity_integrable` — interval-integrability of
  the fibre density `s ↦ ∫₀¹ ‖Zf(x,s)‖² dx` (Task B);
* `actual_zak_total_fiber_mass_eq_norm_sq` — the Zak/Plancherel total-mass
  identity `∫₀¹ fiberDensity (Zf) s ds = ∫_ℝ ‖f‖²` (Task D), the honest tie
  between total fibre mass and the window's `L²`-mass that forbids the `F = 0`
  witness;
* `actual_zak_active_set_positive_of_nonzero_window` — positive-measure active
  fibres for a nonzero window (Task D).

All four are unconditional (no `sorry`, no `axiom`): they are thin wrappers around
the already-proven concrete results `concreteZakDense_periodic_s`,
`concrete_fiberDensity_integrable`, `concreteZakDense_plancherel`, and
`concrete_active_set_positive_measure`.  They work **a.e.**/at the
representative level and never use the zero fibre function.
-/

namespace CriticalMixedHRT

/-- **Task B — frequency-periodicity of the actual Zak representative.**

The concrete dense-class Zak transform is `1`-periodic in the frequency variable
`s`: `Zf(x, s+1) = Zf(x, s)` for every `x, s`.  (Holds pointwise, hence a.e.) -/
theorem actual_zak_representative_periodic_s (f : ℝ → ℂ) (x s : ℝ) :
    concreteZakDense f x (s + 1) = concreteZakDense f x s :=
  concreteZakDense_periodic_s f x s

/-- **Task B — interval-integrability of the actual Zak fibre density.**

For a bounded measurable window `f` supported in `[0,N)`, the fibre density
`s ↦ ∫₀¹ ‖Zf(x,s)‖² dx` of the concrete dense-class Zak transform is
interval-integrable on `[0,1]`. -/
theorem actual_zak_representative_fiberDensity_integrable (N : ℕ) (f : ℝ → ℂ)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → f t = 0)
    (hmeas : Measurable f)
    (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    IntervalIntegrable (fiberDensity (concreteZakDense f)) volume 0 1 :=
  concrete_fiberDensity_integrable N f hsupp hmeas hbdd

/-- **Task D — total fibre mass equals the window `L²`-mass (Zak/Plancherel).**

For a bounded measurable window `f` supported in `[0,N)`, the total fibre mass of
the concrete dense-class Zak transform equals the window's `L²`-mass:
`∫₀¹ fiberDensity (Zf) s ds = ∫_ℝ ‖f‖²`.  This is the honest Plancherel tie that
forbids the degenerate `F = 0` extraction. -/
theorem actual_zak_total_fiber_mass_eq_norm_sq (N : ℕ) (f : ℝ → ℂ)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → f t = 0)
    (hmeas : Measurable f)
    (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    (∫ s in (0:ℝ)..1, fiberDensity (concreteZakDense f) s) = ∫ t, ‖f t‖ ^ 2 := by
  unfold fiberDensity
  exact concreteZakDense_plancherel N f hsupp hmeas hbdd

/-- **Task D — positive-measure active fibres from a nonzero window.**

For a bounded measurable window `f` supported in `[0,N)` with positive `L²`-mass,
the active fibre set `{s : 0 < ∫₀¹ ‖Zf(x,s)‖² dx}` of the concrete dense-class Zak
transform has positive Lebesgue measure. -/
theorem actual_zak_active_set_positive_of_nonzero_window (N : ℕ) (f : ℝ → ℂ)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → f t = 0)
    (hmeas : Measurable f)
    (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hf : 0 < ∫ t, ‖f t‖ ^ 2) :
    0 < MeasureTheory.volume (activeSet (concreteZakDense f) ∩ Set.Ioc (0:ℝ) 1) :=
  concrete_active_set_positive_measure N f hsupp hmeas hbdd hf

end CriticalMixedHRT
