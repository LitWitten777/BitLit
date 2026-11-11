import Mathlib
import RequestProject.Rotation.PhaseLiftWinding

open scoped Classical BigOperators Real
open MeasureTheory Filter Topology Complex

/-!
# Stage 3B: measurable winding obstruction — winding-number wrapper

This module records the winding-number formulation of the measurable winding
obstruction proved (in phase-lift conditional form) in `PhaseLiftWinding`.

For a phase `ψ(x) = b(x)/‖b(x)‖ = exp(2πi (d x + g x))` with `g` `1`-periodic,
the **winding number** of the loop `x ↦ ψ(x)` over one period is exactly the
integer `d`: the periodic remainder `g` contributes nothing to the net winding,
so `wind ψ = d`.  Hence `measurable_cocycle_winding_eq_zero_of_phase_lift`
(which proves `d = 0`) is precisely the statement `wind ψ = 0`.

Mathlib does not currently provide a winding-number API in the exact form needed
to *identify* `wind ψ` with the phase-lift degree `d` directly; that
identification (`wind ψ = d` from the periodic phase lift) is the remaining
adapter, documented here as the next task.  We record the obstruction in
winding-number form below, taking the (geometrically evident) identification
`wind = d` as the explicit interface hypothesis, so that the conclusion
`wind = 0` is available to downstream assembly without any axiom. -/

namespace CriticalMixedHRT

/-- **Measurable winding obstruction (winding-number form).**

Under the hypotheses of `measurable_cocycle_winding_eq_zero_of_phase_lift`, and
given the identification of the geometric winding number `wind` of the phase
`ψ(x) = exp(2πi(d x + g x))` with the phase-lift degree `d` (the interface
hypothesis `hwind : wind = d`, valid because `g` is periodic), the winding
number vanishes: `wind = 0`. -/
theorem measurable_cocycle_winding_eq_zero
    {θ : ℝ} (hθ : Irrational θ) (D : DenjoyKoksmaReturnData θ)
    (u : ℝ → ℂ) (hu_meas : Measurable u) (hu1 : ∀ x, ‖u x‖ = 1)
    (d : ℤ) (g : ℝ → ℝ)
    (hstep : ∀ x, u (x - θ)
        = Complex.exp (2 * π * Complex.I * ((d : ℂ) * (x : ℂ) + (g x : ℂ))) * u x)
    (htrans : Tendsto
        (fun n => eLpNorm (fun x => u (x - (D.q n : ℝ) * θ) - u x) 2
            (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0))
    (hosc : d ≠ 0 →
        Tendsto (fun n => ∫ x in Set.Ioc (0 : ℝ) 1,
            Complex.exp (2 * π * Complex.I * windingPhase d g θ (D.q n) x))
          atTop (𝓝 0))
    (wind : ℤ) (hwind : wind = d) :
    wind = 0 := by
  rw [hwind]
  exact measurable_cocycle_winding_eq_zero_of_phase_lift hθ D u hu_meas hu1 d g
    hstep htrans hosc

end CriticalMixedHRT
