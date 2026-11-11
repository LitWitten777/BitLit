import Mathlib
import RequestProject.Rotation.MeasurableWinding

open scoped Classical BigOperators Real
open MeasureTheory Filter Topology Complex

/-!
# Winding-number adapter (Run C, Task 2)

The measurable winding obstruction `measurable_cocycle_winding_eq_zero_of_phase_lift`
(Stage 3B) proves that the *phase-lift degree* `d` vanishes.  This module relates
that integer to an honest **winding number**, defined here by the standard
contour integral
```
  windingNumberIntegral b = (2πi)⁻¹ ∫₀¹ b'(x)/b(x) dx,
```
and provides public wrappers stated in winding-number language.

The key analytic identification proved here, `windingNumberIntegral_eq_of_phase_lift`,
is that for a genuinely `C¹` phase lift `b(x) = exp(2πi(d x + g(x)))` with `g`
real-valued and `1`-periodic, the contour integral equals `d`:
```
  windingNumberIntegral b = d,
```
because `b'/b = 2πi(d + g')` and `∫₀¹ g' = g(1) - g(0) = 0`.  This is exactly
the statement "`d` is the winding number of the loop".

The public obstruction wrapper `measurable_cocycle_winding_eq_zero_public` then
concludes `wind = 0` once `wind` is identified with the phase-lift degree `d`,
the standard (documented) identification.
-/

namespace CriticalMixedHRT

/-- The **winding number** of a (nonvanishing, `C¹`) loop `b`, defined by the
standard contour integral `(2πi)⁻¹ ∫₀¹ b'(x)/b(x) dx`. -/
noncomputable def windingNumberIntegral (b : ℝ → ℂ) : ℂ :=
  (2 * π * Complex.I)⁻¹ * ∫ x in (0 : ℝ)..1, deriv b x / b x

/-
**The contour winding number equals the phase-lift degree.**

If `b(x) = exp(2πi(d x + g(x)))` for a real `1`-periodic `C¹` remainder `g`
(`g 1 = g 0`, with continuous derivative `g'`), then
`windingNumberIntegral b = d`.
-/
theorem windingNumberIntegral_eq_of_phase_lift
    (b : ℝ → ℂ) (d : ℤ) (g g' : ℝ → ℝ)
    (hlift : ∀ x, b x = Complex.exp (2 * π * Complex.I * ((d : ℂ) * (x : ℂ) + (g x : ℂ))))
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg'cont : Continuous g')
    (hper : g 1 = g 0) :
    windingNumberIntegral b = (d : ℂ) := by
  -- By definition of $b$, we know that its derivative is $b'(x) = 2\pi i (d + g'(x)) b(x)$.
  have hb' : ∀ x, deriv b x = 2 * Real.pi * Complex.I * ((d : ℂ) + (g' x : ℂ)) * b x := by
    rw [ show b = _ from funext hlift ] ; intro x; erw [ HasDerivAt.deriv ( HasDerivAt.comp x ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul _ <| HasDerivAt.add ( HasDerivAt.const_mul _ <| hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) <| HasDerivAt.ofReal_comp <| hg x ) ) ] ; ring;
    norm_num ; ring;
  -- Substitute hb' into the integral.
  have h_integral : ∫ x in (0 : ℝ)..1, deriv b x / b x = ∫ x in (0 : ℝ)..1, 2 * Real.pi * Complex.I * ((d : ℂ) + (g' x : ℂ)) := by
    refine' intervalIntegral.integral_congr fun x _ => _;
    rw [ hb', mul_div_cancel_right₀ _ ( by rw [ hlift ] ; exact Complex.exp_ne_zero _ ) ];
  -- Evaluate the integral $\int_0^1 (d + g'(x)) \, dx$.
  have h_integral_eval : ∫ x in (0 : ℝ)..1, (d : ℂ) + (g' x : ℂ) = (d : ℂ) := by
    rw [ intervalIntegral.integral_add ] <;> norm_num;
    · rw [ intervalIntegral.integral_ofReal ];
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      exacts [ g, by norm_num [ hper ], fun x hx => hg x, hg'cont.intervalIntegrable _ _ ];
    · exact Continuous.intervalIntegrable ( by continuity ) _ _;
  unfold windingNumberIntegral; rw [ h_integral, intervalIntegral.integral_const_mul, h_integral_eval ] ; ring ; norm_num [ Real.pi_ne_zero, Complex.I_ne_zero ] ;
  norm_num [ mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero ]

/-- **Public measurable winding obstruction (winding-number form).**

Restates `measurable_cocycle_winding_eq_zero_of_phase_lift` in winding-number
language: for a measurable unit-modulus `1`-periodic cocycle `u` with phase-lift
degree `d`, given the standard identification of the winding number `wind` with
`d` (`hwind`), the winding number vanishes. -/
theorem measurable_cocycle_winding_eq_zero_public
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
    wind = 0 :=
  measurable_cocycle_winding_eq_zero hθ D u hu_meas hu1 d g hstep htrans hosc wind hwind

end CriticalMixedHRT