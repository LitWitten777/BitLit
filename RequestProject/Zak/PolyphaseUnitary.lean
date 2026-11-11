import Mathlib
import RequestProject.Zak.L2Zak

open scoped Classical BigOperators Real
open Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — periodic gauge and pointwise unitarity of the polyphase fibre

The periodic Zak gauge `K_s(x) = e^{-2πi s x} F(x,s)` removes the
quasiperiodicity in the time variable, turning each Zak fibre into an honest
periodic function.  The polyphase (gauge) factor `e^{-2πi s x}` has modulus
`1`, so the gauge is *pointwise unitary*:

`‖K_s(x)‖ = ‖F(x,s)‖`.

Consequently the fibre `L²`-densities of `K` and of `F` coincide, which is what
lets the active-set defined through `K` be computed through the raw Zak transform
`F` (used in `FiberOperator.lean`).
-/

namespace CriticalMixedHRT

/-- The periodic Zak gauge `K_s(x) = e^{-2πi s x} F(x,s)`. -/
noncomputable def zakGauge (F : ℝ → ℝ → ℂ) (s x : ℝ) : ℂ :=
  Complex.exp (-2 * ↑Real.pi * Complex.I * (↑s : ℂ) * (↑x : ℂ)) * F x s

/-- The polyphase gauge factor has modulus one. -/
theorem norm_gauge_factor (s x : ℝ) :
    ‖Complex.exp (-2 * ↑Real.pi * Complex.I * (↑s : ℂ) * (↑x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have : (-2 * ↑Real.pi * Complex.I * (↑s : ℂ) * (↑x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

/-- Pointwise unitarity of the periodic gauge: `‖K_s(x)‖ = ‖F(x,s)‖`. -/
theorem norm_zakGauge (F : ℝ → ℝ → ℂ) (s x : ℝ) :
    ‖zakGauge F s x‖ = ‖F x s‖ := by
  rw [zakGauge, norm_mul, norm_gauge_factor, one_mul]

/-- The fibre `L²`-densities of `K_s` and of `F(·,s)` coincide:
`∫₀¹ ‖K_s(x)‖² dx = ∫₀¹ ‖F(x,s)‖² dx`. -/
theorem integral_norm_sq_zakGauge (F : ℝ → ℝ → ℂ) (s : ℝ) :
    (∫ x in (0:ℝ)..1, ‖zakGauge F s x‖ ^ 2) = ∫ x in (0:ℝ)..1, ‖F x s‖ ^ 2 := by
  apply intervalIntegral.integral_congr
  intro x _
  show ‖zakGauge F s x‖ ^ 2 = ‖F x s‖ ^ 2
  rw [norm_zakGauge]

end CriticalMixedHRT
