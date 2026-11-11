import Mathlib
import RequestProject.Rotation.FourierReturnSums
import RequestProject.Rotation.DenjoyKoksmaPeriodicDischarge
import RequestProject.Analytic.JointPeriodicLog
import RequestProject.HRT.NormalizedReturnCocycle

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

/-!
# Task C — `1`-periodicity adapters for the functions fed to periodic Denjoy–Koksma

The corrected periodic Denjoy–Koksma interface (`RealDenjoyKoksmaPeriodic θ` and
`DenjoyKoksmaReturnData.ofPeriodicDK`) only applies its estimate to `1`-periodic
functions: the `HasBV` predicate of `ofPeriodicDK` is
`ConcreteHasBV g ∧ Function.Periodic g 1`.  For the corrected endpoints to be
genuinely (non-vacuously) usable, the functions that the Denjoy–Koksma estimate
is actually applied to must be shown `1`-periodic.

This module collects the narrow periodicity adapters required, reusing existing
ingredients:

* `trigPoly_periodic_one` — finite trigonometric polynomials are `1`-periodic;
* `periodic_log_remainder_periodic` — the trig-approximation remainder
  `φ - trigPoly a s` is `1`-periodic when `φ` is (the function fed to
  `TrigApproxInVariation`);
* `holonomy_return_function_periodic` — the return multiplier `Bmult` is
  `1`-periodic in the time variable (from
  `NormalizedReturnData.Bmult_periodic_one_x`);
* `return_log_zero_mean_function_periodic` — the joint periodic logarithm
  produced by `analytic_zero_winding_log_on_cylinder` is `1`-periodic in the
  circle variable (re-export).

No broad new analytic facts are proved here; each lemma is a thin adapter over an
already-established result.
-/

namespace CriticalMixedHRT

/-- A finite trigonometric polynomial `∑_{k ∈ s} a_k e^{2πi k x}` is `1`-periodic:
each Fourier mode has period `1` (because `e^{2πi k}=1` for integer `k`). -/
theorem trigPoly_periodic_one (a : ℤ → ℂ) (s : Finset ℤ) :
    Function.Periodic (trigPoly a s) 1 := by
  intro x
  unfold trigPoly
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  have hx : ((x + 1 : ℝ) : ℂ) = (x : ℂ) + 1 := by push_cast; ring
  rw [hx, mul_add, mul_one, Complex.exp_add]
  have : Complex.exp (2 * π * Complex.I * (k : ℂ)) = 1 := by
    rw [show (2 * π * Complex.I * (k : ℂ)) = (k : ℂ) * (2 * π * Complex.I) by ring]
    rw [Complex.exp_int_mul]
    simp [Complex.exp_two_pi_mul_I]
  rw [this, mul_one]

/-- **Periodicity of the trig-approximation remainder.**

If `φ` is `1`-periodic, then the trigonometric-approximation remainder
`x ↦ φ x - trigPoly a s x` is `1`-periodic.  This is exactly the periodicity
side-condition needed to verify the `HasBV` field of
`DenjoyKoksmaReturnData.ofPeriodicDK` for the remainder functions appearing in
`TrigApproxInVariation`. -/
theorem periodic_log_remainder_periodic {φ : ℝ → ℂ} (hφ : Function.Periodic φ 1)
    (a : ℤ → ℂ) (s : Finset ℤ) :
    Function.Periodic (fun x => φ x - trigPoly a s x) 1 :=
  hφ.sub (trigPoly_periodic_one a s)

/-- **Periodicity of the return-multiplier holonomy function.**

The scalar return multiplier `Bmult x s`, as a function of the time variable `x`
(for a fixed circle parameter `s`), is `1`-periodic.  This is a restatement of
`NormalizedReturnData.Bmult_periodic_one_x` in `Function.Periodic` form, the form
required to feed the periodic Denjoy–Koksma interface. -/
theorem holonomy_return_function_periodic (D : NormalizedReturnData) (s : ℝ) :
    Function.Periodic (fun x => D.Bmult x s) 1 := by
  intro x
  exact D.Bmult_periodic_one_x x s

/-- **Periodicity of the return-multiplier function in the circle variable.**

The scalar return multiplier `Bmult x s`, as a function of the circle variable
`s` (for a fixed time `x`), is `1`-periodic
(`NormalizedReturnData.Bmult_periodic_one_s`). -/
theorem holonomy_return_function_periodic_s (D : NormalizedReturnData) (x : ℝ) :
    Function.Periodic (fun s => D.Bmult x s) 1 := by
  intro s
  exact D.Bmult_periodic_one_s x s

/-- **Periodicity of the joint periodic logarithm (return-log zero-mean function).**

For a nonvanishing, `C¹`, `1`-periodic, analytically zero-winding family `A`, the
joint periodic logarithm produced by `analytic_zero_winding_log_on_cylinder`
satisfies `exp (ell s x) = A s x` and is `1`-periodic in the circle variable `x`
for every `s`.  This re-exports the periodicity conclusion in the precise form
needed by the periodic Denjoy–Koksma / holonomy chain. -/
theorem return_log_zero_mean_function_periodic
    (A A' : ℝ → ℝ → ℂ)
    (hderiv : ∀ s x, HasDerivAt (A s) (A' s x) x)
    (hA'cont : ∀ s, Continuous (A' s))
    (hne : ∀ s x, A s x ≠ 0)
    (hper : ∀ s, Function.Periodic (A s) 1)
    (hwind : ∀ s, ∫ x in (0 : ℝ)..1, A' s x / A s x = 0) :
    ∃ ell : ℝ → ℝ → ℂ,
      (∀ s x, Complex.exp (ell s x) = A s x) ∧
      (∀ s, Function.Periodic (ell s) 1) := by
  obtain ⟨ell, hexp, hper_ell, _⟩ :=
    analytic_zero_winding_log_on_cylinder A A' hderiv hA'cont hne hper hwind
  exact ⟨ell, hexp, hper_ell⟩

end CriticalMixedHRT
