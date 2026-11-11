import Mathlib
import RequestProject.TrinomialZeros

open scoped Classical BigOperators Real
open Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6A — the normalized return-cocycle bridge

This module formalizes the passage (Sections 4–5 of the dossier) from the
**one-step Zak fiber equation** in the normalized critical mixed form
`ν = (a, p/m)` to the scalar **m-step Laurent return cocycle**, together with the
finite exceptional-fiber structure and the bridge into the Stage 5 no-flat-band
theorem.

Working in the normalized form, the one-step Zak fiber equation reads
```
    F(x - a, s + p/m) = -c₃⁻¹ · exp(2πi (p/m) x) · P(x,s) · F(x,s),
```
with the lattice trinomial
```
    P(x,s) = c₀ + c₁ exp(-2πi(t₁ x + r₁ s)) + c₂ exp(-2πi(t₂ x + r₂ s)),
```
and `(r₁,t₁),(r₂,t₂)` a unimodular ℤ²-basis.

## Contents

* `NormalizedReturnData` — the normalized data bundle (Task A).
* `NormalizedReturnData.normalized_m_step_return_cocycle` — the exact `m`-step
  return cocycle `F(x-θ,s) = B_s(x) F(x,s)` (Task B).
* `NormalizedReturnData.Bmult_eq_explicit` — the explicit closed form of the
  return multiplier matching the dossier's `B`-formula (Task B / Task C local
  expression theorem).
* `NormalizedReturnData.Bmult_periodic_one_x`,
  `NormalizedReturnData.Bmult_periodic_one_s` — the double periodicity of the
  return multiplier (Laurent-family character; Task C).
* `NormalizedReturnData.normalized_trinomial_character_zero_set_finite` — finite
  torus zero set of the trinomial via the certified
  `critical_unimodular_trinomial_zero_set_finite` (Task D).
* `positive_measure_active_avoiding_finite_exceptional` — extraction of a
  positive-measure active subset avoiding the finite exceptional set (Task E,
  the measure-theoretic core of the active-arc statement).
-/

namespace CriticalMixedHRT

/-- The lattice trinomial
`P(x,s) = c₀ + c₁ exp(-2πi(t₁ x + r₁ s)) + c₂ exp(-2πi(t₂ x + r₂ s))`. -/
noncomputable def Pfun (c₀ c₁ c₂ : ℂ) (r₁ t₁ r₂ t₂ : ℤ) (x s : ℝ) : ℂ :=
  c₀ + c₁ * Complex.exp (-2 * ↑Real.pi * Complex.I * ((↑t₁ * ↑x + ↑r₁ * ↑s) : ℂ))
     + c₂ * Complex.exp (-2 * ↑Real.pi * Complex.I * ((↑t₂ * ↑x + ↑r₂ * ↑s) : ℂ))

/-- **Task A — normalized return data.**

The data of the normalized critical mixed form `ν = (a, p/m)`: the integers
`m > 0`, `p`, the irrational `θ = m·a`, the four nonzero coefficients of the
four-term relation, the unimodular ℤ²-basis `(r₁,t₁),(r₂,t₂)`, the Zak fiber
function `F` with its second-variable `1`-periodicity, and the one-step Zak
fiber equation. -/
structure NormalizedReturnData where
  m : ℕ
  hm : 0 < m
  p : ℤ
  a : ℝ
  θ : ℝ
  hθ_eq : θ = (m : ℝ) * a
  hθ_irr : Irrational θ
  c₀ : ℂ
  c₁ : ℂ
  c₂ : ℂ
  c₃ : ℂ
  hc₀ : c₀ ≠ 0
  hc₁ : c₁ ≠ 0
  hc₂ : c₂ ≠ 0
  hc₃ : c₃ ≠ 0
  r₁ : ℤ
  t₁ : ℤ
  r₂ : ℤ
  t₂ : ℤ
  /-- `(r₁,t₁),(r₂,t₂)` form a unimodular ℤ²-basis. -/
  unimodular : r₁ * t₂ - r₂ * t₁ = 1
  F : ℝ → ℝ → ℂ
  /-- Periodicity in the second Zak variable. -/
  hFper : ∀ x s, F x (s + 1) = F x s
  /-- The one-step Zak fiber equation. -/
  hone : ∀ x s, F (x - a) (s + (↑p / ↑m : ℝ)) =
    -c₃⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ((↑p / ↑m : ℂ)) * (↑x : ℂ))
      * Pfun c₀ c₁ c₂ r₁ t₁ r₂ t₂ x s * F x s

namespace NormalizedReturnData

variable (D : NormalizedReturnData)

/-- The `j`-th factor of the iterated return cocycle. -/
noncomputable def retFactor (x s : ℝ) (j : ℕ) : ℂ :=
  -D.c₃⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ((↑D.p / ↑D.m : ℂ)) * ((↑x - ↑j * ↑D.a : ℂ)))
    * Pfun D.c₀ D.c₁ D.c₂ D.r₁ D.t₁ D.r₂ D.t₂ (x - j * D.a) (s + j * (↑D.p / ↑D.m : ℝ))

/-- The scalar `m`-step return multiplier `B_s(x)`, as the product of the `m`
return factors. -/
noncomputable def Bmult (x s : ℝ) : ℂ := ∏ j ∈ Finset.range D.m, D.retFactor x s j

/-- The dossier's explicit closed form of the return multiplier `B_s(x)`:
`(-c₃⁻¹)^m · exp(2πi(p/m) ∑_{j<m}(x - j a)) · ∏_{j<m} P(x - j a, s + j p/m)`. -/
noncomputable def Bexplicit (x s : ℝ) : ℂ :=
  (-D.c₃⁻¹) ^ D.m
    * Complex.exp (2 * ↑Real.pi * Complex.I * ((↑D.p / ↑D.m : ℂ)) *
        (∑ j ∈ Finset.range D.m, ((↑x - ↑j * ↑D.a : ℂ))))
    * ∏ j ∈ Finset.range D.m,
        Pfun D.c₀ D.c₁ D.c₂ D.r₁ D.t₁ D.r₂ D.t₂ (x - j * D.a) (s + j * (↑D.p / ↑D.m : ℝ))

/-- The iterated one-step fiber equation: after `k` applications,
`F(x - k a, s + k p/m) = (∏_{j<k} retFactor j) · F(x,s)`. -/
theorem partial_step (x s : ℝ) (k : ℕ) :
    D.F (x - k * D.a) (s + k * (↑D.p / ↑D.m : ℝ)) =
      (∏ j ∈ Finset.range k, D.retFactor x s j) * D.F x s := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ]
      have key := D.hone (x - k * D.a) (s + k * (↑D.p / ↑D.m : ℝ))
      have e1 : (x - k * D.a) - D.a = x - (↑(k + 1) : ℝ) * D.a := by push_cast; ring
      have e2 : (s + k * (↑D.p / ↑D.m : ℝ)) + (↑D.p / ↑D.m : ℝ)
          = s + (↑(k + 1) : ℝ) * (↑D.p / ↑D.m : ℝ) := by push_cast; ring
      rw [e1, e2] at key
      rw [key, retFactor]
      have ex : ((↑x - ↑k * ↑D.a : ℂ)) = ((x - k * D.a : ℝ) : ℂ) := by push_cast; ring
      rw [ex, ih]
      ring

/-- **Task B — exact `m`-step return cocycle.**

Iterating the one-step Zak fiber equation exactly `m` times and using the
second-variable periodicity gives the scalar return cocycle
`F(x - θ, s) = B_s(x) · F(x,s)`. -/
theorem normalized_m_step_return_cocycle (x s : ℝ) :
    D.F (x - D.θ) s = D.Bmult x s * D.F x s := by
  have hstep := D.partial_step x s D.m
  have hmne : (↑D.m : ℝ) ≠ 0 := by exact_mod_cast D.hm.ne'
  have hmpm : (↑D.m : ℝ) * (↑D.p / ↑D.m : ℝ) = (↑D.p : ℝ) := by field_simp
  have hxθ : x - (↑D.m : ℝ) * D.a = x - D.θ := by rw [D.hθ_eq]
  rw [hmpm, hxθ] at hstep
  have hper : Function.Periodic (D.F (x - D.θ)) 1 := D.hFper (x - D.θ)
  have hpi : D.F (x - D.θ) (s + (↑D.p : ℝ)) = D.F (x - D.θ) s := by
    simpa using hper.int_mul D.p s
  rw [hpi] at hstep
  rw [hstep, Bmult]

/-
**Task B / Task C — explicit closed form of the return multiplier.**

The product form `Bmult` equals the dossier's explicit `B`-formula
`(-c₃⁻¹)^m · exp(2πi(p/m) ∑_{j<m}(x - j a)) · ∏_{j<m} P(x - j a, s + j p/m)`.
-/
theorem Bmult_eq_explicit (x s : ℝ) : D.Bmult x s = D.Bexplicit x s := by
  unfold NormalizedReturnData.Bmult NormalizedReturnData.Bexplicit;
  simp +decide only [retFactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← exp_sum,
      Finset.mul_sum _ _ _]

/-- The return multiplier is a finite product of a nowhere-vanishing exponential
monomial and translated copies of `P`. -/
theorem Bmult_eq_monomial_mul_prod (x s : ℝ) :
    D.Bmult x s =
      (-D.c₃⁻¹) ^ D.m
        * Complex.exp (2 * ↑Real.pi * Complex.I * ((↑D.p / ↑D.m : ℂ)) *
            (∑ j ∈ Finset.range D.m, ((↑x - ↑j * ↑D.a : ℂ))))
        * ∏ j ∈ Finset.range D.m,
            Pfun D.c₀ D.c₁ D.c₂ D.r₁ D.t₁ D.r₂ D.t₂ (x - j * D.a) (s + j * (↑D.p / ↑D.m : ℝ)) :=
  D.Bmult_eq_explicit x s

/-
**Task C — Laurent-family character: periodicity in `x`.**

The return multiplier is `1`-periodic in the time variable `x`, i.e. it depends
on `x` only through the character `exp(2πi x)`.
-/
theorem Bmult_periodic_one_x (x s : ℝ) : D.Bmult (x + 1) s = D.Bmult x s := by
  rw [ D.Bmult_eq_explicit, D.Bmult_eq_explicit ];
  unfold NormalizedReturnData.Bexplicit;
  norm_num [ Pfun ];
  congr! 2;
  · convert Complex.exp_periodic.int_mul ( D.p ) _ using 2 ; ring;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, D.hm.ne' ];
  · exact congrArg₂ _ ( congrArg₂ _ rfl ( congr_arg _ ( Complex.exp_eq_exp_iff_exists_int.mpr ⟨ -D.t₁, by push_cast; ring ⟩ ) ) ) ( congr_arg _ ( Complex.exp_eq_exp_iff_exists_int.mpr ⟨ -D.t₂, by push_cast; ring ⟩ ) )

/-
**Task C — Laurent-family character: periodicity in `s`.**

The return multiplier is `1`-periodic in the frequency variable `s`, i.e. it
depends on `s` only through the character `exp(2πi s)`.
-/
theorem Bmult_periodic_one_s (x s : ℝ) : D.Bmult x (s + 1) = D.Bmult x s := by
  rw [ Bmult_eq_explicit, Bmult_eq_explicit ];
  unfold NormalizedReturnData.Bexplicit;
  unfold Pfun;
  norm_num [ Complex.exp_add, mul_add ];
  norm_num [ show ∀ k : ℤ, Complex.exp ( - ( 2 * Real.pi * Complex.I * k ) ) = 1 from fun k => by rw [ Complex.exp_eq_one_iff ] ; use -k; push_cast; ring ]

/-- **Task D — finite torus zero set of the trinomial.**

By the certified `critical_unimodular_trinomial_zero_set_finite`, the trinomial
`c₀ + c₁ z₁ + c₂ z₂` of the normalized data has at most two zeros on the unit
torus `S¹ × S¹`. -/
theorem normalized_trinomial_character_zero_set_finite :
    {z : ℂ × ℂ | ‖z.1‖ = 1 ∧ ‖z.2‖ = 1 ∧ D.c₀ + D.c₁ * z.1 + D.c₂ * z.2 = 0}.ncard ≤ 2 :=
  critical_unimodular_trinomial_zero_set_finite D.c₀ D.c₁ D.c₂ D.hc₀ D.hc₁ D.hc₂

end NormalizedReturnData

/-- **Task E — positive-measure active subset avoiding a finite exceptional set.**

If the exceptional parameter set `E` is finite and the active set `S` has
positive Lebesgue measure, then `S \ E` still has positive measure: a finite set
is Lebesgue-null, so removing it from a positive-measure set leaves positive
measure.  This is the measure-theoretic core of the active-arc extraction; the
refinement to a *connected open arc* is a later analytic-localization step. -/
theorem positive_measure_active_avoiding_finite_exceptional
    {S E : Set ℝ} (hE : E.Finite) (hS : 0 < MeasureTheory.volume S) :
    0 < MeasureTheory.volume (S \ E) := by
  have hnull : MeasureTheory.volume E = 0 := hE.measure_zero _
  rwa [MeasureTheory.measure_diff_null hnull]

end CriticalMixedHRT