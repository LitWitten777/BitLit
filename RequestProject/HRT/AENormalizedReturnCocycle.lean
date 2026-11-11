import Mathlib
import RequestProject.HRT.NormalizedReturnCocycle
import RequestProject.HRT.FiberOperator
import RequestProject.HRT.NontrivialAEFiberExtraction

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B (a.e. refactor) — the a.e.-level normalized return cocycle

This module introduces the **almost-everywhere** analogue of
`NormalizedReturnData`.  Whereas `NormalizedReturnData` carries the one-step Zak
fibre equation `F(x-a, s+p/m) = … · F(x,s)` for *every* `(x,s)`, the structure
`AENormalizedReturnData` only asks the one-step equation to hold for **almost
every** `s` and, for each such `s`, **almost every** `x`.  This is the honest
output of applying an `L²` isometry to a four-term HRT relation: the relation
between `L²` classes descends only to an a.e. equality of representatives.

The previous run had to upgrade the a.e. one-step equation to a pointwise one
(`StandardPointwiseFiberUpgradeTheorem`), which is *too strong* for arbitrary
`L²` quotient data.  Here we avoid that upgrade entirely by iterating the
one-step equation **a.e.**:

* `ae_shift_real` — translation invariance of the a.e. filter on `ℝ`.
* `AENormalizedReturnData.ae_partial_step` — the a.e. `k`-fold iterate.
* `AENormalizedReturnData.ae_normalized_m_step_return_cocycle` — the a.e. `m`-step
  return cocycle `F(x-θ,s) = B_s(x) F(x,s)`.

The active-fibre positivity (`h_active_pos`) and the genuine a.e. one-step
equation forbid the degenerate `F = 0` witness, so this structure is honest.
No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/

namespace CriticalMixedHRT

/-
**Translation invariance of the a.e. filter on `ℝ`.**

If a predicate holds for almost every real number, it holds for almost every
real number after a fixed translation.
-/
theorem ae_shift_real {c : ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ x ∂(volume : Measure ℝ), P x) :
    ∀ᵐ x ∂(volume : Measure ℝ), P (x + c) := by
  rw [ MeasureTheory.ae_iff ] at *;
  rw [ ← MeasureTheory.measure_preimage_add_right ];
  swap;
  exacts [ -c, by simpa using h ]

/-- **Task B (a.e.) — a.e.-level normalized return data.**

The almost-everywhere analogue of `NormalizedReturnData`: the algebraic data of
the normalized critical mixed form together with a fibre function `F` whose
one-step Zak fibre equation holds **almost everywhere** (`hone_ae`) and whose
active fibre set carries positive measure (`h_active_pos`), forbidding the
degenerate `F = 0` witness. -/
structure AENormalizedReturnData where
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
  /-- Periodicity in the second Zak variable (holds pointwise). -/
  hFper : ∀ x s, F x (s + 1) = F x s
  /-- The one-step Zak fibre equation, holding **a.e. in `s`, then a.e. in `x`**. -/
  hone_ae : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
    oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ F x s
  /-- The active fibre set carries positive measure (forbids `F = 0`). -/
  h_active_pos : 0 < MeasureTheory.volume (activeSet F ∩ Set.Ioc (0 : ℝ) 1)

namespace AENormalizedReturnData

variable (D : AENormalizedReturnData)

/-- The `j`-th factor of the iterated return cocycle (same closed form as in the
pointwise `NormalizedReturnData`). -/
noncomputable def retFactor (x s : ℝ) (j : ℕ) : ℂ :=
  -D.c₃⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ((↑D.p / ↑D.m : ℂ)) * ((↑x - ↑j * ↑D.a : ℂ)))
    * Pfun D.c₀ D.c₁ D.c₂ D.r₁ D.t₁ D.r₂ D.t₂ (x - j * D.a) (s + j * (↑D.p / ↑D.m : ℝ))

/-- The scalar `m`-step return multiplier `B_s(x)`, as the product of the `m`
return factors. -/
noncomputable def Bmult (x s : ℝ) : ℂ := ∏ j ∈ Finset.range D.m, D.retFactor x s j

/-- **The degenerate dummy pointwise return data.**

A `NormalizedReturnData` carrying the *same algebraic data* as `D` (so the same
`θ`, the same irrationality witness `hθ_irr`, …) but with the trivial fibre
function `F = 0`.  The pointwise one-step equation holds for `F = 0` because both
sides vanish.  This is used **only** to plumb `D.θ`/`D.hθ_irr` into the Stage 5
no-flat-band bridge, whose statement does not depend on the fibre function at all;
the genuine fibre content of `D` lives in `hone_ae`/`h_active_pos` and in the a.e.
iteration lemmas below. -/
noncomputable def toDummyNormalized : NormalizedReturnData where
  m := D.m
  hm := D.hm
  p := D.p
  a := D.a
  θ := D.θ
  hθ_eq := D.hθ_eq
  hθ_irr := D.hθ_irr
  c₀ := D.c₀
  c₁ := D.c₁
  c₂ := D.c₂
  c₃ := D.c₃
  hc₀ := D.hc₀
  hc₁ := D.hc₁
  hc₂ := D.hc₂
  hc₃ := D.hc₃
  r₁ := D.r₁
  t₁ := D.t₁
  r₂ := D.r₂
  t₂ := D.t₂
  unimodular := D.unimodular
  F := fun _ _ => 0
  hFper := fun _ _ => rfl
  hone := by intro x s; simp

/-- The dummy normalized data has the same `θ` as `D` (definitionally). -/
@[simp] theorem toDummyNormalized_θ : D.toDummyNormalized.θ = D.θ := rfl

/-- The dummy normalized data's return multiplier agrees with `D.Bmult`
(both depend only on the shared algebraic data, not on the fibre function). -/
theorem toDummyNormalized_Bmult (x s : ℝ) :
    D.toDummyNormalized.Bmult x s = D.Bmult x s := rfl

/-
**Task C (a.e.) — a.e. iterate of the one-step equation.**

After `k` a.e. applications of the one-step Zak fibre equation, for almost every
`s` and (for each such `s`) almost every `x`,
`F(x - k a, s + k p/m) = (∏_{j<k} retFactor x s j) · F(x,s)`.
-/
theorem ae_partial_step (k : ℕ) :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
      D.F (x - k * D.a) (s + k * (↑D.p / ↑D.m : ℝ)) =
        (∏ j ∈ Finset.range k, D.retFactor x s j) * D.F x s := by
  have := @ae_shift_real;
  induction' k with k ih <;> simp_all +decide [ Finset.prod_range_succ ];
  have hshift : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ), oneStepEquation D.m D.p D.a D.c₀ D.c₁ D.c₂ D.c₃ D.r₁ D.t₁ D.r₂ D.t₂ D.F (x - k * D.a) (s + k * (D.p / D.m)) := by
    exact Filter.Eventually.mono ( this D.hone_ae ) fun s hs => Filter.Eventually.mono ( this hs ) fun x hx => by simpa using hx;
  filter_upwards [ ih, hshift ] with s hs hs' ; filter_upwards [ hs, hs' ] with x hx hx' ; simp_all +decide [ oneStepEquation ] ; ring;
  convert hx' using 1 <;> push_cast [ AENormalizedReturnData.retFactor ] <;> ring

/-
**Task C (a.e.) — the a.e. `m`-step return cocycle.**

Iterating the one-step Zak fibre equation `m` times a.e. and using the
(pointwise) second-variable periodicity gives the scalar return cocycle
`F(x - θ, s) = B_s(x) · F(x,s)` for almost every `s` and almost every `x`.
-/
theorem ae_normalized_m_step_return_cocycle :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
      D.F (x - D.θ) s = D.Bmult x s * D.F x s := by
  convert D.ae_partial_step D.m using 3;
  simp +decide [ D.hθ_eq, mul_div_cancel₀, D.hm.ne' ];
  ext x; rw [ show D.F ( x - ↑D.m * D.a ) ( _ + ↑D.p ) = D.F ( x - ↑D.m * D.a ) _ from by simpa using Function.Periodic.int_mul ( D.hFper ( x - ↑D.m * D.a ) ) D.p _ ] ;
  rfl

end AENormalizedReturnData

end CriticalMixedHRT