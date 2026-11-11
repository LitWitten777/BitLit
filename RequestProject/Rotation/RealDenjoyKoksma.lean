import Mathlib
import RequestProject.Rotation.DenjoyKoksmaDischarge

/-!
# Real Denjoy–Koksma: faithfulness analysis of the `dk_real` interface

This module performs the real-Denjoy–Koksma combinatorics analysis requested by
the run.  Its first, decisive contribution is a *no-`sorry`* proof that the
`dk_real` field of `CriticalMixedHRT.RealDenjoyKoksma` — and hence the entire
`RealDenjoyKoksma θ` structure — is **unsatisfiable as stated**.

The reason is a missing periodicity hypothesis.  The field reads
```
dk_real : ∀ h : ℝ → ℝ, ConcreteHasBVReal h → periodMeanReal h = 0 →
  ∀ (n : ℕ) (x : ℝ),
    |∑ j ∈ Finset.range (q n), h (x - j θ)| ≤ concreteVariationReal h
```
Here `ConcreteHasBVReal h` and `concreteVariationReal h` only constrain `h` on
`[0,1]`, and `periodMeanReal h` only integrates over `[0,1]`, yet the Birkhoff
sum evaluates `h` at the arbitrary real points `x - j θ`.  Choosing `h` to vanish
on `[0,1]` (so it has zero variation and zero mean there) but to be nonzero at a
point outside `[0,1]` produces a Birkhoff sum exceeding the variation bound `0`.

The classical Denjoy–Koksma theorem is true only for **1-periodic** functions;
the existing field omits periodicity and is therefore false.  We prove this
rigorously below (`dk_real_predicate_false`, `realDenjoyKoksma_isEmpty`).

The corrected, faithful interface and the reduction of the genuine (periodic)
real Denjoy–Koksma inequality to the continued-fraction *star-discrepancy*
combinatorics are developed in
`RequestProject.Rotation.OrbitPartition` and
`RequestProject.Rotation.ContinuedFractionTowers`.
-/

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

namespace CriticalMixedHRT

/-- A test function vanishing on `[0,1]` but equal to `1` at the point `2`. -/
noncomputable def dkTestFun : ℝ → ℝ := fun y => if y = (2 : ℝ) then 1 else 0

theorem dkTestFun_eq_zero_on {y : ℝ} (hy : y ≤ 1) : dkTestFun y = 0 := by
  unfold dkTestFun
  rw [if_neg (by intro h; rw [h] at hy; norm_num at hy)]

theorem dkTestFun_two : dkTestFun 2 = 1 := by
  unfold dkTestFun; rw [if_pos rfl]

theorem dkTestFun_nonneg (y : ℝ) : 0 ≤ dkTestFun y := by
  unfold dkTestFun; split <;> norm_num

/-
The test function has zero concrete variation (it vanishes on `[0,1]`).
-/
theorem concreteVariationReal_dkTestFun : concreteVariationReal dkTestFun = 0 := by
  unfold concreteVariationReal;
  rw [ eVariationOn.eq_of_eqOn ];
  rotate_right;
  exact fun _ => 0;
  · norm_num [ eVariationOn ];
  · exact fun x hx => dkTestFun_eq_zero_on hx.2

/-
The test function has zero concrete bounded variation (it vanishes on `[0,1]`).
-/
theorem concreteHasBVReal_dkTestFun : ConcreteHasBVReal dkTestFun := by
  refine' ne_of_lt ( lt_of_le_of_lt ( iSup_le _ ) _ );
  exact 0;
  · simp +decide [ dkTestFun ];
    grind;
  · norm_num

/-
The test function has zero period mean (it vanishes on `(0,1]`).
-/
theorem periodMeanReal_dkTestFun : periodMeanReal dkTestFun = 0 := by
  exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx => dkTestFun_eq_zero_on hx.2

/-
**The `dk_real` predicate (without periodicity) is false.**

For any rotation number `θ`, denominator sequence `q`, and index `n` with
`0 < q n`, the real Denjoy–Koksma inequality fails for the test function
`dkTestFun` at `x = 2`: its full-period Birkhoff sum is `≥ 1` while its concrete
variation is `0`.
-/
theorem dk_real_predicate_false (θ : ℝ) (q : ℕ → ℕ) (n : ℕ) (hn : 0 < q n) :
    ¬ (∀ h : ℝ → ℝ, ConcreteHasBVReal h → periodMeanReal h = 0 →
        ∀ (x : ℝ),
          |∑ j ∈ Finset.range (q n), h (x - (j : ℝ) * θ)|
            ≤ concreteVariationReal h) := by
  push_neg;
  refine' ⟨ dkTestFun, _, _, 2, _ ⟩ <;> norm_num [ concreteHasBVReal_dkTestFun, periodMeanReal_dkTestFun, concreteVariationReal_dkTestFun ];
  refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x _ => _ ) ( Finset.mem_range.mpr hn ) ) );
  · norm_num [ dkTestFun ];
  · exact dkTestFun_nonneg _

/-
**The existing `RealDenjoyKoksma θ` structure is uninhabitable.**

Because its `dk_real` field is the false (non-periodic) Denjoy–Koksma predicate,
no term of type `RealDenjoyKoksma θ` can exist, for any `θ`.  Consequently every
theorem of the previous discharge run that is conditional on a `RealDenjoyKoksma`
hypothesis is vacuously conditional, and a faithful (periodic) reformulation is
required.
-/
theorem realDenjoyKoksma_isEmpty (θ : ℝ) : IsEmpty (RealDenjoyKoksma θ) := by
  constructor;
  intro S
  apply dk_real_predicate_false θ S.toRotationReturnData.q 0 (S.toRotationReturnData.q_pos 0);
  exact fun h hbv hmean x => S.dk_real h hbv hmean 0 x

end CriticalMixedHRT