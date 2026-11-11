import Mathlib
import RequestProject.Zak.ConcreteZakDense

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the concrete dense test subspace of `L²(ℝ)`

TASK B of the a.e.-Zak rewiring run.  The honest a.e.-level Zak model
(`l2ZakModelAE_of_dense_data`) consumes a **dense `ℂ`-submodule** `D` of
`Lp ℂ 2 volume`, closed under the time-frequency shift, on which the concrete
Zak transform is a densely-defined isometry.

This module supplies that submodule concretely as the class of (`L²`-classes of)
**continuous, compactly supported** functions `ℝ → ℂ`.  This is the natural test
class for the concrete Zak transform `concreteZakDense`:

* it is genuinely a `ℂ`-submodule of `Lp ℂ 2 volume`
  (`concreteZakDenseSubspace`);
* it is **dense** in `L²(ℝ)` (`concreteZakDenseSubspace_dense`), via Mathlib's
  `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`;
* its representatives are closed under the time-frequency shift `shiftFun`
  (`concreteZakDenseSubspace_closed_under_shift`) and under pure modulation
  (`concreteZakDenseSubspace_closed_under_modulation`);
* each member has a continuous compactly supported representative, to which the
  finite-support Plancherel identity `concreteZakDense_plancherel` applies
  (`concreteZakDenseSubspace_to_fun`).
-/

namespace CriticalMixedHRT

/-- The membership predicate of the concrete dense test subspace: an `L²`-class
`f` belongs iff it has a continuous, compactly supported representative. -/
def IsCcSupp (f : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  ∃ g : ℝ → ℂ, Continuous g ∧ HasCompactSupport g ∧ (f : ℝ → ℂ) =ᵐ[volume] g

/-- The `ℂ`-submodule of `L²(ℝ) = Lp ℂ 2 volume` of classes with a continuous,
compactly supported representative. -/
def concreteZakDenseSubspace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) where
  carrier := {f | IsCcSupp f}
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁c, hg₁s, hf₁⟩ ⟨g₂, hg₂c, hg₂s, hf₂⟩
    refine ⟨g₁ + g₂, hg₁c.add hg₂c, hg₁s.add hg₂s, ?_⟩
    filter_upwards [Lp.coeFn_add f₁ f₂, hf₁, hf₂] with x hx hx₁ hx₂
    rw [hx]; simp [hx₁, hx₂]
  zero_mem' := by
    refine ⟨0, continuous_const, HasCompactSupport.zero, ?_⟩
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with x hx
    rw [hx]
  smul_mem' := by
    rintro c f ⟨g, hgc, hgs, hf⟩
    refine ⟨c • g, hgc.const_smul c, hgs.smul_left, ?_⟩
    filter_upwards [Lp.coeFn_smul c f, hf] with x hx hx₁
    simp [hx, hx₁]

theorem mem_concreteZakDenseSubspace_iff (f : Lp ℂ 2 (volume : Measure ℝ)) :
    f ∈ concreteZakDenseSubspace ↔ IsCcSupp f := Iff.rfl

/-- Every member of the dense subspace has a continuous compactly supported
representative (the test class on which the concrete Zak Plancherel identity
holds). -/
theorem concreteZakDenseSubspace_to_fun (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : f ∈ concreteZakDenseSubspace) :
    ∃ g : ℝ → ℂ, Continuous g ∧ HasCompactSupport g ∧ (f : ℝ → ℂ) =ᵐ[volume] g := hf

/-
**TASK B (density).** The continuous compactly supported classes are dense in
`L²(ℝ)`.
-/
theorem concreteZakDenseSubspace_dense :
    Dense (concreteZakDenseSubspace : Set (Lp ℂ 2 (volume : Measure ℝ))) := by
  refine' fun f => Metric.mem_closure_iff.2 fun ε hε => _;
  -- Apply Mathlib's `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` to `f`'s `MemLp` (from `Lp.memLp f`): it yields `g : ℝ → ℂ` with `HasCompactSupport g`, `eLpNorm (f - g) 2 volume ≤ ε`, `Continuous g`, and `MemLp g 2 volume`.
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℂ, HasCompactSupport g ∧ eLpNorm ( (f : ℝ → ℂ) - g ) 2 volume ≤ ENNReal.ofReal (ε / 2) ∧ Continuous g ∧ MemLp g 2 volume := by
    convert MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le ( show 2 ≠ ∞ by norm_num ) ( MeasureTheory.Lp.memLp f ) ( show ENNReal.ofReal ( ε / 2 ) ≠ 0 by positivity ) using 1;
  refine' ⟨ hg.2.2.2.toLp g, _, _ ⟩ <;> norm_num at *;
  · exact ⟨ g, hg.2.2.1, hg.1, by simpa using hg.2.2.2.coeFn_toLp ⟩;
  · convert lt_of_le_of_lt ( ENNReal.toReal_mono _ hg.2.1 ) _ using 1;
    · rw [ MeasureTheory.Lp.dist_def ];
      rw [ MeasureTheory.eLpNorm_congr_ae ];
      filter_upwards [ hg.2.2.2.coeFn_toLp ] with x hx using by aesop;
    · norm_num;
    · rw [ ENNReal.toReal_ofReal ] <;> linarith

/-
**TASK B (shift closure).** If `g` is continuous with compact support then so
is its time-frequency shift `shiftFun a b g`; hence the `L²`-class of the shifted
representative again lies in the dense subspace.
-/
theorem concreteZakDenseSubspace_closed_under_shift (a b : ℝ) (g : ℝ → ℂ)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Continuous (shiftFun a b g) ∧ HasCompactSupport (shiftFun a b g) := by
  refine' ⟨ _, _ ⟩;
  · exact Continuous.mul ( Complex.continuous_exp.comp <| by continuity ) <| hgc.comp <| by continuity;
  · have h_compact_support : HasCompactSupport (fun t => g (t - a)) := by
      convert hgs.comp_homeomorph ( Homeomorph.subRight a ) using 1;
    exact HasCompactSupport.mul_left h_compact_support

/-- **TASK B (modulation closure).** Pure modulation `shiftFun 0 b` preserves
continuity and compact support. -/
theorem concreteZakDenseSubspace_closed_under_modulation (b : ℝ) (g : ℝ → ℂ)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Continuous (shiftFun 0 b g) ∧ HasCompactSupport (shiftFun 0 b g) :=
  concreteZakDenseSubspace_closed_under_shift 0 b g hgc hgs

end CriticalMixedHRT