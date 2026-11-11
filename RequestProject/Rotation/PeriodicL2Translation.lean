import Mathlib
import RequestProject.Rotation.ReturnData
import RequestProject.Rotation.DenjoyKoksmaInterface

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

/-!
# Part A: strong continuity of periodic `L²` translations

This module proves the strong-continuity statement for translations on the
additive circle and transports it to real `1`-periodic functions, discharging
the `htrans` hypothesis of Stage 3A.

The architecture is:

1. `addCircle_translation_tendsto_eLpNorm` — strong continuity of translations
   on `L²(AddCircle 1)`, proved from the Mathlib continuity of the
   `DomAddAct`-action on `Lᵖ`.
2. `periodic_descent_apply` — a `1`-periodic function descends through the
   quotient map: `AddCircle.liftIoc 1 0 h (mk x) = h x`.
3. `periodic_eLpNorm_translation_tendsto` — the real-periodic interval version.
4. `periodic_eLpNorm_return_translation_tendsto` — the return-sequence
   specialization producing exactly the `htrans` form.
-/

namespace CriticalMixedHRT

/-
**Strong continuity of translations on `L²(AddCircle 1)`.**

If `H ∈ L²` over the Haar (probability) measure on `AddCircle 1` and
`t n → 0`, then `‖H(· - t n) - H‖₂ → 0`.
-/
theorem addCircle_translation_tendsto_eLpNorm
    (H : AddCircle (1 : ℝ) → ℂ)
    (hmem : MemLp H 2 (volume : Measure (AddCircle (1 : ℝ))))
    (t : ℕ → AddCircle (1 : ℝ)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto
      (fun n => eLpNorm (fun y => H (y - t n) - H y) 2
        (volume : Measure (AddCircle (1 : ℝ)))) atTop (𝓝 0) := by
  -- Apply the fact that the L^2 norm is continuous.
  have h_cont : Filter.Tendsto (fun n => eLpNorm (fun y => H (y - t n) - H y) 2 (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ)))) Filter.atTop (nhds 0) := by
    have h_cont : Filter.Tendsto (fun n => (DomAddAct.mk (-(t n)) : (AddCircle (1 : ℝ))ᵈᵃᵃ) +ᵥ hmem.toLp H) Filter.atTop (nhds (hmem.toLp H)) := by
      have h_strong_cont : Filter.Tendsto (fun n => (DomAddAct.mk (-(t n)) : (AddCircle (1 : ℝ))ᵈᵃᵃ)) Filter.atTop (nhds (DomAddAct.mk 0)) := by
        convert Filter.Tendsto.comp ( DomAddAct.mkHomeomorph.continuous.tendsto _ ) ( Filter.Tendsto.neg ht ) using 1;
        norm_num;
      -- Apply the continuity of the action.
      have h_cont : Continuous (fun g : (AddCircle (1 : ℝ))ᵈᵃᵃ => g +ᵥ (hmem.toLp H)) := by
        convert continuous_id.vadd continuous_const using 1;
        haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩; exact inferInstance;
      convert h_cont.continuousAt.tendsto.comp h_strong_cont using 1 ; aesop
    have h_cont : Filter.Tendsto (fun n => eLpNorm (fun y => (DomAddAct.mk (-(t n)) +ᵥ hmem.toLp H).1 y - H y) 2 (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ)))) Filter.atTop (nhds 0) := by
      convert Filter.Tendsto.comp ( show Filter.Tendsto ( fun f : Lp ℂ 2 volume => eLpNorm ( fun y => f y - H y ) 2 volume ) ( nhds ( hmem.toLp H ) ) ( nhds 0 ) from ?_ ) h_cont using 2 ; ring!;
      exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm (fun n => n) H hmem).mp fun ⦃U⦄ a => a
    refine' h_cont.congr' _;
    filter_upwards [ ] with n;
    rw [ eLpNorm_congr_ae ];
    have h_ae_eq : (DomAddAct.mk (-(t n)) +ᵥ hmem.toLp H) =ᵐ[volume] (fun y => H (-t n + y)) := by
      exact MeasureTheory.AEEqFun.coeFn_mk _ _ |> fun h => h.trans ( by filter_upwards [ hmem.coeFn_toLp ] with y hy; aesop );
    filter_upwards [ h_ae_eq ] with y hy using by rw [ hy ] ; simp +decide [ sub_eq_neg_add ] ;
  convert h_cont using 1

/-
A `1`-periodic function descends through the quotient map `ℝ → AddCircle 1`:
`AddCircle.liftIoc 1 0 h` composed with the quotient map is `h` itself.
-/
theorem periodic_descent_apply
    (h : ℝ → ℂ) (hper : Function.Periodic h 1) (x : ℝ) :
    AddCircle.liftIoc (1 : ℝ) 0 h ((x : AddCircle (1 : ℝ))) = h x := by
  rw [ AddCircle.liftIoc ];
  simp +decide [ AddCircle.equivIoc ];
  convert hper.int_mul ( toIocDiv ( show 0 < ( 1 : ℝ ) by norm_num ) 0 x ) x using 1 ; norm_num [ toIocMod ];
  convert hper.int_mul ( -toIocDiv ( show 0 < ( 1 : ℝ ) by norm_num ) 0 x ) x using 1 ; norm_num [ toIocDiv ] ; ring!;
  have := hper.int_mul ( toIocDiv ( show 0 < ( 1 : ℝ ) by norm_num ) 0 x ) x; aesop;

/-
**Real-periodic interval version of strong continuity of translations.**

For a measurable `1`-periodic `h` with `h ∈ L²` over one period `Ioc 0 1`, if a
real sequence `t n → 0`, then
`‖h(· - t n) - h‖₂ → 0` over `Ioc 0 1`.
-/
theorem periodic_eLpNorm_translation_tendsto
    (h : ℝ → ℂ) (hper : Function.Periodic h 1) (hmeas : Measurable h)
    (hmem : MemLp h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto
      (fun n => eLpNorm (fun x => h (x - t n) - h x) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
  -- Set `H := AddCircle.liftIoc 1 0 h`. Since `hmem : MemLp h 2 (volume.restrict (Ioc 0 1))` and `Ioc 0 1 = Ioc 0 (0+1)`, `MemLp.memLp_liftIoc` gives `hMH : MemLp H 2 (volume : Measure (AddCircle 1))`.
  set H : AddCircle (1 : ℝ) → ℂ := AddCircle.liftIoc (1 : ℝ) 0 h
  have hMH : MemLp H 2 (volume : Measure (AddCircle (1 : ℝ))) := by
    convert MeasureTheory.MemLp.memLp_liftIoc _;
    aesop;
  have h_claim : ∀ n : ℕ, eLpNorm (fun x => h (x - t n) - h x) 2 (volume.restrict (Set.Ioc 0 1)) = eLpNorm (fun y => H (y - (t n : AddCircle (1 : ℝ))) - H y) 2 volume := by
    intro n
    have h_eq : (fun x => h (x - t n) - h x) = (fun y => H (y - (t n : AddCircle (1 : ℝ))) - H y) ∘ (fun x : ℝ => (x : AddCircle (1 : ℝ))) := by
      ext x; simp [H, periodic_descent_apply];
      have := periodic_descent_apply h hper ( x - t n ) ; have := periodic_descent_apply h hper x; aesop;
    rw [ h_eq, eLpNorm_comp_measurePreserving ];
    · exact MeasureTheory.AEStronglyMeasurable.sub ( hMH.comp_measurePreserving ( MeasureTheory.measurePreserving_sub_right _ _ ) |> fun h => h.aestronglyMeasurable ) hMH.aestronglyMeasurable;
    · convert AddCircle.measurePreserving_mk 1 0 using 1;
      norm_num;
  convert addCircle_translation_tendsto_eLpNorm H hMH ( fun n => ( t n : AddCircle ( 1 : ℝ ) ) ) _ using 1;
  · exact funext h_claim;
  · convert Filter.Tendsto.comp ( continuous_quotient_mk'.tendsto 0 ) ht using 1

/-
**Return-sequence specialization (the `htrans` form).**

For a measurable `1`-periodic `h ∈ L²(Ioc 0 1)` and Denjoy–Koksma return data
`D` for `θ`, the return-time translations satisfy the exact `htrans`
conclusion required by
`measurable_cocycle_holonomy_quantized_of_periodic_log`.
-/
theorem periodic_eLpNorm_return_translation_tendsto
    {θ : ℝ} (D : DenjoyKoksmaReturnData θ)
    (h : ℝ → ℂ) (hper : Function.Periodic h 1) (hmeas : Measurable h)
    (hmem : MemLp h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    Tendsto
      (fun n => eLpNorm (fun x => h (x - (D.q n : ℝ) * θ) - h x) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) := by
  -- Apply the periodic_eLpNorm_translation_tendsto theorem.
  have h_periodic : ∀ n : ℕ, ∀ x : ℝ, h (x - (D.q n : ℝ) * θ) = h (x - ((D.q n : ℝ) * θ - (D.p n : ℝ)) - (D.p n : ℝ)) := by
    exact fun n x => congr_arg h ( by ring );
  convert periodic_eLpNorm_translation_tendsto h hper hmeas hmem ( fun n => ( D.q n : ℝ ) * θ - D.p n ) _ using 1;
  · ext n; congr; ext x; rw [ h_periodic n x ] ;
    exact congr_arg₂ _ ( by simpa using Function.Periodic.int_mul hper ( -D.p n ) ( x - ( D.q n * θ - D.p n ) ) ) rfl;
  · exact D.tendsto_return

end CriticalMixedHRT