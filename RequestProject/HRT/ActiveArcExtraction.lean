import Mathlib
import RequestProject.HRT.NormalizedReturnCocycle

open scoped Classical BigOperators Real ENNReal
open MeasureTheory

set_option maxHeartbeats 1000000

/-!
# Part D — positive-measure active arc avoiding a finite exceptional set

This module extracts, from a positive-measure active parameter set `S` and a
finite exceptional set `E`, a positive-measure active subset disjoint from `E`,
and — strengthening this — a nonempty open interval `(a,b)` disjoint from `E` on
which `S` still has positive measure.

* `positive_measure_active_subset_avoiding_finite_exceptional` — the
  measure-theoretic core (a finite set is Lebesgue-null, so removing it from a
  positive-measure set leaves positive measure).
* `positive_measure_active_arc_avoiding_finite_exceptional` — the connected open
  interval form.
-/

namespace CriticalMixedHRT

/-- **Part D (subset form).**  If the exceptional parameter set `E` is finite and
the active set `S` has positive Lebesgue measure, then `S \ E` still has positive
measure. -/
theorem positive_measure_active_subset_avoiding_finite_exceptional
    {S E : Set ℝ} (hE : E.Finite) (hS : 0 < MeasureTheory.volume S) :
    0 < MeasureTheory.volume (S \ E) := by
  have hnull : MeasureTheory.volume E = 0 := hE.measure_zero _
  rwa [MeasureTheory.measure_diff_null hnull]

/-- Auxiliary: a positive-measure set `T` has positive measure inside some
bounded open interval `(-N, N)`. -/
theorem exists_bounded_arc_pos_measure
    {T : Set ℝ} (hT : 0 < MeasureTheory.volume T) :
    ∃ N : ℕ, 0 < MeasureTheory.volume (T ∩ Set.Ioo (-(N : ℝ)) N) := by
  by_contra h
  push_neg at h
  simp only [nonpos_iff_eq_zero] at h
  have hsub : T ⊆ ⋃ N : ℕ, T ∩ Set.Ioo (-(N : ℝ)) N := by
    intro x hx
    obtain ⟨N, hN⟩ := exists_nat_gt (|x|)
    refine Set.mem_iUnion.mpr ⟨N, hx, ?_⟩
    constructor
    · have := neg_abs_le x; nlinarith [abs_nonneg x]
    · have := le_abs_self x; nlinarith [abs_nonneg x]
  have hz : MeasureTheory.volume T = 0 :=
    measure_mono_null hsub (measure_iUnion_null (fun N => h N))
  rw [hz] at hT; exact lt_irrefl _ hT

/-
**Part D (arc form).**  If the exceptional parameter set `E` is finite and
the active set `S` has positive Lebesgue measure, then there is a nonempty open
interval `(a, b)`, disjoint from `E`, on which `S` still has positive measure.

Proof by induction on the finite set `E`: removing a point splits an interval
into two halves, one of which keeps positive measure.
-/
theorem positive_measure_active_arc_avoiding_finite_exceptional
    {S E : Set ℝ} (hE : E.Finite) (hS : 0 < MeasureTheory.volume S) :
    ∃ a b : ℝ, a < b ∧ Set.Ioo a b ∩ E = ∅ ∧
      0 < MeasureTheory.volume (S ∩ Set.Ioo a b) := by
  -- Strengthen the statement so the induction hypothesis is usable: prove the auxiliary claim that for any finite `E`, if `0 < volume (S \ E)` then there exist `a < b` with `Set.Ioo a b ∩ E = ∅` and `0 < volume (S ∩ Set.Ioo a b)`.
  have h_ind : ∀ (E : Finset ℝ), 0 < volume (S \ E) → ∃ a b : ℝ, a < b ∧ Set.Ioo a b ∩ E = ∅ ∧ 0 < volume (S ∩ Set.Ioo a b) := by
    intro E hE_pos
    induction' E using Finset.induction with e E ih;
    · obtain ⟨ N, hN ⟩ := exists_bounded_arc_pos_measure hS;
      exact ⟨ -N, N, by linarith [ show ( N : ℝ ) > 0 from Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hN ) ) ], by norm_num, hN ⟩;
    · obtain ⟨ a, b, hab, hE, hS ⟩ := ‹0 < volume ( S \ ↑E ) → _› ( by
        exact hE_pos.trans_le ( MeasureTheory.measure_mono <| by aesop_cat ) );
      by_cases he : e ∈ Set.Ioo a b;
      · -- Since $e \in (a, b)$, we can split $(a, b)$ into two intervals $(a, e)$ and $(e, b)$.
        have h_split : volume (S ∩ Set.Ioo a b) ≤ volume (S ∩ Set.Ioo a e) + volume (S ∩ Set.Ioo e b) := by
          have h_split : S ∩ Set.Ioo a b ⊆ (S ∩ Set.Ioo a e) ∪ (S ∩ Set.Ioo e b) ∪ {e} := by
            grind;
          refine' le_trans ( MeasureTheory.measure_mono h_split ) _;
          refine' le_trans ( MeasureTheory.measure_union_le _ _ ) _;
          exact le_trans ( add_le_add ( MeasureTheory.measure_union_le _ _ ) le_rfl ) ( by norm_num );
        by_cases h_case : volume (S ∩ Set.Ioo a e) > 0;
        · grind;
        · refine' ⟨ e, b, he.2, _, _ ⟩ <;> simp_all +decide [ Set.ext_iff ];
          · exact fun x hx₁ hx₂ => ⟨ by linarith, hE x ( by linarith ) ( by linarith ) ⟩;
          · exact lt_of_lt_of_le hS h_split;
      · grind;
  convert h_ind hE.toFinset _;
  · aesop;
  · rw [ MeasureTheory.measure_diff_null ] ; aesop;
    exact hE.toFinset.countable_toSet.measure_zero MeasureTheory.MeasureSpace.volume

end CriticalMixedHRT