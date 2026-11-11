import Mathlib
import RequestProject.Rotation.ContinuedFractionTowers
import RequestProject.Rotation.OrbitPartition

/-!
# Koksma's inequality and the corrected periodic Denjoy–Koksma estimate

The corrected periodic real Denjoy–Koksma field
`RealDenjoyKoksmaPeriodic.dk_real_periodic` (see
`RequestProject.Rotation.OrbitPartition`) is the classical periodic
Denjoy–Koksma inequality.  Classically it follows from the purely combinatorial
orbit star-discrepancy bound `|#{j<Q : fract(x-jθ) ≤ t} − Q·t| ≤ 1`
(`StandardRealDenjoyKoksmaCombinatorics.star_discrepancy_le_one`) via **Koksma's
inequality**.

This module proves Koksma's inequality (`koksma_real_periodic`), via the
elementary order-statistic / interval-localization argument:

* sort the `Q` fractional parts `y_j = fract(x-jθ)` into `z_0 ≤ … ≤ z_{Q-1}`;
* the discrepancy bound localizes the `k`-th order statistic: `z_k ∈ [k/Q,(k+1)/Q]`;
* on each interval `I_k = [k/Q,(k+1)/Q]`, `|h(z_k) − Q∫_{I_k} h| ≤ Var(h; I_k)`;
* summing and using additivity of the variation over the partition gives the bound.

The result discharges the periodic DK estimate `dk_real_periodic` modulo the
single remaining combinatorial input `StandardRealDenjoyKoksmaCombinatorics`
(the three-gap star-discrepancy bound for continued-fraction denominators), via
the constructor `RealDenjoyKoksmaPeriodic.ofCombinatorics`.
-/

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

namespace CriticalMixedHRT

/-! ## Supporting lemmas -/

/-
A function of bounded variation on `[0,1]` is interval-integrable on `[0,1]`.
(`BoundedVariationOn` ⟹ difference of monotone ⟹ interval-integrable.)
-/
theorem bv_intervalIntegrable {h : ℝ → ℝ} (hbv : ConcreteHasBVReal h) :
    IntervalIntegrable h volume 0 1 := by
  obtain ⟨ p, q, hp, hq, h_eq ⟩ := ( show ∃ p q : ℝ → ℝ, MonotoneOn p ( Set.Icc 0 1 ) ∧ MonotoneOn q ( Set.Icc 0 1 ) ∧ h = p - q from by
                                      have h_locally_bounded_variation : LocallyBoundedVariationOn h (Set.Icc 0 1) :=
                                        BoundedVariationOn.locallyBoundedVariationOn hbv
                                      have := h_locally_bounded_variation.exists_monotoneOn_sub_monotoneOn; aesop; );
  rw [ h_eq ];
  rw [ intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one ];
  exact ( hp.integrableOn_isCompact ( CompactIccSpace.isCompact_Icc ) ) |> fun h => h.sub ( hq.integrableOn_isCompact ( CompactIccSpace.isCompact_Icc ) )

/-
Additivity of the extended variation over two adjacent closed intervals.
-/
theorem eVar_Icc_add (h : ℝ → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    eVariationOn h (Set.Icc a b) + eVariationOn h (Set.Icc b c)
      = eVariationOn h (Set.Icc a c) := by
  have := @eVariationOn.Icc_add_Icc;
  simpa using this h hab hbc ( Set.mem_univ b )

/-
Telescoping additivity of the extended variation over a monotone partition.
-/
theorem eVar_sum_adjacent (h : ℝ → ℝ) (a : ℕ → ℝ) (ha : Monotone a) (n : ℕ) :
    ∑ k ∈ Finset.range n, eVariationOn h (Set.Icc (a k) (a (k + 1)))
      = eVariationOn h (Set.Icc (a 0) (a n)) := by
  induction' n with n ih;
  · simp +decide [ eVariationOn.subsingleton ];
  · rw [ Finset.sum_range_succ, ih, eVar_Icc_add _ ( ha n.zero_le ) ( ha n.le_succ ) ]

/-
For a monotone tuple `z`, the set `{i : z i ≤ t}` is an initial segment:
`z k ≤ t` iff `k` is below the count of indices with value `≤ t`.
-/
theorem monotone_filter_card_iff {Q : ℕ} (z : Fin Q → ℝ) (hz : Monotone z) (t : ℝ)
    (k : Fin Q) :
    z k ≤ t ↔ (k : ℕ) < (Finset.univ.filter (fun i => z i ≤ t)).card :=
  (Tuple.lt_card_le_iff_apply_le_of_monotone hz).symm

/-
Counting is invariant under reindexing by a permutation.
-/
theorem filter_card_perm {Q : ℕ} (σ : Equiv.Perm (Fin Q)) (p : Fin Q → Prop)
    [DecidablePred p] :
    (Finset.univ.filter (fun i => p (σ i))).card
      = (Finset.univ.filter p).card := by
  rw [ Finset.card_filter, Finset.card_filter ];
  conv_rhs => rw [ ← Equiv.sum_comp σ ] ;

/-
**Order-statistic localization.**  Given a monotone enumeration `z` of `Q`
points in `[0,1)` whose counting function satisfies the unit star-discrepancy
bound, the `k`-th order statistic lies in `[k/Q, (k+1)/Q]`.
-/
theorem koksma_order_stat {Q : ℕ} (hQ : 0 < Q) (z : Fin Q → ℝ) (hz : Monotone z)
    (hzmem : ∀ k, z k ∈ Set.Ico (0 : ℝ) 1)
    (hdisc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |((Finset.univ.filter (fun i => z i ≤ t)).card : ℝ) - (Q : ℝ) * t| ≤ 1)
    (k : Fin Q) :
    z k ∈ Set.Icc ((k : ℕ) / (Q : ℝ)) (((k : ℕ) + 1) / (Q : ℝ)) := by
  constructor <;> contrapose! hdisc;
  · -- Let $t = z k$.
    use z k;
    -- Since $z$ is monotone, the set $\{i \mid z_i \leq z_k\}$ contains at least the first $k+1$ elements.
    have h_card : (Finset.univ.filter (fun i => z i ≤ z k)).card ≥ k + 1 := by
      refine' le_trans _ ( Finset.card_mono <| show Finset.Iic k ⊆ Finset.filter ( fun i => z i ≤ z k ) Finset.univ from fun i hi => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hz <| Finset.mem_Iic.mp hi ⟩ ) ; aesop;
    exact ⟨ ⟨ hzmem k |>.1, hzmem k |>.2.le ⟩, by rw [ abs_of_nonneg ] <;> nlinarith [ show ( Finset.card ( Finset.filter ( fun i => z i ≤ z k ) Finset.univ ) : ℝ ) ≥ k + 1 by exact_mod_cast h_card, show ( Q : ℝ ) > 0 by positivity, mul_div_cancel₀ ( k : ℝ ) ( by positivity : ( Q : ℝ ) ≠ 0 ) ] ⟩;
  · -- Choose $t$ such that $\frac{k+1}{Q} < t < z_k$.
    obtain ⟨t, ht⟩ : ∃ t : ℝ, (k + 1 : ℝ) / Q < t ∧ t < z k ∧ t ∈ Set.Icc 0 1 := by
      exact ⟨ ( ( k + 1 ) / Q + z k ) / 2, by linarith, by linarith, ⟨ by linarith [ show ( 0 : ℝ ) ≤ ( k + 1 ) / Q by positivity ], by linarith [ Set.mem_Ico.mp ( hzmem k ) ] ⟩ ⟩;
    -- Since $t < z_k$, we have $C(t) \leq k$.
    have hCt_le_k : (Finset.univ.filter (fun i => z i ≤ t)).card ≤ k := by
      have hCt_le_k : ∀ i : Fin Q, z i ≤ t → i.val < k := by
        exact fun i hi => lt_of_not_ge fun hi' => by linarith [ hz hi' ] ;
      exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun i => z i ≤ t ) Finset.univ ⊆ Finset.Iio k from fun i hi => Finset.mem_Iio.mpr ( hCt_le_k i <| Finset.mem_filter.mp hi |>.2 ) ) ) ( by simpa );
    refine' ⟨ t, ht.2.2, _ ⟩;
    rw [ abs_of_nonpos ] <;> nlinarith [ show ( Finset.card ( Finset.filter ( fun i => z i ≤ t ) Finset.univ ) : ℝ ) ≤ k from mod_cast hCt_le_k, show ( Q : ℝ ) > 0 by positivity, mul_div_cancel₀ ( ( k : ℝ ) + 1 ) ( by positivity : ( Q : ℝ ) ≠ 0 ) ]

/-
**Per-interval Koksma bound.**  On the interval `I = [k/Q,(k+1)/Q]` (length
`1/Q`), for any point `zk ∈ I`, the deviation of `h zk` from the (scaled) mean of
`h` over `I` is bounded by the variation of `h` over `I`.
-/
theorem koksma_interval_bound {h : ℝ → ℝ} (hbv : ConcreteHasBVReal h)
    (hint : IntervalIntegrable h volume 0 1)
    {Q : ℕ} (hQ : 0 < Q) {k : ℕ} (hk : k < Q) {zk : ℝ}
    (hzk : zk ∈ Set.Icc ((k : ℝ) / (Q : ℝ)) (((k : ℝ) + 1) / (Q : ℝ))) :
    |h zk - (Q : ℝ) * ∫ t in ((k : ℝ) / (Q : ℝ))..(((k : ℝ) + 1) / (Q : ℝ)), h t|
      ≤ (eVariationOn h (Set.Icc ((k : ℝ) / (Q : ℝ)) (((k : ℝ) + 1) / (Q : ℝ)))).toReal := by
  have h_bound : ∀ t ∈ Set.Icc ((k : ℝ) / Q) (((k : ℝ) + 1) / Q), |h zk - h t| ≤ (eVariationOn h (Set.Icc ((k : ℝ) / Q) (((k : ℝ) + 1) / Q))).toReal := by
    intro t ht;
    convert ENNReal.toReal_mono _ ( eVariationOn.edist_le h hzk ht ) using 1;
    exact ne_of_lt ( lt_of_le_of_lt ( eVariationOn.mono _ <| Set.Icc_subset_Icc ( by positivity ) <| by rw [ div_le_iff₀ <| by positivity ] ; norm_cast ; linarith ) <| lt_top_iff_ne_top.mpr hbv );
  have h_integral_bound : |∫ t in ((k : ℝ) / Q)..(((k : ℝ) + 1) / Q), (h zk - h t)| ≤ (eVariationOn h (Set.Icc ((k : ℝ) / Q) (((k : ℝ) + 1) / Q))).toReal * ((k + 1 : ℝ) / Q - (k : ℝ) / Q) := by
    rw [ intervalIntegral.integral_of_le ( by gcongr ; linarith ) ];
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
    refine' fun t => ( eVariationOn h ( Set.Icc ( k / Q : ℝ ) ( ( k + 1 ) / Q : ℝ ) ) |> ENNReal.toReal );
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
    · norm_num;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using h_bound t <| Set.Ioc_subset_Icc_self ht;
    · norm_num [ mul_comm, add_div, hQ.ne' ];
  rw [ intervalIntegral.integral_sub ] at h_integral_bound <;> norm_num at *;
  · rw [ abs_le ] at *;
    field_simp at *;
    grind;
  · apply_rules [ IntervalIntegrable.mono_set, Set.Icc_subset_Icc ] <;> norm_num;
    · exact ⟨ by positivity, by positivity ⟩;
    · exact ⟨ div_le_one_of_le₀ ( mod_cast hk.le ) ( by positivity ), div_le_one_of_le₀ ( mod_cast by linarith ) ( by positivity ) ⟩

/-
**Integral split** over the uniform partition of `[0,1]` into `Q` pieces.
-/
theorem koksma_integral_split {h : ℝ → ℝ} (hint : IntervalIntegrable h volume 0 1)
    {Q : ℕ} (hQ : 0 < Q) :
    (Q : ℝ) * ∫ t in (0 : ℝ)..1, h t
      = ∑ j ∈ Finset.range Q, (Q : ℝ) * ∫ t in ((j : ℝ) / (Q : ℝ))..(((j : ℝ) + 1) / (Q : ℝ)), h t := by
  rw [ ← Finset.mul_sum _ _ _, eq_comm ];
  have := @intervalIntegral.sum_integral_adjacent_intervals;
  convert congr_arg ( fun x : ℝ => ( Q : ℝ ) * x ) ( @this ℝ _ _ h volume ( fun k => ( k : ℝ ) / Q ) Q _ ) using 1 <;> norm_num [ hQ.ne' ];
  intro k hk; convert ‹IntervalIntegrable h volume 0 1›.mono_set _ using 1; (
  rw [ Set.uIcc_of_le ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith ), Set.uIcc_of_le ( by norm_num ) ] ; exact Set.Icc_subset_Icc ( by positivity ) ( by rw [ div_le_iff₀ ( by positivity ) ] ; norm_cast ; linarith ) ;);

/-
**Variation sum** over the uniform partition equals the total variation.
-/
theorem koksma_var_sum {h : ℝ → ℝ} (hbv : ConcreteHasBVReal h) {Q : ℕ} (hQ : 0 < Q) :
    ∑ j ∈ Finset.range Q,
        (eVariationOn h (Set.Icc ((j : ℝ) / (Q : ℝ)) (((j : ℝ) + 1) / (Q : ℝ)))).toReal
      = concreteVariationReal h := by
  have h_sum : ∑ j ∈ Finset.range Q, eVariationOn h (Set.Icc (j / Q : ℝ) ((j + 1) / Q : ℝ)) = eVariationOn h (Set.Icc 0 1) := by
    convert eVar_sum_adjacent h ( fun j => ( j : ℝ ) / Q ) _ Q using 1 <;> norm_num [ hQ.ne' ];
    exact fun i j hij => div_le_div_of_nonneg_right ( Nat.cast_le.mpr hij ) ( Nat.cast_nonneg _ );
  rw [ ← ENNReal.toReal_sum, h_sum ];
  · rfl;
  · intro j hj; exact ne_of_lt ( lt_of_le_of_lt ( eVariationOn.mono _ <| Set.Icc_subset_Icc ( by positivity ) <| by rw [ div_le_iff₀ <| by positivity ] ; norm_cast ; linarith [ Finset.mem_range.mp hj ] ) <| lt_top_iff_ne_top.mpr hbv ) ;

/-! ## The general Koksma inequality -/

/-
**General Koksma inequality** for a finite point set in `[0,1)`.

If `y : Fin Q → ℝ` is a family of points in `[0,1)` whose orbit counting function
satisfies the unit star-discrepancy bound `|#{k : y k ≤ t} − Q·t| ≤ 1` for all
`t ∈ [0,1]`, then for every bounded-variation `h`,
`|∑_k h(y_k) − Q·∫₀¹ h| ≤ Var(h; [0,1])`.
-/
theorem koksma_general {Q : ℕ} (hQ : 0 < Q) (y : Fin Q → ℝ)
    (hy : ∀ k, y k ∈ Set.Ico (0 : ℝ) 1)
    {h : ℝ → ℝ} (hbv : ConcreteHasBVReal h)
    (hdisc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |((Finset.univ.filter (fun k => y k ≤ t)).card : ℝ) - (Q : ℝ) * t| ≤ 1) :
    |(∑ k, h (y k)) - (Q : ℝ) * ∫ t in (0 : ℝ)..1, h t| ≤ concreteVariationReal h := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin Q), Monotone (fun k => y (σ k)) := by
    exact ⟨ Tuple.sort y, Tuple.monotone_sort y ⟩;
  -- Apply the Koksma inequality to the sorted sequence $z = y \circ \sigma$.
  have h_koksma_sorted : |∑ k : Fin Q, h (y (σ k)) - (Q : ℝ) * ∫ t in (0 : ℝ)..1, h t| ≤ ∑ k : Fin Q, (eVariationOn h (Set.Icc ((k : ℝ) / Q) (((k : ℝ) + 1) / Q))).toReal := by
    have h_koksma_sorted : ∀ k : Fin Q, |h (y (σ k)) - (Q : ℝ) * ∫ t in ((k : ℝ) / Q)..(((k : ℝ) + 1) / Q), h t| ≤ (eVariationOn h (Set.Icc ((k : ℝ) / Q) (((k : ℝ) + 1) / Q))).toReal := by
      intro k
      have h_order_stat : y (σ k) ∈ Set.Icc ((k : ℝ) / Q) (((k : ℝ) + 1) / Q) := by
        apply koksma_order_stat hQ (fun k => y (σ k)) hσ (fun k => hy (σ k)) (fun t ht => by
          convert hdisc t ht using 1;
          rw [ Finset.card_filter, Finset.card_filter ];
          rw [ Equiv.sum_comp σ fun i => if y i ≤ t then 1 else 0 ]) k;
      apply koksma_interval_bound hbv (bv_intervalIntegrable hbv) hQ k.isLt h_order_stat;
    convert Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun i _ => h_koksma_sorted i using 2;
    rw [ Finset.sum_sub_distrib, ← Finset.mul_sum _ _ _, koksma_integral_split ( bv_intervalIntegrable hbv ) hQ ];
    norm_num [ Finset.mul_sum _ _ _, Finset.sum_range ];
  convert h_koksma_sorted using 1;
  · rw [ Equiv.sum_comp σ fun k => h ( y k ) ];
  · convert koksma_var_sum hbv hQ |> Eq.symm using 1;
    rw [ Finset.sum_range ]

/-! ## Connecting to the orbit discrepancy -/

/-
The orbit count equals the cardinality of the corresponding `Fin Q` filter.
-/
theorem orbitCount_eq_fin_card (θ : ℝ) (Q : ℕ) (x t : ℝ) :
    orbitCount θ Q x t
      = (Finset.univ.filter (fun k : Fin Q => Int.fract (x - (k : ℕ) * θ) ≤ t)).card := by
  refine' Finset.card_bij _ _ _ _;
  use fun a ha => ⟨ ⌊a⌋₊, by
    rw [ Nat.floor_lt' ] <;> aesop ⟩
  all_goals generalize_proofs at *;
  · aesop;
  · simp +zetaDelta at *;
  · intro b hb; use b; aesop;

/-
**Koksma's inequality (periodic real form).**

From the orbit star-discrepancy bound `|orbitDiscrepancy θ Q x t| ≤ 1`, the
periodic real Denjoy–Koksma inequality follows for every `1`-periodic,
bounded-variation, zero-mean function `h`.
-/
theorem koksma_real_periodic {θ : ℝ} (Q : ℕ) (x : ℝ)
    (hdisc : ∀ t ∈ Set.Icc (0 : ℝ) 1, |orbitDiscrepancy θ Q x t| ≤ 1)
    (h : ℝ → ℝ) (hper : Function.Periodic h 1) (hbv : ConcreteHasBVReal h)
    (hmean : periodMeanReal h = 0) :
    |∑ j ∈ Finset.range Q, h (x - (j : ℝ) * θ)| ≤ concreteVariationReal h := by
  by_cases hQ : 0 < Q;
  · convert koksma_general hQ ( fun k => Int.fract ( x - ( k : ℝ ) * θ ) ) _ hbv _ using 1;
    · rw [ intervalIntegral.integral_of_le zero_le_one, periodMeanReal ] at *;
      rw [ Finset.sum_range ];
      simp +decide [ ← periodic_eval_fract hper, hmean ];
    · exact fun k => ⟨ Int.fract_nonneg _, Int.fract_lt_one _ ⟩;
    · intro t ht; specialize hdisc t ht; simp_all +decide [ orbitCount_eq_fin_card, orbitDiscrepancy ] ;
  · convert CriticalMixedHRT.concreteVariationReal_nonneg h using 1 ; aesop

/-! ## The exact periodic Koksma interface and the combinatorial reduction -/

/-- **The exact periodic Koksma inequality interface.**

The reduction from the orbit star-discrepancy bound to the periodic real
Denjoy–Koksma estimate, as a single `Prop` over the rotation number `θ`.  This is
exactly Koksma's inequality; it is *proved* below in
`standardPeriodicKoksmaInequality_proved`. -/
def StandardPeriodicKoksmaInequality (θ : ℝ) : Prop :=
  ∀ (Q : ℕ) (x : ℝ),
    (∀ t ∈ Set.Icc (0 : ℝ) 1, |orbitDiscrepancy θ Q x t| ≤ 1) →
    ∀ h : ℝ → ℝ, Function.Periodic h 1 → ConcreteHasBVReal h → periodMeanReal h = 0 →
      |∑ j ∈ Finset.range Q, h (x - (j : ℝ) * θ)| ≤ concreteVariationReal h

/-- **Koksma's inequality holds (for every rotation number).**  Wraps
`koksma_real_periodic`. -/
theorem standardPeriodicKoksmaInequality_proved (θ : ℝ) :
    StandardPeriodicKoksmaInequality θ :=
  fun Q x hdisc h hper hbv hmean => koksma_real_periodic Q x hdisc h hper hbv hmean

/-- **Faithful periodic interface from the combinatorial star-discrepancy
interface.**

Given Koksma's inequality (`StandardPeriodicKoksmaInequality θ`, which is proved)
together with the combinatorial star-discrepancy interface
`StandardRealDenjoyKoksmaCombinatorics θ`, this builds the faithful periodic real
Denjoy–Koksma data `RealDenjoyKoksmaPeriodic θ`.

Composed with `standardPeriodicKoksmaInequality_proved`, this reduces the entire
corrected periodic Denjoy–Koksma interface to the single combinatorial input
`StandardRealDenjoyKoksmaCombinatorics θ` (the three-gap star-discrepancy bound
for continued-fraction denominators). -/
noncomputable def RealDenjoyKoksmaPeriodic.ofCombinatorics {θ : ℝ}
    (K : StandardPeriodicKoksmaInequality θ)
    (C : StandardRealDenjoyKoksmaCombinatorics θ) : RealDenjoyKoksmaPeriodic θ where
  toRotationReturnData := C.toRotationReturnData
  q_tendsto := C.q_tendsto
  dk_real_periodic := fun h hper hbv hmean n x =>
    K (C.toRotationReturnData.q n) x
      (fun t ht => C.star_discrepancy_le_one n x t ht) h hper hbv hmean

/-- **The corrected periodic Denjoy–Koksma interface, reduced to the single
combinatorial star-discrepancy input.**

From `StandardRealDenjoyKoksmaCombinatorics θ` alone, the faithful periodic real
Denjoy–Koksma data is constructed (Koksma's inequality being already discharged). -/
noncomputable def RealDenjoyKoksmaPeriodic.ofStarDiscrepancy {θ : ℝ}
    (C : StandardRealDenjoyKoksmaCombinatorics θ) : RealDenjoyKoksmaPeriodic θ :=
  RealDenjoyKoksmaPeriodic.ofCombinatorics (standardPeriodicKoksmaInequality_proved θ) C

end CriticalMixedHRT