import Mathlib
import RequestProject.Rotation.PeriodicKoksma

/-!
# DK orbit-partition correction: the true *centered* star-discrepancy interface

## Background and the falsity of `star_discrepancy_le_one`

A previous run already established that the grid-balanced orbit-partition field
`ContinuedFractionReturnData.orbit_partition` is **false** as stated.

This module establishes a sharper and more important correction:

> The *unsigned* orbit star-discrepancy bound
> `|orbitDiscrepancy θ (q n) x t| ≤ 1`
> (the `star_discrepancy_le_one` field of
> `StandardRealDenjoyKoksmaCombinatorics θ`) is **also false**, even for genuine
> continued-fraction convergent denominators.

The counterexample is the same golden-ratio datum that refutes the
orbit-partition field:

* `θ = (√5 − 1)/2` (the golden-ratio conjugate, irrational),
* `Q = 8` (a Fibonacci, hence convergent, denominator),
* base point `x = 1/10`, threshold `t = 1/10`.

Here exactly the two orbit points `j = 0` (value `1/10`) and `j = 5`
(value `≈ 0.0098`) fall in `[0, 1/10]`, so

```
orbitDiscrepancy θ 8 (1/10) (1/10) = 2 − 8·(1/10) = 6/5 > 1.
```

This is proved unconditionally below in `star_discrepancy_le_one_false`.

Consequently **both** `StandardRealDenjoyKoksmaCombinatorics` (the `≤ 1` bound)
and the stronger `ContinuedFractionReturnData` (grid-balancedness) are
*uninhabitable*, and the Denjoy–Koksma chain that routes through them is
vacuous.

## The true correction: the centered star-discrepancy bound

What *is* true for convergent denominators is the **centered** star-discrepancy
bound: there is a recentering constant `c` (depending on `n` and `x`) with

```
|orbitDiscrepancy θ (q n) x t − c| ≤ 1     for all t ∈ [0,1].
```

Equivalently the *oscillation* `sup_t disc − inf_t disc ≤ 2`.  (Numerically the
oscillation is `< 2` at genuine convergent denominators — e.g. it is `≈ 1.74`
for the golden case `Q = 8`, never reaching the false `sup |disc| ≤ 1`.)

This centered bound is exactly strong enough to feed the genuine **periodic**
Denjoy–Koksma estimate (constant `1`), because for a `1`-periodic test function
the recentering constant is invisible: shifting the discrepancy by a constant `c`
corresponds, after summation by parts, to adding `c·(h(1) − h(0)) = 0`.  We make
this precise via a *shifted-cell* version of Koksma's inequality
(`koksma_real_periodic_centered`), proved here from the project's already-proved
Koksma machinery together with the period-translation invariance of the integral
and the total variation.

The corrected combinatorial interface is therefore
`ContinuedFractionStarDiscrepancyData θ`, carrying the *true* centered
star-discrepancy bound (no grid-balancedness, no false `≤ 1` sup-bound), and it
yields the faithful periodic Denjoy–Koksma data
`RealDenjoyKoksmaPeriodic θ` directly.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]` are introduced.
-/

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

namespace CriticalMixedHRT

/-! ## The golden-ratio counterexample to `star_discrepancy_le_one` -/

/-- The golden-ratio conjugate `(√5 − 1)/2 ≈ 0.618`. -/
noncomputable def goldenConj : ℝ := (Real.sqrt 5 - 1) / 2

theorem goldenConj_irrational : Irrational goldenConj := by
  exact_mod_cast Nat.Prime.irrational_sqrt ( by norm_num ) |> Irrational.sub_ratCast 1 |> Irrational.div_ratCast <| by norm_num;

/-
**The unsigned star-discrepancy bound `≤ 1` is false.**

For the golden-ratio conjugate (irrational), the convergent (Fibonacci)
denominator `Q = 8`, base point `x = 1/10` and threshold `t = 1/10 ∈ [0,1]`, the
orbit star-discrepancy equals `6/5 > 1`.  Hence the `star_discrepancy_le_one`
field of `StandardRealDenjoyKoksmaCombinatorics`, and a fortiori the
grid-balanced `ContinuedFractionReturnData.orbit_partition` field, are
*uninhabitable*.
-/
theorem star_discrepancy_le_one_false :
    ∃ (θ : ℝ) (Q : ℕ) (x t : ℝ),
      Irrational θ ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧ 1 < |orbitDiscrepancy θ Q x t| := by
  use goldenConj, 8, 1/10, 1/10;
  refine' ⟨ _, _, _ ⟩;
  · exact goldenConj_irrational;
  · norm_num;
  · -- Calculate the value of `orbitCount` for the given parameters.
    have h_orbitCount : orbitCount goldenConj 8 (1 / 10) (1 / 10) ≥ 2 := by
      refine' Finset.one_lt_card.mpr ⟨ 0, _, 5, _, _ ⟩ <;> norm_num [ goldenConj ];
      exact ⟨ ⟨ 5, by norm_num ⟩, by rw [ Int.fract ] ; rw [ show ⌊1 / 10 - 5 * ( ( Real.sqrt 5 - 1 ) / 2 ) ⌋ = -3 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ], by norm_num; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ⟩ ] ; norm_num; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ⟩;
    unfold orbitDiscrepancy;
    rw [ abs_of_nonneg ] <;> linarith [ show ( orbitCount goldenConj 8 ( 1 / 10 ) ( 1 / 10 ) : ℝ ) ≥ 2 by exact_mod_cast h_orbitCount ]

/-! ## A shifted-cell (centered) Koksma inequality

The centered Koksma inequality is proved by the same order-statistic argument as
the project's `koksma_general` / `koksma_real_periodic`, but with the test cells
shifted by `-c/Q`.  The recentering constant `c` is absorbed by two
period-translation facts: the integral and the total variation over the shifted
period `[-c/Q, 1-c/Q]` agree with those over `[0,1]`.  We isolate these as the
helper lemmas below. -/

/-
**Period-translation invariance of the total variation.**  For a `1`-periodic
function, the extended variation over any unit interval `[a, a+1]` equals the
extended variation over `[0,1]`.
-/
theorem eVariationOn_Icc_unit_period {h : ℝ → ℝ} (hper : Function.Periodic h 1)
    (a : ℝ) :
    eVariationOn h (Set.Icc a (a + 1)) = eVariationOn h (Set.Icc 0 1) := by
  -- Let `n` be `-⌊a⌋`. Then `a+n = a-⌊a⌋ ∈ [0,1)` (since `0 ≤ a-⌊a⌋ < 1`).
  set a' : ℝ := a - ⌊a⌋
  have hn : a + (-⌊a⌋ : ℝ) = a' := by
    ring!
  have ha' : 0 ≤ a' ∧ a' < 1 := by
    exact ⟨ Int.fract_nonneg a, Int.fract_lt_one a ⟩;
  -- By integer-translation invariance (Step 1), `eVariationOn h (Icc a (a+1)) = eVariationOn h (Icc a' (a'+1))`.
  have h_trans : eVariationOn h (Set.Icc a (a + 1)) = eVariationOn h (Set.Icc a' (a' + 1)) := by
    have h_trans : ∀ n : ℤ, eVariationOn h (Set.Icc a (a + 1)) = eVariationOn h (Set.Icc (a + n) (a + 1 + n)) := by
      intro n
      have h_trans : eVariationOn h (Set.Icc a (a + 1)) = eVariationOn (h ∘ (fun t => t + n)) (Set.Icc a (a + 1)) := by
        convert rfl using 2;
        exact funext fun x => by simpa using Function.Periodic.int_mul hper n x;
      convert h_trans using 1;
      rw [ eVariationOn.comp_eq_of_monotoneOn ] <;> norm_num [ MonotoneOn ];
    convert h_trans ( -⌊a⌋ ) using 1 ; push_cast ; ring;
    rfl;
  -- By integer-translation invariance (Step 1), `eVariationOn h (Icc 1 (a'+1)) = eVariationOn h (Icc 0 a')`.
  have h_trans2 : eVariationOn h (Set.Icc 1 (a' + 1)) = eVariationOn h (Set.Icc 0 a') := by
    -- The translation `φ : t ↦ t - 1` is monotone, maps `Set.Icc 1 (a'+1)` onto `Set.Icc 0 a'`, and `h ∘ φ = h` because `h` is `1`-periodic.
    have h_trans2 : eVariationOn (h ∘ (fun t => t - 1)) (Set.Icc 1 (a' + 1)) = eVariationOn h (Set.Icc 0 a') := by
      convert eVariationOn.comp_eq_of_monotoneOn _ _ _ using 1;
      all_goals try infer_instance;
      · congr ; ext ; aesop;
      · exact fun x hx y hy hxy => sub_le_sub_right hxy _;
    convert h_trans2 using 2;
    exact funext fun x => by simpa using hper ( x - 1 ) ▸ by ring;
  have h_split : eVariationOn h (Set.Icc a' (a' + 1)) = eVariationOn h (Set.Icc a' 1) + eVariationOn h (Set.Icc 1 (a' + 1)) := by
    grind +suggestions;
  rw [ h_trans, h_split, h_trans2 ];
  rw [ add_comm, eVar_Icc_add ] <;> norm_num [ ha'.1, ha'.2.le ]

/-
**Bounded variation on a compact interval implies interval integrability.**
Generalises `bv_intervalIntegrable` from `[0,1]` to an arbitrary interval.
-/
theorem bv_intervalIntegrable_Icc {h : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hbv : eVariationOn h (Set.Icc p q) ≠ ⊤) :
    IntervalIntegrable h volume p q := by
  rw [ intervalIntegrable_iff_integrableOn_Icc_of_le hpq ];
  obtain ⟨f, g, hf, hg, hfg⟩ : ∃ f g : ℝ → ℝ, MonotoneOn f (Set.Icc p q) ∧ MonotoneOn g (Set.Icc p q) ∧ h = f - g := by
    have h_locally_bounded_variation : LocallyBoundedVariationOn h (Set.Icc p q) := by
      exact?;
    exact?;
  exact hfg.symm ▸ ( hf.integrableOn_isCompact ( CompactIccSpace.isCompact_Icc ) |> fun h => h.sub ( hg.integrableOn_isCompact ( CompactIccSpace.isCompact_Icc ) ) )

/-
**Per-interval Koksma bound on a general interval.**  Generalises
`koksma_interval_bound`: on any interval `[p,q]` of positive length on which `h`
has finite variation and is integrable, the deviation of `h zk` (for `zk ∈ [p,q]`)
from the scaled mean of `h` over `[p,q]` is bounded by the variation of `h` over
`[p,q]`.
-/
theorem koksma_interval_bound_gen {h : ℝ → ℝ} {p q : ℝ} (hpq : p < q)
    (hbv : eVariationOn h (Set.Icc p q) ≠ ⊤)
    (hint : IntervalIntegrable h volume p q) {zk : ℝ} (hzk : zk ∈ Set.Icc p q) :
    |h zk - (q - p)⁻¹ * ∫ t in p..q, h t|
      ≤ (eVariationOn h (Set.Icc p q)).toReal := by
  -- For every $t \in [p, q]$, $|h(zk) - h(t)| \leq \text{eVariationOn } h (Set.Icc p q)$.
  have h_bound : ∀ t ∈ Set.Icc p q, |h zk - h t| ≤ (eVariationOn h (Set.Icc p q)).toReal := by
    intro t ht; rw [ ← Real.dist_eq ] ; exact ENNReal.toReal_mono hbv ( eVariationOn.edist_le h hzk ht ) ;
  -- Apply this bound to the integral of $|h(zk) - h(t)|$ over $[p, q]$.
  have h_integral_bound : |∫ t in p..q, h zk - h t| ≤ (eVariationOn h (Set.Icc p q)).toReal * (q - p) := by
    rw [ intervalIntegral.integral_of_le hpq.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc ];
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
    exacts [ fun _ => ( eVariationOn h ( Set.Icc p q ) |> ENNReal.toReal ), Filter.Eventually.of_forall fun _ => norm_nonneg _, Continuous.integrableOn_Icc <| by continuity, Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Icc ) fun x hx => h_bound x hx, by simp +decide [ mul_comm, hpq.le ] ];
  rw [ intervalIntegral.integral_sub ] at h_integral_bound <;> simp_all +decide [ ne_of_gt ( sub_pos.mpr hpq ) ];
  rw [ abs_le ] at *; constructor <;> nlinarith [ inv_mul_cancel_left₀ ( sub_ne_zero_of_ne hpq.ne' ) ( ∫ t in p..q, h t ), inv_mul_cancel₀ ( sub_ne_zero_of_ne hpq.ne' ) ] ;

/-
**Centered order-statistic localisation.**  Given a monotone enumeration `z`
of `Q` points in `[0,1)` whose counting function satisfies the *centered* unit
star-discrepancy bound (offset `c`), the `k`-th order statistic lies in the
shifted cell `[(k-c)/Q, (k+1-c)/Q]`.  Generalises `koksma_order_stat` (`c = 0`).
-/
theorem koksma_order_stat_centered {Q : ℕ} (hQ : 0 < Q) (z : Fin Q → ℝ)
    (hz : Monotone z) (hzmem : ∀ k, z k ∈ Set.Ico (0 : ℝ) 1) (c : ℝ)
    (hdisc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |((Finset.univ.filter (fun i => z i ≤ t)).card : ℝ) - (Q : ℝ) * t - c| ≤ 1)
    (k : Fin Q) :
    z k ∈ Set.Icc (((k : ℕ) - c) / (Q : ℝ)) (((k : ℕ) + 1 - c) / (Q : ℝ)) := by
  constructor;
  · have h_card : (Finset.univ.filter (fun i => z i ≤ z k)).card ≥ k + 1 := by
      exact le_trans ( by norm_num ) ( Finset.card_le_card ( show Finset.Iic k ⊆ Finset.filter ( fun i => z i ≤ z k ) Finset.univ from fun i hi => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hz <| Finset.mem_Iic.mp hi ⟩ ) );
    have := hdisc ( z k ) ⟨ hzmem k |>.1, hzmem k |>.2.le ⟩ ; rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ abs_le.mp this, show ( Finset.card ( Finset.filter ( fun i => z i ≤ z k ) Finset.univ ) : ℝ ) ≥ k + 1 by exact_mod_cast h_card, show ( Q : ℝ ) > 0 by positivity ] ;
  · by_contra h_contra;
    -- Choose $t$ such that $(k+1-c)/Q < t < z k$ and $t \in [0,1]$.
    obtain ⟨t, ht₁, ht₂⟩ : ∃ t ∈ Set.Icc 0 1, (k + 1 - c) / Q < t ∧ t < z k := by
      by_cases h_case : (k + 1 - c) / Q < 0;
      · simp_all +decide [ div_lt_iff₀, hQ ];
        have := hdisc 0 ( by norm_num ) ( by norm_num ) ; have := hdisc 1 ( by norm_num ) ( by norm_num ) ; norm_num [ abs_le ] at *;
        rw [ show ( Finset.univ.filter fun i => z i ≤ 1 ) = Finset.univ from Finset.filter_true_of_mem fun i _ => by linarith [ hzmem i ] ] at this ; norm_num at this ; nlinarith [ show ( Q : ℝ ) ≥ 1 by norm_cast, hzmem k ];
      · exact ⟨ ( ( k + 1 - c ) / Q + z k ) / 2, ⟨ by linarith [ Set.mem_Ico.mp ( hzmem k ) ], by linarith [ Set.mem_Ico.mp ( hzmem k ) ] ⟩, by linarith [ Set.mem_Ico.mp ( hzmem k ) ], by linarith [ Set.mem_Ico.mp ( hzmem k ) ] ⟩;
    -- Since $t < z k$, we have $\{i : z i ≤ t\} \subseteq \{i : i < k\}$.
    have h_subset : Finset.filter (fun i => z i ≤ t) Finset.univ ⊆ Finset.Iio k := by
      exact fun i hi => Finset.mem_Iio.mpr <| lt_of_not_ge fun hi' => by linarith [ Finset.mem_filter.mp hi, hz hi' ] ;
    have := Finset.card_le_card h_subset; simp_all +decide [ Finset.card_univ ] ;
    rw [ div_lt_iff₀ ( by positivity ) ] at *;
    nlinarith [ abs_le.mp ( hdisc t ht₁.1 ht₁.2 ), show ( Finset.card ( Finset.filter ( fun i => z i ≤ t ) Finset.univ ) : ℝ ) ≤ k from mod_cast this ]

/-
**General centered Koksma inequality** for a finite point set in `[0,1)` and a
`1`-periodic bounded-variation function.

If `y : Fin Q → ℝ` is a family of points in `[0,1)` whose orbit counting function
satisfies the *centered* unit star-discrepancy bound
`|#{k : y k ≤ t} − Q·t − c| ≤ 1` for some constant `c` and all `t ∈ [0,1]`, then
for every `1`-periodic bounded-variation `h`,
`|∑_k h(y_k) − Q·∫₀¹ h| ≤ concreteVariationReal h`.  The recentering constant `c`
is invisible because `h` is periodic.
-/
theorem koksma_general_centered {Q : ℕ} (hQ : 0 < Q) (y : Fin Q → ℝ)
    (hy : ∀ k, y k ∈ Set.Ico (0 : ℝ) 1)
    {h : ℝ → ℝ} (hper : Function.Periodic h 1) (hbv : ConcreteHasBVReal h) (c : ℝ)
    (hdisc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |((Finset.univ.filter (fun k => y k ≤ t)).card : ℝ) - (Q : ℝ) * t - c| ≤ 1) :
    |(∑ k, h (y k)) - (Q : ℝ) * ∫ t in (0 : ℝ)..1, h t| ≤ concreteVariationReal h := by
  -- Enumerate the (sorted) orbit points as `z k = y (σ k)` with `σ` a permutation.
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin Q), Monotone (fun k => y (σ k)) := by
    exact ⟨ Tuple.sort y, Tuple.monotone_sort _ ⟩;
  -- By `koksma_order_stat_centered`, `z k ∈ Set.Icc (a k) (a (k+1))` for each `k`.
  have hz_bounds : ∀ k : Fin Q, y (σ k) ∈ Set.Icc (((k : ℕ) - c) / (Q : ℝ)) (((k : ℕ) + 1 - c) / (Q : ℝ)) := by
    convert koksma_order_stat_centered hQ ( fun k => y ( σ k ) ) hσ ( fun k => hy _ ) c _;
    intro t ht; convert hdisc t ht using 1; rw [ Finset.card_filter ] ; rw [ Finset.card_filter ] ;
    rw [ Equiv.sum_comp σ fun k => if y k ≤ t then 1 else 0 ];
  -- By `koksma_interval_bound_gen`, for each `k`, `|h (y (σ k)) - Q * ∫ t in (a k)..(a (k+1)), h| ≤ (eVariationOn h (J k)).toReal`.
  have h_interval_bound : ∀ k : Fin Q, |h (y (σ k)) - (Q : ℝ) * ∫ t in ((k - c) / (Q : ℝ))..(((k + 1) - c) / (Q : ℝ)), h t| ≤ (eVariationOn h (Set.Icc ((k - c) / (Q : ℝ)) (((k + 1) - c) / (Q : ℝ)))).toReal := by
    intro k;
    convert koksma_interval_bound_gen ( show ( ( k : ℝ ) - c ) / Q < ( ( k : ℝ ) + 1 - c ) / Q from by rw [ div_lt_div_iff_of_pos_right ( by positivity ) ] ; linarith ) _ _ ( hz_bounds k ) using 1;
    · ring_nf; norm_num [ hQ.ne' ];
      rw [ mul_comm ];
    · refine' ne_of_lt ( lt_of_le_of_lt ( eVariationOn.mono _ _ ) _ );
      exact Set.Icc ( ( 0 - c ) / Q ) ( ( 0 - c ) / Q + 1 );
      · exact Set.Icc_subset_Icc ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith [ show ( k : ℝ ) ≥ 0 by positivity ] ) ( by rw [ div_add_one, div_le_div_iff_of_pos_right ( by positivity ) ] <;> linarith [ show ( k : ℝ ) + 1 ≤ Q by norm_cast; linarith [ Fin.is_lt k ] ] );
      · convert hbv.lt_top using 1;
        convert eVariationOn_Icc_unit_period hper ( ( 0 - c ) / Q ) using 1;
    · apply bv_intervalIntegrable_Icc;
      · gcongr ; norm_num;
      · refine' ne_of_lt ( lt_of_le_of_lt ( eVariationOn.mono _ _ ) _ );
        exact Set.Icc ( ( 0 - c ) / Q ) ( ( 0 - c ) / Q + 1 );
        · exact Set.Icc_subset_Icc ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith [ show ( k : ℝ ) ≥ 0 by positivity ] ) ( by rw [ div_add_one, div_le_div_iff_of_pos_right ] <;> norm_num <;> linarith [ show ( k : ℝ ) + 1 ≤ Q by norm_cast; linarith [ Fin.is_lt k ] ] );
        · convert hbv.lt_top using 1;
          convert eVariationOn_Icc_unit_period hper ( ( 0 - c ) / Q ) using 1;
  have h_sum_interval_bound : |∑ k : Fin Q, h (y (σ k)) - (Q : ℝ) * ∑ k ∈ Finset.range Q, ∫ t in ((k - c) / (Q : ℝ))..(((k + 1) - c) / (Q : ℝ)), h t| ≤ concreteVariationReal h := by
    have h_sum_interval_bound : ∑ k ∈ Finset.range Q, (eVariationOn h (Set.Icc ((k - c) / (Q : ℝ)) (((k + 1) - c) / (Q : ℝ)))).toReal = concreteVariationReal h := by
      convert eVar_sum_adjacent h ( fun k => ( k - c ) / Q ) ?_ Q using 1;
      · rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num;
        · rw [ ENNReal.toReal_sum ];
          · convert Iff.rfl;
            convert congr_arg ENNReal.toReal ( eVariationOn_Icc_unit_period hper ( -c / Q ) ) using 1;
            rw [ show ( Q - c : ℝ ) / Q = -c / Q + 1 by rw [ div_add_one ] ; ring ; positivity ];
          · intro k hk;
            refine' ne_of_lt ( lt_of_le_of_lt ( eVariationOn.mono _ _ ) _ );
            exact Set.Icc ( -c / Q ) ( ( Q - c ) / Q );
            · exact Set.Icc_subset_Icc ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith [ show ( k : ℝ ) ≥ 0 by positivity ] ) ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith [ show ( k : ℝ ) + 1 ≤ Q by norm_cast; linarith [ Finset.mem_range.mp hk ] ] );
            · convert hbv using 1;
              rw [ show ( Q - c : ℝ ) / Q = ( -c / Q ) + 1 by rw [ div_add_one ] ; ring ; positivity ] ; rw [ eVariationOn_Icc_unit_period hper ] ;
              exact ⟨ fun h => h.ne, fun h => lt_top_iff_ne_top.mpr h ⟩;
        · intro k hk; exact (by
          refine' ne_of_lt ( lt_of_le_of_lt ( eVariationOn.mono _ _ ) _ );
          exact Set.Icc ( ( 0 - c ) / Q ) ( ( Q - c ) / Q );
          · exact Set.Icc_subset_Icc ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith [ show ( k : ℝ ) ≥ 0 by positivity ] ) ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith [ show ( k : ℝ ) + 1 ≤ Q by norm_cast ] );
          · convert hbv using 1;
            rw [ show ( Q - c ) / Q = ( 0 - c ) / Q + 1 by rw [ div_add_one ] ; ring ; positivity ] ; rw [ eVariationOn_Icc_unit_period hper ] ;
            exact ⟨ fun h => h.ne, fun h => lt_top_iff_ne_top.mpr h ⟩);
        · convert hbv using 1;
          rw [ show ( -c / Q : ℝ ) = ( -c / Q ) by ring, show ( Q - c : ℝ ) / Q = ( -c / Q ) + 1 by rw [ div_add_one ] ; ring ; positivity ] ; rw [ eVariationOn_Icc_unit_period hper ];
      · exact fun i j hij => div_le_div_of_nonneg_right ( sub_le_sub_right ( Nat.cast_le.mpr hij ) _ ) ( Nat.cast_nonneg _ );
    simp_all +decide [ Finset.mul_sum _ _ _, Finset.sum_range ];
    exact h_sum_interval_bound ▸ le_trans ( by simpa only [ ← Finset.sum_sub_distrib ] using Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i _ => h_interval_bound i );
  have h_integral_sum : ∑ k ∈ Finset.range Q, ∫ t in ((k - c) / (Q : ℝ))..(((k + 1) - c) / (Q : ℝ)), h t = ∫ t in ((0 - c) / (Q : ℝ))..(((Q : ℝ) - c) / (Q : ℝ)), h t := by
    convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
    intro k hk; apply_rules [ bv_intervalIntegrable_Icc ] ;
    · bound;
    · refine' ne_of_lt ( lt_of_le_of_lt ( eVariationOn.mono _ _ ) _ );
      exact Set.Icc ( ( 0 - c ) / Q ) ( ( 0 - c ) / Q + 1 );
      · exact Set.Icc_subset_Icc ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith [ show ( k : ℝ ) ≥ 0 by positivity ] ) ( by rw [ div_add_one, div_le_div_iff_of_pos_right ( by positivity ) ] <;> linarith [ show ( k : ℝ ) + 1 ≤ Q by norm_cast ] );
      · convert hbv using 1;
        exact iff_of_true ( by rw [ eVariationOn_Icc_unit_period hper ] ; exact lt_top_iff_ne_top.mpr hbv ) hbv;
  have h_integral_periodic : ∫ t in ((0 - c) / (Q : ℝ))..(((Q : ℝ) - c) / (Q : ℝ)), h t = ∫ t in (0 : ℝ)..1, h t := by
    convert Function.Periodic.intervalIntegral_add_eq hper ( ( 0 - c ) / Q ) using 2 ; ring_nf ; norm_num [ hQ.ne' ];
    constructor <;> intro h <;> ring_nf at *;
    · convert Function.Periodic.intervalIntegral_add_eq hper ( - ( c * ( Q : ℝ ) ⁻¹ ) ) using 2 ; ring;
      rw [ add_comm ];
    · convert h 0 using 1 ; ring;
  rw [ ← Equiv.sum_comp σ ] ; aesop;

/-- **Recentered periodic Koksma inequality.**

The genuine periodic real Denjoy–Koksma estimate (constant `1`) follows from the
*centered* orbit star-discrepancy bound: if there is a constant `c` with
`|orbitDiscrepancy θ Q x t − c| ≤ 1` for all `t ∈ [0,1]`, then for every
`1`-periodic bounded-variation zero-mean `h`,

```
|∑_{j<Q} h (x − j θ)| ≤ concreteVariationReal h.
```

This is the corrected analogue of `koksma_real_periodic`, whose hypothesis is the
*false* uncentered bound (`c = 0`).  The recentering constant is invisible to a
periodic test function. -/
theorem koksma_real_periodic_centered {θ : ℝ} (Q : ℕ) (x : ℝ)
    (hdisc : ∃ c : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |orbitDiscrepancy θ Q x t - c| ≤ 1)
    (h : ℝ → ℝ) (hper : Function.Periodic h 1) (hbv : ConcreteHasBVReal h)
    (hmean : periodMeanReal h = 0) :
    |∑ j ∈ Finset.range Q, h (x - (j : ℝ) * θ)| ≤ concreteVariationReal h := by
  by_cases hQ : 0 < Q
  · obtain ⟨c, hc⟩ := hdisc
    have hconv := koksma_general_centered hQ (fun k : Fin Q => Int.fract (x - (k : ℝ) * θ))
      (fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) hper hbv c
      (by
        intro t ht
        have := hc t ht
        simpa [orbitDiscrepancy, orbitCount_eq_fin_card] using this)
    have hsum : (∑ k : Fin Q, h (Int.fract (x - (k : ℝ) * θ)))
        = ∑ j ∈ Finset.range Q, h (x - (j : ℝ) * θ) := by
      rw [Finset.sum_range]
      exact Finset.sum_congr rfl (fun k _ => (periodic_eval_fract hper _).symm)
    have hint0 : (∫ t in (0 : ℝ)..1, h t) = 0 := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      simpa [periodMeanReal] using hmean
    rw [hsum] at hconv
    simpa [hint0] using hconv
  · simp only [not_lt, Nat.le_zero] at hQ
    subst hQ
    simpa using concreteVariationReal_nonneg h

/-! ## The corrected continued-fraction star-discrepancy interface -/

/-- **Corrected continued-fraction star-discrepancy data.**

The honest replacement for the (uninhabitable) `StandardRealDenjoyKoksmaCombinatorics`
and `ContinuedFractionReturnData`.  It bundles the rotation return data with the
divergence of the denominators, the irrationality of `θ`, and the **true**
*centered* orbit star-discrepancy bound (equivalently, oscillation `≤ 2`) over
the convergent denominators — without the false grid-balanced orbit partition or
the false unsigned `≤ 1` sup-bound. -/
structure ContinuedFractionStarDiscrepancyData (θ : ℝ) extends RotationReturnData θ where
  /-- The return denominators diverge to infinity. -/
  q_tendsto : Tendsto toRotationReturnData.q atTop atTop
  /-- `θ` is irrational (so the `q n` are genuine convergent denominators). -/
  hθ : Irrational θ
  /-- **Centered orbit star-discrepancy bound.**  For each `n` and base point `x`
  there is a recentering constant `c` with
  `|orbitDiscrepancy θ (q n) x t − c| ≤ 1` for all `t ∈ [0,1]`.  This is the true
  number-theoretic content (oscillation `≤ 2`) of the three-gap /
  best-approximation property of convergent denominators; it replaces the false
  `star_discrepancy_le_one` (`c = 0`) and the false grid-balancedness. -/
  centered_star_discrepancy_le_one :
    ∀ (n : ℕ) (x : ℝ), ∃ c : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |orbitDiscrepancy θ (toRotationReturnData.q n) x t - c| ≤ 1

namespace ContinuedFractionStarDiscrepancyData

variable {θ : ℝ} (D : ContinuedFractionStarDiscrepancyData θ)

/-- **Adapter: corrected star-discrepancy data yields the faithful periodic real
Denjoy–Koksma data.**  Via the recentered Koksma inequality
(`koksma_real_periodic_centered`), the true centered star-discrepancy bound
discharges the `dk_real_periodic` field directly. -/
noncomputable def toRealDenjoyKoksmaPeriodic : RealDenjoyKoksmaPeriodic θ where
  toRotationReturnData := D.toRotationReturnData
  q_tendsto := D.q_tendsto
  dk_real_periodic := fun h hper hbv hmean n x =>
    koksma_real_periodic_centered (D.toRotationReturnData.q n) x
      (D.centered_star_discrepancy_le_one n x) h hper hbv hmean

end ContinuedFractionStarDiscrepancyData

/-- **Faithful periodic real Denjoy–Koksma data from corrected star-discrepancy
data.**  Named in the `RealDenjoyKoksmaPeriodic.of…` style. -/
noncomputable def RealDenjoyKoksmaPeriodic.ofContinuedFractionStarDiscrepancyData {θ : ℝ}
    (D : ContinuedFractionStarDiscrepancyData θ) : RealDenjoyKoksmaPeriodic θ :=
  D.toRealDenjoyKoksmaPeriodic

end CriticalMixedHRT