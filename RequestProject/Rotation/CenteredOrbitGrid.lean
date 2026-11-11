import Mathlib
import RequestProject.Rotation.StarDiscrepancyCorrection

/-!
# Centered orbit grid ⇒ centered star-discrepancy bound

The corrected continued-fraction interface
`ContinuedFractionStarDiscrepancyData θ`
(`RequestProject.Rotation.StarDiscrepancyCorrection`) carries the *true* centered
orbit star-discrepancy bound

```
∀ n x, ∃ c, ∀ t ∈ [0,1], |orbitDiscrepancy θ (q n) x t − c| ≤ 1
```

(equivalently oscillation `≤ 2`).  This module reduces that analytic-over-all-`t`
bound to a strictly *combinatorial* and *finite* statement about the sorted orbit
points — the **centered orbit grid** property: for each `n` and base point `x`
there is a sorting permutation `σ` of the `q n` orbit points
`fract (x − j θ)` and a recentering constant `c` placing the `i`-th sorted point
in the *shifted* grid cell `[(i−c)/(q n), (i+1−c)/(q n))`.

This is the honest centered replacement of the **false** grid-balanced
`orbit_partition` field (which used `c = 0`, see
`star_discrepancy_le_one_false`).  It is exactly the three-distance /
best-approximation content for convergent denominators: the `q n` orbit points
divide `[0,1)` into at most two/three gap lengths, all close to `1/(q n)`, so the
sorted points track an evenly spaced grid up to the single shift `c`.

The reduction proved here (`centered_discrepancy_abs_le_one_of_centered_grid`) is
the converse direction of the project's `koksma_order_stat_centered`: a centered
grid for the sorted points yields the centered discrepancy bound directly, with
the *same* constant `c`.

This isolates the remaining number-theoretic gap as the single combinatorial
`Prop` `StandardCenteredOrbitGridProperty θ q`, strictly smaller than the
all-`t` discrepancy field, and wires it into a constructor for
`ContinuedFractionStarDiscrepancyData θ`.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]` are introduced.
-/

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

namespace CriticalMixedHRT

/-! ## The combinatorial centered grid ⇒ centered discrepancy core -/

/-
**Centered grid ⇒ centered discrepancy.**

If a family `p : Fin Q → ℝ` of points in `[0,1)` admits a sorting permutation `σ`
with `p ∘ σ` monotone and *centered* grid-balanced for a constant `c`
(`p (σ i) ∈ [(i−c)/Q, (i+1−c)/Q)`), then the centered unnormalized
star-discrepancy of `p` at any `t ∈ [0,1]`, recentered by the *same* `c`, is at
most `1` in absolute value:

```
|#{ i : p i ≤ t } − Q·t − c| ≤ 1.
```

This is the converse of `koksma_order_stat_centered`.
-/
theorem centered_discrepancy_abs_le_one_of_centered_grid {Q : ℕ} (hQ : 0 < Q)
    (p : Fin Q → ℝ) (hmem : ∀ i, p i ∈ Set.Ico (0 : ℝ) 1)
    (σ : Equiv.Perm (Fin Q)) (c : ℝ)
    (hmono : Monotone (fun i : Fin Q => p (σ i)))
    (hgrid : ∀ i : Fin Q,
        ((i : ℝ) - c) / (Q : ℝ) ≤ p (σ i) ∧
        p (σ i) < ((i : ℝ) + 1 - c) / (Q : ℝ))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |((Finset.univ.filter (fun i : Fin Q => p i ≤ t)).card : ℝ) - (Q : ℝ) * t - c| ≤ 1 := by
  refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
  · by_cases hN : (Finset.univ.filter (fun i => p i ≤ t)).card = 0;
    · simp_all +decide [ Finset.ext_iff ];
      rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
      · have := hgrid ⟨ 0, hQ ⟩ ; have := hgrid ⟨ Q - 1, Nat.sub_lt hQ zero_lt_one ⟩ ; simp_all +decide [ div_le_iff₀, lt_div_iff₀ ];
        nlinarith [ hmem ( σ ⟨ 0, hQ ⟩ ), hmem ( σ ⟨ Q - 1, Nat.sub_lt hQ zero_lt_one ⟩ ), show ( Q : ℝ ) ≥ 1 by norm_cast ];
      · tauto;
    · -- Let $j = N - 1$. Then $j < N$.
      obtain ⟨j, hj⟩ : ∃ j : Fin Q, (j : ℕ) = (Finset.univ.filter (fun i => p i ≤ t)).card - 1 ∧ (j : ℕ) < (Finset.univ.filter (fun i => p i ≤ t)).card := by
        exact ⟨ ⟨ ( Finset.card ( Finset.filter ( fun i => p i ≤ t ) Finset.univ ) - 1 ), Nat.lt_of_lt_of_le ( Nat.pred_lt hN ) ( Nat.le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ⟩, rfl, Nat.pred_lt hN ⟩;
      -- By `monotone_fin_filter_le_card_iff`, we have `p (σ j) ≤ t`.
      have h_pj_le_t : p (σ j) ≤ t := by
        have h_pj_le_t : (Finset.univ.filter (fun i => p (σ i) ≤ t)).card ≥ j.val + 1 := by
          rw [ Finset.card_filter ] at *;
          rw [ Equiv.sum_comp σ fun i => if p i ≤ t then 1 else 0 ] ; aesop;
        contrapose! h_pj_le_t;
        exact lt_of_le_of_lt ( Finset.card_le_card fun i hi => Finset.mem_Iio.mpr <| show i < j from lt_of_not_ge fun hi' => by linarith [ Finset.mem_filter.mp hi, hmono hi' ] ) ( by simp );
      have := hgrid j;
      rw [ div_le_iff₀ ( by positivity ), lt_div_iff₀ ( by positivity ) ] at this ; nlinarith [ show ( j : ℝ ) + 1 = Finset.card ( Finset.filter ( fun i => p i ≤ t ) Finset.univ ) by exact_mod_cast by omega ];
  · by_cases hN : Finset.card (Finset.filter (fun i => p i ≤ t) Finset.univ) < Q;
    · -- Since $N < Q$, we have $t < p (σ N)$.
      have h_lt : t < p (σ ⟨Finset.card (Finset.filter (fun i => p i ≤ t) Finset.univ), by linarith⟩) := by
        have h_lt : ∀ i : Fin Q, (Finset.univ.filter (fun j => p (σ j) ≤ t)).card ≤ i.val → t < p (σ i) := by
          intros i hi_card
          by_contra h_contra
          have h_filter : Finset.filter (fun j => p (σ j) ≤ t) Finset.univ ⊇ Finset.Iic i := by
            exact fun j hj => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_trans ( hmono <| Finset.mem_Iic.mp hj ) <| le_of_not_gt h_contra ⟩;
          exact absurd ( Finset.card_le_card h_filter ) ( by simpa [ Finset.card_univ ] using by linarith );
        convert h_lt ⟨ Finset.card ( Finset.filter ( fun i => p i ≤ t ) Finset.univ ), by linarith ⟩ _;
        convert Finset.card_image_le;
        rotate_left;
        exact fun i => σ.symm i;
        infer_instance;
        ext; simp +decide [ Equiv.symm_apply_eq ] ;
      have := hgrid ⟨ Finset.card ( Finset.filter ( fun i => p i ≤ t ) Finset.univ ), by linarith ⟩ ; rw [ lt_div_iff₀ ( by positivity ) ] at *; nlinarith [ show ( Q : ℝ ) ≥ 1 by norm_cast ] ;
    · norm_num [ show Finset.card ( Finset.filter ( fun i => p i ≤ t ) Finset.univ ) = Q from le_antisymm ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ( not_lt.mp hN ) ] at *;
      have := hgrid ⟨ 0, hQ ⟩ ; have := hgrid ⟨ Q - 1, Nat.sub_lt hQ zero_lt_one ⟩ ; rcases Q with ( _ | _ | Q ) <;> norm_num at *;
      · contradiction;
      · linarith [ hmem ( σ 0 ) ];
      · rw [ div_le_iff₀, lt_div_iff₀ ] at * <;> nlinarith [ hmem ( σ 0 ), hmem ( σ ⟨ Q + 1, by linarith ⟩ ) ]

/-! ## The centered orbit grid property -/

/-- **Centered orbit grid property.**

The honest centered replacement of the false grid-balanced orbit partition.  For
each `n` and base point `x` there is a sorting permutation `σ` of the `q n` orbit
points `fract (x − j θ)` and a recentering constant `c` such that the sorted
points are monotone and the `i`-th sorted point lies in the shifted grid cell
`[(i−c)/(q n), (i+1−c)/(q n))`.

This is the three-distance / best-approximation theorem for convergent
denominators, isolated as a finite combinatorial statement.  It is strictly
smaller than the all-`t` centered discrepancy field of
`ContinuedFractionStarDiscrepancyData`. -/
def StandardCenteredOrbitGridProperty (θ : ℝ) (q : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (x : ℝ),
    ∃ (σ : Equiv.Perm (Fin (q n))) (c : ℝ),
      Monotone (fun i : Fin (q n) => Int.fract (x - ((σ i : ℕ) : ℝ) * θ)) ∧
      ∀ i : Fin (q n),
        ((i : ℝ) - c) / (q n : ℝ) ≤ Int.fract (x - ((σ i : ℕ) : ℝ) * θ) ∧
        Int.fract (x - ((σ i : ℕ) : ℝ) * θ) < ((i : ℝ) + 1 - c) / (q n : ℝ)

/-- **Centered orbit grid ⇒ centered star-discrepancy field.**

From the centered orbit grid property for a positive denominator sequence `q`,
the centered orbit star-discrepancy bound (the `centered_star_discrepancy_le_one`
field of `ContinuedFractionStarDiscrepancyData`) follows. -/
theorem continued_fraction_centered_star_discrepancy_le_one {θ : ℝ} {q : ℕ → ℕ}
    (hq : ∀ n, 0 < q n) (H : StandardCenteredOrbitGridProperty θ q) :
    ∀ (n : ℕ) (x : ℝ), ∃ c : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |orbitDiscrepancy θ (q n) x t - c| ≤ 1 := by
  intro n x
  obtain ⟨σ, c, hmono, hgrid⟩ := H n x
  refine ⟨c, fun t ht => ?_⟩
  have hcard := centered_discrepancy_abs_le_one_of_centered_grid (hq n)
    (fun i : Fin (q n) => Int.fract (x - ((i : ℕ) : ℝ) * θ))
    (fun i => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) σ c hmono hgrid t ht
  rw [orbitDiscrepancy, orbitCount_eq_fin_card]
  exact hcard

/-! ## Constructing the corrected star-discrepancy data from the centered grid -/

/-- **Constructor: centered orbit grid ⇒ corrected star-discrepancy data.**

Given rotation return data `R` with diverging denominators, irrationality of `θ`,
and the centered orbit grid property for `R.q`, this assembles the honest
`ContinuedFractionStarDiscrepancyData θ` — with the true centered
star-discrepancy bound discharged from the (strictly smaller, finite) grid
property via `continued_fraction_centered_star_discrepancy_le_one`.  No false
grid-balanced `orbit_partition` and no false unsigned `≤ 1` bound are used. -/
def ContinuedFractionStarDiscrepancyData.ofCenteredOrbitGrid {θ : ℝ}
    (R : RotationReturnData θ) (hqt : Tendsto R.q atTop atTop) (hθ : Irrational θ)
    (H : StandardCenteredOrbitGridProperty θ R.q) :
    ContinuedFractionStarDiscrepancyData θ where
  toRotationReturnData := R
  q_tendsto := hqt
  hθ := hθ
  centered_star_discrepancy_le_one :=
    continued_fraction_centered_star_discrepancy_le_one R.q_pos H

/-- **`ContinuedFractionStarDiscrepancyData` proved from the centered grid.**

The honest corrected star-discrepancy data, built from the centered orbit grid
property (the isolated three-distance blocker).  This is the existence form
requested as `ContinuedFractionStarDiscrepancyData_proved`. -/
theorem ContinuedFractionStarDiscrepancyData_proved {θ : ℝ}
    (R : RotationReturnData θ) (hqt : Tendsto R.q atTop atTop) (hθ : Irrational θ)
    (H : StandardCenteredOrbitGridProperty θ R.q) :
    Nonempty (ContinuedFractionStarDiscrepancyData θ) :=
  ⟨ContinuedFractionStarDiscrepancyData.ofCenteredOrbitGrid R hqt hθ H⟩

/-- **Faithful periodic real Denjoy–Koksma data from the proved centered
discrepancy.**  Composes the centered-grid constructor with the recentered Koksma
inequality (`koksma_real_periodic_centered`, via
`RealDenjoyKoksmaPeriodic.ofContinuedFractionStarDiscrepancyData`). -/
noncomputable def real_denjoy_koksma_periodic_from_proved_centered_discrepancy
    {θ : ℝ} (R : RotationReturnData θ) (hqt : Tendsto R.q atTop atTop)
    (hθ : Irrational θ) (H : StandardCenteredOrbitGridProperty θ R.q) :
    RealDenjoyKoksmaPeriodic θ :=
  RealDenjoyKoksmaPeriodic.ofContinuedFractionStarDiscrepancyData
    (ContinuedFractionStarDiscrepancyData.ofCenteredOrbitGrid R hqt hθ H)

end CriticalMixedHRT