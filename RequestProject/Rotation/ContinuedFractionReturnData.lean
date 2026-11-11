import Mathlib
import RequestProject.Rotation.PeriodicKoksma

/-!
# Enriched continued-fraction return data and the star-discrepancy bound

The corrected periodic Denjoy–Koksma chain is reduced (see
`RequestProject.Rotation.PeriodicKoksma`) to the single combinatorial input
`StandardRealDenjoyKoksmaCombinatorics θ`, whose only nontrivial field is the
orbit **star-discrepancy bound**

```
|orbitDiscrepancy θ (q n) x t| ≤ 1   for t ∈ [0,1].
```

The abstract `RotationReturnData θ` only records `q n · θ − p n → 0`, which is
**not** enough for this bound: the star-discrepancy estimate needs the
best-approximation / orbit-partition structure of continued-fraction
convergents.

This module isolates exactly that missing number-theoretic content as the
**orbit-partition** field of an enriched structure
`ContinuedFractionReturnData θ`, and then *proves* the star-discrepancy bound
from it.  The orbit-partition field states the classical fact that, for a
continued-fraction return denominator `Q = q n`, the `Q` orbit points
`fract (x − j θ)`, `j < Q`, are **grid-balanced**: after sorting, the `i`-th
point lies in the grid cell `[i/Q, (i+1)/Q)`.  This is the standard
three-gap / best-approximation equidistribution property of convergent
denominators, and it is exactly equivalent to the discrepancy bound `≤ 1`.

Consequently this module provides the adapter

```
ContinuedFractionReturnData.toStandardRealDenjoyKoksmaCombinatorics
```

so that the *entire* corrected periodic Denjoy–Koksma chain is reduced to
constructing a `ContinuedFractionReturnData θ` (equivalently, establishing the
grid-balanced orbit partition for convergent denominators).

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]` are introduced.
-/

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

namespace CriticalMixedHRT

/-! ## The combinatorial grid ⇒ discrepancy core -/

/-
For a monotone function on `Fin Q`, the points lying below a threshold `t`
form an initial segment: `f i ≤ t` holds **iff** `i` is among the first
`#{ j : f j ≤ t }` indices.  This is the key down-set lemma behind the
discrepancy bound.
-/
theorem monotone_fin_filter_le_card_iff {Q : ℕ} (f : Fin Q → ℝ) (hf : Monotone f)
    (t : ℝ) (i : Fin Q) :
    f i ≤ t ↔ (i : ℕ) < (Finset.univ.filter (fun j : Fin Q => f j ≤ t)).card := by
  constructor <;> intro hi;
  · refine' lt_of_lt_of_le _ ( Finset.card_mono <| show Finset.Iic i ⊆ Finset.filter ( fun j => f j ≤ t ) Finset.univ from fun j hj => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hf ( Finset.mem_Iic.mp hj ) |> le_trans <| hi ⟩ ) ; aesop;
  · contrapose! hi;
    exact le_trans ( Finset.card_le_card fun j hj => Finset.mem_Iio.mpr <| show j < i from lt_of_not_ge fun h => not_lt_of_ge ( Finset.mem_filter.mp hj |>.2 ) <| lt_of_lt_of_le hi <| hf h ) ( by simp )

/-
**Grid ⇒ discrepancy.**  If a family `p : Fin Q → ℝ` admits a sorting
permutation `σ` with `p ∘ σ` monotone and grid-balanced
(`p (σ i) ∈ [i/Q, (i+1)/Q)`), then the unnormalized star-discrepancy of `p` at
any `t ∈ [0,1]` is at most `1` in absolute value.
-/
theorem discrepancy_abs_le_one_of_grid {Q : ℕ} (hQ : 0 < Q) (p : Fin Q → ℝ)
    (σ : Equiv.Perm (Fin Q))
    (hmono : Monotone (fun i : Fin Q => p (σ i)))
    (hgrid : ∀ i : Fin Q,
        (i : ℝ) / (Q : ℝ) ≤ p (σ i) ∧ p (σ i) < ((i : ℝ) + 1) / (Q : ℝ))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |((Finset.univ.filter (fun i : Fin Q => p i ≤ t)).card : ℝ) - (Q : ℝ) * t| ≤ 1 := by
  refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
  · by_cases hc : (Finset.univ.filter (fun i => p i ≤ t)).card = 0;
    · norm_num [ hc ] ; nlinarith [ ht.1, ht.2 ];
    · have h_card : (Finset.univ.filter (fun i => p i ≤ t)).card - 1 < Q := by
        exact lt_of_lt_of_le ( Nat.sub_lt ( Nat.pos_of_ne_zero hc ) zero_lt_one ) ( le_trans ( Finset.card_le_univ _ ) ( by simp ) )
      have h_card_le : ((Finset.univ.filter (fun i => p i ≤ t)).card - 1 : ℝ) / Q ≤ t := by
        have h_card_le : p (σ ⟨(Finset.univ.filter (fun i => p i ≤ t)).card - 1, h_card⟩) ≤ t := by
          have h_card_le : (Finset.univ.filter (fun i => p (σ i) ≤ t)).card = (Finset.univ.filter (fun i => p i ≤ t)).card := by
            rw [ Finset.card_filter, Finset.card_filter ];
            conv_rhs => rw [ ← Equiv.sum_comp σ ] ;
          convert monotone_fin_filter_le_card_iff ( fun i => p ( σ i ) ) hmono t ⟨ ( Finset.univ.filter ( fun i => p i ≤ t ) |> Finset.card ) - 1, h_card ⟩ |>.2 _ using 1;
          exact h_card_le.symm ▸ Nat.pred_lt hc;
        convert le_trans _ h_card_le using 1;
        convert hgrid _ |>.1 using 1 ; norm_num [ Nat.cast_sub ( Nat.one_le_iff_ne_zero.mpr hc ) ]
      have h_card_le' : ((Finset.univ.filter (fun i => p i ≤ t)).card : ℝ) ≤ Q * t + 1 := by
        rw [ div_le_iff₀ ] at h_card_le <;> first | positivity | linarith;
      linarith [h_card_le'];
  · by_cases hc : (Finset.univ.filter (fun i => p i ≤ t)).card < Q;
    · -- By `monotone_fin_filter_le_card_iff f hmono t`, for every `i : Fin Q`, `f i ≤ t ↔ (i:ℕ) < c`.
      have h_filter : ∀ i : Fin Q, (p (σ i)) ≤ t ↔ i.val < (Finset.univ.filter (fun i => p i ≤ t)).card := by
        convert monotone_fin_filter_le_card_iff ( fun i => p ( σ i ) ) hmono t using 1;
        rw [ Finset.card_filter, Finset.card_filter ];
        rw [ Equiv.sum_comp σ fun i => if p i ≤ t then 1 else 0 ];
      -- By `h_filter`, we have `t < p (σ (Fin.mk c hc))`.
      have h_t_lt : t < p (σ (Fin.mk (Finset.univ.filter (fun i => p i ≤ t)).card hc)) := by
        exact lt_of_not_ge fun h => by have := h_filter ⟨ Finset.card ( Finset.filter ( fun i => p i ≤ t ) Finset.univ ), hc ⟩ ; aesop;
      have := hgrid ⟨ Finset.card ( Finset.filter ( fun i => p i ≤ t ) Finset.univ ), hc ⟩ ; rw [ lt_div_iff₀ ( by positivity ) ] at this; norm_num at * ; nlinarith;
    · nlinarith [ show ( Finset.card ( Finset.filter ( fun i => p i ≤ t ) Finset.univ ) : ℝ ) ≥ Q by exact_mod_cast le_of_not_gt hc, ht.1, ht.2 ]

/-- **Orbit-partition ⇒ star-discrepancy bound.**  If the `Q` orbit points
`fract (x − j θ)`, `j < Q`, are grid-balanced via a sorting permutation `σ`, then
the orbit star-discrepancy at `t ∈ [0,1]` is `≤ 1`. -/
theorem orbitDiscrepancy_abs_le_one_of_orbit_partition {θ : ℝ} {Q : ℕ} (hQ : 0 < Q)
    (x t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (σ : Equiv.Perm (Fin Q))
    (hmono : Monotone (fun i : Fin Q => Int.fract (x - ((σ i : ℕ) : ℝ) * θ)))
    (hgrid : ∀ i : Fin Q,
        (i : ℝ) / (Q : ℝ) ≤ Int.fract (x - ((σ i : ℕ) : ℝ) * θ) ∧
        Int.fract (x - ((σ i : ℕ) : ℝ) * θ) < ((i : ℝ) + 1) / (Q : ℝ)) :
    |orbitDiscrepancy θ Q x t| ≤ 1 := by
  have hcard := discrepancy_abs_le_one_of_grid hQ
    (fun i : Fin Q => Int.fract (x - ((i : ℕ) : ℝ) * θ)) σ hmono hgrid t ht
  rw [orbitDiscrepancy, orbitCount_eq_fin_card]
  exact hcard

/-! ## The enriched continued-fraction return-data structure -/

/-- **Enriched continued-fraction return data.**

`DEPRECATED_FALSE_AS_STATED`.  The `orbit_partition` (grid-balancedness) field of
this structure is **mathematically false**, so the structure is *uninhabitable*
and must not be used as final evidence.  Counterexample (verified in Lean): for
the golden-ratio conjugate `θ = (√5−1)/2`, the convergent (Fibonacci) denominator
`q n = 8` and base point `x = 1/10`, the sorted orbit's grid-cell indices are
`[0,0,1,3,3,5,6,6]` (cell `0` doubled, cells `2,4,7` missed), so no sorting
permutation is grid-balanced.  In fact even the *weaker* unsigned bound
`star_discrepancy_le_one` (`≤ 1`) derived below is false (the discrepancy reaches
`6/5` here) — see `CriticalMixedHRT.star_discrepancy_le_one_false`.  The honest
replacement is `CriticalMixedHRT.ContinuedFractionStarDiscrepancyData`, carrying
the *true* centered star-discrepancy (oscillation `≤ 2`) bound
(`RequestProject.Rotation.StarDiscrepancyCorrection`).

Extends the abstract `RotationReturnData θ` with the genuinely number-theoretic
content that the abstract data lacks: the divergence of the denominators and the
**grid-balanced orbit partition** of each convergent-denominator orbit.

The `orbit_partition` field is the classical three-gap / best-approximation fact
for continued-fraction convergents: the `q n` orbit points `fract (x − j θ)`,
`j < q n`, after sorting, fall one per grid cell `[i/(q n), (i+1)/(q n))`.  It is
exactly the content needed (and equivalent) to the orbit star-discrepancy bound
`≤ 1`; the latter is derived below in
`ContinuedFractionReturnData.star_discrepancy_le_one`. -/
structure ContinuedFractionReturnData (θ : ℝ) extends RotationReturnData θ where
  /-- The return denominators diverge to infinity. -/
  q_tendsto : Tendsto toRotationReturnData.q atTop atTop
  /-- **Grid-balanced orbit partition** for each convergent-denominator orbit:
  for every `n` and base point `x` there is a sorting permutation `σ` of the
  `q n` orbit points `fract (x − j θ)` making them monotone and placing the
  `i`-th sorted point in the grid cell `[i/(q n), (i+1)/(q n))`. -/
  orbit_partition :
    ∀ (n : ℕ) (x : ℝ),
      ∃ σ : Equiv.Perm (Fin (toRotationReturnData.q n)),
        Monotone (fun i : Fin (toRotationReturnData.q n) =>
          Int.fract (x - ((σ i : ℕ) : ℝ) * θ)) ∧
        ∀ i : Fin (toRotationReturnData.q n),
          (i : ℝ) / (toRotationReturnData.q n : ℝ)
              ≤ Int.fract (x - ((σ i : ℕ) : ℝ) * θ) ∧
          Int.fract (x - ((σ i : ℕ) : ℝ) * θ)
              < ((i : ℝ) + 1) / (toRotationReturnData.q n : ℝ)

namespace ContinuedFractionReturnData

variable {θ : ℝ} (D : ContinuedFractionReturnData θ)

/-- **The orbit star-discrepancy bound, derived from the grid-balanced orbit
partition.**  This is exactly the `star_discrepancy_le_one` field of
`StandardRealDenjoyKoksmaCombinatorics θ`. -/
theorem star_discrepancy_le_one :
    ∀ (n : ℕ) (x : ℝ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      |orbitDiscrepancy θ (D.toRotationReturnData.q n) x t| ≤ 1 := by
  intro n x t ht
  obtain ⟨σ, hmono, hgrid⟩ := D.orbit_partition n x
  exact orbitDiscrepancy_abs_le_one_of_orbit_partition (D.q_pos n) x t ht σ hmono hgrid

/-- **Adapter: enriched continued-fraction return data yields the combinatorial
star-discrepancy interface.**  Composed with the discharged Koksma inequality,
this reduces the whole corrected periodic Denjoy–Koksma chain to constructing a
`ContinuedFractionReturnData θ`. -/
def toStandardRealDenjoyKoksmaCombinatorics :
    StandardRealDenjoyKoksmaCombinatorics θ where
  toRotationReturnData := D.toRotationReturnData
  q_tendsto := D.q_tendsto
  star_discrepancy_le_one := D.star_discrepancy_le_one

end ContinuedFractionReturnData

/-- **Faithful periodic real Denjoy–Koksma data from enriched
continued-fraction return data.**  Koksma's inequality having been discharged,
this builds `RealDenjoyKoksmaPeriodic θ` directly from a
`ContinuedFractionReturnData θ`. -/
noncomputable def RealDenjoyKoksmaPeriodic.ofContinuedFractionReturnData {θ : ℝ}
    (D : ContinuedFractionReturnData θ) : RealDenjoyKoksmaPeriodic θ :=
  RealDenjoyKoksmaPeriodic.ofStarDiscrepancy
    D.toStandardRealDenjoyKoksmaCombinatorics

end CriticalMixedHRT