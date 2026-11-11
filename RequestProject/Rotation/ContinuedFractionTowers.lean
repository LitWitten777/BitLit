import Mathlib
import RequestProject.Rotation.DenjoyKoksmaDischarge
import RequestProject.Rotation.OrbitPartition

/-!
# Star-discrepancy combinatorics for the orbit (the isolated remaining target)

The faithful (periodic) real Denjoy–Koksma interface `RealDenjoyKoksmaPeriodic θ`
(see `RequestProject.Rotation.OrbitPartition`) carries the analytic inequality
over *all* `1`-periodic bounded-variation zero-mean functions.  Classically that
analytic statement follows from a single purely *combinatorial* fact about the
orbit — the **star-discrepancy bound** — via **Koksma's inequality**.

This module isolates that combinatorial fact:

```
|#{ j < Q : fract (x - j θ) ≤ t } − Q · t| ≤ 1   for all t ∈ [0,1].
```

For continued-fraction return denominators `Q = q n` this bound is the classical
three-gap / best-approximation discrepancy estimate (not in Mathlib).  It is a
*strictly smaller and more combinatorial* interface than the analytic
`dk_real_periodic` field: it makes no reference to bounded variation, integrals,
or arbitrary functions — only to counting orbit points.

## What is proved here (no `sorry`)

* the orbit-counting / discrepancy definitions;
* the candidate strictly-smaller interface `StandardRealDenjoyKoksmaCombinatorics`;
* the periodicity reduction `periodic_eval_fract` (Birkhoff sums of a periodic
  function only see the fractional parts of the orbit), an ingredient of Koksma's
  inequality;
* the boundary value `orbitDiscrepancy_one` of the discrepancy function.

## What remains (the exact isolated gap)

Two classical facts not in Mathlib:

1. **Koksma's inequality** (analytic reduction): from `star_discrepancy_le_one`,
   derive the `dk_real_periodic` field of `RealDenjoyKoksmaPeriodic θ`.  Its proof
   is Stieltjes integration by parts pairing the discrepancy with the Stieltjes
   measure of a bounded-variation function, machinery currently absent from
   Mathlib.
2. **The discrepancy bound itself** for continued-fraction denominators (the
   three-gap / best-approximation estimate).

Given a proof of (1) as `koksma_real_periodic`, the constructor
`RealDenjoyKoksmaPeriodic.ofCombinatorics` (below in commented form) would build
the faithful interface from `StandardRealDenjoyKoksmaCombinatorics`.
-/

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

namespace CriticalMixedHRT

/-- Number of orbit points `fract (x - j θ)`, `j < Q`, lying in `[0, t]`. -/
noncomputable def orbitCount (θ : ℝ) (Q : ℕ) (x t : ℝ) : ℕ :=
  ((Finset.range Q).filter (fun j => Int.fract (x - (j : ℝ) * θ) ≤ t)).card

/-- The signed (unnormalized) star-discrepancy function of the orbit segment:
`#{ j < Q : fract (x - j θ) ≤ t } − Q · t`. -/
noncomputable def orbitDiscrepancy (θ : ℝ) (Q : ℕ) (x t : ℝ) : ℝ :=
  (orbitCount θ Q x t : ℝ) - (Q : ℝ) * t

/-- **The candidate strictly-smaller combinatorial interface.**

`DEPRECATED_FALSE_AS_STATED`.  The `star_discrepancy_le_one` field (`≤ 1`) of this
structure is **mathematically false**, so the structure is *uninhabitable* and
must not be used as final evidence.  Counterexample (verified in Lean): for the
golden-ratio conjugate `θ = (√5−1)/2`, the convergent denominator `q n = 8`, base
point `x = 1/10` and threshold `t = 1/10`, the orbit star-discrepancy equals
`6/5 > 1` — see `CriticalMixedHRT.star_discrepancy_le_one_false`.  The honest
replacement is `CriticalMixedHRT.ContinuedFractionStarDiscrepancyData`, carrying
the *true* centered star-discrepancy bound (`|orbitDiscrepancy θ (q n) x t − c| ≤ 1`
for a recentering constant `c`, i.e. oscillation `≤ 2`); via the recentered
Koksma inequality `CriticalMixedHRT.koksma_real_periodic_centered` it yields the
faithful periodic Denjoy–Koksma data directly
(`RequestProject.Rotation.StarDiscrepancyCorrection`).

Bundles the rotation return data with divergence of the denominators and the
orbit star-discrepancy bound `≤ 1` over the convergent denominators.  This is the
purely combinatorial heart of the Denjoy–Koksma theorem; everything analytic
(bounded variation, integrals, Koksma's inequality) is derived from it.

Compared with the analytic `RealDenjoyKoksmaPeriodic.dk_real_periodic` field, this
interface is *strictly smaller and more combinatorial*: it quantifies only over
the real parameters `n, x, t` and an integer count, with no reference to
bounded-variation functions, total variation, or integrals. -/
structure StandardRealDenjoyKoksmaCombinatorics (θ : ℝ) extends RotationReturnData θ where
  /-- The return denominators diverge to infinity. -/
  q_tendsto : Tendsto toRotationReturnData.q atTop atTop
  /-- The orbit star-discrepancy over the convergent denominators is `≤ 1`. -/
  star_discrepancy_le_one :
    ∀ (n : ℕ) (x : ℝ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      |orbitDiscrepancy θ (toRotationReturnData.q n) x t| ≤ 1

/-
A `1`-periodic function evaluated at a real point equals its value at the
fractional part of that point.  Hence the Birkhoff sums appearing in
Denjoy–Koksma only see the fractional parts of the orbit `x - j θ`, which is what
the star-discrepancy counts.  This is the first reduction step of Koksma's
inequality.
-/
theorem periodic_eval_fract {h : ℝ → ℝ} (hper : Function.Periodic h 1) (y : ℝ) :
    h y = h (Int.fract y) := by
  simpa [ Int.fract_eq_iff ] using Function.Periodic.int_mul hper ( ⌊y⌋ ) ( Int.fract y )

/-
The discrepancy vanishes at the right endpoint `t = 1`: every fractional part
`fract (x - j θ)` lies in `[0,1)`, so all `Q` points are counted, giving
`orbitDiscrepancy θ Q x 1 = Q - Q·1 = 0`.
-/
theorem orbitDiscrepancy_one (θ : ℝ) (Q : ℕ) (x : ℝ) :
    orbitDiscrepancy θ Q x 1 = 0 := by
  unfold orbitDiscrepancy orbitCount;
  rw [ Finset.filter_true_of_mem ] <;> norm_num;
  · rw [ Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range, sub_self ];
  · exact fun a ha => Int.fract_lt_one _ |> le_of_lt

/-
The faithful periodic interface from the combinatorial interface, *conditional on
Koksma's inequality*.  Uncomment once `koksma_real_periodic` (Stieltjes
integration by parts) is available:

```
theorem koksma_real_periodic {θ : ℝ} (Q : ℕ) (x : ℝ)
    (hdisc : ∀ t ∈ Set.Icc (0 : ℝ) 1, |orbitDiscrepancy θ Q x t| ≤ 1)
    (h : ℝ → ℝ) (hper : Function.Periodic h 1) (hbv : ConcreteHasBVReal h)
    (hmean : periodMeanReal h = 0) :
    |∑ j ∈ Finset.range Q, h (x - (j : ℝ) * θ)| ≤ concreteVariationReal h

noncomputable def RealDenjoyKoksmaPeriodic.ofCombinatorics {θ : ℝ}
    (C : StandardRealDenjoyKoksmaCombinatorics θ) : RealDenjoyKoksmaPeriodic θ where
  toRotationReturnData := C.toRotationReturnData
  q_tendsto := C.q_tendsto
  dk_real_periodic := fun h hper hbv hmean n x =>
    koksma_real_periodic (C.toRotationReturnData.q n) x
      (fun t ht => C.star_discrepancy_le_one n x t ht) h hper hbv hmean
```
-/

end CriticalMixedHRT