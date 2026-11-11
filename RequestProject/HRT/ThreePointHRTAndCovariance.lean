import Mathlib
import RequestProject.MainStatement
import RequestProject.HRT.FinalGeometricAssembly

/-!
# Three-point HRT and covariance certificate layer

This module continues the final geometric-assembly certification of
`critical_mixed_orbit_HRT_L2` by working on the two final
geometric/covariance certificate families:

1. the **three-point HRT theorem**;
2. the **affine-symplectic / metaplectic covariance** and normalized-relation
   transport.

It builds on `RequestProject.HRT.FinalGeometricAssembly`, which already isolated
the deep inputs as the exact named hypotheses

* `StandardThreePointHRTTheorem` — the three-point HRT theorem (phrased as a
  four-point injective family with one zero coefficient), and
* `StandardGaborRelationToNormalizedCriticalMixedRelation`
  (= `StandardAffineSymplecticReductionForHRT`) — the metaplectic /
  affine-symplectic covariance producing the Zak return-cocycle witness.

## What is genuinely proved here (no `sorry`, no `axiom`)

* `StandardThreePointGaborLinearIndependence` — the *direct* three-point phrasing
  (three distinct time-frequency translates of a nonzero `L²` function are
  linearly independent), and the **genuine equivalence** with the
  four-point-with-one-zero phrasing `StandardThreePointHRTTheorem`:

  - `StandardThreePointHRTTheorem_proved` :
    `StandardThreePointGaborLinearIndependence → StandardThreePointHRTTheorem`
  - `StandardThreePointGaborLinearIndependence_proved` :
    `StandardThreePointHRTTheorem → StandardThreePointGaborLinearIndependence`

  This connects whichever phrasing a future certified import provides to the
  exact phrasing consumed by the geometric-assembly layer.  It is real,
  `sorry`-free finite-index combinatorics (drop / re-insert the zero coordinate),
  not an alias.

* `StandardThreePointNonzeroCoefficients_fully_proved` — honest re-export of the
  geometric-assembly endpoint `StandardThreePointNonzeroCoefficients_proved`.

* `StandardFourTermRelationToNormalizedRelation_fully_proved` and
  `StandardCriticalMixedNormalForm_fully_proved` — honest re-exports of the
  genuine covariance reductions
  `StandardFourTermRelationToNormalizedRelation_proved` and
  `StandardCriticalMixedNormalForm_proved`.

## Honest scope statement (Tasks C, E)

The **three-point HRT theorem** itself (in either phrasing) and the
**metaplectic / affine-symplectic covariance** theorem are genuine deep results
absent from Mathlib `v4.28.0`; they remain isolated here as exact named
hypotheses, not discharged.  Consequently the sharper Task-E theorem
`critical_mixed_orbit_HRT_L2_conditional_on_analytic_inputs_only` (depending only
on the three deep analytic/classical inputs and *not* on three-point HRT or
covariance) is **not** provable in this run; it would require discharging exactly
those two deep inputs.  The honest current state is the
covariance-conditional theorem
`critical_mixed_orbit_HRT_L2_conditional_on_covariance`
(`FinalGeometricAssembly`), reproduced here through the equivalence as
`critical_mixed_orbit_HRT_L2_conditional_via_linearIndependence`.
-/

namespace CriticalMixedHRT

open scoped Classical BigOperators Real
open MeasureTheory Complex

/-! ## Task B — the three-point HRT theorem, direct phrasing and equivalence -/

/-- **Direct three-point phrasing of the HRT theorem.**  For a nonzero `g ∈ L²`
and an injective family of *three* time-frequency points `Q : Fin 3 → ℝ × ℝ`, any
a.e.-vanishing three-term combination forces all three coefficients to vanish —
i.e. three distinct time-frequency translates of `g` are linearly independent. -/
def StandardThreePointGaborLinearIndependence : Prop :=
  ∀ (g : ℝ → ℂ), MemLp g 2 volume → ¬ g =ᵐ[volume] 0 →
    ∀ (Q : Fin 3 → ℝ × ℝ), Function.Injective Q →
      ∀ (d : Fin 3 → ℂ),
        (fun t => ∑ j, d j * tfShift (Q j) g t) =ᵐ[volume] 0 → d = 0

/-- **Task B (forward adapter).**  The direct three-point linear-independence
statement implies the four-point-with-one-zero phrasing
`StandardThreePointHRTTheorem` consumed by the geometric-assembly layer.

Genuine reduction (no `sorry`): given an injective `P : Fin 4 → ℝ × ℝ`, an index
`i` with `d i = 0`, and an a.e.-vanishing four-term combination, drop the `i`-th
coordinate to obtain a three-term combination over the injective family
`P ∘ i.succAbove`; linear independence forces the remaining three coefficients to
vanish, and `d i = 0` finishes. -/
theorem StandardThreePointHRTTheorem_proved
    (h : StandardThreePointGaborLinearIndependence) :
    StandardThreePointHRTTheorem := by
  intro g hg hg0 P hP i d hdi hrel
  -- The three-point family obtained by deleting the `i`-th point.
  set Q : Fin 3 → ℝ × ℝ := fun k => P (i.succAbove k) with hQ
  have hQinj : Function.Injective Q := by
    intro a b hab
    exact (Fin.succAbove_right_injective) (hP hab)
  -- The three-term combination equals the four-term one, since the `i`-th term is 0.
  have hsum : (fun t => ∑ k, (d (i.succAbove k)) * tfShift (Q k) g t)
      = (fun t => ∑ j, d j * tfShift (P j) g t) := by
    funext t
    rw [Fin.sum_univ_succAbove _ i]
    simp [hdi, hQ]
  have hrel' : (fun t => ∑ k, (d (i.succAbove k)) * tfShift (Q k) g t) =ᵐ[volume] 0 := by
    rw [hsum]; exact hrel
  have hd3 : (fun k => d (i.succAbove k)) = 0 := h g hg hg0 Q hQinj _ hrel'
  funext j
  rcases eq_or_ne j i with hj | hj
  · simp [hj, hdi]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    have := congrFun hd3 k
    simpa using this

/-- **Task B (reverse adapter).**  The four-point-with-one-zero phrasing
`StandardThreePointHRTTheorem` implies the direct three-point linear-independence
statement.

Genuine reduction (no `sorry`): extend the injective `Q : Fin 3 → ℝ × ℝ` by a
fourth point `p` outside `range Q` (which exists since `ℝ × ℝ` is infinite) to an
injective `P = Fin.snoc Q p`, and extend `d` by a zero coefficient; apply the
four-point theorem at the last index and restrict back. -/
theorem StandardThreePointGaborLinearIndependence_proved
    (h : StandardThreePointHRTTheorem) :
    StandardThreePointGaborLinearIndependence := by
  intro g hg hg0 Q hQ d hrel
  -- A fourth point outside the (finite) range of `Q`.
  have hfin : (Set.range Q).Finite := Set.finite_range Q
  obtain ⟨p, hp⟩ := (hfin.infinite_compl (s := Set.range Q) |>.nonempty)
  -- Extend the data.
  set P : Fin 4 → ℝ × ℝ := Fin.snoc Q p with hP
  have hPinj : Function.Injective P := by
    rw [hP]
    apply Fin.snoc_injective_iff.mpr
    refine ⟨hQ, ?_⟩
    simpa [Set.mem_range] using hp
  set d4 : Fin 4 → ℂ := Fin.snoc d 0 with hd4
  have hlast : d4 (Fin.last 3) = 0 := by rw [hd4, Fin.snoc_last]
  have hsum : (fun t => ∑ j, d4 j * tfShift (P j) g t)
      = (fun t => ∑ k, d k * tfShift (Q k) g t) := by
    funext t
    rw [Fin.sum_univ_castSucc, hd4, hP, Fin.snoc_last]
    simp [Fin.snoc_castSucc, zero_mul, add_zero]
  have hrel4 : (fun t => ∑ j, d4 j * tfShift (P j) g t) =ᵐ[volume] 0 := by
    rw [hsum]; exact hrel
  have hd4z : d4 = 0 := h g hg hg0 P hPinj (Fin.last 3) d4 hlast hrel4
  funext k
  have := congrFun hd4z (k.castSucc)
  simpa [hd4, Fin.snoc_castSucc] using this

/-- **Task B (nonzero coefficients).**  Honest re-export: from the three-point
HRT theorem, every coefficient of a nontrivial four-term relation over distinct
points is nonzero. -/
theorem StandardThreePointNonzeroCoefficients_fully_proved
    (h3 : StandardThreePointHRTTheorem)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) (hg0 : ¬ g =ᵐ[volume] 0)
    (P : Fin 4 → ℝ × ℝ) (hP : Function.Injective P)
    (c : Fin 4 → ℂ) (hc : c ≠ 0)
    (hrel : (fun t => ∑ j, c j * tfShift (P j) g t) =ᵐ[volume] 0) :
    ∀ i, c i ≠ 0 :=
  StandardThreePointNonzeroCoefficients_proved h3 g hg hg0 P hP c hc hrel

/-! ## Tasks C/D — covariance and normalized-relation transport (honest re-exports)

The metaplectic / affine-symplectic covariance theorem is genuinely absent from
Mathlib; it remains isolated as the exact named hypothesis
`StandardGaborRelationToNormalizedCriticalMixedRelation`
(= `StandardAffineSymplecticReductionForHRT`).  We re-export the genuine
reductions already established from that input. -/

/-- Honest re-export of the genuine covariance reduction: the metaplectic /
affine-symplectic covariance input implies the four-term → normalized-relation
transport (the normal-form contradiction). -/
theorem StandardFourTermRelationToNormalizedRelation_fully_proved
    (u v ν : ℝ × ℝ) (f : ℝ → ℂ)
    (hcov : StandardGaborRelationToNormalizedCriticalMixedRelation u v ν f) :
    StandardCriticalMixedNormalForm u v ν f :=
  StandardFourTermRelationToNormalizedRelation_proved u v ν f hcov

/-- Honest re-export of the genuine covariance reduction under the
affine-symplectic name. -/
theorem StandardCriticalMixedNormalForm_fully_proved
    (u v ν : ℝ × ℝ) (f : ℝ → ℂ)
    (hcov : StandardAffineSymplecticReductionForHRT u v ν f) :
    StandardCriticalMixedNormalForm u v ν f :=
  StandardCriticalMixedNormalForm_proved u v ν f hcov

/-! ## Conditional final theorem via the linear-independence phrasing -/

/-- **Conditional final theorem (linear-independence phrasing).**

The exact conclusion `c = 0` of `critical_mixed_orbit_HRT_L2`, proved from

* `h3li` — the **three-point HRT theorem in its direct linear-independence
  phrasing** (`StandardThreePointGaborLinearIndependence`), and
* `hcov` — the **metaplectic / affine-symplectic covariance**
  (`StandardGaborRelationToNormalizedCriticalMixedRelation`),

carrying every hypothesis of the original main theorem verbatim.  This routes the
direct three-point phrasing through `StandardThreePointHRTTheorem_proved` and the
covariance input through the genuine geometric-assembly reduction.  The main
theorem `critical_mixed_orbit_HRT_L2` itself is untouched. -/
theorem critical_mixed_orbit_HRT_L2_conditional_via_linearIndependence
    (u v : ℝ × ℝ) (α β : ℝ) (ν : ℝ × ℝ)
    (hν : ν = (α * u.1 + β * v.1, α * u.2 + β * v.2))
    (hsymp : |symp u v| = 1)
    (hdistinct : ([(0 : ℝ × ℝ), u, v, ν] : List (ℝ × ℝ)).Nodup)
    (hrank : Module.finrank ℚ (Submodule.span ℚ ({1, α, β} : Set ℝ)) = 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 volume) (hf0 : ¬ f =ᵐ[volume] 0)
    (h3li : StandardThreePointGaborLinearIndependence)
    (hcov : StandardGaborRelationToNormalizedCriticalMixedRelation u v ν f)
    (c : Fin 4 → ℂ)
    (hrel : (fun t => c 0 * tfShift 0 f t + c 1 * tfShift u f t
              + c 2 * tfShift v f t + c 3 * tfShift ν f t) =ᵐ[volume] 0) :
    c = 0 :=
  critical_mixed_orbit_HRT_L2_conditional_on_covariance u v α β ν hν hsymp
    hdistinct hrank f hf hf0 (StandardThreePointHRTTheorem_proved h3li) hcov c hrel

end CriticalMixedHRT
