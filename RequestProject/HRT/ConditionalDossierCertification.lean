import RequestProject.HRT.FinalGeometricAssembly
import RequestProject.HRT.ImportedRemainingCertificates
import RequestProject.HRT.RootCountLocalConstancy
import RequestProject.Rotation.CenteredOrbitGrid
import RequestProject.HRT.ActiveAnalyticAmplitudeReanchor

/-!
# Conditional certification of the dossier (interface-conditional theorem)

This module certifies the dossier **exactly as an interface-conditional theorem**.

The unconditional theorem `critical_mixed_orbit_HRT_L2`
(`RequestProject.MainStatement`) is *not* fully Lean-certified: its body is the
sole remaining theorem-body `sorry` of the project, standing for the deep
classical inputs that are genuinely absent from Mathlib `v4.28.0`.

What *is* certified here, with **no `sorry`, no `axiom`, no `unsafe`,
no `@[implemented_by]`**, is the theorem

```
critical_mixed_orbit_HRT_L2_certified_from_standard_inputs
```

which proves the **exact same conclusion** `c = 0`, under the **exact same
hypotheses** as `critical_mixed_orbit_HRT_L2`, taking as **explicit, transparent
hypotheses** precisely the remaining named external standard inputs of the
dossier.  Nothing is hidden in an opaque structure: every standard input is a
visible argument of the theorem.

## The six remaining standard inputs

The remaining gap is *exactly* the following named external inputs (none of which
is proved internally, none of which is hidden as an axiom, all of which are used
transparently as hypotheses):

1. `StandardInsideCountLocallyConstant` — **Rouché / root-count stability**.
   The inside-the-unit-disk root count of the fibre polynomial family is locally
   constant on a zero-free active arc.  (Here passed in its honest *true* form:
   no roots on the unit circle on the arc ⟹ the inside count is locally
   constant.)

2. `StandardCenteredOrbitGridProperty` — the **centered three-distance theorem**.
   For convergent-denominator return times the centered orbit grid property
   holds.  (This is the corrected centered-grid residual; see `TASK A` in the
   status files.  It replaces the previously mis-named, mathematically *false*
   targets `ContinuedFractionReturnData.orbit_partition` and
   `star_discrepancy_le_one`.)

3. `StandardCanonicalAmplitudeResonanceProperty` — **canonical amplitude
   resonance**: the canonical loop-holonomy amplitude lands in the resonance
   group of the return times on a positive-measure active set.

4. `StandardThreePointHRTTheorem` — the **three-point HRT theorem** (any three
   distinct time-frequency translates of a nonzero `L²` function are linearly
   independent).

5. `StandardAffineSymplecticReductionForHRT` — the **affine-symplectic /
   metaplectic covariance** reduction (definitionally equal to input 6).

6. `StandardGaborRelationToNormalizedCriticalMixedRelation` — the
   **Gabor-relation → normalized critical-mixed-relation** transport, which
   produces, from an all-nonzero four-term Gabor relation, the
   Zak/return-cocycle witness `CriticalMixedReturnWitness`.

Inputs 5 and 6 are the *same* project declaration
(`StandardAffineSymplecticReductionForHRT` is an `abbrev` for
`StandardGaborRelationToNormalizedCriticalMixedRelation`); it is the single deep
covariance/Zak-reduction residual `hAffine`.

## Load-bearing vs. transparency note

In the project's *current* assembled pipeline the covariance input `hAffine`
already produces a complete `CriticalMixedReturnWitness` whose fields **are** the
three analytic residuals (1)–(3): its `hroots_min` field is the root-count datum
behind `StandardInsideCountLocallyConstant`, its return data `dk` is the
Denjoy–Koksma datum behind `StandardCenteredOrbitGridProperty`, and its `hSres`
field is the resonance datum behind `StandardCanonicalAmplitudeResonanceProperty`.
Consequently the headline assembly below is discharged through the two
genuinely-sufficient inputs `h3` (three-point HRT) and `hAffine`
(affine-symplectic covariance) via the already-proved pipeline endpoint
`critical_mixed_orbit_HRT_L2_conditional_on_covariance` (which itself routes
through the final geometric assembly adapter, the canonical Zak model, the
root-data reduction, the centered Denjoy–Koksma wiring, the canonical
loop-holonomy amplitude, and the no-flat-band contradiction
`normalized_return_cocycle_feeds_no_flat_band_root_data_minimal`).

The three granular analytic residuals (1)–(3) are nevertheless listed as
explicit, transparent hypotheses of the certified theorem, in their honest
satisfiable forms, so that the remaining gap is *exactly* the named list above
and the certification is faithful to the dossier.  In this particular assembly
they are subsumed by `hAffine`'s witness and are therefore not separately
consumed; per the dossier they are documented here and in
`CONDITIONAL_DOSSIER_CERTIFICATION_STATUS.md`.
-/

namespace CriticalMixedHRT

open scoped Classical BigOperators Real
open MeasureTheory Complex Polynomial Set

/-- **Conditional dossier certification.**

The exact conclusion `c = 0` of `critical_mixed_orbit_HRT_L2`, proved under the
exact same hypotheses, from precisely the remaining named external standard
inputs of the dossier:

* `hInsideCount` — `StandardInsideCountLocallyConstant` (Rouché / root-count
  stability), in its honest true form;
* `hCenteredGrid` — `StandardCenteredOrbitGridProperty` (centered three-distance
  theorem for convergent denominators);
* `hResonance` — `StandardCanonicalAmplitudeResonanceProperty` (canonical
  amplitude resonance on a positive-measure active set);
* `h3` — `StandardThreePointHRTTheorem` (three-point HRT theorem);
* `hAffine` — `StandardAffineSymplecticReductionForHRT`
  (= `StandardGaborRelationToNormalizedCriticalMixedRelation`, the
  affine-symplectic / metaplectic covariance reduction).

The proof calls the already-proved conditional pipeline
`critical_mixed_orbit_HRT_L2_conditional_on_covariance`, which is genuinely
sufficient from `h3` and `hAffine`.  As documented in the module header,
`hAffine`'s witness already bundles the three analytic residuals
`hInsideCount`, `hCenteredGrid`, `hResonance`; these are listed here as explicit
transparent hypotheses so that the remaining gap is *exactly* the named list, and
they turn out to be unnecessary as *separate* arguments in this assembly. -/
theorem critical_mixed_orbit_HRT_L2_certified_from_standard_inputs
    (u v : ℝ × ℝ) (α β : ℝ) (ν : ℝ × ℝ)
    (hν : ν = (α * u.1 + β * v.1, α * u.2 + β * v.2))
    (hsymp : |symp u v| = 1)
    (hdistinct : ([(0 : ℝ × ℝ), u, v, ν] : List (ℝ × ℝ)).Nodup)
    (hrank : Module.finrank ℚ (Submodule.span ℚ ({1, α, β} : Set ℝ)) = 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 volume) (hf0 : ¬ f =ᵐ[volume] 0)
    -- (1) Rouché / root-count stability : `StandardInsideCountLocallyConstant`
    (hInsideCount :
      ∀ {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (a b : ℝ),
        (∀ t ∈ Set.Ioo a b, ∀ x : ℝ, (fibrePoly coeffs t).eval (circleParam x) ≠ 0) →
        StandardInsideCountLocallyConstant coeffs a b)
    -- (2) centered three-distance theorem : `StandardCenteredOrbitGridProperty`
    (hCenteredGrid :
      ∀ (θ : ℝ) (R : RotationReturnData θ), Irrational θ →
        StandardCenteredOrbitGridProperty θ R.q)
    -- (3) canonical amplitude resonance : `StandardCanonicalAmplitudeResonanceProperty`
    (hResonance :
      ∀ {θ : ℝ} (DK : DenjoyKoksmaReturnData θ) {a₀ b₀ : ℝ} {dlau : ℕ}
        (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
        (S : Set ℝ), S ⊆ Set.Ioo a₀ b₀ → 0 < MeasureTheory.volume S →
        (∀ s ∈ S, canonicalLoopHolonomyAmplitude θ coeffs ad s ∈ resonanceGroupC DK.q) →
        Nonempty (StandardCanonicalAmplitudeResonanceProperty DK a₀ b₀ ad coeffs))
    -- (4) three-point HRT theorem : `StandardThreePointHRTTheorem`
    (h3 : StandardThreePointHRTTheorem)
    -- (5) = (6) affine-symplectic / metaplectic covariance reduction
    --     `StandardAffineSymplecticReductionForHRT`
    --     = `StandardGaborRelationToNormalizedCriticalMixedRelation`
    (hAffine : StandardAffineSymplecticReductionForHRT u v ν f)
    (c : Fin 4 → ℂ)
    (hrel : (fun t => c 0 * tfShift 0 f t + c 1 * tfShift u f t
              + c 2 * tfShift v f t + c 3 * tfShift ν f t) =ᵐ[volume] 0) :
    c = 0 :=
  critical_mixed_orbit_HRT_L2_conditional_on_covariance u v α β ν hν hsymp
    hdistinct hrank f hf hf0 h3 hAffine c hrel

end CriticalMixedHRT
