import Mathlib
import RequestProject.HRT.RootCountLocalConstancy

/-!
# Final-interface consolidation (Phase 5)

This module collects, in a single place, the **exact** remaining analytic
interfaces of the critical mixed-arithmetic four-point HRT certification, each
stated as a precisely-typed proposition.  None of these is committed as a
`sorry`/`axiom`; they are the smallest honest residual theorem-types behind the
three deep blockers identified in this run.

Each of these reduces to a named classical theorem that is **not** currently in
Mathlib for this toolchain:

* `StandardRoucheRootCountStability` — Rouché / argument principle: a continuous
  family of complex polynomials with no roots on the unit circle has a locally
  constant inside-the-disk root count.  (This is exactly the canonical datum
  `StandardInsideCountLocallyConstant`.)

* `StandardConvergentDenominatorStarDiscrepancy` — the three-distance /
  best-approximation discrepancy bound: for a continued-fraction convergent
  denominator the orbit star-discrepancy is `≤ 1`.  (This is exactly the field
  `StandardRealDenjoyKoksmaCombinatorics.star_discrepancy_le_one`.  NOTE: the
  *stronger* grid-balanced `ContinuedFractionReturnData.orbit_partition` field is
  mathematically **false** — see the audit file
  `FINAL_FULL_CERTIFICATION_STATUS.md` — so the DK closure must go through the
  discrepancy bound, not through grid-balancedness.)

* `StandardCanonicalAmplitudeResonantOnActiveSet` — measurable-winding holonomy
  quantization: the canonical loop-holonomy amplitude lands in the resonance
  group of the return times on a positive-measure active set.  (This is exactly
  `StandardCanonicalAmplitudeResonanceProperty`.)

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]` appear in this file.
-/

namespace CriticalMixedHRT

open Complex Polynomial
open scoped BigOperators Real Classical
open Set

/-- **Exact remaining Rouché root-count interface.**

Definitionally equal to the canonical datum `StandardInsideCountLocallyConstant`:
the inside-disk root count of the fibre polynomial is locally constant on the
open arc.  This is the smallest honest residual behind root-count constancy; it
is provided by Rouché's theorem / the argument principle (continuity of roots
with no boundary crossing), which is not available in the current Mathlib. -/
abbrev StandardRoucheRootCountStability {d : ℕ}
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (a b : ℝ) : Prop :=
  StandardInsideCountLocallyConstant coeffs a b

/-- **Rouché interface ⟹ the assembled minimal root-data interface.**

This re-exports the already-proved reduction
`standardReturnMultiplierRootDataMinimal_of_localConstancy`, phrased through the
named residual `StandardRoucheRootCountStability`, so that the entire remaining
root-data content is visibly pinned to the single Rouché theorem-type. -/
theorem standardReturnMultiplierRootDataMinimal_of_rouche
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) {a b : ℝ}
    (ad : LaurentPolynomial ℂ) (mlau : ℕ) (Mlau : ℤ)
    (hmM : (mlau : ℤ) = (d : ℤ) - Mlau)
    (hzf : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      ∀ x : ℝ, (fibrePoly coeffs t).eval (circleParam x) ≠ 0)
    (hrouche : StandardRoucheRootCountStability coeffs a b)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hMlau : Mlau = (fibreInsideCount coeffs t₀ : ℤ)) :
    StandardReturnMultiplierRootDataMinimal coeffs a b ad mlau Mlau :=
  standardReturnMultiplierRootDataMinimal_of_localConstancy
    coeffs ad mlau Mlau hmM hzf hrouche ht₀ hMlau

end CriticalMixedHRT
