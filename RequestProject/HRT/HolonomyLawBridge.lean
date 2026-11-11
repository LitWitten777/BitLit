import Mathlib
import RequestProject.HRT.HolonomyIdentificationDischarge
import RequestProject.AnalyticRigidity

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000

/-!
# Analytic–algebraic holonomy bridge discharge run

This module performs the **analytic–algebraic holonomy bridge discharge run** for
the conditional final assembly theorem.  Its purpose is to remove or further
minimize the single remaining holonomy-identification field

```
  hJalg : gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t
```

of `CriticalMixedHolonomyIdentificationInterface`
(`HolonomyIdentificationDischarge.lean`).

## Task A — the exact data flow

The field `hJalg` equates the *analytic* gauge value
`gaugeReturnMultiplier H θ t = H t · exp(-2π i θ t)` with the *algebraic* loop
holonomy `algReturnHolonomy coeffs ad t`.  Following the intended mathematical
content:

1. the gauged cocycle is `A_t(x) = exp(2π i θ t) · B_t(x)` with `B_t` the
   algebraic Laurent return loop;
2. the analytic holonomy `H` of `A` is **constant** on the active interval
   `(a₀, b₀)` by the resonance / analytic-rigidity argument
   (`analytic_map_into_resonance_group_constant`);
3. the holonomy of `B` is therefore `exp(-2π i θ t)` times that constant;
4. the previous run proved that the loop holonomy of `B` equals
   `algReturnHolonomy coeffs ad t` (`return_multiplier_holonomy_eq_integral_log`);
5. hence `gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t`.

The classification of each ingredient is recorded in
`HOLONOMY_LAW_BRIDGE_STATUS.md`.

## Task B — the analytic holonomy constancy law (CLOSED_IN_LEAN)

Step 2 above is *fully discharged inside Lean* as
`active_analytic_holonomy_constant`: the analytic, nonvanishing amplitude `H`,
whose values lie in the Haar-null resonance group on the positive-measure active
set `S`, is constant on the whole active window `(a₀, b₀)`.  This is exactly the
analytic-rigidity input previously regarded as the irreducible obstacle, and it
no longer needs to be assumed.

## Tasks C/D/E — the residual algebraic-phase identity

After discharging the analytic-rigidity constancy, the only residual content of
`hJalg` is the *pointwise algebraic-phase identity*

```
  algReturnHolonomy coeffs ad t = H s₀ · exp(-2π i θ t),
```

which references the analytic amplitude **only through its single constant value**
`H s₀` at one reference fibre, together with the rotation phase.  It carries no
analytic-function content whatsoever — the entire analytic-rigidity argument has
been internalized.  This residual is isolated as the single-field interface
`CriticalMixedHolonomyConstancyInterface`, strictly smaller and more explicit
than `CriticalMixedHolonomyIdentificationInterface` (whose field `hJalg` still
refers to the analytic amplitude `H` as a function of the fibre).

From this constancy interface we reconstruct
`CriticalMixedHolonomyIdentificationInterface`
(`CriticalMixedHolonomyConstancyInterface.toHolonomyIdentification`), and the
headline endpoint
`critical_mixed_final_contradiction_with_holonomy_constancy_interface` restates
the conditional final contradiction using it.

Full unconditional discharge of `hJalg` (Task D's interface-free endpoint) is
*not* achieved: it would require the link between the abstract Zak-model
amplitude `H` and the concrete algebraic return loop `evalBiLaurentPoly`, which
is genuinely absent from the available interface data.

No axioms, `sorry`s, or `admit`s are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Task B — the analytic holonomy constancy law -/

/-- **Analytic holonomy constancy on the active window (CLOSED_IN_LEAN).**

The analytic, nonvanishing amplitude `H` from the active/analytic Zak-model
interface, whose values lie in the Haar-null resonance group `resonanceGroupC
DK.q` on the positive-measure active set `S`, is **constant** on the active
window `(a₀, b₀)`.

This is the analytic-rigidity step (step 2 of the holonomy law): it discharges,
*inside Lean*, the constancy of the analytic holonomy on the active interval via
`analytic_map_into_resonance_group_constant`. -/
theorem active_analytic_holonomy_constant
    {θ : ℝ} {DK : DenjoyKoksmaReturnData θ} {a₀ b₀ : ℝ}
    (hq : Tendsto DK.q atTop atTop)
    (analytic : CriticalMixedActiveAnalyticInterface θ DK a₀ b₀) :
    ∀ s ∈ Set.Ioo a₀ b₀, ∀ t ∈ Set.Ioo a₀ b₀, analytic.H s = analytic.H t := by
  apply analytic_map_into_resonance_group_constant DK.q hq (Set.Ioo a₀ b₀)
    isOpen_Ioo (convex_Ioo a₀ b₀).isPreconnected analytic.H analytic.hH analytic.hHne
  refine lt_of_lt_of_le analytic.hSpos (measure_mono ?_)
  intro s hs
  exact ⟨analytic.hSU hs, analytic.hSres s hs⟩

/-! ## Task E — the minimal holonomy-constancy interface -/

/-- **Minimal `HOLONOMY_CONSTANCY` interface.**

The strictly smaller and more explicit replacement for the holonomy-
identification interface `CriticalMixedHolonomyIdentificationInterface`.  After
the analytic-rigidity constancy of `H` is discharged in Lean
(`active_analytic_holonomy_constant`), the only residual content of `hJalg` is
the *pointwise algebraic-phase identity*

```
  algReturnHolonomy coeffs ad t = H s₀ · exp(-2π i θ t),
```

which references the analytic amplitude only through its single constant value
`H s₀` at one reference fibre `s₀ ∈ (a₀, b₀)`, together with the rotation phase.
There is no analytic-function content remaining. -/
structure CriticalMixedHolonomyConstancyInterface (θ : ℝ) (a₀ b₀ : ℝ) {dlau : ℕ}
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (H : ℝ → ℂ) where
  s₀ : ℝ
  hs₀ : s₀ ∈ Set.Ioo a₀ b₀
  hAlgPhase : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
    algReturnHolonomy coeffs ad t =
      H s₀ * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (t : ℂ))

/-! ## Task B/C — the holonomy law from active analytic data -/

/-- **The gauge value equals the algebraic loop holonomy on active fibres.**

Combining the discharged analytic constancy of `H`
(`active_analytic_holonomy_constant`) with the residual algebraic-phase identity
(`CriticalMixedHolonomyConstancyInterface.hAlgPhase`) proves, for every active
fibre, the analytic↔algebraic holonomy law

```
  gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t.
```

This is exactly the field `hJalg` of the holonomy-identification interface,
derived rather than assumed. -/
theorem gauge_return_multiplier_eq_algReturnHolonomy_of_active_fibers
    {θ : ℝ} {DK : DenjoyKoksmaReturnData θ} {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (hq : Tendsto DK.q atTop atTop)
    (analytic : CriticalMixedActiveAnalyticInterface θ DK a₀ b₀)
    (hconst : CriticalMixedHolonomyConstancyInterface θ a₀ b₀ ad coeffs analytic.H) :
    ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      gaugeReturnMultiplier analytic.H θ t = algReturnHolonomy coeffs ad t := by
  intro t ht ht_ne
  have hconstH := active_analytic_holonomy_constant hq analytic t ht hconst.s₀ hconst.hs₀
  unfold gaugeReturnMultiplier
  rw [hconstH]
  exact (hconst.hAlgPhase t ht ht_ne).symm

/-- Re-export of `gauge_return_multiplier_eq_algReturnHolonomy_of_active_fibers`
under the alternative `alg_holonomy_eq_gauge` name. -/
theorem return_multiplier_alg_holonomy_eq_gauge_of_active_fibers
    {θ : ℝ} {DK : DenjoyKoksmaReturnData θ} {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (hq : Tendsto DK.q atTop atTop)
    (analytic : CriticalMixedActiveAnalyticInterface θ DK a₀ b₀)
    (hconst : CriticalMixedHolonomyConstancyInterface θ a₀ b₀ ad coeffs analytic.H) :
    ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      algReturnHolonomy coeffs ad t = gaugeReturnMultiplier analytic.H θ t :=
  fun t ht ht_ne =>
    (gauge_return_multiplier_eq_algReturnHolonomy_of_active_fibers hq analytic hconst
      t ht ht_ne).symm

/-- **Construct the holonomy-identification interface from the constancy
interface plus active analytic data.**

The discharged analytic constancy together with the residual algebraic-phase
identity reconstructs the full
`CriticalMixedHolonomyIdentificationInterface`. -/
def CriticalMixedHolonomyConstancyInterface.toHolonomyIdentification
    {θ : ℝ} {DK : DenjoyKoksmaReturnData θ} {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (hq : Tendsto DK.q atTop atTop)
    (analytic : CriticalMixedActiveAnalyticInterface θ DK a₀ b₀)
    (hconst : CriticalMixedHolonomyConstancyInterface θ a₀ b₀ ad coeffs analytic.H) :
    CriticalMixedHolonomyIdentificationInterface θ a₀ b₀ ad coeffs analytic.H where
  hJalg := gauge_return_multiplier_eq_algReturnHolonomy_of_active_fibers hq analytic hconst

/-- **Task C — the holonomy-identification interface is satisfied by the active
analytic data plus the constancy interface.**

Named endpoint asserting that the return-cocycle active/analytic data, together
with the minimal holonomy-constancy interface, *constructs* the
holonomy-identification interface internally (rather than assuming it as a
separate package). -/
theorem return_cocycle_satisfies_holonomy_identification_interface
    {θ : ℝ} {DK : DenjoyKoksmaReturnData θ} {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (hq : Tendsto DK.q atTop atTop)
    (analytic : CriticalMixedActiveAnalyticInterface θ DK a₀ b₀)
    (hconst : CriticalMixedHolonomyConstancyInterface θ a₀ b₀ ad coeffs analytic.H) :
    Nonempty (CriticalMixedHolonomyIdentificationInterface θ a₀ b₀ ad coeffs analytic.H) :=
  ⟨hconst.toHolonomyIdentification hq analytic⟩

/-! ## Task E — the conditional final contradiction with the constancy interface -/

/-- **Conditional final contradiction from the holonomy-constancy interface.**

The strongest endpoint of this run.  It restates
`critical_mixed_final_contradiction_with_holonomy_identification_interface` with
the holonomy-identification interface `CriticalMixedHolonomyIdentificationInterface`
(whose field is the analytic-function identification `hJalg`) replaced by the
strictly smaller and more explicit `CriticalMixedHolonomyConstancyInterface`
(whose field `hAlgPhase` references the analytic amplitude only through its single
constant value `H s₀`).  The analytic-rigidity constancy of `H` is discharged
internally via `active_analytic_holonomy_constant`.

The conditional contradiction now depends only on:

* `DK_VARIATION_INTERFACE`  (`dk`),
* `ROOT_DATA_INTERFACE`     (`rootData`),
* `ZAK_MODEL_INTERFACE`     (`analytic`),

together with the single residual algebraic-phase field `hAlgPhase`. -/
theorem critical_mixed_final_contradiction_with_holonomy_constancy_interface
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (hconst : CriticalMixedHolonomyConstancyInterface D.θ a₀ b₀ ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_holonomy_identification_interface D dk
    rootData analytic (hconst.toHolonomyIdentification dk.hq analytic)

end CriticalMixedHRT
