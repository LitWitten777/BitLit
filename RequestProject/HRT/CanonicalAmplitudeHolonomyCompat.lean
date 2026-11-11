import Mathlib
import RequestProject.HRT.CanonicalHolonomyAmplitude
import RequestProject.HRT.CertificateInputSynthesis

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000

/-!
# Canonical amplitude / holonomy compatibility run

This module performs the **canonical amplitude / holonomy compatibility run** for
the conditional final assembly theorem.  It addresses the single residual
analytic↔algebraic bridge

```
  H t = canonicalGaugeAmplitude θ coeffs ad t      (on the active arc),
```

equivalently

```
  gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t      (on the active arc),
```

which the previous *canonical holonomy amplitude run*
(`CanonicalHolonomyAmplitude.lean`) isolated as the field `hHcanon` of
`CriticalMixedCanonicalAmplitudeInterface`, and which the *holonomy-identification
discharge run* (`HolonomyIdentificationDischarge.lean`) isolated as the field
`hJalg` of `CriticalMixedHolonomyIdentificationInterface`.

## Task A — the exact residual

The exact remaining hypothesis is the pointwise identity, on the active arc, of
the analytic gauge value `gaugeReturnMultiplier H θ t = H t · exp(-2π i θ t)` with
the choice-free algebraic loop holonomy `algReturnHolonomy coeffs ad t`.  Three
mutually equivalent shapes are used in the project:

* `StandardGaugeMultiplierEqualsAlgHolonomy` —
  `gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t`;
* `StandardCanonicalAmplitudeCompatibility` —
  `H t = canonicalGaugeAmplitude θ coeffs ad t`;
* the `hJholo`/`hJgauge` form carried by `CriticalMixedWindingInterface`.

The classification of each ingredient is recorded in
`CANONICAL_AMPLITUDE_HOLONOMY_STATUS.md`.

## Task C — the algebraic holonomy identification (already proved)

The step "the periodic-log integral of the return multiplier equals the
root-product algebraic holonomy",
`StandardPeriodicLogIntegralEqualsRootHolonomy`, is **already discharged**
unconditionally as `return_multiplier_holonomy_eq_integral_log`
(`HolonomyIdentificationDischarge.lean`).  It is re-exported here and is *not* a
blocker.

## Tasks B/D — the compatibility follows from the active-fibre return cocycle

The key result of this run, `canonical_amplitude_compatibility_of_winding`, shows
that the residual compatibility is **not** independent data: given the active-fibre
winding interface `CriticalMixedWindingInterface` (the holonomy / phase-lift data
`J`, `hJgauge`, `hJholo`) together with the minimal root data, the canonical
amplitude compatibility `H t = canonicalGaugeAmplitude θ coeffs ad t` is *derived*
on the active arc.  The proof:

1. synthesises a continuous `1`-periodic logarithm `ell` of the return loop from
   the root factorisation (`evalBiLaurentPoly_periodic_log_of_roots`);
2. evaluates `hJholo` at `ell` to identify `J t` with `exp(∫₀¹ ell)`;
3. rewrites `J t = gaugeReturnMultiplier H θ t` via `hJgauge`;
4. identifies `exp(∫₀¹ ell)` with `algReturnHolonomy coeffs ad t` via the
   already-proved `return_multiplier_holonomy_eq_integral_log`;
5. converts the gauge identity to the canonical-amplitude form.

## Tasks E/F — the smallest exact blocker and the downstream contradiction

The minimal active-arc compatibility interface
`StandardCanonicalAmplitudeCompatibility` is strictly smaller than the previous
whole-window `CriticalMixedCanonicalAmplitudeInterface` (it is quantified only
over active fibres).  From it, together with the already-discharged analytic
constancy of `H`, we construct the holonomy-constancy interface internally and
restate the conditional final contradiction
(`critical_mixed_final_contradiction_with_canonical_amplitude_compat`).

No axioms, `sorry`s, or `admit`s are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Task C — the algebraic holonomy identification (re-export, already proved) -/

/-- **`STANDARD_PERIODIC_LOG_INTEGRAL_EQUALS_ROOT_HOLONOMY` (already proved).**

The periodic-log integral of the return multiplier equals the choice-free
root-product algebraic holonomy.  This is a re-export of the already-discharged
`return_multiplier_holonomy_eq_integral_log`; it is *not* a blocker. -/
theorem StandardPeriodicLogIntegralEqualsRootHolonomy {d : ℕ}
    (mlau : ℕ) (Mlau : ℤ) (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (t : ℝ) (ht_ne : evalLaurentCircle ad t ≠ 0)
    (hroots_min_t :
      (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
      ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau)
    (ell_t : ℝ → ℂ)
    (hell : IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t)) :
    Complex.exp (∫ x in (0:ℝ)..1, ell_t x) = algReturnHolonomy coeffs ad t :=
  return_multiplier_holonomy_eq_integral_log mlau Mlau ad coeffs h_ad_coeff t
    ht_ne hroots_min_t ell_t hell

/-! ## Pointwise translation between the gauge form and the canonical-amplitude form -/

/-- From the gauge identity `gaugeReturnMultiplier H θ t = algReturnHolonomy …`,
the abstract amplitude `H t` equals the canonical algebraic amplitude. -/
theorem H_eq_canonicalGaugeAmplitude_of_gauge_eq_alg {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (H : ℝ → ℂ) (t : ℝ)
    (h : gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t) :
    H t = canonicalGaugeAmplitude θ coeffs ad t := by
  have hexp :
      Complex.exp (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) *
        Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have h0 : (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) +
        (-2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) = 0 := by ring
    rw [h0, Complex.exp_zero]
  rw [canonicalGaugeAmplitude, ← h, gaugeReturnMultiplier]
  rw [show Complex.exp (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) *
        (H t * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (t : ℂ)))
      = H t * (Complex.exp (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) *
          Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (t : ℂ))) by ring,
    hexp, mul_one]

/-- From the canonical-amplitude identity `H t = canonicalGaugeAmplitude …`, the
analytic gauge value equals the choice-free algebraic loop holonomy. -/
theorem gauge_eq_alg_of_H_eq_canonicalGaugeAmplitude {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (H : ℝ → ℂ) (t : ℝ)
    (h : H t = canonicalGaugeAmplitude θ coeffs ad t) :
    gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t := by
  have hgauge := gaugeReturnMultiplier_canonicalGaugeAmplitude θ coeffs ad t
  rw [gaugeReturnMultiplier] at hgauge ⊢
  rw [h]
  exact hgauge

/-! ## Tasks E/F — the minimal active-arc compatibility interfaces -/

/-- **`STANDARD_CANONICAL_AMPLITUDE_COMPATIBILITY` interface.**

The smallest exact form of the residual analytic↔algebraic bridge: on the
*active* arc (fibres with nonzero leading coefficient), the abstract analytic
amplitude `H` equals the canonical algebraic amplitude
`canonicalGaugeAmplitude θ coeffs ad`.  Strictly smaller than the previous
whole-window `CriticalMixedCanonicalAmplitudeInterface` (quantified only over
active fibres). -/
structure StandardCanonicalAmplitudeCompatibility (θ : ℝ) (a₀ b₀ : ℝ) {dlau : ℕ}
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (H : ℝ → ℂ) where
  hHcanon_active : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
    H t = canonicalGaugeAmplitude θ coeffs ad t

/-- **`STANDARD_GAUGE_MULTIPLIER_EQUALS_ALG_HOLONOMY` interface.**

The equivalent gauge-form of the residual bridge: on the active arc, the analytic
gauge value equals the choice-free algebraic loop holonomy. -/
structure StandardGaugeMultiplierEqualsAlgHolonomy (θ : ℝ) (a₀ b₀ : ℝ) {dlau : ℕ}
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (H : ℝ → ℂ) where
  hJalg : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
    gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t

/-- The two minimal interfaces are inter-derivable (gauge form ⇒ canonical form). -/
def StandardGaugeMultiplierEqualsAlgHolonomy.toCanonicalAmplitudeCompat
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (g : StandardGaugeMultiplierEqualsAlgHolonomy θ a₀ b₀ ad coeffs H) :
    StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs H where
  hHcanon_active := fun t ht ht_ne =>
    H_eq_canonicalGaugeAmplitude_of_gauge_eq_alg θ coeffs ad H t (g.hJalg t ht ht_ne)

/-- The two minimal interfaces are inter-derivable (canonical form ⇒ gauge form). -/
def StandardCanonicalAmplitudeCompatibility.toGaugeMultiplierEqualsAlg
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (c : StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs H) :
    StandardGaugeMultiplierEqualsAlgHolonomy θ a₀ b₀ ad coeffs H where
  hJalg := fun t ht ht_ne =>
    gauge_eq_alg_of_H_eq_canonicalGaugeAmplitude θ coeffs ad H t (c.hHcanon_active t ht ht_ne)

/-! ## Tasks B/D — the compatibility follows from the active-fibre return cocycle -/

/-- **The gauge value equals the algebraic loop holonomy, from the winding
interface plus root data.**

Given the active-fibre winding interface (the holonomy / phase-lift data `J`,
`hJgauge`, `hJholo`) and the minimal root data, the gauge identity
`gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t` holds on every
active fibre.  A continuous `1`-periodic logarithm `ell` of the return loop is
synthesised from the root factorisation, `hJholo` is evaluated at `ell`, and the
algebraic side is identified via `return_multiplier_holonomy_eq_integral_log`. -/
theorem gaugeReturnMultiplier_eq_algReturnHolonomy_of_winding
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (wind : CriticalMixedWindingInterface θ a₀ b₀ Mlau ad coeffs H) :
    ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t := by
  intro t ht ht_ne
  obtain ⟨r, hfact, hrootmap⟩ :=
    return_multiplier_local_root_factorization coeffs ad rootData.h_ad_coeff t ht_ne
  have hrootmap' : (fibrePoly coeffs t).roots = Multiset.map r Finset.univ.val := hrootmap
  obtain ⟨hoff, hM, hm⟩ := rootData.hroots_min t ht ht_ne
  have hr_off : ∀ i, ‖r i‖ ≠ 1 := root_offcircle_transfer r _ hrootmap' hoff
  have hMint : Mlau = ↑((Finset.univ.filter (fun i : Fin dlau => ‖r i‖ < 1)).card) := by
    rw [hM, root_count_transfer r _ hrootmap' (fun z => ‖z‖ < 1)]
  obtain ⟨ell, hell⟩ :=
    evalBiLaurentPoly_periodic_log_of_roots Mlau coeffs t (evalLaurentCircle ad t)
      ht_ne r hr_off hMint hfact
  have hJ := wind.hJholo t ht ht_ne ell hell
  have hg := wind.hJgauge t ht
  have halg :=
    return_multiplier_holonomy_eq_integral_log mlau Mlau ad coeffs rootData.h_ad_coeff t
      ht_ne ⟨hoff, hM, hm⟩ ell hell
  rw [gaugeReturnMultiplier, ← hg, hJ, halg]

/-- **The canonical amplitude compatibility follows from the winding interface
plus root data.**

The headline derivation of this run: the residual analytic↔algebraic bridge
`H t = canonicalGaugeAmplitude θ coeffs ad t` on the active arc is *not*
independent data — it is constructed from the active-fibre return-cocycle
holonomy data (the winding interface) and the minimal root data. -/
def canonical_amplitude_compatibility_of_winding
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (wind : CriticalMixedWindingInterface θ a₀ b₀ Mlau ad coeffs H) :
    StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs H where
  hHcanon_active := fun t ht ht_ne =>
    H_eq_canonicalGaugeAmplitude_of_gauge_eq_alg θ coeffs ad H t
      (gaugeReturnMultiplier_eq_algReturnHolonomy_of_winding rootData wind t ht ht_ne)

/-! ## Tasks E/F — the holonomy-constancy interface and downstream contradiction -/

/-- **The minimal active-arc compatibility interface constructs the
holonomy-constancy interface.**

From the active-arc canonical amplitude compatibility together with the
already-discharged analytic constancy of `H`
(`active_analytic_holonomy_constant`), the holonomy-constancy interface is
constructed internally.  Strictly smaller than
`canonical_amplitude_satisfies_holonomy_constancy_interface` (which used the
whole-window compatibility field). -/
noncomputable def canonical_amplitude_compat_satisfies_holonomy_constancy_interface
    {θ : ℝ} {DK : DenjoyKoksmaReturnData θ} {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (hq : Tendsto DK.q atTop atTop)
    (analytic : CriticalMixedActiveAnalyticInterface θ DK a₀ b₀)
    (compat : StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs analytic.H) :
    CriticalMixedHolonomyConstancyInterface θ a₀ b₀ ad coeffs analytic.H := by
  have hne := MeasureTheory.nonempty_of_measure_ne_zero (ne_of_gt analytic.hSpos)
  set s₀ := hne.choose with hs₀def
  have hs₀ : s₀ ∈ Set.Ioo a₀ b₀ := analytic.hSU hne.choose_spec
  refine ⟨s₀, hs₀, ?_⟩
  intro t ht ht_ne
  have hHt : analytic.H t = analytic.H s₀ :=
    active_analytic_holonomy_constant hq analytic t ht s₀ hs₀
  have hgauge : gaugeReturnMultiplier analytic.H θ t = algReturnHolonomy coeffs ad t :=
    gauge_eq_alg_of_H_eq_canonicalGaugeAmplitude θ coeffs ad analytic.H t
      (compat.hHcanon_active t ht ht_ne)
  rw [← hgauge, gaugeReturnMultiplier, hHt]

/-- **Conditional final contradiction from the minimal active-arc canonical
amplitude compatibility interface.**

The strongest endpoint of this run.  It restates
`critical_mixed_final_contradiction_with_holonomy_constancy_interface` using the
strictly smaller active-arc compatibility interface
`StandardCanonicalAmplitudeCompatibility` in place of the holonomy-constancy
interface.  The conditional contradiction depends only on:

* `DK_VARIATION_INTERFACE`  (`dk`),
* `ROOT_DATA_INTERFACE`     (`rootData`),
* `ZAK_MODEL_INTERFACE`     (`analytic`),

together with the single minimal canonical-amplitude compatibility field. -/
theorem critical_mixed_final_contradiction_with_canonical_amplitude_compat
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (compat : StandardCanonicalAmplitudeCompatibility D.θ a₀ b₀ ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_holonomy_constancy_interface D dk rootData
    analytic
    (canonical_amplitude_compat_satisfies_holonomy_constancy_interface dk.hq analytic compat)

/-- **Conditional final contradiction with the canonical-amplitude compatibility
discharged from the winding interface.**

Combines `canonical_amplitude_compatibility_of_winding` with the previous
endpoint: from the four explicit interfaces (DK, root data, active/analytic,
winding) the contradiction follows, with the canonical-amplitude compatibility
derived internally rather than assumed.  This certifies that the residual
analytic↔algebraic bridge is exactly the content of the active-fibre winding /
holonomy interface. -/
theorem critical_mixed_final_contradiction_with_winding_canonical_amplitude_closed
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (wind : CriticalMixedWindingInterface D.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_canonical_amplitude_compat D dk rootData
    analytic (canonical_amplitude_compatibility_of_winding rootData wind)

end CriticalMixedHRT
