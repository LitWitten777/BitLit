import Mathlib
import RequestProject.HRT.WindingInterfaceDischarge

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000

/-!
# Holonomy-identification discharge run

This module performs the **holonomy-identification discharge run** for the
conditional final assembly theorem.  Its purpose is to remove or minimize the
single remaining substantive field `hJholo` of the minimal winding interface
`CriticalMixedMinimalWindingInterface` (in `WindingInterfaceDischarge.lean`).

## Task A — the exact statement of `hJholo`

For a fibre `t ∈ (a₀, b₀)` with nonzero leading coefficient
`evalLaurentCircle ad t ≠ 0`, and for **any** continuous `1`-periodic logarithm
`ell_t` of the bivariate Laurent return loop `evalBiLaurentPoly coeffs Mlau t`,
the field asserts the holonomy identification
```
  gaugeReturnMultiplier H θ t = exp (∫₀¹ ell_t).
```
Here `gaugeReturnMultiplier H θ t = H t · exp(-2π i θ t)` is the *analytic* gauge
value, while `exp(∫₀¹ ell_t)` is the *algebraic* loop holonomy.

Objects appearing:

* holonomy function `J = gaugeReturnMultiplier H θ` — the geometric gauge;
* gauge holonomy `gaugeReturnMultiplier H θ` — `H t · exp(-2π i θ t)`;
* periodic logarithm `ell_t` — any `IsPeriodicLog` of the return loop;
* bivariate Laurent evaluation loop `evalBiLaurentPoly coeffs Mlau t`;
* active interval/window `(a₀, b₀)`;
* return multiplier — the fibre polynomial `fibrePoly coeffs t`;
* analytic amplitude `H`.

## Task B — adapter equalities (proved here, no axioms)

By the Jensen holonomy formula `complex_jensen_holonomy_product` together with
the canonical root factorisation `return_multiplier_local_root_factorization`,
the algebraic side `exp(∫₀¹ ell_t)` is **independent of the choice of `ell_t`**
and equals the choice-free algebraic loop holonomy
```
  algReturnHolonomy coeffs ad t
    = evalLaurentCircle ad t · ∏_{z ∈ roots(fibrePoly), ‖z‖>1} (−z).
```
This is `return_multiplier_holonomy_eq_integral_log`.  Consequently the `hJholo`
field is *equivalent*, given the root-data interface, to the strictly smaller and
more explicit purely algebraic identification
```
  gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t,
```
with no quantification over periodic logarithms and no integral.

## Tasks C/D — outcome

The remaining identity `gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t`
equates the *analytic* gauge value `H t · exp(-2π i θ t)` with the *algebraic*
root product.  This is the genuine analytic↔algebraic bridge and cannot be
derived inside the project from the available stages, so full discharge of
`hJholo` (and hence complete removal of the winding interface, Task C) is not
achieved.  Per the Task D fallback policy we therefore isolate exactly this one
equality as the single-field interface
`CriticalMixedHolonomyIdentificationInterface`, which is strictly smaller and
more explicit than `CriticalMixedMinimalWindingInterface` (it drops the
`∀ ell_t` quantifier and the loop integral).  The headline endpoint
`critical_mixed_final_contradiction_with_holonomy_identification_interface`
restates the conditional final contradiction using it.

No axioms, `sorry`s, or `admit`s are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Choice-free algebraic loop holonomy -/

/-- **Choice-free algebraic loop holonomy of the return multiplier on a fibre.**

`algReturnHolonomy coeffs ad t = evalLaurentCircle ad t · ∏ (−z)` over the roots
`z` of the canonical fibre polynomial `fibrePoly coeffs t` with `‖z‖ > 1`
(counted with multiplicity, via the roots multiset).  This is exactly the value
of the loop holonomy `exp(∫₀¹ ell_t)` predicted by the Jensen holonomy formula,
but written without reference to any choice of root enumeration or periodic
logarithm. -/
noncomputable def algReturnHolonomy {d : ℕ}
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) : ℂ :=
  evalLaurentCircle ad t *
    (((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).map (fun z => -z)).prod

/-- The choice-free algebraic holonomy, expressed via a `Fin d`-root enumeration
`r` of the fibre polynomial: the multiset product over the outside roots equals
the finite product `∏_{i : 1 < ‖r i‖} (−r i)`. -/
lemma algReturnHolonomy_eq_root_product {d : ℕ}
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) (r : Fin d → ℂ)
    (hrootmap : (fibrePoly coeffs t).roots = Multiset.map r Finset.univ.val) :
    algReturnHolonomy coeffs ad t =
      evalLaurentCircle ad t *
        ∏ i ∈ Finset.univ.filter (fun i : Fin d => 1 < ‖r i‖), (-r i) := by
  unfold algReturnHolonomy
  congr 1
  rw [hrootmap, Multiset.filter_map, Multiset.map_map, Finset.prod]
  rfl

/-! ## Task B — the holonomy / integral-log identification -/

/-- **The loop holonomy equals the choice-free algebraic holonomy.**

Given the minimal geometric root data on the fibre `t` (roots off the unit
circle and the inside count `Mlau`), the loop holonomy `exp(∫₀¹ ell_t)` of *any*
periodic logarithm `ell_t` of the bivariate Laurent return loop equals the
choice-free algebraic loop holonomy `algReturnHolonomy coeffs ad t`.

This is the Jensen holonomy formula `complex_jensen_holonomy_product` combined
with the canonical root factorisation
`return_multiplier_local_root_factorization` and the multiset/finite-product
transfer `algReturnHolonomy_eq_root_product`.  In particular the right-hand side
is independent of the choice of `ell_t`. -/
theorem return_multiplier_holonomy_eq_integral_log {d : ℕ}
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
    Complex.exp (∫ x in (0:ℝ)..1, ell_t x) = algReturnHolonomy coeffs ad t := by
  obtain ⟨hoff, hM, _hm⟩ := hroots_min_t
  obtain ⟨r, hfact, hrootmap⟩ :=
    return_multiplier_local_root_factorization coeffs ad h_ad_coeff t ht_ne
  have hrootmap' : (fibrePoly coeffs t).roots = Multiset.map r Finset.univ.val := hrootmap
  have hr_off : ∀ i, ‖r i‖ ≠ 1 := root_offcircle_transfer r _ hrootmap' hoff
  have hMint : Mlau = ↑((Finset.univ.filter (fun i : Fin d => ‖r i‖ < 1)).card) := by
    rw [hM, root_count_transfer r _ hrootmap' (fun z => ‖z‖ < 1)]
  have hP : ∀ x : ℝ, evalBiLaurentPoly coeffs Mlau t x =
      circleParam x ^ (-Mlau) * evalLaurentCircle ad t *
        ∏ i : Fin d, (circleParam x - r i) :=
    fun x => evalBiLaurentPoly_eq_factored coeffs Mlau t r (evalLaurentCircle ad t) hfact x
  have hjensen := complex_jensen_holonomy_product hP ht_ne hr_off hMint hell
  rw [hjensen, algReturnHolonomy_eq_root_product coeffs ad t r hrootmap']

/-- **Holonomy identification from the algebraic identification.**

If the analytic gauge value coincides with the choice-free algebraic holonomy
(`hJalg`), then it coincides with the loop holonomy `exp(∫₀¹ ell_t)` of any
periodic logarithm of the return loop.  This converts the purely algebraic
identity into the `hJholo` form. -/
theorem return_multiplier_holonomy_identification {d : ℕ}
    (mlau : ℕ) (Mlau : ℤ) (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (H : ℝ → ℂ) (θ : ℝ) (t : ℝ) (ht_ne : evalLaurentCircle ad t ≠ 0)
    (hroots_min_t :
      (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
      ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau)
    (hJalg : gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t)
    (ell_t : ℝ → ℂ)
    (hell : IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t)) :
    gaugeReturnMultiplier H θ t = Complex.exp (∫ x in (0:ℝ)..1, ell_t x) := by
  rw [hJalg,
    (return_multiplier_holonomy_eq_integral_log mlau Mlau ad coeffs h_ad_coeff t
      ht_ne hroots_min_t ell_t hell)]

/-- Re-export of `return_multiplier_holonomy_identification` under the gauge name. -/
theorem gauge_return_multiplier_holonomy_identification {d : ℕ}
    (mlau : ℕ) (Mlau : ℤ) (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (H : ℝ → ℂ) (θ : ℝ) (t : ℝ) (ht_ne : evalLaurentCircle ad t ≠ 0)
    (hroots_min_t :
      (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
      ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau)
    (hJalg : gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t)
    (ell_t : ℝ → ℂ)
    (hell : IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t)) :
    gaugeReturnMultiplier H θ t = Complex.exp (∫ x in (0:ℝ)..1, ell_t x) :=
  return_multiplier_holonomy_identification mlau Mlau ad coeffs h_ad_coeff H θ t
    ht_ne hroots_min_t hJalg ell_t hell

/-! ## Task D — the minimal holonomy-identification interface -/

/-- **Minimal `HOLONOMY_IDENTIFICATION` interface.**

The strictly smaller and more explicit replacement for the minimal winding
interface `CriticalMixedMinimalWindingInterface`.  Its single field `hJalg`
asserts the purely algebraic holonomy identification of the analytic gauge value
with the choice-free algebraic loop holonomy `algReturnHolonomy coeffs ad t`,
with no quantification over periodic logarithms and no loop integral. -/
structure CriticalMixedHolonomyIdentificationInterface (θ : ℝ) (a₀ b₀ : ℝ)
    {dlau : ℕ} (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ) (H : ℝ → ℂ) where
  hJalg : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
    gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t

/-- **Interval form: the holonomy-identification interface yields `hJholo`.**

Combining the algebraic identification interface with the root-data interface
(supplying the per-fibre geometric root data) discharges, for every fibre and
every periodic logarithm, the `hJholo` identification of the gauge value with the
loop holonomy `exp(∫₀¹ ell_t)`. -/
theorem local_certificate_holonomy_identification_from_periodic_log
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (holoId : CriticalMixedHolonomyIdentificationInterface θ a₀ b₀ ad coeffs H) :
    ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
        gaugeReturnMultiplier H θ t = Complex.exp (∫ x in (0:ℝ)..1, ell_t x) := by
  intro t ht ht_ne ell_t hell
  exact return_multiplier_holonomy_identification mlau Mlau ad coeffs
    rootData.h_ad_coeff H θ t ht_ne (rootData.hroots_min t ht ht_ne)
    (holoId.hJalg t ht ht_ne) ell_t hell

/-- The holonomy-identification interface (together with the root-data
interface) yields the minimal winding interface. -/
noncomputable def CriticalMixedHolonomyIdentificationInterface.toMinimalWinding
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (holoId : CriticalMixedHolonomyIdentificationInterface θ a₀ b₀ ad coeffs H)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs) :
    CriticalMixedMinimalWindingInterface θ a₀ b₀ Mlau ad coeffs H where
  hJholo := local_certificate_holonomy_identification_from_periodic_log rootData holoId

/-! ## Task C/D — the conditional final contradiction -/

/-- **Conditional final contradiction from the holonomy-identification interface.**

The strongest endpoint of this run.  It restates
`critical_mixed_final_contradiction_with_minimal_winding_interface` with the
minimal winding interface `CriticalMixedMinimalWindingInterface` (whose field is
the integral-form `hJholo`) replaced by the strictly smaller and more explicit
`CriticalMixedHolonomyIdentificationInterface` (whose field is the purely
algebraic identification `hJalg`, with no `∀ ell_t` quantifier and no integral).

The conditional contradiction now depends only on:

* `DK_VARIATION_INTERFACE`  (`dk`),
* `ROOT_DATA_INTERFACE`     (`rootData`),
* `ZAK_MODEL_INTERFACE`     (`analytic`),

together with the single algebraic holonomy-identification field. -/
theorem critical_mixed_final_contradiction_with_holonomy_identification_interface
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (holoId : CriticalMixedHolonomyIdentificationInterface D.θ a₀ b₀ ad coeffs
      analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_minimal_winding_interface D dk rootData
    analytic (holoId.toMinimalWinding rootData)

end CriticalMixedHRT