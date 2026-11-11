import Mathlib
import RequestProject.HRT.RootDataMinimalInterface

open Complex Polynomial Finset
open scoped BigOperators Real Classical
open Set

set_option maxHeartbeats 1000000

/-!
# Root-count constancy from local constancy — canonical reduction of `Mlau`

`RootDataMinimalInterface.lean` reduced the certificate's root-data interface to a
single genuinely-missing analytic input, `StandardRootCountConstancyOnActiveArc`:
per fibre `t` in the active arc, the inside-disk root count of the fibre
polynomial equals a fixed integer `Mlau`.  In that form `Mlau` appears as free
"magic" data: a single integer that the count must equal at *every* fibre.

This module makes `Mlau` **canonical** and isolates the irreducible analytic input
in its smallest natural form.  The classical content behind root-count constancy
is *local*: as the parameter `t` varies and no root crosses the unit circle, the
number of roots strictly inside the unit disk is **locally constant** (Rouché /
continuity of roots).  Global constancy on the connected open arc then follows
from preconnectedness, and `Mlau` is no longer free data — it is pinned to the
count at any single reference fibre.

Main declarations:

* `fibreInsideCount` — the inside-disk root count of the fibre polynomial.
* `StandardInsideCountLocallyConstant` — the canonical (Rouché) analytic input:
  the inside-disk root count is locally constant on the open arc.  This is the
  smallest exact analytic datum remaining.
* `rootCount_constancy_of_locallyConstant` — local constancy together with a
  reference value at one fibre yields the global constancy datum
  `StandardRootCountConstancyOnActiveArc`; `Mlau` is pinned to the reference
  fibre.
* `standardReturnMultiplierRootDataMinimal_of_localConstancy` — assembles the full
  canonical reduced root-data interface `StandardReturnMultiplierRootDataMinimal`
  from the degree compatibility, the zero-free active arc, local constancy, and a
  reference value.
* `normalized_return_cocycle_feeds_no_flat_band_root_data_local_constancy` — the
  Stage 6A → Stage 5 bridge driven by the local-constancy interface, with the
  global root count, off-circle condition, outside count, factorisation, root
  enumeration, and periodic-log input all synthesised internally.
-/

namespace CriticalMixedHRT

/-- **Inside-disk root count of the fibre polynomial.**

The number of roots of `fibrePoly coeffs t` that lie strictly inside the unit
disk.  This is exactly the quantity appearing as the inside-count datum `(2)` of
the minimal geometric interface `hroots_min`. -/
noncomputable def fibreInsideCount {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (t : ℝ) : ℕ :=
  ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card

/-- **The canonical (Rouché) analytic input.**

The inside-disk root count `fibreInsideCount coeffs t` is *locally constant* as
the parameter `t` ranges over the open arc `Ioo a b`.  This is the smallest exact
analytic datum behind root-count constancy: on an open parameter arc where no
root crosses the unit circle, the number of roots inside the unit disk does not
jump.  Compared with `StandardRootCountConstancyOnActiveArc`, the free integer
`Mlau` is eliminated. -/
def StandardInsideCountLocallyConstant {d : ℕ}
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (a b : ℝ) : Prop :=
  IsLocallyConstant (fun t : ↥(Set.Ioo a b) => fibreInsideCount coeffs (t : ℝ))

/-- **Local constancy + a reference value ⟹ global constancy datum.**

If the inside-disk root count is locally constant on the open arc `Ioo a b`, and
equals `Mlau` at a single reference fibre `t₀ ∈ Ioo a b`, then it equals `Mlau` at
*every* active fibre, i.e. the global constancy datum
`StandardRootCountConstancyOnActiveArc` holds.  Here `Mlau` is no longer free
data: it is pinned to the reference fibre by `hMlau`. -/
theorem rootCount_constancy_of_locallyConstant
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) {a b : ℝ}
    (ad : LaurentPolynomial ℂ) (Mlau : ℤ)
    (hlc : StandardInsideCountLocallyConstant coeffs a b)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hMlau : Mlau = (fibreInsideCount coeffs t₀ : ℤ)) :
    StandardRootCountConstancyOnActiveArc coeffs a b ad Mlau := by
  intro t ht _had
  haveI : PreconnectedSpace ↥(Set.Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  have key : fibreInsideCount coeffs t = fibreInsideCount coeffs t₀ :=
    hlc.apply_eq_of_preconnectedSpace (⟨t, ht⟩ : ↥(Set.Ioo a b)) (⟨t₀, ht₀⟩ : ↥(Set.Ioo a b))
  show Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card
  rw [hMlau]
  exact_mod_cast key.symm

/-- **Assembled canonical reduced root-data interface from local constancy.**

From the degree compatibility `(mlau : ℤ) = d - Mlau`, the zero-free active arc,
the local constancy of the inside count, and a reference value pinning `Mlau`, we
obtain the full canonical reduced interface
`StandardReturnMultiplierRootDataMinimal`, which (by
`standardReturnMultiplierRootDataMinimal_implies_hroots_min`) implies the
certificate's `hroots_min`. -/
theorem standardReturnMultiplierRootDataMinimal_of_localConstancy
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) {a b : ℝ}
    (ad : LaurentPolynomial ℂ) (mlau : ℕ) (Mlau : ℤ)
    (hmM : (mlau : ℤ) = (d : ℤ) - Mlau)
    (hzf : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      ∀ x : ℝ, (fibrePoly coeffs t).eval (circleParam x) ≠ 0)
    (hlc : StandardInsideCountLocallyConstant coeffs a b)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hMlau : Mlau = (fibreInsideCount coeffs t₀ : ℤ)) :
    StandardReturnMultiplierRootDataMinimal coeffs a b ad mlau Mlau :=
  ⟨hmM, hzf, rootCount_constancy_of_locallyConstant coeffs ad Mlau hlc ht₀ hMlau⟩

/-- **Stage 6A → Stage 5 bridge driven by the local-constancy interface.**

This is the strongest no-`sorry` Stage 6A bridge in Run A.  Compared with
`normalized_return_cocycle_feeds_no_flat_band_root_data_closed`, the inside-count
datum (`hin`, which carried the free integer `Mlau`) is replaced by:

* `hlc` — the inside-disk root count is *locally constant* on the active arc
  (the canonical Rouché/continuity content);
* `ht₀`, `hMlau` — `Mlau` is the inside count at a single reference fibre `t₀`.

The global root count, the off-circle condition, the outside count, the
factorisation identity, the root enumeration, and the periodic-logarithm input
are all synthesised internally.  The remaining holonomy identification is the
choice-free `hJholo`. -/
theorem normalized_return_cocycle_feeds_no_flat_band_root_data_local_constancy
    (D : NormalizedReturnData)
    (DK : DenjoyKoksmaReturnData D.θ)
    (hq : Filter.Tendsto DK.q Filter.atTop Filter.atTop)
    {a₀ b₀ : ℝ}
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H (Set.Ioo a₀ b₀))
    (hHne : ∀ s ∈ Set.Ioo a₀ b₀, H s ≠ 0)
    (S : Set ℝ) (hSU : S ⊆ Set.Ioo a₀ b₀)
    (hSpos : 0 < MeasureTheory.volume S)
    (hSres : ∀ s ∈ S, H s ∈ resonanceGroupC DK.q)
    (E : Set ℝ) (hE : E.Finite)
    (J : ℝ → ℂ)
    (hJgauge : ∀ s ∈ Set.Ioo a₀ b₀,
        J s = H s * Complex.exp (-2 * π * Complex.I * (D.θ : ℂ) * (s : ℂ)))
    {dlau : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (had : ad ≠ 0)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨dlau, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hmM : (mlau : ℤ) = (dlau : ℤ) - Mlau)
    (hzf : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ x : ℝ, (fibrePoly coeffs t).eval (circleParam x) ≠ 0)
    (hlc : StandardInsideCountLocallyConstant coeffs a₀ b₀)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a₀ b₀)
    (hMlau : Mlau = (fibreInsideCount coeffs t₀ : ℤ))
    (hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
        J t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)) :
    False := by
  have hin : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card :=
    rootCount_constancy_of_locallyConstant coeffs ad Mlau hlc ht₀ hMlau
  exact normalized_return_cocycle_feeds_no_flat_band_root_data_closed D DK hq H hH
    hHne S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hmM
    hzf hin hJholo

end CriticalMixedHRT
