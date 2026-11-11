import Mathlib
import RequestProject.HRT.ReturnMultiplierRootData
import RequestProject.HRT.ReturnCocycleToNoFlatBand

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000

/-!
# Root-data adapter — the minimal local-certificate root-data interface

The imported local holonomy certificate consumes, per fibre `t`, the root
factorisation data `hroots`:

```
∃ r : Fin d → ℂ,
  (∀ i, ‖r i‖ ≠ 1) ∧
  M = #{i : ‖r i‖ < 1} ∧
  #{i : 1 < ‖r i‖} = m ∧
  C (ad(t)) · ∏ᵢ (X − r i) = ∑ⱼ C (coeffsⱼ(t)) Xʲ.
```

`ReturnMultiplierRootData.lean` showed that the *factorisation identity* and the
*root enumeration* `r` are not independent input: they are produced canonically
from the polynomial-in-`z` representation by the fundamental theorem of algebra
(`return_multiplier_local_root_factorization`).  This module uses that to reduce
`hroots` to its **minimal substantive core**: the purely geometric facts about
the roots of the canonical fibre polynomial `fibrePoly coeffs t`, namely

* `hoff`  — no root lies on the unit circle, and
* `hM`/`hm` — the inside / outside root counts equal `M` and `m`,

stated directly on the canonical roots multiset `(fibrePoly coeffs t).roots`.

* `return_multiplier_root_data_for_certificate` — per-fibre: the minimal
  geometric data yields the full certificate `hroots` existential at `t`.
* `local_certificate_root_data_adapter` — interval form: the minimal interface
  `hroots_min` over `(a,b)` yields the certificate's `hroots` over `(a,b)`.
* `root_data_minimal_interface_for_return_multiplier` — the certificate's
  `hroots` over an interval is *implied by* the minimal interface; this is the
  smallest exact root-data interface tied directly to the polynomial-in-`z`
  representation.
* `normalized_return_cocycle_feeds_no_flat_band_root_data_minimal` — the Stage 6A
  → Stage 5 bridge driven by the minimal root-data interface (`hroots_min`) and
  the choice-free holonomy identification `hJholo` (periodic-log input
  synthesised internally, as in `..._synthesized`).
-/

namespace CriticalMixedHRT

/-- **Per-fibre minimal root-data interface.**

From the canonical factorisation `return_multiplier_local_root_factorization`
together with the purely geometric data on the canonical roots multiset
(`hoff`, `hM`, `hm`), we obtain the exact root-factorisation existential `hroots`
consumed by the imported local holonomy certificate, at the fibre `t`. -/
theorem return_multiplier_root_data_for_certificate
    {d : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (t : ℝ) (had_t : evalLaurentCircle ad t ≠ 0)
    (hoff : ∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1)
    (hM : Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card)
    (hm : ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau) :
    ∃ r : Fin d → ℂ,
      (∀ i, ‖r i‖ ≠ 1) ∧
      Mlau = ↑((Finset.univ.filter (fun i : Fin d => ‖r i‖ < 1)).card) ∧
      (Finset.univ.filter (fun i : Fin d => 1 < ‖r i‖)).card = mlau ∧
      Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) =
        ∑ j : Fin (d + 1),
          Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ) := by
  obtain ⟨r, hfact, hrootmap⟩ :=
    return_multiplier_local_root_factorization coeffs ad h_ad_coeff t had_t
  -- The canonical multiset identity, transported to `fibrePoly coeffs t`.
  have hrm : (fibrePoly coeffs t).roots = Multiset.map r Finset.univ.val := hrootmap
  refine ⟨r, ?_, ?_, ?_, hfact⟩
  · exact root_offcircle_transfer r _ hrm hoff
  · rw [hM, root_count_transfer r _ hrm (fun z => ‖z‖ < 1)]
  · rw [← hm, root_count_transfer r _ hrm (fun z => 1 < ‖z‖)]

/-- **Interval form of the root-data adapter.**

Given the minimal geometric root-data interface `hroots_min` on the window
`(a,b)` — for each fibre with nonzero leading coefficient, the roots of the
canonical fibre polynomial avoid the unit circle and have inside / outside
counts `Mlau` / `mlau` — we obtain the certificate's full `hroots` data on
`(a,b)`. -/
theorem local_certificate_root_data_adapter
    {a b : ℝ} {d : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hroots_min : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
      ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau) :
    ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin d → ℂ,
        (∀ i, ‖r i‖ ≠ 1) ∧
        Mlau = ↑((Finset.univ.filter (fun i : Fin d => ‖r i‖ < 1)).card) ∧
        (Finset.univ.filter (fun i : Fin d => 1 < ‖r i‖)).card = mlau ∧
        Polynomial.C (evalLaurentCircle ad t) *
            ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) =
          ∑ j : Fin (d + 1),
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ) := by
  intro t ht had_t
  obtain ⟨hoff, hM, hm⟩ := hroots_min t ht had_t
  exact return_multiplier_root_data_for_certificate mlau Mlau ad coeffs h_ad_coeff
    t had_t hoff hM hm

/-- **The smallest exact root-data interface.**

This restates `local_certificate_root_data_adapter`: the certificate's full
root-factorisation data `hroots` on a window `(a,b)` is *implied by* the minimal
interface `hroots_min`, which carries only the irreducible geometric content
(roots off the unit circle and the inside / outside counts) stated directly on
the canonical fibre polynomial `fibrePoly coeffs t = ∑ⱼ C (coeffsⱼ(t)) Xʲ`.

The factorisation identity and the root enumeration `r` of the original `hroots`
are no longer caller-supplied data — they are synthesised internally from the
polynomial-in-`z` representation by the fundamental theorem of algebra. -/
theorem root_data_minimal_interface_for_return_multiplier
    {a b : ℝ} {d : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hroots_min : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
      ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau) :
    ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin d → ℂ,
        (∀ i, ‖r i‖ ≠ 1) ∧
        Mlau = ↑((Finset.univ.filter (fun i : Fin d => ‖r i‖ < 1)).card) ∧
        (Finset.univ.filter (fun i : Fin d => 1 < ‖r i‖)).card = mlau ∧
        Polynomial.C (evalLaurentCircle ad t) *
            ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) =
          ∑ j : Fin (d + 1),
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ) :=
  local_certificate_root_data_adapter mlau Mlau ad coeffs h_ad_coeff hroots_min

/-- **Stage 6A → Stage 5 bridge driven by the minimal root-data interface.**

This is the strongest no-`sorry` form of the Stage 6A bridge produced in this
run.  Compared with `normalized_return_cocycle_feeds_no_flat_band_synthesized`,
the explicit root-factorisation data `hroots` is replaced by the strictly
smaller minimal interface `hroots_min` (no caller-supplied root enumeration and
no caller-supplied factorisation identity — these are synthesised internally
from the polynomial-in-`z` representation by the FTA).  The periodic-logarithm
input is synthesised internally exactly as in `..._synthesized`, and the
remaining holonomy identification is the choice-free `hJholo`.

What is left in `hroots_min` is exactly the irreducible geometric content of the
local certificate: the roots of the canonical fibre polynomial avoid the unit
circle, and their inside / outside counts equal `Mlau` and `mlau`. -/
theorem normalized_return_cocycle_feeds_no_flat_band_root_data_minimal
    (D : NormalizedReturnData)
    (DK : DenjoyKoksmaReturnData D.θ)
    (hq : Tendsto DK.q atTop atTop)
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
    (hroots_min : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
      ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau)
    (hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
        J t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)) :
    False := by
  have hroots :
      ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
        ∃ r : Fin dlau → ℂ,
          (∀ i, ‖r i‖ ≠ 1) ∧
          Mlau = ↑((Finset.univ.filter (fun i : Fin dlau => ‖r i‖ < 1)).card) ∧
          (Finset.univ.filter (fun i : Fin dlau => 1 < ‖r i‖)).card = mlau ∧
          Polynomial.C (evalLaurentCircle ad t) *
              ∏ i : Fin dlau, (Polynomial.X - Polynomial.C (r i)) =
            ∑ j : Fin (dlau + 1),
              Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ) :=
    local_certificate_root_data_adapter mlau Mlau ad coeffs h_ad_coeff hroots_min
  exact normalized_return_cocycle_feeds_no_flat_band_synthesized D DK hq H hH hHne
    S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT
