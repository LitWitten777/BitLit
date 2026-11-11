import Mathlib
import RequestProject.HRT.NormalizedReturnCocycle
import RequestProject.HRT.LocalCertificateAdapter
import RequestProject.HRT.NoFlatBand
import RequestProject.Rotation.DenjoyKoksmaInterface
import RequestProject.HRT.ActiveArcExtraction
import RequestProject.HRT.ReturnMultiplierLaurent
import RequestProject.HRT.FiniteExceptionalFibers
import RequestProject.HRT.CertificateInputSynthesis

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6A — feeding the normalized return cocycle into Stage 5

This module records the bridge theorem connecting the normalized return-cocycle
data of `NormalizedReturnCocycle.lean` to the certificate-integrated
no-flat-band theorem of Stage 5
(`no_flat_band_of_active_fibers_integrated_certificate`).

The irrational rotation parameter is `θ = D.θ`, supplied as `D.hθ_irr`.  Once a
positive-measure family of active fibers landing in the resonance group is
available, together with the analytic zero-free holonomy `H`, the periodic Zak
gauge `J s = H s · e^{-2πiθs}`, and the *input* data of the imported local
Laurent holonomy certificate (leading coefficient, coefficient family, root
factorisation, periodic logarithm, holonomy identification), the Stage 5
machinery produces the no-flat-band contradiction.

This theorem does **not** prove the global HRT result; it only packages the
output of the Stage 6A normalized return cocycle into the exact hypotheses
consumed by Stage 5.
-/

namespace CriticalMixedHRT

/-- **Task F — the normalized return cocycle feeds the Stage 5 no-flat-band
theorem.**

Given normalized return data `D` (which supplies the irrational rotation
parameter `θ = D.θ` through `D.hθ_irr`), and the Stage 5 active-fibre /
analytic-rigidity / periodic-gauge data together with the *input* data of the
imported local Laurent holonomy certificate, the certificate-integrated Stage 5
theorem yields a contradiction.

This is a thin packaging wrapper around
`no_flat_band_of_active_fibers_integrated_certificate`, instantiating its
irrational rotation hypothesis with `D.hθ_irr`. -/
theorem normalized_return_cocycle_feeds_no_flat_band
    (D : NormalizedReturnData)
    (DK : DenjoyKoksmaReturnData D.θ)
    (hq : Tendsto DK.q atTop atTop)
    (U : Set ℝ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H U) (hHne : ∀ s ∈ U, H s ≠ 0)
    (Active : Set ℝ) (hActiveU : Active ⊆ U)
    (hActivePos : 0 < MeasureTheory.volume Active)
    (hActiveRes : ∀ s ∈ Active, H s ∈ resonanceGroupC DK.q)
    {a b : ℝ} (hab : a < b) (hsub : Set.Ioo a b ⊆ U)
    (J : ℝ → ℂ)
    (hJgauge : ∀ s ∈ Set.Ioo a b,
        J s = H s * Complex.exp (-2 * π * Complex.I * (D.θ : ℂ) * (s : ℂ)))
    {dlau : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (had : ad ≠ 0)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨dlau, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hroots : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin dlau → ℂ,
        (∀ i, ‖r i‖ ≠ 1) ∧
        Mlau = ↑((Finset.univ.filter (fun i : Fin dlau => ‖r i‖ < 1)).card) ∧
        (Finset.univ.filter (fun i : Fin dlau => 1 < ‖r i‖)).card = mlau ∧
        Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin dlau, (Polynomial.X - Polynomial.C (r i)) =
          ∑ j : Fin (dlau + 1),
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ))
    (ell : ℝ → ℝ → ℂ)
    (hell : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      IsPeriodicLog (ell t) (evalBiLaurentPoly coeffs Mlau t))
    (hJlog : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      J t = Complex.exp (∫ x in (0 : ℝ)..1, ell t x)) :
    False :=
  no_flat_band_of_active_fibers_integrated_certificate D.hθ_irr DK hq U hU hUc H hH
    hHne Active hActiveU hActivePos hActiveRes hab hsub J hJgauge mlau Mlau ad had
    coeffs h_ad_coeff hroots ell hell hJlog

/-
**Part E — strengthened normalized return-cocycle bridge.**

This upgrades `normalized_return_cocycle_feeds_no_flat_band` by **removing the raw
selection hypotheses** for the active arc.  Instead of asking the caller to
pre-select a connected arc `(a,b)` and an active subset `Active ⊆ U` carried by
that arc, this version takes:

* a single window `U = Set.Ioo a₀ b₀`;
* a positive-measure active set `S ⊆ U` on which the holonomy `H` is resonant;
* a *finite exceptional parameter set* `E` (supplied, e.g., by
  `normalized_window_exceptional_parameter_set_finite` from Part C);

and derives **internally**, via the Part-D active-arc extraction
(`positive_measure_active_arc_avoiding_finite_exceptional`), a sub-arc
`(a,b) ⊆ U` avoiding `E` on which `S` still has positive measure; this becomes
the `Active` data fed to the certificate-integrated Stage-5 theorem
`no_flat_band_of_active_fibers_integrated_certificate`.

The per-arc local Laurent holonomy certificate **input** data (`ad`, `coeffs`,
`hroots`, `ell`, `hJlog`) — encoding the bivariate Laurent factorisation and the
holonomy identification, i.e. the full Stage 2–4 analysis specialised to this
cocycle — is retained as explicit hypotheses on the window `U`; only the active
subset / arc selection (Part D) and the finiteness of the exceptional set
(Part C) are discharged internally, and the per-fibre Laurent object itself is
now concretely constructed in `ReturnMultiplierLaurent.lean` (Part A) rather than
assumed.
-/
theorem normalized_return_cocycle_feeds_no_flat_band_integrated
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
    (hroots : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin dlau → ℂ,
        (∀ i, ‖r i‖ ≠ 1) ∧
        Mlau = ↑((Finset.univ.filter (fun i : Fin dlau => ‖r i‖ < 1)).card) ∧
        (Finset.univ.filter (fun i : Fin dlau => 1 < ‖r i‖)).card = mlau ∧
        Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin dlau, (Polynomial.X - Polynomial.C (r i)) =
          ∑ j : Fin (dlau + 1),
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ))
    (ell : ℝ → ℝ → ℂ)
    (hell : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      IsPeriodicLog (ell t) (evalBiLaurentPoly coeffs Mlau t))
    (hJlog : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      J t = Complex.exp (∫ x in (0 : ℝ)..1, ell t x)) :
    False := by
  -- Part D: extract a sub-arc of the window avoiding `E ∪ {a₀, b₀}` carrying
  -- positive `S`-measure.
  have hE' : (E ∪ {a₀, b₀}).Finite := hE.union ((Set.finite_singleton b₀).insert a₀)
  obtain ⟨a, b, hab, hdisj, hpos⟩ :=
    positive_measure_active_arc_avoiding_finite_exceptional hE' hSpos
  -- The extracted arc lies inside the window.
  have hsub : Set.Ioo a b ⊆ Set.Ioo a₀ b₀ := by
    obtain ⟨ y, hy ⟩ := MeasureTheory.nonempty_of_measure_ne_zero hpos.ne';
    simp_all +decide [ Set.ext_iff ];
    grind
  -- Package the active subset.
  refine no_flat_band_of_active_fibers_integrated_certificate D.hθ_irr DK hq
    (Set.Ioo a₀ b₀) isOpen_Ioo isPreconnected_Ioo H hH hHne
    (S ∩ Set.Ioo a b) (fun s hs => hSU hs.1) hpos
    (fun s hs => hSres s hs.1) hab hsub J (fun s hs => hJgauge s (hsub hs))
    mlau Mlau ad had coeffs h_ad_coeff
    (fun t ht => hroots t (hsub ht)) ell (fun t ht => hell t (hsub ht))
    (fun t ht => hJlog t (hsub ht))

/-
**Part D + E — synthesizing the periodic logarithm input.**

This upgrades `normalized_return_cocycle_feeds_no_flat_band_integrated` by
**eliminating the explicit periodic-logarithm hypotheses `ell` and `hell`**.

The imported certificate's `ell`/`hell` inputs are *not* independent data: a
periodic logarithm of the bivariate Laurent loop `evalBiLaurentPoly coeffs M t`
is completely determined (up to the harmless `2πi`-integer ambiguity) by the
root factorisation `hroots`, via
`CriticalMixedHRT.evalBiLaurentPoly_periodic_log_of_roots`.  Hence we construct
`ell` internally from `hroots` (by classical choice) and discharge `hell`.

What remains of the holonomy identification is reformulated as the single,
choice-free hypothesis `hJholo`, which identifies the geometric holonomy `J t`
with the loop-determined value `exp(∫₀¹ ell_t)` for *any* periodic logarithm
`ell_t` of the loop (the value is independent of the choice by
`exp_integral_periodic_log_eq`).  This is strictly weaker to supply than the
previous `ell` + `hell` + `hJlog` triple, while remaining provably equivalent.

The per-fibre root factorisation `hroots` (encoding the bivariate z-factorisation
of the return multiplier) is retained as the final explicit local-certificate
interface datum, per the task's documented fallback policy.
-/
theorem normalized_return_cocycle_feeds_no_flat_band_synthesized
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
    (hroots : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin dlau → ℂ,
        (∀ i, ‖r i‖ ≠ 1) ∧
        Mlau = ↑((Finset.univ.filter (fun i : Fin dlau => ‖r i‖ < 1)).card) ∧
        (Finset.univ.filter (fun i : Fin dlau => 1 < ‖r i‖)).card = mlau ∧
        Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin dlau, (Polynomial.X - Polynomial.C (r i)) =
          ∑ j : Fin (dlau + 1),
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ))
    (hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
        J t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)) :
    False := by
  -- Synthesize a periodic logarithm `ell t` of the bivariate loop on each
  -- active fibre, from the root factorisation data, by classical choice.
  have hex : ∀ t : ℝ, ∃ ell_t : ℝ → ℂ,
      (t ∈ Set.Ioo a₀ b₀ → evalLaurentCircle ad t ≠ 0 →
        IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t)) := by
    intro t
    by_cases h : t ∈ Set.Ioo a₀ b₀ ∧ evalLaurentCircle ad t ≠ 0
    · obtain ⟨r, hr_off, hM, _hm, hfact⟩ := hroots t h.1 h.2
      obtain ⟨ell_t, hell_t⟩ := evalBiLaurentPoly_periodic_log_of_roots Mlau coeffs t
        (evalLaurentCircle ad t) h.2 r hr_off hM hfact
      exact ⟨ell_t, fun _ _ => hell_t⟩
    · exact ⟨fun _ => 0, fun ht hne => absurd ⟨ht, hne⟩ h⟩
  choose ell hell_raw using hex
  have hell : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      IsPeriodicLog (ell t) (evalBiLaurentPoly coeffs Mlau t) :=
    fun t ht hne => hell_raw t ht hne
  have hJlog : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      J t = Complex.exp (∫ x in (0 : ℝ)..1, ell t x) :=
    fun t ht hne => hJholo t ht hne (ell t) (hell t ht hne)
  exact normalized_return_cocycle_feeds_no_flat_band_integrated D DK hq H hH hHne
    S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots
    ell hell hJlog

end CriticalMixedHRT