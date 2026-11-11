import Mathlib
import RequestProject.FinalAssembly
import RequestProject.WindingNumberWrapper
import RequestProject.HRT.LocalCertificateAdapter

open Complex Finset
open scoped BigOperators Real

set_option maxHeartbeats 1000000

/-!
# Certificate input synthesis — periodic logarithm from root factorisation data

This module turns the per-fibre **root factorisation data** consumed by the
imported local holonomy certificate into the **periodic logarithm** input that
the certificate also requires.  It exposes a public version of the construction
performed (privately) inside `WindingNumberWrapper.lean`:

* `evalBiLaurentPoly_periodic_log_of_roots` — from the explicit factorisation
  `Polynomial.C ad_val · ∏ (X − r i) = ∑ⱼ C (coeffsⱼ(t)) Xʲ` of the bivariate
  Laurent loop on a fibre `t`, together with the off-circle root condition
  `‖r i‖ ≠ 1` and the winding bookkeeping `M = #{i : ‖r i‖ < 1}`, it produces a
  continuous `1`-periodic logarithm of `evalBiLaurentPoly coeffs M t`.

The point is that the certificate's separate `ell`/`hell` inputs are *not*
independent data: they are completely determined (up to the harmless
`2πi`-integer ambiguity) by the root factorisation `hroots`.  Consequently the
explicit `ell` and `hell` hypotheses of the Stage 6A → Stage 5 bridge can be
discharged internally; this is used in
`normalized_return_cocycle_feeds_no_flat_band_synthesized` in
`ReturnCocycleToNoFlatBand.lean`.
-/

namespace CriticalMixedHRT

/-- **Periodic logarithm from root factorisation data.**

Given, on a fibre `t`, the factorisation of the bivariate Laurent loop
`evalBiLaurentPoly coeffs M t` into `circleParam x ^ (-M) · ad_val · ∏ᵢ (z − rᵢ)`
(packaged as the polynomial identity `hfact`), with `ad_val ≠ 0`, all roots off
the unit circle (`hr_off`), and the standard winding count `hM`, there is a
continuous `1`-periodic logarithm of `evalBiLaurentPoly coeffs M t`.

This is a public wrapper around the (private) construction in
`WindingNumberWrapper.lean`, built from `factored_loop_has_periodic_log` and
`evalBiLaurentPoly_eq_factored`. -/
theorem evalBiLaurentPoly_periodic_log_of_roots
    {d : ℕ} (M : ℤ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (t : ℝ)
    (ad_val : ℂ) (had : ad_val ≠ 0) (r : Fin d → ℂ)
    (hr_off : ∀ i, ‖r i‖ ≠ 1)
    (hM : M = ↑((Finset.univ.filter (fun i : Fin d => ‖r i‖ < 1)).card))
    (hfact : Polynomial.C ad_val * ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) =
        ∑ j : Fin (d + 1), Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ)) :
    ∃ ell : ℝ → ℂ, IsPeriodicLog ell (evalBiLaurentPoly coeffs M t) := by
  refine ⟨ _, (factored_loop_has_periodic_log M ad_val r had hr_off hM).cont,
            (factored_loop_has_periodic_log M ad_val r had hr_off hM).periodic, fun x => ?_⟩
  rw [(factored_loop_has_periodic_log M ad_val r had hr_off hM).exp_eq,
      evalBiLaurentPoly_eq_factored coeffs M t r ad_val hfact]

end CriticalMixedHRT
