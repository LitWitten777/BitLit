import Mathlib
import RequestProject.NoLaurentObstruction
import RequestProject.FinalAssembly
import RequestProject.WindingNumberWrapper
import RequestProject.HRT.NoFlatBand

open scoped BigOperators Real
open Complex

/-!
# Stage-5 adapter for the imported local holonomy certificate

This module bridges the **imported** local Laurent holonomy certificate
(`local_holonomy_certificate_full_periodic_log_form`, in the certificate
package's `evalLaurentCircle` encoding of Laurent polynomials) to the **Stage-5
interface** of the critical mixed project, which expresses the resulting Laurent
relation through the project's own evaluation map `evalChar` and the `ℕ`-indexed
`Finset.range` encoding consumed by
`CriticalMixedHRT.no_flat_band_of_laurent_holonomy_certificate`.

The two evaluation maps coincide on their common underlying type
`ℤ →₀ ℂ = LaurentPolynomial ℂ`; this is the conversion lemma
`CriticalMixedHRT.evalChar_eq_evalLaurentCircle`.  The adapter theorem
`CriticalMixedHRT.local_holonomy_certificate_full_periodic_log_form_adapter`
then repackages the imported certificate's output (a `Fin (N+1)`-indexed family
of Laurent polynomials, evaluated through `evalLaurentCircle`) into the
`Finset.range`/`evalChar` form expected by Stage 5, introducing no new
hypotheses and no axioms.
-/

namespace CriticalMixedHRT

/-
**Encoding conversion.** The project's circle-evaluation map `evalChar` on a
Laurent polynomial encoded as `ℤ →₀ ℂ` agrees with the certificate package's
`evalLaurentCircle` on the same datum (`LaurentPolynomial ℂ` is definitionally
`ℤ →₀ ℂ`).
-/
theorem evalChar_eq_evalLaurentCircle (p : LaurentPolynomial ℂ) (t : ℝ) :
    evalChar p t = evalLaurentCircle p t := by
  unfold evalChar;
  convert p.sum_single using 2 ; ring;
  unfold evalLaurentCircle ; ring ;
  simp +decide [ LaurentPolynomial.eval₂, Finsupp.sum ];
  constructor <;> intro h <;> rw [ ← Finsupp.sum_single p ] at * ;
  · convert Finsupp.sum_single ( p.sum Finsupp.single ) using 1;
    exact Finset.sum_congr rfl fun x hx => by aesop;
  · convert congr_arg ( fun x : LaurentPolynomial ℂ => x |> LaurentPolynomial.eval₂ ( RingHom.id ℂ ) ( Units.mk0 ( Complex.exp ( 2 * Real.pi * t * Complex.I ) ) ( Complex.exp_ne_zero _ ) ) ) h using 1 ; ring!;
    · induction' ( Finsupp.sum p Finsupp.single |> Finsupp.support ) using Finset.induction <;> simp_all +decide [ Finset.sum_insert, Finset.sum_singleton ];
      exact Or.inl ( by rw [ ← Complex.exp_int_mul ] ; ring );
    · simp +decide [ Finsupp.sum, LaurentPolynomial.eval₂ ];
      grind +revert

/-- **Stage-5 adapter for the imported local holonomy certificate.**

Given exactly the data consumed by the imported certificate
`local_holonomy_certificate_full_periodic_log_form` — a nonzero leading Laurent
coefficient `ad`, the Laurent coefficient family `coeffs`, the per-fibre root
factorisation `hroots`, a periodic logarithm `ell` of the bivariate Laurent
loop `evalBiLaurentPoly coeffs M`, and the holonomy `J t = exp(∫₀¹ ell t)` — this
adapter produces, on a possibly smaller nonempty sub-arc `Ioo a' b'`, a finite
family of Laurent polynomials `Acoef 0,…,Acoef Dlau` (in the project's `ℤ →₀ ℂ`
encoding), not all zero, satisfying the holonomy relation

```
    ∑_{r=0}^{Dlau} evalChar (Acoef r) t · (J t)^r = 0
```

in the `Finset.range`/`evalChar` form consumed by
`no_flat_band_of_laurent_holonomy_certificate`.  It is a thin wrapper around the
imported certificate, converting the `Fin (N+1)` index set to `Finset.range` and
the `evalLaurentCircle` evaluation to `evalChar` via
`evalChar_eq_evalLaurentCircle`. -/
theorem local_holonomy_certificate_full_periodic_log_form_adapter
    {a b : ℝ} (hab : a < b)
    {d : ℕ} (m : ℕ) (M : ℤ)
    (ad : LaurentPolynomial ℂ) (had : ad ≠ 0)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hroots : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin d → ℂ,
        (∀ i, ‖r i‖ ≠ 1) ∧
        M = ↑((Finset.univ.filter (fun i : Fin d => ‖r i‖ < 1)).card) ∧
        (Finset.univ.filter (fun i : Fin d => 1 < ‖r i‖)).card = m ∧
        Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) =
          ∑ j : Fin (d + 1),
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ))
    (ell : ℝ → ℝ → ℂ)
    (hell : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      IsPeriodicLog (ell t) (evalBiLaurentPoly coeffs M t))
    (J : ℝ → ℂ)
    (hJ : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      J t = Complex.exp (∫ x in (0 : ℝ)..1, ell t x)) :
    ∃ a' b' : ℝ,
      a < a' ∧ a' < b' ∧ b' < b ∧
      ∃ (Dlau : ℕ) (Acoef : ℕ → (ℤ →₀ ℂ)),
        (∃ r ∈ Finset.range (Dlau + 1), Acoef r ≠ 0) ∧
        ∀ t ∈ Set.Ioo a' b',
          ∑ r ∈ Finset.range (Dlau + 1), evalChar (Acoef r) t * (J t) ^ r = 0 := by
  obtain ⟨a', b', ha', hab', hb', N, A, hAne, hcert⟩ :=
    local_holonomy_certificate_full_periodic_log_form hab m M ad had coeffs
      h_ad_coeff hroots ell hell J hJ
  refine ⟨a', b', ha', hab', hb', N,
    (fun r => if h : r < N + 1 then A ⟨r, h⟩ else 0), ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hAne
    refine ⟨(n : ℕ), Finset.mem_range.mpr n.isLt, ?_⟩
    simp only [n.isLt, dif_pos]
    simpa using hn
  · intro t ht
    have hconv := hcert t ht
    rw [← Fin.sum_univ_eq_sum_range
      (fun r => evalChar (if h : r < N + 1 then A ⟨r, h⟩ else 0) t * (J t) ^ r) (N + 1)]
    rw [← hconv]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hi : (i : ℕ) < N + 1 := i.isLt
    simp only [hi, dif_pos, Fin.eta]
    rw [evalChar_eq_evalLaurentCircle]

/-- **Deliverable 3 (integrated) — the certificate-integrated no-flat-band theorem.**

This is the upgrade of `no_flat_band_of_active_fibers_and_certificate` in which the
local Laurent holonomy certificate is *no longer* assumed as a raw output
hypothesis.  Instead, the theorem consumes exactly the **input** data of the
imported certificate `local_holonomy_certificate_full_periodic_log_form` (the
leading Laurent coefficient `ad`, the coefficient family `coeffs`, the per-fibre
root factorisation `hroots`, the periodic logarithm `ell` of the Laurent loop,
and the holonomy identification `J t = exp(∫₀¹ ell t)`), together with the
active-fibre/analytic-rigidity data and the periodic-gauge relation
`J s = H s · e^{-2πiθs}`.

Internally it:

1. turns the active fibres into a *constant* holonomy `H ≡ C := H s₀` on `U`
   (`constant_holonomy_of_active_fibers`);
2. undoes the gauge to obtain the exact irrational-character law
   `J s = C · e^{-2πiθs}`;
3. invokes the adapted local certificate
   `local_holonomy_certificate_full_periodic_log_form_adapter` to *produce*
   nontrivial Laurent polynomials with `∑ᵣ evalChar(Aᵣ)(s)·J(s)ʳ = 0` on a
   sub-arc;
4. feeds these to `no_flat_band_of_laurent_holonomy_certificate`, whose certified
   no-Laurent obstruction yields the contradiction.

Thus Stage 5 is certificate-integrated: the imported endpoint is called
internally rather than carried as a hypothesis. -/
theorem no_flat_band_of_active_fibers_integrated_certificate
    {θ : ℝ} (hθ : Irrational θ) (D : DenjoyKoksmaReturnData θ)
    (hq : Filter.Tendsto D.q Filter.atTop Filter.atTop)
    (U : Set ℝ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H U) (hHne : ∀ s ∈ U, H s ≠ 0)
    (Active : Set ℝ) (hActiveU : Active ⊆ U)
    (hActivePos : 0 < MeasureTheory.volume Active)
    (hActiveRes : ∀ s ∈ Active, H s ∈ resonanceGroupC D.q)
    {a b : ℝ} (hab : a < b) (hsub : Set.Ioo a b ⊆ U)
    (J : ℝ → ℂ)
    (hJgauge : ∀ s ∈ Set.Ioo a b,
        J s = H s * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (s : ℂ)))
    {d : ℕ} (m : ℕ) (M : ℤ)
    (ad : LaurentPolynomial ℂ) (had : ad ≠ 0)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hroots : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin d → ℂ,
        (∀ i, ‖r i‖ ≠ 1) ∧
        M = ↑((Finset.univ.filter (fun i : Fin d => ‖r i‖ < 1)).card) ∧
        (Finset.univ.filter (fun i : Fin d => 1 < ‖r i‖)).card = m ∧
        Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) =
          ∑ j : Fin (d + 1),
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ))
    (ell : ℝ → ℝ → ℂ)
    (hell : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      IsPeriodicLog (ell t) (evalBiLaurentPoly coeffs M t))
    (hJlog : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      J t = Complex.exp (∫ x in (0 : ℝ)..1, ell t x)) :
    False := by
  -- Step 1: constant holonomy on `U`.
  have hconst := constant_holonomy_of_active_fibers D hq U hU hUc H hH hHne
    Active hActiveU hActivePos hActiveRes
  obtain ⟨s₀, hs₀⟩ : (Set.Ioo a b).Nonempty := ⟨(a + b) / 2, by constructor <;> linarith⟩
  have hCne : H s₀ ≠ 0 := hHne s₀ (hsub hs₀)
  -- Step 2: the exact irrational-character holonomy law on `Ioo a b`.
  have hlaw : ∀ s ∈ Set.Ioo a b,
      J s = H s₀ * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (s : ℂ)) := by
    intro s hs
    rw [hJgauge s hs, hconst s (hsub hs) s₀ (hsub hs₀)]
  -- Step 3: invoke the adapted local certificate to PRODUCE the Laurent relation.
  obtain ⟨a', b', ha', hab', hb', Dlau, Acoef, hA_ne, hcert⟩ :=
    local_holonomy_certificate_full_periodic_log_form_adapter hab m M ad had
      coeffs h_ad_coeff hroots ell hell J hJlog
  -- Step 4: the law restricted to the sub-arc, then the no-Laurent obstruction.
  have hlaw' : ∀ s ∈ Set.Ioo a' b',
      J s = H s₀ * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (s : ℂ)) := by
    intro s hs
    exact hlaw s ⟨lt_trans ha' hs.1, lt_trans hs.2 hb'⟩
  exact no_flat_band_of_laurent_holonomy_certificate θ hθ (H s₀) hCne hab' J hlaw'
    Dlau Acoef hA_ne hcert

end CriticalMixedHRT