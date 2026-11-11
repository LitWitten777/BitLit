import Mathlib
import RequestProject.HolonomyCertificate.Full.LaurentSetup

open Complex Polynomial Finset
open scoped BigOperators Real Classical

set_option maxHeartbeats 1000000

/-!
# Return-multiplier root data — canonical factorisation of the fibre polynomial

The imported local holonomy certificate
(`local_holonomy_certificate_full_periodic_log_form`) consumes, per fibre `t`,
the *root factorisation data* `hroots`:

* an explicit root enumeration `r : Fin d → ℂ`,
* the off-circle condition `∀ i, ‖r i‖ ≠ 1`,
* the winding bookkeeping `M = #{i : ‖r i‖ < 1}`, `#{i : 1 < ‖r i‖} = m`,
* the polynomial factorisation identity
  `C (ad(t)) · ∏ᵢ (X − r i) = ∑ⱼ C (coeffsⱼ(t)) Xʲ`.

This module shows that the **factorisation existence** and the **root
enumeration** parts of this data are *not* independent input: starting from the
polynomial-in-`z` representation `∑ⱼ C (coeffsⱼ(t)) Xʲ` of the return multiplier
(constructed in `ReturnMultiplierPolynomialInZ.lean`), and using only the
nonvanishing of its leading coefficient `evalLaurentCircle ad t ≠ 0`, the
fundamental theorem of algebra (`IsAlgClosed.splits` over `ℂ`) produces a
canonical root enumeration `r` with both the factorisation identity *and* the
multiset identity `roots = Multiset.map r univ.val`.

The latter multiset identity lets every root-count over `Fin d` be transferred
to a count over the canonical roots multiset, so the only genuinely substantive
remaining data are the **geometric** facts: the roots avoid the unit circle, and
the inside/outside counts equal `M` and `m`.  These are isolated as the minimal
root-data interface in `RootDataAdapter.lean`.

Main declarations:

* `polyOfCoeffs` — the fibre polynomial `∑ⱼ C (c j) Xʲ`;
* `polyOfCoeffs_coeff`, `polyOfCoeffs_natDegree`, `polyOfCoeffs_leadingCoeff`;
* `multiset_eq_map_fin` — a multiset of card `n` is `Multiset.map f univ.val`;
* `polyOfCoeffs_root_factorization` — the canonical factorisation + multiset id;
* `fibrePoly` — the certificate's per-fibre polynomial in `coeffs`/`t`;
* `return_multiplier_local_root_factorization` — the canonical factorisation,
  stated directly on the certificate's polynomial-in-`z` representation;
* `root_count_transfer`, `root_offcircle_transfer` — count / off-circle bridges
  from the canonical roots multiset to the `Fin d` enumeration.
-/

namespace CriticalMixedHRT

/-- The fibre polynomial `∑ⱼ C (c j) Xʲ` built from a coefficient vector
`c : Fin (d+1) → ℂ`. -/
noncomputable def polyOfCoeffs {d : ℕ} (c : Fin (d + 1) → ℂ) : Polynomial ℂ :=
  ∑ j : Fin (d + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)

/-- The `k`-th coefficient of `polyOfCoeffs c` is `c ⟨k, _⟩` if `k ≤ d`, else `0`. -/
lemma polyOfCoeffs_coeff {d : ℕ} (c : Fin (d + 1) → ℂ) (k : ℕ) :
    (polyOfCoeffs c).coeff k = if h : k < d + 1 then c ⟨k, h⟩ else 0 := by
  unfold polyOfCoeffs
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split
  · next h =>
    rw [Finset.sum_eq_single (⟨k, h⟩ : Fin (d + 1))]
    · simp
    · intro b _ hb
      have : k ≠ (b : ℕ) := by intro hbk; exact hb (Fin.ext hbk.symm)
      simp [this]
    · intro hcon; simp at hcon
  · next h =>
    apply Finset.sum_eq_zero
    intro j _
    have : k ≠ (j : ℕ) := by intro hbk; subst hbk; exact h j.2
    simp [this]

/-- If the top coefficient `c (Fin.last d)` is nonzero, `polyOfCoeffs c` has
degree exactly `d`. -/
lemma polyOfCoeffs_natDegree {d : ℕ} (c : Fin (d + 1) → ℂ)
    (hd : c (Fin.last d) ≠ 0) : (polyOfCoeffs c).natDegree = d := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [polyOfCoeffs_coeff]
    split
    · next h => omega
    · rfl
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [polyOfCoeffs_coeff]
    simp only [Nat.lt_succ_self, dif_pos]
    convert hd using 2

/-- The leading coefficient of `polyOfCoeffs c` is its top coefficient. -/
lemma polyOfCoeffs_leadingCoeff {d : ℕ} (c : Fin (d + 1) → ℂ)
    (hd : c (Fin.last d) ≠ 0) :
    (polyOfCoeffs c).leadingCoeff = c (Fin.last d) := by
  rw [Polynomial.leadingCoeff, polyOfCoeffs_natDegree c hd, polyOfCoeffs_coeff]
  simp only [Nat.lt_succ_self, dif_pos]
  rfl

/-- A multiset of cardinality `n` is the image of `Finset.univ : Finset (Fin n)`
under some function `f : Fin n → ℂ` (a `Fin n`-enumeration of the multiset). -/
theorem multiset_eq_map_fin (s : Multiset ℂ) (n : ℕ) (h : Multiset.card s = n) :
    ∃ f : Fin n → ℂ, s = Multiset.map f Finset.univ.val := by
  induction s using Quotient.inductionOn with
  | _ L =>
    have hlen : L.length = n := by simpa using h
    have hofFn : List.ofFn (fun i : Fin n => L.get (Fin.cast hlen.symm i)) = L := by
      conv_rhs => rw [← List.ofFn_get L]
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2; simp
    refine ⟨fun i => L.get (Fin.cast hlen.symm i), ?_⟩
    rw [Fin.univ_val_map, hofFn]; rfl

/-- **Canonical root factorisation of the fibre polynomial** (abstract form).

Over `ℂ`, the polynomial `polyOfCoeffs c` splits (fundamental theorem of
algebra); if its top coefficient is nonzero, there is a `Fin d`-enumeration `r`
of its roots with the factorisation identity *and* the multiset identity
`roots = Multiset.map r univ.val`. -/
theorem polyOfCoeffs_root_factorization {d : ℕ} (c : Fin (d + 1) → ℂ)
    (hd : c (Fin.last d) ≠ 0) :
    ∃ r : Fin d → ℂ,
      Polynomial.C (c (Fin.last d)) *
          ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) = polyOfCoeffs c ∧
      (polyOfCoeffs c).roots = Multiset.map r Finset.univ.val := by
  set P := polyOfCoeffs c with hP
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hcard : P.roots.card = d := by
    rw [Polynomial.splits_iff_card_roots.mp hsplit, polyOfCoeffs_natDegree c hd]
  obtain ⟨r, hr⟩ := multiset_eq_map_fin P.roots d hcard
  refine ⟨r, ?_, hr⟩
  have hfact := hsplit.eq_prod_roots
  rw [polyOfCoeffs_leadingCoeff c hd] at hfact
  rw [hfact, hr]
  congr 1
  rw [Multiset.map_map]
  rfl

/-- **Root-count transfer.**  Given the canonical multiset identity
`roots = Multiset.map r univ.val`, any count over `Fin d` of a predicate applied
to `r` equals the count of that predicate over the roots multiset. -/
lemma root_count_transfer {d : ℕ} (r : Fin d → ℂ) (roots : Multiset ℂ)
    (hr : roots = Multiset.map r Finset.univ.val) (p : ℂ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin d => p (r i))).card =
      (Multiset.filter p roots).card := by
  rw [hr, Multiset.filter_map, Multiset.card_map]; rfl

/-- **Off-circle transfer.**  If every root in the multiset is off the unit
circle and `roots = Multiset.map r univ.val`, then every enumerated `r i` is off
the unit circle. -/
lemma root_offcircle_transfer {d : ℕ} (r : Fin d → ℂ) (roots : Multiset ℂ)
    (hr : roots = Multiset.map r Finset.univ.val)
    (hoff : ∀ z ∈ roots, ‖z‖ ≠ 1) : ∀ i, ‖r i‖ ≠ 1 := by
  intro i
  apply hoff
  rw [hr]
  exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩

/-- The certificate's per-fibre polynomial in `coeffs` and `t`:
`∑ⱼ C (evalLaurentCircle (coeffsⱼ) t) Xʲ`.  This is exactly the right-hand side of
the factorisation identity in the certificate's `hroots` hypothesis. -/
noncomputable def fibrePoly {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (t : ℝ) : Polynomial ℂ :=
  polyOfCoeffs (fun j => evalLaurentCircle (coeffs j) t)

lemma fibrePoly_eq {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (t : ℝ) :
    fibrePoly coeffs t =
      ∑ j : Fin (d + 1),
        Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ) := rfl

/-- **Canonical root factorisation of the return multiplier**, stated directly on
the certificate's polynomial-in-`z` representation.

For each fibre `t` with nonzero leading coefficient `evalLaurentCircle ad t`,
there is a `Fin d`-enumeration `r` of the roots of the fibre polynomial
`∑ⱼ C (evalLaurentCircle (coeffsⱼ) t) Xʲ`, satisfying both the factorisation
identity required by the imported certificate and the multiset identity
`roots = Multiset.map r univ.val`.

This synthesises the *factorisation* and *root-enumeration* parts of the
certificate's `hroots` data from the polynomial-in-`z` representation alone (no
geometric input). -/
theorem return_multiplier_local_root_factorization
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad) (t : ℝ)
    (had_t : evalLaurentCircle ad t ≠ 0) :
    ∃ r : Fin d → ℂ,
      Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) =
        ∑ j : Fin (d + 1),
          Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ) ∧
      (∑ j : Fin (d + 1),
          Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ)).roots
        = Multiset.map r Finset.univ.val := by
  have hlast : (fun j => evalLaurentCircle (coeffs j) t) (Fin.last d)
      = evalLaurentCircle ad t := by
    simp only [Fin.last]
    rw [show (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1))
          = ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ from rfl, h_ad_coeff]
  have hd : (fun j => evalLaurentCircle (coeffs j) t) (Fin.last d) ≠ 0 := by
    rw [hlast]; exact had_t
  obtain ⟨r, hfact, hroots⟩ :=
    polyOfCoeffs_root_factorization (fun j => evalLaurentCircle (coeffs j) t) hd
  refine ⟨r, ?_, ?_⟩
  · rw [← hlast]; exact hfact
  · exact hroots

end CriticalMixedHRT
