import Mathlib

set_option maxHeartbeats 1000000

open scoped Classical BigOperators Real
open Complex

/-!
# No-Laurent irrational-character obstruction (Theorem 3.2 / `C2`)

This file formalizes the imported algebraic endpoint `C2` of the dossier:
if Laurent polynomials `A₀,…,A_D` satisfy
`∑ᵣ Aᵣ(e^{2πis}) (C e^{-2πiθs})ʳ = 0` on a nonempty interval, with `θ`
irrational and `C ≠ 0`, then every `Aᵣ` is the zero Laurent polynomial.

It is proved from a clean self-contained lemma: a finite linear combination
of exponentials `s ↦ e^{λ s}` with **distinct** frequencies `λ` that vanishes
on an open interval must have all coefficients zero
(`exp_sum_eq_zero_on_interval`).  The key point feeding into it is that, for
`θ` irrational, the frequencies `2πi(k - θr)` arising from distinct pairs
`(r, k)` are distinct.
-/

namespace CriticalMixedHRT

/-- Evaluation of a Laurent polynomial (encoded as `ℤ →₀ ℂ`) at the point
`e^{2πi s}` on the circle. -/
noncomputable def evalChar (p : ℤ →₀ ℂ) (s : ℝ) : ℂ :=
  ∑ k ∈ p.support, p k * Complex.exp (2 * π * Complex.I * (k : ℂ) * (s : ℂ))

/-
**Exponential independence on an interval.** A finite family of
exponentials with pairwise distinct (complex) frequencies that sum to zero on
a nonempty open interval has all coefficients zero.
-/
theorem exp_sum_eq_zero_on_interval
    {ι : Type*} (S : Finset ι) (lam : ι → ℂ) (c : ι → ℂ)
    (hinj : Set.InjOn lam S) {a b : ℝ} (hab : a < b)
    (h : ∀ s ∈ Set.Ioo a b, ∑ i ∈ S, c i * Complex.exp (lam i * (s : ℂ)) = 0) :
    ∀ i ∈ S, c i = 0 := by
  revert h;
  intro h₀;
  -- By induction on the size of $S$, we can prove that if the sum of exponentials is zero on an open interval, then all coefficients must be zero.
  induction' hn : S.card using Nat.strong_induction_on with n ih generalizing S lam c a b;
  by_cases hS : S.Nonempty;
  · -- Choose $i₀ \in S$.
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ ∈ S, True := by
      exact ⟨ hS.choose, hS.choose_spec, trivial ⟩;
    -- Define $g(s) = \sum_{i \in S} c_i e^{(\lambda_i - \lambda_{i₀}) s}$.
    set g : ℝ → ℂ := fun s => ∑ i ∈ S, c i * Complex.exp ((lam i - lam i₀) * s) with hg_def
    have hg_zero : ∀ s ∈ Set.Ioo a b, g s = 0 := by
      simp_all +decide [ sub_mul, Complex.exp_sub ];
      simp_all +decide [ ← mul_div_assoc, ← Finset.sum_div _ _ _ ]
    have hg_deriv_zero : ∀ s ∈ Set.Ioo a b, ∑ i ∈ S, c i * (lam i - lam i₀) * Complex.exp ((lam i - lam i₀) * s) = 0 := by
      have hg_deriv_zero : ∀ s ∈ Set.Ioo a b, deriv g s = ∑ i ∈ S, c i * (lam i - lam i₀) * Complex.exp ((lam i - lam i₀) * s) := by
        intro s hs
        have hg_deriv : deriv g s = ∑ i ∈ S, deriv (fun s : ℝ => c i * Complex.exp ((lam i - lam i₀) * s)) s := by
          convert deriv_sum _ ; aesop;
          exact fun i hi => DifferentiableAt.mul ( differentiableAt_const _ ) ( Complex.differentiableAt_exp.comp _ ( DifferentiableAt.mul ( differentiableAt_const _ ) ( differentiableAt_id.comp _ Complex.ofRealCLM.differentiableAt ) ) );
        rw [ hg_deriv ];
        refine' Finset.sum_congr rfl fun i hi => _;
        convert HasDerivAt.deriv ( HasDerivAt.const_mul ( c i ) ( HasDerivAt.comp s ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul ( lam i - lam i₀ ) ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ) ) ) using 1 ; norm_num ; ring;
      exact fun s hs => hg_deriv_zero s hs ▸ HasDerivAt.deriv ( HasDerivAt.congr_of_eventuallyEq ( hasDerivAt_const _ _ ) ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hs.1 hs.2 ) fun x hx => hg_zero x hx ) ) ▸ by simp +decide ;
    have hg_erase_zero : ∀ i ∈ S.erase i₀, c i * (lam i - lam i₀) = 0 := by
      contrapose! ih;
      refine' ⟨ Finset.card ( S.erase i₀ ), _, S.erase i₀, fun i => lam i - lam i₀, fun i => c i * ( lam i - lam i₀ ), _, a, b, hab, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_erase_of_mem hi₀.1 ];
      · exact hn ▸ Finset.card_pos.mpr hS;
      · exact fun x hx y hy hxy => hinj ( by aesop ) ( by aesop ) ( by linear_combination' hxy )
    have hc_zero : ∀ i ∈ S.erase i₀, c i = 0 := by
      exact fun i hi => eq_zero_of_ne_zero_of_mul_right_eq_zero ( sub_ne_zero_of_ne <| hinj.ne ( Finset.mem_of_mem_erase hi ) hi₀.1 <| by aesop ) <| hg_erase_zero i hi
    have hc_i₀_zero : c i₀ = 0 := by
      specialize h₀ ( ( a + b ) / 2 ) ⟨ by linarith, by linarith ⟩ ; rw [ Finset.sum_eq_single i₀ ] at h₀ <;> aesop;
    exact fun i hi => if hi' : i = i₀ then hi'.symm ▸ hc_i₀_zero else hc_zero i (Finset.mem_erase_of_ne_of_mem hi' hi);
  · aesop

/-
**Theorem 3.2 / `C2` (no-Laurent irrational-character obstruction).**
-/
theorem no_laurent_irrational_character_obstruction
    (θ : ℝ) (hθ : Irrational θ) (Cc : ℂ) (hC : Cc ≠ 0)
    (D : ℕ) (A : ℕ → (ℤ →₀ ℂ))
    {a b : ℝ} (hab : a < b)
    (hvanish : ∀ s ∈ Set.Ioo a b,
       ∑ r ∈ Finset.range (D + 1),
         evalChar (A r) s * (Cc * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (s : ℂ))) ^ r = 0) :
    ∀ r ∈ Finset.range (D + 1), A r = 0 := by
  -- Step 1: Show that the rearranged sum equals the hypothesis sum.
  have h_rearrange : ∀ s ∈ Set.Ioo a b, (∑ x ∈ (Finset.range (D + 1)).sigma (fun r => (A r).support), (A x.1 x.2) * Cc ^ x.1 * Complex.exp (2 * Real.pi * Complex.I * (x.2 - θ * x.1) * s)) = 0 := by
    intro s hs; convert hvanish s hs using 1; simp +decide [ evalChar, mul_pow, ← Complex.exp_nat_mul ] ; ring_nf;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, sub_eq_add_neg, Complex.exp_add ];
    rw [ Finset.sum_sigma' ];
  -- Step 2: Show that the function `lam` is injective on `S`.
  have h_inj : Set.InjOn (fun x : Σ _ : ℕ, ℤ => 2 * Real.pi * Complex.I * ((x.2 : ℂ) - θ * (x.1 : ℂ))) (Finset.sigma (Finset.range (D + 1)) (fun r => (A r).support)) := by
    intros x hx y hy hxy; simp_all +decide [ Complex.ext_iff, Real.pi_ne_zero ] ;
    by_cases h : x.fst = y.fst;
    · aesop;
    · exact False.elim <| hθ.ne_rat ( ( x.snd - y.snd ) / ( x.fst - y.fst ) ) <| by push_cast; rw [ eq_div_iff ( sub_ne_zero_of_ne <| mod_cast h ) ] ; linarith;
  -- Step 3: Apply the lemma `exp_sum_eq_zero_on_interval`.
  have h_apply_lemma : ∀ x ∈ (Finset.range (D + 1)).sigma (fun r => (A r).support), (A x.1 x.2) * Cc ^ x.1 = 0 := by
    convert exp_sum_eq_zero_on_interval _ _ _ h_inj hab _ using 1;
    convert h_rearrange using 1;
  intro r hr; ext k; specialize h_apply_lemma ⟨ r, k ⟩ ; aesop;

end CriticalMixedHRT