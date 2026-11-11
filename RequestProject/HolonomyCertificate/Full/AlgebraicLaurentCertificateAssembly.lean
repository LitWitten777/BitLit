import Mathlib
import RequestProject.HolonomyCertificate.Full.LaurentSetup
import RequestProject.HolonomyCertificate.Full.LaurentDenominatorFull
import RequestProject.HolonomyCertificate.Full.TrueSubsetProductDescentToLaurent

/-!
# Algebraic Laurent Certificate Assembly
-/

open scoped BigOperators
open Polynomial Finset

set_option maxHeartbeats 800000

noncomputable section

/-! ## Part 1: evalLaurentCircle as a ring homomorphism -/

def evalLaurentCircleHom (t : ℝ) : LaurentPolynomial ℂ →+* ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ)
    (Units.mk0 (Complex.exp (2 * Real.pi * t * Complex.I))
      (Complex.exp_ne_zero _))

theorem evalLaurentCircle_eq_hom (f : LaurentPolynomial ℂ) (t : ℝ) :
    evalLaurentCircle f t = evalLaurentCircleHom t f := rfl

theorem evalLaurentCircle_mul (f g : LaurentPolynomial ℂ) (t : ℝ) :
    evalLaurentCircle (f * g) t = evalLaurentCircle f t * evalLaurentCircle g t :=
  map_mul (evalLaurentCircleHom t) f g

theorem evalLaurentCircle_pow (f : LaurentPolynomial ℂ) (n : ℕ) (t : ℝ) :
    evalLaurentCircle (f ^ n) t = (evalLaurentCircle f t) ^ n :=
  map_pow (evalLaurentCircleHom t) f n

theorem evalLaurentCircle_add (f g : LaurentPolynomial ℂ) (t : ℝ) :
    evalLaurentCircle (f + g) t = evalLaurentCircle f t + evalLaurentCircle g t :=
  map_add (evalLaurentCircleHom t) f g

theorem evalLaurentCircle_zero (t : ℝ) :
    evalLaurentCircle 0 t = 0 :=
  map_zero (evalLaurentCircleHom t)

theorem evalLaurentCircle_one (t : ℝ) :
    evalLaurentCircle 1 t = 1 :=
  map_one (evalLaurentCircleHom t)

/-! ## Part 2: A nonzero Laurent polynomial has a nonzero evaluation -/

theorem exp_two_pi_image_infinite {a b : ℝ} (hab : a < b) :
    Set.Infinite ((fun (t : ℝ) => Complex.exp (2 * ↑Real.pi * ↑t * Complex.I)) '' Set.Ioo a b) := by
  have h_exp_inj : ∀ t₁ t₂ : ℝ, a < t₁ → t₁ < t₂ → t₂ < t₁ + 1 / 2 → Complex.exp (2 * Real.pi * t₁ * Complex.I) ≠ Complex.exp (2 * Real.pi * t₂ * Complex.I) := by
    intro t₁ t₂ ht₁ ht₂ ht₃; rw [ Ne.eq_def, Complex.exp_eq_exp_iff_exists_int ] ; rintro ⟨ k, hk ⟩ ; rcases k with ⟨ _ | k ⟩ <;> norm_num [ Complex.ext_iff ] at hk <;> nlinarith [ Real.pi_pos ] ;
  by_cases h : b ≤ a + 1 / 2;
  · refine' Set.Infinite.image _ ( Set.Ioo_infinite hab );
    exact fun x hx y hy hxy => le_antisymm ( le_of_not_gt fun hxy' => h_exp_inj _ _ hy.1 hxy' ( by linarith [ hx.1, hx.2, hy.1, hy.2 ] ) hxy.symm ) ( le_of_not_gt fun hxy' => h_exp_inj _ _ hx.1 hxy' ( by linarith [ hx.1, hx.2, hy.1, hy.2 ] ) hxy );
  · refine' Set.Infinite.mono _ ( Set.Ioo_infinite ( show a < a + 1 / 2 by linarith ) |> Set.Infinite.image fun x => _ );
    exact Set.image_subset_iff.mpr fun x hx => Set.mem_image_of_mem _ ⟨ hx.1, by linarith [ hx.2 ] ⟩;
    exact fun hx y hy hxy => le_antisymm ( le_of_not_gt fun hxy' => h_exp_inj _ _ hy.1 hxy' ( by linarith [ hx.1, hx.2, hy.1, hy.2 ] ) hxy.symm ) ( le_of_not_gt fun hxy' => h_exp_inj _ _ hx.1 hxy' ( by linarith [ hx.1, hx.2, hy.1, hy.2 ] ) hxy )

theorem evalLaurentCircle_ne_zero_exists
    (f : LaurentPolynomial ℂ) (hf : f ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, evalLaurentCircle f t ≠ 0 := by
  contrapose! hf with h;
  -- By definition of $f$, we can write it as $f = g * T^{-n}$ for some polynomial $g$ and integer $n$.
  obtain ⟨g, n, hg⟩ : ∃ g : Polynomial ℂ, ∃ n : ℕ, f = g.toLaurent * LaurentPolynomial.T (-n : ℤ) := by
    have h_decomp : ∀ f : LaurentPolynomial ℂ, ∃ g : Polynomial ℂ, ∃ n : ℕ, f = g.toLaurent * LaurentPolynomial.T (-n : ℤ) := by
      intro f;
      induction' f using LaurentPolynomial.induction_on with n f g hf hg;
      · exact ⟨ Polynomial.C n, 0, by simp +decide ⟩;
      · obtain ⟨ g₁, n₁, rfl ⟩ := hf
        obtain ⟨ g₂, n₂, rfl ⟩ := hg
        use g₁ * Polynomial.X ^ n₂ + g₂ * Polynomial.X ^ n₁, n₁ + n₂
        simp [mul_add, add_mul, pow_add];
      · rename_i k c hc;
        refine' ⟨ Polynomial.C c * Polynomial.X ^ ( k + 1 ), 0, _ ⟩ ; simp +decide [ mul_assoc, ← LaurentPolynomial.T_add ];
      · rename_i k hk;
        refine' ⟨ Polynomial.C k, ‹ℕ› + 1, _ ⟩ ; simp +decide [ sub_eq_add_neg, add_assoc ];
        exact Or.inl ( by rw [ add_comm ] );
    exact h_decomp f;
  -- Since $g$ is a polynomial and $g.eval(exp(2πit)) = 0$ for all $t \in (a, b)$, it follows that $g$ has infinitely many roots.
  have h_inf_roots : Set.Infinite {z : ℂ | g.eval z = 0} := by
    have h_g_zero : ∀ t ∈ Set.Ioo a b, g.eval (Complex.exp (2 * Real.pi * t * Complex.I)) = 0 := by
      intro t ht; specialize h t ht; simp_all +decide [ evalLaurentCircle ] ;
    have h_g_zero_poly : Set.Infinite (Set.image (fun t : ℝ => Complex.exp (2 * Real.pi * t * Complex.I)) (Set.Ioo a b)) := by
      exact?;
    exact h_g_zero_poly.mono <| Set.image_subset_iff.mpr h_g_zero;
  exact Classical.not_not.1 fun h => h_inf_roots <| Set.Finite.subset ( g.roots.toFinset.finite_toSet ) <| by aesop_cat;

/-! ## Part 3: Continuity of evalLaurentCircle -/

theorem evalLaurentCircle_continuous (f : LaurentPolynomial ℂ) :
    Continuous (evalLaurentCircle f) := by
  -- By definition of $f$, we can write it as a finite sum of terms of the form $c_i T^i$.
  obtain ⟨n, c, hc⟩ : ∃ n : ℤ, ∃ c : ℤ → ℂ, f = ∑ i ∈ Finset.Icc (-n) n, c i • (LaurentPolynomial.T i) := by
    obtain ⟨s, hs⟩ : ∃ s : Finset ℤ, f = ∑ i ∈ s, f i • LaurentPolynomial.T i := by
      use f.support;
      convert f.sum_single;
      · exact?;
      · convert f.sum_single;
        exact Finset.sum_congr rfl fun _ _ => by simp +decide [ Algebra.smul_def ] ;
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ∀ i ∈ s, -n ≤ i ∧ i ≤ n := by
      exact ⟨ ∑ i ∈ s, |i|, fun i hi => ⟨ by cases abs_cases i <;> linarith [ Finset.single_le_sum ( fun x _ => abs_nonneg x ) hi ], by cases abs_cases i <;> linarith [ Finset.single_le_sum ( fun x _ => abs_nonneg x ) hi ] ⟩ ⟩;
    refine' ⟨ n, fun i => if i ∈ s then f i else 0, _ ⟩;
    convert hs using 1;
    rw [ ← Finset.sum_subset ( show s ⊆ Finset.Icc ( -n ) n from fun i hi => Finset.mem_Icc.mpr ( hn i hi ) ) ] <;> simp +contextual [ Finset.sum_ite ];
  -- Substitute the expression for $f$ into the evaluation.
  have h_eval : ∀ t : ℝ, evalLaurentCircle f t = ∑ i ∈ Finset.Icc (-n) n, c i * (Complex.exp (2 * Real.pi * t * Complex.I)) ^ i := by
    intro t
    simp [hc, evalLaurentCircle];
    refine' Finset.sum_congr rfl fun i hi => _;
    erw [ Algebra.smul_def ] ; aesop;
  rw [ show evalLaurentCircle f = _ from funext h_eval ];
  fun_prop (disch := norm_num)

/-! ## Part 4: Arc shrinking -/

theorem arc_shrink_avoid_zeros
    {a b : ℝ} (hab : a < b)
    (f : LaurentPolynomial ℂ) (hf : f ≠ 0) :
    ∃ a' b' : ℝ, a < a' ∧ a' < b' ∧ b' < b ∧
      ∀ t ∈ Set.Ioo a' b', evalLaurentCircle f t ≠ 0 := by
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ ∈ Set.Ioo a b, evalLaurentCircle f t₀ ≠ 0 := evalLaurentCircle_ne_zero_exists f hf hab;
  obtain ⟨ ε, hε, hε' ⟩ := Metric.mem_nhds_iff.mp ( IsOpen.mem_nhds ( isOpen_compl_singleton.preimage ( show Continuous fun t => evalLaurentCircle f t from evalLaurentCircle_continuous f ) ) ht₀.2 );
  simp +zetaDelta at *;
  exact ⟨ t₀, ht₀.1.1, t₀ + Min.min ( b - t₀ ) ε / 2, by linarith [ lt_min ( sub_pos.mpr ht₀.1.2 ) hε ], by linarith [ min_le_left ( b - t₀ ) ε, min_le_right ( b - t₀ ) ε ], fun t ht₁ ht₂ => hε' <| Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ min_le_left ( b - t₀ ) ε, min_le_right ( b - t₀ ) ε ], by linarith [ min_le_left ( b - t₀ ) ε, min_le_right ( b - t₀ ) ε ] ⟩ ⟩

/-! ## Part 5: Subset-product polynomial properties -/

theorem subsetProductPolyR_natDegree (d m : ℕ) (ad : ℂ) (r : Fin d → ℂ) :
    (subsetProductPolyR d m ad r).natDegree = Nat.choose d m := by
  erw [ Polynomial.natDegree_prod ];
  · erw [ Finset.sum_congr rfl fun _ _ => Polynomial.natDegree_X_sub_C _ ] ; simp +decide [ Finset.card_univ ];
  · exact fun i hi => Polynomial.X_sub_C_ne_zero _

theorem subsetProductPolyR_isRoot (d m : ℕ) (ad : ℂ) (r : Fin d → ℂ)
    (E : Finset (Fin d)) (hE : E.card = m) :
    Polynomial.IsRoot (subsetProductPolyR d m ad r) (ad * ∏ i ∈ E, (-r i)) := by
  unfold subsetProductPolyR;
  simp +decide [ Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero ];
  exact ⟨ E, hE, Or.inl rfl ⟩

theorem poly_eval_eq_sum_fin {R : Type*} [CommSemiring R] (p : Polynomial R) (x : R)
    (B : ℕ) (hB : p.natDegree ≤ B) :
    p.eval x = ∑ n : Fin (B + 1), p.coeff n * x ^ (n : ℕ) := by
  rw [ Polynomial.eval_eq_sum_range' ];
  rw [ Finset.sum_range, Fin.sum_univ_castSucc ];
  linarith

/-! ## Part 6: evalLaurentCircle commutes with MvPolynomial.eval₂ -/

theorem evalLaurentCircle_mvpoly_eval₂
    {d : ℕ} (a : Fin d → LaurentPolynomial ℂ)
    (G : MvPolynomial (Fin d) ℤ) (t : ℝ) :
    evalLaurentCircle (MvPolynomial.eval₂ (Int.castRingHom (LaurentPolynomial ℂ)) a G) t =
    MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => evalLaurentCircle (a i) t) G := by
  unfold evalLaurentCircle;
  simp +decide [ MvPolynomial.eval₂_eq' ]

/-! ## Part 7: Helpers for the leading coefficient and the algebraic relation -/

theorem monic_leading_coeff_eq_one {R : Type*} [CommRing R] {p : Polynomial R}
    (hp : p.Monic) (B : ℕ) (hB : p.natDegree = B) :
    p.coeff B = 1 := by
  rw [← hB]; exact hp.coeff_natDegree

theorem descent_coeff_identity
    (d m : ℕ)
    (N_fn : ℕ → ℕ) (G_fn : ℕ → MvPolynomial (Fin (d + 1)) ℤ)
    (h_desc : ∀ n : ℕ,
      ∀ (ad_K : ℂ) (had_K : ad_K ≠ 0)
      (a_K : Fin (d + 1) → ℂ) (r_K : Fin d → ℂ)
      (hfactor : Polynomial.C ad_K * ∏ i : Fin d,
        (Polynomial.X - Polynomial.C (r_K i))
        = ∑ j : Fin (d + 1),
          Polynomial.C (a_K j) * Polynomial.X ^ (j : ℕ)),
      ad_K ^ N_fn n * (subsetProductPolyR d m ad_K r_K).coeff n =
        MvPolynomial.eval₂ (Int.castRingHom ℂ) a_K (G_fn n))
    (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (N_max : ℕ)
    (h_ge : ∀ n : ℕ, n ≤ Nat.choose d m → N_fn n ≤ N_max)
    (t : ℝ)
    (had_t : evalLaurentCircle ad t ≠ 0)
    (r : Fin d → ℂ)
    (hfact : Polynomial.C (evalLaurentCircle ad t) *
      ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) =
      ∑ j : Fin (d + 1),
        Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ))
    (n : ℕ) (hn : n ≤ Nat.choose d m) :
    evalLaurentCircle
      (ad ^ (N_max - N_fn n) *
        MvPolynomial.eval₂ (Int.castRingHom (LaurentPolynomial ℂ)) coeffs (G_fn n)) t =
    (evalLaurentCircle ad t) ^ N_max *
      (subsetProductPolyR d m (evalLaurentCircle ad t) r).coeff n := by
  -- Specialize h_desc at K = ℂ
  have h_spec : (evalLaurentCircle ad t) ^ N_fn n *
    (subsetProductPolyR d m (evalLaurentCircle ad t) r).coeff n =
    MvPolynomial.eval₂ (Int.castRingHom ℂ)
      (fun j => evalLaurentCircle (coeffs j) t) (G_fn n) :=
    h_desc n (evalLaurentCircle ad t) had_t
      (fun j => evalLaurentCircle (coeffs j) t) r hfact
  -- LHS: distribute evalLaurentCircle over multiplication and power
  rw [evalLaurentCircle_mul, evalLaurentCircle_pow, evalLaurentCircle_mvpoly_eval₂]
  -- By h_spec, the eval₂ part = (evalLaurentCircle ad t)^(N_fn n) * coeff n
  rw [← h_spec, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (h_ge n hn)]

theorem algebraic_sum_eq_zero
    {B : ℕ}
    (D_val : ℂ)
    (_coeffs_val : Fin (B + 1) → ℂ)
    (A_val : Fin (B + 1) → ℂ)
    (J_val : ℂ)
    (p : Polynomial ℂ)
    (hp_deg : p.natDegree ≤ B)
    (hp_root : p.IsRoot J_val)
    (h_A : ∀ n : Fin (B + 1), A_val n = D_val * p.coeff n) :
    ∑ n : Fin (B + 1), A_val n * J_val ^ (n : ℕ) = 0 := by
  have := poly_eval_eq_sum_fin p J_val ( B ) hp_deg; simp_all +decide [ Polynomial.eval_eq_sum_range ] ;
  simp +decide [ mul_assoc, ← Finset.mul_sum _ _ _, ← this ]

/-! ## Part 8: Main assembly theorem -/

theorem algebraic_laurent_certificate_from_jensen_identity
    {a b : ℝ}
    (hab : a < b)
    (d m : ℕ)
    (ad : LaurentPolynomial ℂ)
    (had : ad ≠ 0)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (_h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (J : ℝ → ℂ)
    (h_factor :
      ∀ t ∈ Set.Ioo a b,
      evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin d → ℂ,
      ∃ E : Finset (Fin d),
        E.card = m ∧
        Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin d,
            (Polynomial.X - Polynomial.C (r i))
        =
        ∑ j : Fin (d + 1),
          Polynomial.C (evalLaurentCircle (coeffs j) t) *
            Polynomial.X ^ (j : ℕ)
        ∧
        J t =
          evalLaurentCircle ad t *
          ∏ i ∈ E, (-r i)) :
    ∃ a' b' : ℝ,
      a < a' ∧ a' < b' ∧ b' < b ∧
      ∃ N : ℕ,
      ∃ A : Fin (N + 1) → LaurentPolynomial ℂ,
        (∃ n : Fin (N + 1), A n ≠ 0) ∧
        ∀ t ∈ Set.Ioo a' b',
          ∑ n : Fin (N + 1),
            evalLaurentCircle (A n) t * (J t) ^ (n : ℕ) = 0 := by
  obtain ⟨a', b', ha', hb', hab'⟩ : ∃ a' b', a < a' ∧ a' < b' ∧ b' < b ∧ ∀ t ∈ Set.Ioo a' b', evalLaurentCircle ad t ≠ 0 := by
    exact?;
  -- Get N_fn and G_fn from universal_coeff_descent, specialized to ℂ
  have h_ucd := @universal_coeff_descent
  set N_fn : ℕ → ℕ := fun n => Classical.choose (h_ucd d m n)
  set G_fn : ℕ → MvPolynomial (Fin (d + 1)) ℤ := fun n => Classical.choose (Classical.choose_spec (h_ucd d m n))
  have h_desc : ∀ n : ℕ, ∀ (ad_K : ℂ) (had_K : ad_K ≠ 0)
    (a_K : Fin (d + 1) → ℂ) (r_K : Fin d → ℂ)
    (hfactor : Polynomial.C ad_K * ∏ i : Fin d, (Polynomial.X - Polynomial.C (r_K i)) =
      ∑ j : Fin (d + 1), Polynomial.C (a_K j) * Polynomial.X ^ (j : ℕ)),
    ad_K ^ N_fn n * (subsetProductPolyR d m ad_K r_K).coeff n =
      MvPolynomial.eval₂ (Int.castRingHom ℂ) a_K (G_fn n) := by
    intro n; exact Classical.choose_spec (Classical.choose_spec (h_ucd d m n))
  obtain ⟨N_max, hN_max⟩ : ∃ N_max : ℕ, ∀ n : ℕ, n ≤ Nat.choose d m → N_fn n ≤ N_max := by
    exact ⟨ Finset.sup ( Finset.range ( Nat.choose d m + 1 ) ) N_fn, fun n hn => Finset.le_sup ( f := N_fn ) ( Finset.mem_range_succ_iff.mpr hn ) ⟩;
  -- Define A n as ad^(N_max - N_fn n) * MvPolynomial.eval₂ coeffs (G_fn n).
  set A : Fin (Nat.choose d m + 1) → LaurentPolynomial ℂ := fun n => ad ^ (N_max - N_fn n) * MvPolynomial.eval₂ (Int.castRingHom (LaurentPolynomial ℂ)) coeffs (G_fn n);
  refine' ⟨ a', b', ha', hb', hab'.1, _, A, _, _ ⟩;
  · refine' ⟨ ⟨ Nat.choose d m, Nat.lt_succ_self _ ⟩, _ ⟩;
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ ∈ Set.Ioo a' b', evalLaurentCircle ad t₀ ≠ 0 := by
      exact ⟨ ( a' + b' ) / 2, ⟨ by linarith, by linarith ⟩, hab'.2 _ ⟨ by linarith, by linarith ⟩ ⟩;
    obtain ⟨ r, E, hE₁, hE₂, hE₃ ⟩ := h_factor t₀ ⟨ by linarith [ ht₀.1.1 ], by linarith [ ht₀.1.2 ] ⟩ ht₀.2;
    have h_eval : evalLaurentCircle (A ⟨Nat.choose d m, Nat.lt_succ_self _⟩) t₀ = (evalLaurentCircle ad t₀) ^ N_max * (subsetProductPolyR d m (evalLaurentCircle ad t₀) r).coeff (Nat.choose d m) := by
      convert descent_coeff_identity d m N_fn G_fn h_desc ad coeffs N_max hN_max t₀ ht₀.2 r hE₂ ( Nat.choose d m ) ( Nat.le_refl _ ) using 1;
    have h_coeff : (subsetProductPolyR d m (evalLaurentCircle ad t₀) r).coeff (Nat.choose d m) = 1 := by
      grind +suggestions;
    intro h; simp_all +decide [ evalLaurentCircle ] ;
  · intro t ht
    obtain ⟨r, E, hE_card, hE_factor, hE_J⟩ := h_factor t ⟨by linarith [ht.1], by linarith [ht.2]⟩ (hab'.2 t ht);
    convert algebraic_sum_eq_zero ( evalLaurentCircle ad t ^ N_max ) ( fun n => ( subsetProductPolyR d m ( evalLaurentCircle ad t ) r |> Polynomial.coeff ) n ) ( fun n => evalLaurentCircle ( A n ) t ) ( J t ) ( subsetProductPolyR d m ( evalLaurentCircle ad t ) r ) _ _ _ using 1;
    · rw [ subsetProductPolyR_natDegree ];
    · exact hE_J.symm ▸ subsetProductPolyR_isRoot d m _ _ _ hE_card;
    · intro n;
      convert descent_coeff_identity d m N_fn G_fn h_desc ad coeffs N_max hN_max t ( hab'.2 t ht ) r hE_factor n ( Fin.is_le n ) using 1

end