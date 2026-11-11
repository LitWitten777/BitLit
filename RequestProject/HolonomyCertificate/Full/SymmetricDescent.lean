import Mathlib

/-!
# Symmetric polynomial descent helpers

Helper lemmas for expressing symmetric polynomials via elementary symmetric
polynomials using `MvPolynomial.esymmAlgHom_fin_bijective`.
-/

open scoped BigOperators
open MvPolynomial Finset Polynomial

set_option maxHeartbeats 1600000

noncomputable section

/-
The evaluation of `MvPolynomial.esymm (Fin d) ℤ k` at a root family `r`
    equals the multiset esymm of the roots.
-/
theorem eval₂_esymm_eq_multiset_esymm {K : Type*} [CommRing K] {d : ℕ}
    (r : Fin d → K) (k : ℕ) :
    MvPolynomial.eval₂ (Int.castRingHom K) r (MvPolynomial.esymm (Fin d) ℤ k) =
      Multiset.esymm ((Finset.univ : Finset (Fin d)).val.map r) k := by
  unfold Multiset.esymm;
  unfold esymm; simp +decide [ Finset.univ, Multiset.powersetCard_one ] ;
  simp +decide [ Fintype.elems, Finset.powersetCard ];
  -- Since the powersetCard k of a list is just the list of all k-element subsets, and mapping r over each subset is the same as mapping r over the entire list and then taking the powersetCard k, the two multisets are equal.
  have h_eq : Multiset.powersetCard k (Multiset.map r (Multiset.ofList (List.finRange d))) = Multiset.map (fun s => Multiset.map r s) (Multiset.powersetCard k (Multiset.ofList (List.finRange d))) := by
    grind +suggestions;
  convert congr_arg Multiset.sum ( congr_arg ( Multiset.map fun s => Multiset.prod s ) h_eq.symm ) using 1;
  simp +decide [ Multiset.map_pmap ];
  rw [ Multiset.pmap_eq_map ]

/-
Core fundamental theorem of symmetric polynomials:
    any symmetric polynomial in `MvPolynomial (Fin d) ℤ` can be expressed
    as a polynomial in the elementary symmetric polynomials.
-/
theorem symmetric_eval_descends {d : ℕ}
    (P : MvPolynomial (Fin d) ℤ) (hP : P.IsSymmetric) :
    ∃ G : MvPolynomial (Fin d) ℤ,
      ∀ {K : Type*} [CommRing K] (r : Fin d → K),
        MvPolynomial.eval₂ (Int.castRingHom K) r P =
          MvPolynomial.eval₂ (Int.castRingHom K)
            (fun i : Fin d =>
              Multiset.esymm ((Finset.univ : Finset (Fin d)).val.map r) ((i : ℕ) + 1))
            G := by
  obtain ⟨G, hG⟩ : ∃ G : MvPolynomial (Fin d) ℤ, P = MvPolynomial.aeval (fun i => MvPolynomial.esymm (Fin d) ℤ (i.val + 1)) G := by
    have := @MvPolynomial.esymmAlgHom_fin_bijective ℤ;
    obtain ⟨G, hG⟩ : ∃ G : MvPolynomial (Fin d) ℤ, MvPolynomial.aeval (fun i => MvPolynomial.esymm (Fin d) ℤ (i.val + 1)) G = P := by
      obtain ⟨ G, hG ⟩ := this d |>.2 ⟨ P, hP ⟩;
      replace hG := congr_arg Subtype.val hG; simp_all +decide [ esymmAlgHom_apply ] ;
      use G;
    exact ⟨ G, hG.symm ⟩;
  use G;
  intro K _ r; rw [ hG ] ; simp +decide [ MvPolynomial.aeval_def, MvPolynomial.eval₂_comp ] ;
  -- By definition of bind₁, we can rewrite the left-hand side as the evaluation of G at the esymm values.
  have h_bind₁ : ∀ (p : MvPolynomial (Fin d) ℤ), MvPolynomial.eval₂ (Int.castRingHom K) r (bind₁ (fun i => esymm (Fin d) ℤ (i.val + 1)) p) = MvPolynomial.eval₂ (Int.castRingHom K) (fun i => Multiset.esymm ((Finset.univ : Finset (Fin d)).val.map r) (i.val + 1)) p := by
    intro p; induction p using MvPolynomial.induction_on <;> simp_all +decide [ MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X ] ;
    · erw [ MvPolynomial.eval₂_C, MvPolynomial.eval₂_C ];
    · simp +decide [ eval₂_esymm_eq_multiset_esymm ];
  convert h_bind₁ G using 1;
  simp +decide [ List.ofFn_eq_map ]

/-
The coefficient of `universalSubsetProdPoly` at index `n`, when specialized,
    gives the coefficient of `subsetProductPolyR`. This follows from
    `universalSubsetProdPoly_spec`.
-/
theorem universalSubsetProdPoly_coeff_spec_eval {K : Type*} [CommRing K]
    (d m n : ℕ) (ad : K) (r : Fin d → K) :
    MvPolynomial.eval₂ (Int.castRingHom K) (Fin.cons ad r)
      ((∏ I ∈ (Finset.univ : Finset (Fin d)).powersetCard m,
        (Polynomial.X - Polynomial.C
          (MvPolynomial.X (0 : Fin (d + 1)) *
            ∏ i ∈ I, (-(MvPolynomial.X (Fin.succ i) :
              MvPolynomial (Fin (d + 1)) ℤ))))).coeff n) =
    (∏ I ∈ (Finset.univ : Finset (Fin d)).powersetCard m,
      (Polynomial.X - Polynomial.C (ad * ∏ i ∈ I, (-r i)))).coeff n := by
  -- Apply the congruence theorem for coefficients to relate the coefficients of the evaluated polynomial to the coefficients of the original polynomial.
  have h_coeff_congr : ∀ (P : Polynomial (MvPolynomial (Fin (d + 1)) ℤ)), Polynomial.coeff (Polynomial.map (MvPolynomial.eval₂Hom (Int.castRingHom K) (Fin.cons ad r)) P) n = MvPolynomial.eval₂ (Int.castRingHom K) (Fin.cons ad r) (Polynomial.coeff P n) := by
    aesop;
  convert h_coeff_congr _ |> Eq.symm using 1;
  simp +decide [ Polynomial.map_prod ]

/-
Parametric symmetric descent:
    If P ∈ MvPolynomial (Fin (d+1)) ℤ is symmetric in root variables
    (invariant under permutations fixing variable 0), then
    ∃ F such that eval₂ (specializeRoots) P = eval₂ (esymmAssignment) F.

Helper: eval₂(Fin.cons ad r) P = eval ad (map (eval₂Hom r) ((finSuccEquiv) P))
-/
lemma eval₂_finSuccEquiv_eq {d : ℕ} {K : Type*} [CommRing K]
    (P : MvPolynomial (Fin (d + 1)) ℤ) (ad : K) (r : Fin d → K) :
    MvPolynomial.eval₂ (Int.castRingHom K) (Fin.cons ad r) P =
    Polynomial.eval ad (Polynomial.map (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
      (MvPolynomial.finSuccEquiv ℤ d P)) := by
  induction' P using MvPolynomial.induction_on' with P Q hP hQ;
  · simp +decide [ MvPolynomial.monomial_eq, Finsupp.prod_add_index', Polynomial.map_prod ];
    simp +decide [ Polynomial.eval_prod, MvPolynomial.finSuccEquiv_apply ];
    simp +decide [ Fin.prod_univ_succ, MvPolynomial.eval₂_C ];
    erw [ MvPolynomial.eval₂_C ] ; aesop;
  · aesop

theorem parametric_symmetric_descent {d : ℕ}
    (P : MvPolynomial (Fin (d + 1)) ℤ)
    (hsymm : ∀ (sigma : Equiv.Perm (Fin d)) (K : Type) [Field K] (ad : K) (r : Fin d → K),
      MvPolynomial.eval₂ (Int.castRingHom K) (Fin.cons ad r) P =
        MvPolynomial.eval₂ (Int.castRingHom K) (Fin.cons ad (r ∘ sigma)) P) :
    ∃ F : MvPolynomial (Fin (d + 1)) ℤ,
      ∀ {K : Type*} [Field K] (ad : K) (r : Fin d → K),
        MvPolynomial.eval₂ (Int.castRingHom K) (Fin.cons ad r) P =
          MvPolynomial.eval₂ (Int.castRingHom K)
            (fun j : Fin (d + 1) =>
              if (j : ℕ) = 0 then ad
              else Multiset.esymm ((Finset.univ : Finset (Fin d)).val.map r) (j : ℕ))
            F := by
  -- By definition of $P$, we know that it is symmetric in the last $d$ variables.
  have h_symm : ∀ (sigma : Equiv.Perm (Fin d)) (K : Type) [Field K] (ad : K) (r : Fin d → K), Polynomial.map (MvPolynomial.eval₂Hom (Int.castRingHom K) r) (MvPolynomial.finSuccEquiv ℤ d P) = Polynomial.map (MvPolynomial.eval₂Hom (Int.castRingHom K) (r ∘ sigma)) (MvPolynomial.finSuccEquiv ℤ d P) := by
    intros sigma K _ ad r
    have h_eval : Polynomial.eval ad (Polynomial.map (MvPolynomial.eval₂Hom (Int.castRingHom K) r) (MvPolynomial.finSuccEquiv ℤ d P)) = Polynomial.eval ad (Polynomial.map (MvPolynomial.eval₂Hom (Int.castRingHom K) (r ∘ sigma)) (MvPolynomial.finSuccEquiv ℤ d P)) := by
      convert hsymm sigma K ad r using 1 <;> simp +decide [ eval₂_finSuccEquiv_eq ];
    refine' Polynomial.map_injective ( algebraMap K ( AlgebraicClosure K ) ) ( algebraMap K ( AlgebraicClosure K ) ).injective _;
    refine' Polynomial.eq_of_infinite_eval_eq _ _ _;
    refine' Set.infinite_univ.mono fun x _ => _;
    have := hsymm sigma ( AlgebraicClosure K ) x ( fun i => algebraMap K ( AlgebraicClosure K ) ( r i ) ) ; simp_all +decide [ Polynomial.map_map ] ;
    convert this using 1;
    · convert eval₂_finSuccEquiv_eq P x ( fun i => algebraMap K ( AlgebraicClosure K ) ( r i ) ) |> Eq.symm using 1;
    · convert eval₂_finSuccEquiv_eq P x ( fun i => algebraMap K ( AlgebraicClosure K ) ( r ( sigma i ) ) ) |> Eq.symm using 1;
  -- By definition of $P$, we know that each coefficient of $P$ is a symmetric polynomial in the last $d$ variables.
  have h_coeff_symm : ∀ k : ℕ, (MvPolynomial.finSuccEquiv ℤ d P).coeff k ∈ {p : MvPolynomial (Fin d) ℤ | p.IsSymmetric} := by
    intro k
    have h_coeff_symm : ∀ (sigma : Equiv.Perm (Fin d)) (K : Type) [Field K] (r : Fin d → K), MvPolynomial.eval₂ (Int.castRingHom K) r ((MvPolynomial.finSuccEquiv ℤ d P).coeff k) = MvPolynomial.eval₂ (Int.castRingHom K) (r ∘ sigma) ((MvPolynomial.finSuccEquiv ℤ d P).coeff k) := by
      intro sigma K _ r; specialize h_symm sigma K 0 r; replace h_symm := congr_arg ( fun p => p.coeff k ) h_symm; aesop;
    intro sigma;
    refine' MvPolynomial.funext fun x => _;
    convert h_coeff_symm sigma ℚ ( fun i => x i ) |> Eq.symm using 1;
    simp +decide [ MvPolynomial.eval₂_eq', MvPolynomial.eval_rename ];
    simp +decide [ MvPolynomial.eval_eq', Finset.prod_apply ];
    norm_cast;
  choose! G hG using fun k => symmetric_eval_descends ( ( MvPolynomial.finSuccEquiv ℤ d P |> Polynomial.coeff ) k ) ( h_coeff_symm k );
  refine' ⟨ ∑ k ∈ ( MvPolynomial.finSuccEquiv ℤ d P |> Polynomial.support ), MvPolynomial.rename ( Fin.succ ) ( G k ) * MvPolynomial.X 0 ^ k, fun { K } _ ad r => _ ⟩;
  convert eval₂_finSuccEquiv_eq P ad r using 1;
  simp +decide [ Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C, hG ];
  rw [ Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def ];
  refine' Finset.sum_congr rfl fun k hk => _;
  simp +decide [ MvPolynomial.eval₂_rename, hG ];
  convert Or.inl ( Eq.symm ( hG k r ) ) using 1;
  simp +decide [ Function.comp, Multiset.esymm ];
  congr! 2

/-
Denominator clearing for eval₂ with assignment (ad, v₁/ad, ..., v_d/ad).
-/
theorem clear_denom_eval₂ (d : ℕ) (F : MvPolynomial (Fin (d + 1)) ℤ) :
    ∃ (N : ℕ) (G : MvPolynomial (Fin (d + 1)) ℤ),
      ∀ {K : Type*} [Field K] (ad : K) (had : ad ≠ 0) (v : Fin d → K),
        ad ^ N * MvPolynomial.eval₂ (Int.castRingHom K)
          (Fin.cons ad (fun j => v j / ad)) F =
        MvPolynomial.eval₂ (Int.castRingHom K) (Fin.snoc v ad) G := by
  induction' F using MvPolynomial.induction_on with c G H hG hH;
  · refine' ⟨ 0, MvPolynomial.C c, _ ⟩;
    simp +decide;
    intro K _ ad had v; erw [ MvPolynomial.eval₂_C, MvPolynomial.eval₂_C ] ;
  · obtain ⟨ N₁, G₁, hG₁ ⟩ := hG
    obtain ⟨ N₂, G₂, hH₂ ⟩ := hH
    use max N₁ N₂, G₁ * MvPolynomial.X (Fin.last d) ^ (max N₁ N₂ - N₁) + G₂ * MvPolynomial.X (Fin.last d) ^ (max N₁ N₂ - N₂);
    intro K _ ad had v; simp +decide [ ← hG₁ ad had v, ← hH₂ ad had v, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, pow_add ] ;
    simp +decide [ ← mul_assoc, ← pow_add, add_tsub_cancel_of_le ( le_max_left N₁ N₂ ), add_tsub_cancel_of_le ( le_max_right N₁ N₂ ) ];
  · rename_i k hk;
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨ k, rfl ⟩;
    · obtain ⟨ N, G, hG ⟩ := hk;
      refine' ⟨ N, G * MvPolynomial.X ( Fin.last d ), fun { K } _ ad had v => _ ⟩ ; simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm ];
    · obtain ⟨ N, G, hG ⟩ := hk;
      refine' ⟨ N + 1, G * MvPolynomial.X ( Fin.castSucc k ), fun { K } _ ad had v => _ ⟩ ; simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm, Fin.snoc ];
      rw [ ← mul_assoc, mul_div_cancel₀ _ had ]

end