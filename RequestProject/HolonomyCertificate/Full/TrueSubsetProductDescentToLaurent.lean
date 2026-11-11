import Mathlib
import RequestProject.HolonomyCertificate.Full.LaurentSetup
import RequestProject.HolonomyCertificate.Full.LaurentDenominatorFull
import RequestProject.HolonomyCertificate.Full.SymmetricDescent

/-!
# True Subset-Product Descent to Laurent-Localized Coefficients
-/

open scoped BigOperators
open Polynomial Finset

set_option maxHeartbeats 800000

noncomputable section

/-! ## Part 1: The true universal subset-product polynomial -/

/-- The subset-product polynomial over an arbitrary commutative ring. -/
def subsetProductPolyR {R : Type*} [CommRing R] (d m : ℕ) (ad : R) (r : Fin d → R) :
    Polynomial R :=
  ∏ I ∈ (Finset.univ : Finset (Fin d)).powersetCard m,
    (Polynomial.X - Polynomial.C (ad * ∏ i ∈ I, (-r i)))

theorem true_subsetProduct_univ_monic {R : Type*} [CommRing R] (d m : ℕ) (ad : R)
    (r : Fin d → R) :
    (subsetProductPolyR d m ad r).Monic := by
  convert Polynomial.monic_prod_of_monic _ _ fun I hI => Polynomial.monic_X_sub_C ( ad * ∏ i ∈ I, -r i ) using 1

theorem true_subsetProduct_perm_invariant {R : Type*} [CommRing R] (d m : ℕ) (ad : R)
    (r : Fin d → R) (sigma : Equiv.Perm (Fin d)) :
    subsetProductPolyR d m ad (r ∘ sigma) = subsetProductPolyR d m ad r := by
  apply Finset.prod_bij (fun I _ => Finset.image sigma I);
  · simp +contextual [ Finset.mem_powersetCard, Finset.card_image_of_injective _ sigma.injective ];
  · simp +contextual [ Finset.ext_iff ];
    intro a₁ ha₁ a₂ ha₂ h a; specialize h ( sigma a ) ; aesop;
  · intro b hb;
    refine' ⟨ Finset.image sigma.symm b, _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injective, Equiv.injective ];
    simp +decide [ Finset.image_image ];
  · simp +decide [ Finset.prod_image, Equiv.injective ]

theorem true_subsetProduct_univ_coeff_symmetric {R : Type*} [CommRing R] (d m n : ℕ)
    (ad : R) (r : Fin d → R) (sigma : Equiv.Perm (Fin d)) :
    (subsetProductPolyR d m ad (r ∘ sigma)).coeff n =
    (subsetProductPolyR d m ad r).coeff n := by
  rw [true_subsetProduct_perm_invariant]

/-! ## Part 2: Universal symmetric descent -/

def universalSubsetProdPoly (d m : ℕ) :
    Polynomial (MvPolynomial (Fin (d + 1)) ℤ) :=
  ∏ I ∈ (Finset.univ : Finset (Fin d)).powersetCard m,
    (Polynomial.X - Polynomial.C
      (MvPolynomial.X (0 : Fin (d + 1)) *
        ∏ i ∈ I, (-(MvPolynomial.X (Fin.succ i) :
          MvPolynomial (Fin (d + 1)) ℤ))))

def specializeRoots {K : Type*} [CommRing K] (d : ℕ) (ad : K) (r : Fin d → K) :
    Fin (d + 1) → K :=
  Fin.cons ad r

theorem universalSubsetProdPoly_spec {K : Type*} [CommRing K] (d m : ℕ) (ad : K)
    (r : Fin d → K) :
    Polynomial.map (MvPolynomial.eval₂Hom (Int.castRingHom K) (specializeRoots d ad r))
      (universalSubsetProdPoly d m) =
    subsetProductPolyR d m ad r := by
  unfold universalSubsetProdPoly subsetProductPolyR;
  simp +decide [ Polynomial.map_prod, specializeRoots ]

def esymmValue {K : Type*} [CommRing K] {d : ℕ} (r : Fin d → K) (k : ℕ) : K :=
  Multiset.esymm ((Finset.univ : Finset (Fin d)).val.map r) k

def esymmAssignment {K : Type*} [CommRing K] {d : ℕ} (ad : K) (r : Fin d → K) :
    Fin (d + 1) → K :=
  fun j => if (j : ℕ) = 0 then ad else esymmValue r (j : ℕ)

theorem true_subsetProduct_coeff_descends_to_esymm
    (d m n : ℕ) :
    ∃ F : MvPolynomial (Fin (d + 1)) ℤ,
      ∀ {K : Type*} [Field K]
        (ad : K) (r : Fin d → K),
        (subsetProductPolyR d m ad r).coeff n =
          MvPolynomial.eval₂ (Int.castRingHom K) (esymmAssignment ad r) F := by
  -- By the parametric symmetric descent theorem, there exists a polynomial F such that the coefficient of the subset-product polynomial can be expressed as a polynomial in the elementary symmetric polynomials.
  obtain ⟨F, hF⟩ := parametric_symmetric_descent (MvPolynomial.X 0 ^ 0 * (Polynomial.coeff (universalSubsetProdPoly d m) n)) (by
  intros sigma K _ ad r; have := universalSubsetProdPoly_coeff_spec_eval d m n ad r; have := universalSubsetProdPoly_coeff_spec_eval d m n ad ( r ∘ sigma ) ; simp_all +decide [ Finset.prod_mul_distrib, Finset.prod_pow ] ;
  have h_perm : Finset.image (fun I => Finset.image sigma I) (Finset.powersetCard m (Finset.univ : Finset (Fin d))) = Finset.powersetCard m (Finset.univ : Finset (Fin d)) := by
    ext; simp [Finset.mem_image];
    constructor <;> intro h;
    · obtain ⟨ a, ha, rfl ⟩ := h; rw [ Finset.card_image_of_injective _ sigma.injective, ha ] ;
    · exact ⟨ Finset.image sigma.symm ‹_›, by rw [ Finset.card_image_of_injective _ sigma.symm.injective, h ], by rw [ Finset.image_image ] ; aesop ⟩;
  have h_perm : ∏ I ∈ Finset.powersetCard m (Finset.univ : Finset (Fin d)), (Polynomial.X - Polynomial.C (ad * ∏ i ∈ I, (-r (sigma i)))) = ∏ I ∈ Finset.powersetCard m (Finset.univ : Finset (Fin d)), (Polynomial.X - Polynomial.C (ad * ∏ i ∈ I, (-r i))) := by
    conv_rhs => rw [ ← h_perm, Finset.prod_image ( Finset.card_image_iff.mp <| by aesop ) ] ;
    exact Finset.prod_congr rfl fun x hx => by rw [ Finset.prod_image ( by simp +decide [ sigma.injective.eq_iff ] ) ] ;
  unfold universalSubsetProdPoly; aesop;);
  use F; intro K _ ad r; convert @hF K _ ad r using 1;
  convert universalSubsetProdPoly_coeff_spec_eval d m n ad r |> Eq.symm using 1;
  unfold universalSubsetProdPoly; simp +decide [ Fin.prod_univ_succ ] ;

/-! ## Part 3: Vieta specialization -/

theorem true_vieta_elementarySymmetricValue
    {K : Type*} [Field K]
    {d : ℕ}
    (ad : K) (had : ad ≠ 0)
    (a : Fin (d + 1) → K)
    (r : Fin d → K)
    (hfactor :
      Polynomial.C ad * ∏ i : Fin d,
        (Polynomial.X - Polynomial.C (r i))
      =
      ∑ j : Fin (d + 1),
        Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) :
    ∀ k : ℕ, k ≤ d →
      esymmValue r k = (-1) ^ k * a ⟨d - k, by omega⟩ / ad := by
  intro k hk;
  -- By comparing coefficients of $X^{d-k}$ on both sides of the equation $C(ad) * \prod (X - C(r_i)) = \sum C(a_j) * X^j$, we get $ad * (-1)^k * esymm(r, k) = a_{d-k}$.
  have h_coeff : Polynomial.coeff (∏ i, (Polynomial.X - Polynomial.C (r i))) (d - k) = (-1)^k * esymmValue r k := by
    convert Multiset.prod_X_sub_C_coeff ( Finset.univ.val.map r ) _ using 1;
    rotate_left;
    rotate_left;
    exact d - k;
    · simp +decide [ Finset.card_univ ];
    · simp +decide [ Finset.prod ];
      rfl;
    · simp +decide [ esymmValue, hk ];
      rw [ Nat.sub_sub_self hk ];
  replace hfactor := congr_arg ( fun p => Polynomial.coeff p ( d - k ) ) hfactor ; simp_all +decide [ Polynomial.coeff_C_mul ];
  rw [ eq_div_iff had ];
  convert congr_arg ( fun x => x * ( -1 ) ^ k ) hfactor using 1 <;> ring;
  · norm_num [ pow_mul' ];
  · rw [ Finset.sum_eq_single ⟨ d - k, Nat.lt_succ_of_le ( Nat.sub_le _ _ ) ⟩ ] <;> aesop

/-! ## Part 4: Descent to coefficients localized at ad -/

theorem universal_coeff_descent (d m n : ℕ) :
    ∃ (N : ℕ) (G : MvPolynomial (Fin (d + 1)) ℤ),
      ∀ {K : Type*} [Field K]
        (ad : K) (had : ad ≠ 0)
        (a : Fin (d + 1) → K) (r : Fin d → K)
        (hfactor :
          Polynomial.C ad * ∏ i : Fin d,
            (Polynomial.X - Polynomial.C (r i))
          = ∑ j : Fin (d + 1),
            Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)),
        ad ^ N * (subsetProductPolyR d m ad r).coeff n =
          MvPolynomial.eval₂ (Int.castRingHom K) a G := by
  have := @true_subsetProduct_coeff_descends_to_esymm;
  obtain ⟨ F, hF ⟩ := this d m n;
  obtain ⟨ N₀, G₀, hG₀ ⟩ := @clear_denom_eval₂ d F;
  refine' ⟨ N₀, MvPolynomial.bind₁ ( fun j => if h : j.val < d then MvPolynomial.C ( ( -1 ) ^ ( j.val + 1 ) ) * MvPolynomial.X ( Fin.castSucc ⟨ d - ( j.val + 1 ), by omega ⟩ ) else MvPolynomial.X ( Fin.last d ) ) G₀, _ ⟩;
  intro K _ ad had a r hfactor
  rw [hF ad r];
  convert hG₀ ad had ( fun j => ( -1 ) ^ ( j.val + 1 ) * a ⟨ d - ( j.val + 1 ), by omega ⟩ ) using 1;
  · congr! 2;
    ext j; induction j using Fin.inductionOn <;> simp +decide [ *, esymmAssignment ] ;
    rename_i i hi;
    convert true_vieta_elementarySymmetricValue ad had a r hfactor ( i + 1 ) ( by linarith [ Fin.is_lt i ] ) using 1;
  · have h_bind₁ : ∀ (p : MvPolynomial (Fin (d + 1)) ℤ), MvPolynomial.eval₂ (Int.castRingHom K) a (MvPolynomial.bind₁ (fun j => if h : j.val < d then MvPolynomial.C ((-1 : ℤ) ^ (j.val + 1)) * MvPolynomial.X (Fin.castSucc ⟨d - (j.val + 1), by omega⟩) else MvPolynomial.X (Fin.last d)) p) = MvPolynomial.eval₂ (Int.castRingHom K) (Fin.snoc (fun j => (-1 : K) ^ (j.val + 1) * a ⟨d - (j.val + 1), by omega⟩) ad) p := by
      intro p
      induction' p using MvPolynomial.induction_on with p q hp hq;
      · simp +decide [ MvPolynomial.eval₂_C ];
        erw [ MvPolynomial.eval₂_C, MvPolynomial.eval₂_C ];
      · simp +decide [ *, MvPolynomial.eval₂_add ];
        congr! 1;
        · convert hq using 1;
          congr! 2;
          ext; simp +decide [ MvPolynomial.bind₁_X_right ] ;
        · convert ‹_› using 1;
          congr! 2;
          ext; simp +decide [ MvPolynomial.bind₁_X_right ] ;
      · rename_i k hk;
        by_cases hk : k.val < d <;> simp +decide [ hk, Fin.snoc ];
        · aesop;
        · replace hfactor := congr_arg ( fun p => Polynomial.coeff p ( d : ℕ ) ) hfactor ; simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
          rw [ Finset.sum_eq_single ( Fin.last d ) ] at hfactor <;> simp_all +decide [ Fin.ext_iff ];
          · rw [ ← hfactor, Finset.prod_congr rfl fun _ _ => sub_eq_add_neg _ _ ];
            erw [ Finset.prod_congr rfl fun _ _ => by rw [ ← Polynomial.C_neg ] ];
            erw [ Finset.prod_X_add_C_coeff ] ; aesop;
            simp +decide [ Finset.card_univ ];
          · exact fun i hi₁ hi₂ => False.elim <| hi₁ <| hi₂.symm;
    exact h_bind₁ G₀

end