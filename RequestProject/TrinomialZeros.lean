import Mathlib

open scoped Classical BigOperators

/-!
# Critical unimodular trinomial: finite torus zero set (Lemma 5.1)

This file formalizes the self-contained core of Lemma 5.1 of the dossier:
on `S¹ × S¹`, a trinomial `c₀ + c₁ z₁ + c₂ z₂` with all coefficients nonzero
has at most two zeros.

The reduction from characters `χ_{λ₁}, χ_{λ₂}` on `𝕋²` (with `λ₁, λ₂` a
`ℤ`-basis) to this `S¹ × S¹` statement is via the torus automorphism
`z ↦ (χ_{λ₁}(z), χ_{λ₂}(z))`; that bookkeeping is recorded separately.

The key algebraic observation (cleaner than the paper's trigonometric
argument): substituting `z₂ = -(c₀+c₁z₁)/c₂` and its conjugate, every solution
`z₁` satisfies
`(c̄₀c₁) z₁² + (|c₀|²+|c₁|²-|c₂|²) z₁ + (c̄₁c₀) = 0`,
a quadratic with nonzero leading coefficient `c̄₀c₁`, hence at most two roots.
-/

namespace CriticalMixedHRT

/-
**Lemma 5.1 (core).** For nonzero `c₀, c₁, c₂`, the trinomial
`c₀ + c₁ z₁ + c₂ z₂` has at most two zeros on the unit torus `S¹ × S¹`.
-/
theorem critical_unimodular_trinomial_zero_set_finite
    (c0 c1 c2 : ℂ) (h0 : c0 ≠ 0) (h1 : c1 ≠ 0) (h2 : c2 ≠ 0) :
    {z : ℂ × ℂ | ‖z.1‖ = 1 ∧ ‖z.2‖ = 1 ∧ c0 + c1 * z.1 + c2 * z.2 = 0}.ncard ≤ 2 := by
  -- By definition of $S$, we know that every element $(z₁, z₂)$ in $S$ satisfies $z₂ = -(c₀ + c₁ z₁) / c₂$.
  set S := {z : ℂ × ℂ | ‖z.1‖ = 1 ∧ ‖z.2‖ = 1 ∧ c0 + c1 * z.1 + c2 * z.2 = 0}
  have hS : ∀ z ∈ S, z.2 = -(c0 + c1 * z.1) / c2 := by
    exact fun z hz => eq_div_of_mul_eq h2 <| by linear_combination hz.2.2;
  -- By definition of $S$, we know that every element $(z₁, z₂)$ in $S$ satisfies $z₁$ being a root of the polynomial $Q(z₁) = (conj c0 * c1) * z₁^2 + (conj c0 * c0 + conj c1 * c1 - conj c2 * c2) * z₁ + (conj c1 * c0)$.
  set Q : Polynomial ℂ := Polynomial.C (starRingEnd ℂ c0 * c1) * Polynomial.X^2 + Polynomial.C (starRingEnd ℂ c0 * c0 + starRingEnd ℂ c1 * c1 - starRingEnd ℂ c2 * c2) * Polynomial.X + Polynomial.C (starRingEnd ℂ c1 * c0)
  have hQ : ∀ z ∈ S, Q.eval z.1 = 0 := by
    intro z hz
    simp [Q];
    have hz1 : z.1 * starRingEnd ℂ z.1 = 1 := by
      simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq, hz.1 ]
    have hz2 : z.2 * starRingEnd ℂ z.2 = 1 := by
      simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq, hz.2.1 ]
    have hz3 : c0 + c1 * z.1 + c2 * z.2 = 0 := by
      exact hz.2.2
    have hz4 : starRingEnd ℂ c0 + starRingEnd ℂ c1 * starRingEnd ℂ z.1 + starRingEnd ℂ c2 * starRingEnd ℂ z.2 = 0 := by
      simpa using congr_arg Star.star hz3;
    grind;
  -- Since $Q$ is a polynomial of degree at most 2, it has at most 2 roots.
  have hQ_roots : (Set.image Prod.fst S).ncard ≤ 2 := by
    have hQ_roots : (Set.image Prod.fst S).ncard ≤ Q.roots.toFinset.card := by
      rw [ ← Set.ncard_coe_finset ];
      apply Set.ncard_le_ncard;
      · simp +zetaDelta at *;
        intro z hz; specialize hQ z.1 z.2 hz.1 hz.2.1 hz.2.2; simp_all +decide [ Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C ] ;
        exact ne_of_apply_ne ( fun p => p.coeff 2 ) ( by norm_num [ Polynomial.coeff_C, Polynomial.coeff_X, mul_assoc, h0, h1, h2 ] );
      · exact Finset.finite_toSet _;
    refine le_trans hQ_roots <| le_trans ( Multiset.toFinset_card_le _ ) <| le_trans ( Polynomial.card_roots' _ ) ?_;
    rw [ Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero ] ; norm_num;
    rintro ( _ | _ | _ | m ) <;> simp +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt, Q ];
  rwa [ Set.InjOn.ncard_image fun x hx y hy hxy => Prod.ext hxy <| by rw [ hS x hx, hS y hy, hxy ] ] at hQ_roots

end CriticalMixedHRT