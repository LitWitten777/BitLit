import Mathlib
import RequestProject.HRT.ReturnMultiplierLaurent

open Complex
open scoped BigOperators Real

set_option maxHeartbeats 1000000

/-!
# Part A — polynomial-in-`z` representation of the return multiplier

The imported local holonomy certificate consumes the return multiplier as an
*ordinary polynomial in `z`* (after a Laurent shift), namely as

```
    Q(w, z) = a_d(w) z^d + ⋯ + a₀(w),       z^M · L(w, z) = Q(w, z),
```

where `L` is the bivariate Laurent return multiplier.  This module records the
**per-fibre** shift-to-polynomial reduction: for each fixed frequency `s`, the
concrete Laurent polynomial `returnMultiplierLaurent s` (constructed in
`ReturnMultiplierLaurent.lean`) admits a nonnegative integer shift `M` and an
ordinary polynomial `Q : ℂ[X]` such that, on the circle,

```
    B_s(x) · z^M = Q.eval z,        z = circleParam x = e^{2πi x}.
```

This is `return_multiplier_shift_to_polynomial_in_z`.  We also record:

* `evalLaurentCircle_T`, `evalLaurentCircle_toLaurent` — the two evaluation
  bridges between Laurent / ordinary polynomials and circle evaluation;
* `return_multiplier_laurent_ne_zero` — the return multiplier Laurent polynomial
  is nonzero (the underlying `LaurentPolynomial ℂ` is a domain and every factor
  is nonzero), the input needed for a nonzero leading coefficient;
* `return_multiplier_polynomial_in_z_nonzero` and
  `return_multiplier_leading_coefficient_laurent` — the produced polynomial `Q`
  is nonzero and hence has a nonzero leading coefficient (Part B, per-fibre
  form).
-/

namespace CriticalMixedHRT

/-- Circle evaluation of a Laurent monomial `T n` is `z^n` with `z = circleParam t`. -/
theorem evalLaurentCircle_T (n : ℤ) (t : ℝ) :
    evalLaurentCircle (LaurentPolynomial.T n) t = (circleParam t) ^ n := by
  rw [evalLaurentCircle_eq_hom]
  simp only [evalLaurentCircleHom, LaurentPolynomial.eval₂_T, circleParam]
  rw [Units.val_zpow_eq_zpow_val]
  norm_num
  ring_nf

/-- Circle evaluation of the Laurent image of an ordinary polynomial `Q` agrees
with the ordinary evaluation of `Q` at `circleParam t`. -/
theorem evalLaurentCircle_toLaurent (Q : Polynomial ℂ) (t : ℝ) :
    evalLaurentCircle (Polynomial.toLaurent Q) t = Q.eval (circleParam t) := by
  rw [evalLaurentCircle_eq_hom]
  simp only [evalLaurentCircleHom]
  rw [LaurentPolynomial.eval₂_toLaurent]
  have hval : (↑(Units.mk0 (Complex.exp (2 * Real.pi * t * Complex.I))
        (Complex.exp_ne_zero _)) : ℂ) = circleParam t := by
    simp [circleParam]; ring_nf
  rw [hval, Polynomial.eval₂_eq_eval_map]
  simp

namespace NormalizedReturnData

variable (D : NormalizedReturnData)

/-- **Part A — shift-to-polynomial-in-`z` representation of the return multiplier.**

For each fixed frequency `s`, there is a nonnegative integer shift `M` and an
ordinary polynomial `Q : ℂ[X]` (the polynomial-in-`z` form) such that, on the
circle `z = circleParam x = e^{2πi x}`,

```
    B_s(x) · z^M = Q.eval z.
```

Equivalently, `z^M · L(w,z) = Q(w,z)` per fibre, where `L` is the return
multiplier Laurent polynomial.  This is obtained from `LaurentPolynomial`'s
`exists_T_pow` shift together with the circle-evaluation bridges. -/
theorem return_multiplier_shift_to_polynomial_in_z (s : ℝ) :
    ∃ (M : ℕ) (Q : Polynomial ℂ),
      ∀ x : ℝ, D.Bmult x s * (circleParam x) ^ (M : ℕ) = Q.eval (circleParam x) := by
  obtain ⟨n, Q, hQ⟩ := LaurentPolynomial.exists_T_pow (D.returnMultiplierLaurent s)
  refine ⟨n, Q, fun x => ?_⟩
  have h := congrArg (fun L => evalLaurentCircle L x) hQ
  simp only at h
  rw [evalLaurentCircle_toLaurent, evalLaurentCircle_mul, evalLaurentCircle_T,
    D.normalized_return_multiplier_eval_laurent_eq_Bmult s x] at h
  rw [h, zpow_natCast]

/-
The `j`-th translated trinomial factor of the return multiplier is a nonzero
Laurent polynomial.
-/
theorem factorLaurent_ne_zero (s : ℝ) (j : ℕ) : D.factorLaurent s j ≠ 0 := by
  intro h; have := D.factorLaurent_eval s j; simp_all +decide [ Function.Injective, Complex.exp_ne_zero ] ;
  contrapose! this; simp_all +decide [ Pfun ] ;
  by_contra! h_contra; simp_all +decide [ evalLaurentCircle ] ;
  have h_exp_sum_zero : ∀ x : ℝ, D.c₀ + D.c₁ * Complex.exp (-2 * Real.pi * Complex.I * (D.t₁ * x)) * Complex.exp (-2 * Real.pi * Complex.I * (D.t₁ * (-j * D.a) + D.r₁ * (s + j * (D.p / D.m)))) + D.c₂ * Complex.exp (-2 * Real.pi * Complex.I * (D.t₂ * x)) * Complex.exp (-2 * Real.pi * Complex.I * (D.t₂ * (-j * D.a) + D.r₂ * (s + j * (D.p / D.m)))) = 0 := by
    convert fun x => Eq.symm ( h_contra x ) using 2 ; push_cast [ mul_assoc, ← Complex.exp_add ] ; ring;
  have h_exp_sum_zero : ∀ i : ℤ, D.c₀ * (if i = 0 then 1 else 0) + D.c₁ * (if i = D.t₁ then 1 else 0) * Complex.exp (-2 * Real.pi * Complex.I * (D.t₁ * (-j * D.a) + D.r₁ * (s + j * (D.p / D.m)))) + D.c₂ * (if i = D.t₂ then 1 else 0) * Complex.exp (-2 * Real.pi * Complex.I * (D.t₂ * (-j * D.a) + D.r₂ * (s + j * (D.p / D.m)))) = 0 := by
    intro i
    have h_integral : ∫ x in (0 : ℝ)..1, (D.c₀ + D.c₁ * Complex.exp (-2 * Real.pi * Complex.I * (D.t₁ * x)) * Complex.exp (-2 * Real.pi * Complex.I * (D.t₁ * (-j * D.a) + D.r₁ * (s + j * (D.p / D.m)))) + D.c₂ * Complex.exp (-2 * Real.pi * Complex.I * (D.t₂ * x)) * Complex.exp (-2 * Real.pi * Complex.I * (D.t₂ * (-j * D.a) + D.r₂ * (s + j * (D.p / D.m))))) * Complex.exp (2 * Real.pi * Complex.I * i * x) = 0 := by
      simp [h_exp_sum_zero];
      rw [ intervalIntegral.integral_congr fun x hx => by rw [ show ( D.c₀ + D.c₁ * cexp ( - ( 2 * Real.pi * I * ( D.t₁ * x ) ) ) * cexp ( - ( 2 * Real.pi * I * ( - ( D.t₁ * ( j * D.a ) ) + D.r₁ * ( s + j * ( D.p / D.m ) ) ) ) ) + D.c₂ * cexp ( - ( 2 * Real.pi * I * ( D.t₂ * x ) ) ) * cexp ( - ( 2 * Real.pi * I * ( - ( D.t₂ * ( j * D.a ) ) + D.r₂ * ( s + j * ( D.p / D.m ) ) ) ) ) ) = 0 from by simpa using h_exp_sum_zero x ] ] ; norm_num;
    -- Evaluate the integral of each term separately.
    have h_integral_terms : ∀ k : ℤ, ∫ x in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (i - k) * x) = if i = k then 1 else 0 := by
      intro k; split_ifs <;> simp_all +decide [ Complex.exp_ne_zero ] ;
      have := @integral_exp_mul_complex 0 1;
      convert this ( show ( 2 * Real.pi * Complex.I * ( i - k ) : ℂ ) ≠ 0 from mul_ne_zero ( mul_ne_zero ( mul_ne_zero two_ne_zero ( Complex.ofReal_ne_zero.mpr Real.pi_ne_zero ) ) Complex.I_ne_zero ) ( sub_ne_zero.mpr <| by norm_cast ) ) using 1 ; norm_num [ Complex.exp_ne_zero ];
      exact Eq.symm ( div_eq_zero_iff.mpr <| Or.inl <| sub_eq_zero.mpr <| Complex.exp_eq_one_iff.mpr ⟨ i - k, by push_cast; ring ⟩ );
    convert h_integral using 1;
    rw [ intervalIntegral.integral_congr fun x _ => by rw [ add_mul, add_mul ] ];
    rw [ intervalIntegral.integral_add, intervalIntegral.integral_add ] <;> norm_num [ ← Complex.exp_add ] ; ring;
    · congr! 1;
      · convert congr_arg₂ ( · + · ) ( congr_arg ( fun x : ℂ => D.c₀ * x ) ( h_integral_terms 0 ) ) ( congr_arg ( fun x : ℂ => D.c₁ * Complex.exp ( Real.pi * Complex.I * D.t₁ * j * D.a * 2 + ( - ( Real.pi * Complex.I * j * D.r₁ * D.p * ( D.m : ℂ ) ⁻¹ * 2 ) - Real.pi * Complex.I * D.r₁ * s * 2 ) ) * x ) ( h_integral_terms D.t₁ ) ) using 1 ; ring;
        · convert congr_arg₂ ( · + · ) ( congr_arg ( fun x : ℂ => D.c₀ * x ) ( h_integral_terms 0 |> Eq.symm ) ) ( congr_arg ( fun x : ℂ => D.c₁ * x * Complex.exp ( - ( 2 * ( Real.pi * ( I * ( - ( D.t₁ * ( j * D.a ) ) + D.r₁ * ( s + j * ( D.p / D.m ) ) ) ) ) ) ) ) ( h_integral_terms D.t₁ |> Eq.symm ) ) using 1 ; ring;
          · split_ifs <;> ring;
          · norm_num ; ring;
            ac_rfl;
        · congr! 1;
          · convert congr_arg ( fun x : ℂ => D.c₀ * x ) ( h_integral_terms 0 ) using 1 ; ring;
          · convert congr_arg ( fun x : ℂ => D.c₁ * Complex.exp ( Real.pi * Complex.I * D.t₁ * j * D.a * 2 + ( - ( Real.pi * Complex.I * j * D.r₁ * D.p * ( D.m : ℂ ) ⁻¹ * 2 ) - Real.pi * Complex.I * D.r₁ * s * 2 ) ) * x ) ( h_integral_terms D.t₁ ) using 1 ; ring;
            rw [ ← intervalIntegral.integral_const_mul ] ; congr ; ext ; rw [ mul_assoc ] ; rw [ ← Complex.exp_add ] ; ring;
      · convert congr_arg ( fun x : ℂ => D.c₂ * Complex.exp ( Real.pi * Complex.I * j * D.a * D.t₂ * 2 + ( - ( Real.pi * Complex.I * j * D.p * ( D.m : ℂ ) ⁻¹ * D.r₂ * 2 ) - Real.pi * Complex.I * s * D.r₂ * 2 ) ) * x ) ( h_integral_terms D.t₂ ) |> Eq.symm using 1 ; ring;
        · split_ifs <;> ring;
        · norm_num [ mul_assoc, ← Complex.exp_add ] ; ring;
          exact Or.inl ( by rw [ ← intervalIntegral.integral_const_mul ] ; congr; ext; rw [ ← Complex.exp_add ] ; ring );
    · exact Continuous.intervalIntegrable ( by continuity ) _ _;
    · apply_rules [ Continuous.intervalIntegrable ];
      fun_prop (disch := norm_num);
    · apply_rules [ Continuous.intervalIntegrable ];
      fun_prop (disch := norm_num);
    · apply_rules [ Continuous.intervalIntegrable ];
      fun_prop;
  have := h_exp_sum_zero 0; have := h_exp_sum_zero D.t₁; have := h_exp_sum_zero D.t₂; simp_all +decide [ Complex.exp_ne_zero ] ;
  by_cases h : D.t₁ = 0 <;> by_cases h' : D.t₂ = 0 <;> simp_all +decide [ Complex.exp_ne_zero ];
  · have := D.unimodular; simp_all +decide ;
  · norm_num [ ← h_contra ] at *;
    specialize h_exp_sum_zero 0 ; simp_all +decide;
    have := D.factorLaurent_eval s j; simp_all +decide [ Pfun ] ;
    specialize this 0; simp_all +decide [ evalLaurentCircle ] ;
    exact D.hc₂ this;
  · exact absurd ‹D.c₁ = 0› ( D.hc₁ );
  · grind +suggestions

/-
The exponential-monomial prefactor of the return multiplier is nonzero.
-/
theorem monomialLaurent_ne_zero : D.monomialLaurent ≠ 0 := by
  unfold NormalizedReturnData.monomialLaurent;
  simp +decide [ D.hc₃, Complex.exp_ne_zero ];
  exact NeZero.ne (LaurentPolynomial.T D.p)

/-- **Part B (input) — the return multiplier Laurent polynomial is nonzero.**

`returnMultiplierLaurent s` is a product of the nonzero exponential monomial
prefactor and `m` nonzero translated trinomial factors; since `LaurentPolynomial ℂ`
is an integral domain, the product is nonzero. -/
theorem return_multiplier_laurent_ne_zero (s : ℝ) :
    D.returnMultiplierLaurent s ≠ 0 := by
  rw [returnMultiplierLaurent]
  refine mul_ne_zero (D.monomialLaurent_ne_zero) ?_
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j _
  exact D.factorLaurent_ne_zero s j

/-- **Part B (per-fibre) — nonzero polynomial-in-`z` representation.**

The shift-to-polynomial reduction can be taken with a *nonzero* polynomial `Q`:
for each frequency `s` there is a shift `M` and a nonzero `Q : ℂ[X]` with
`B_s(x) · z^M = Q.eval z` on the circle.  Nonvanishing of `Q` follows from
`return_multiplier_laurent_ne_zero` together with injectivity of
`Polynomial.toLaurent` and the fact that `LaurentPolynomial.T` is a unit. -/
theorem return_multiplier_polynomial_in_z_nonzero (s : ℝ) :
    ∃ (M : ℕ) (Q : Polynomial ℂ), Q ≠ 0 ∧
      ∀ x : ℝ, D.Bmult x s * (circleParam x) ^ (M : ℕ) = Q.eval (circleParam x) := by
  obtain ⟨n, Q, hQ⟩ := LaurentPolynomial.exists_T_pow (D.returnMultiplierLaurent s)
  have hQne : Q ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hQ
    rcases mul_eq_zero.mp hQ.symm with h | h
    · exact D.return_multiplier_laurent_ne_zero s h
    · exact (Ne.symm (NeZero.ne' (LaurentPolynomial.T (n : ℤ)))) h
  refine ⟨n, Q, hQne, fun x => ?_⟩
  have h := congrArg (fun L => evalLaurentCircle L x) hQ
  simp only at h
  rw [evalLaurentCircle_toLaurent, evalLaurentCircle_mul, evalLaurentCircle_T,
    D.normalized_return_multiplier_eval_laurent_eq_Bmult s x] at h
  rw [h, zpow_natCast]

/-- **Part B (per-fibre) — nonzero leading coefficient.**

The polynomial-in-`z` representation `Q` of the return multiplier has a nonzero
leading coefficient (it is a nonzero polynomial). -/
theorem return_multiplier_leading_coefficient_laurent (s : ℝ) :
    ∃ (M : ℕ) (Q : Polynomial ℂ), Q.leadingCoeff ≠ 0 ∧
      ∀ x : ℝ, D.Bmult x s * (circleParam x) ^ (M : ℕ) = Q.eval (circleParam x) := by
  obtain ⟨M, Q, hQne, hQ⟩ := D.return_multiplier_polynomial_in_z_nonzero s
  exact ⟨M, Q, Polynomial.leadingCoeff_ne_zero.mpr hQne, hQ⟩

end NormalizedReturnData

end CriticalMixedHRT