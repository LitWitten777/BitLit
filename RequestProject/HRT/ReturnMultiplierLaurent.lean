import Mathlib
import RequestProject.HRT.NormalizedReturnCocycle
import RequestProject.JensenHolonomy
import RequestProject.HolonomyCertificate.Full.AlgebraicLaurentCertificateAssembly
import RequestProject.HRT.LocalCertificateAdapter

open scoped Classical BigOperators Real
open Complex

set_option maxHeartbeats 1000000

/-!
# Part A — concrete Laurent-polynomial construction for the return multiplier

For each fixed frequency `s`, the return multiplier `x ↦ B_s(x)` is a genuine
Laurent polynomial in `z = exp(2πi x)`, built from:

* a nowhere-zero exponential monomial `(-c₃⁻¹)^m · const · z^p`
  (`monomialLaurent`), and
* `m` translated trinomial factors `c₀ + α₁ z^{-t₁} + α₂ z^{-t₂}`
  (`factorLaurent`),

assembled by `returnMultiplierLaurent`.  The evaluation map `evalLaurentCircle`
of the merged certificate package is a ring homomorphism (`evalLaurentCircleHom`),
so the per-fibre evaluation of the constructed Laurent polynomial reproduces
`B_s(x)` exactly:

```
    evalLaurentCircle (returnMultiplierLaurent s) x = Bmult x s.
```

This is the concrete object (built through `LaurentPolynomial.C`,
`LaurentPolynomial.T`, sums and finite products) feeding the certificate-package
encoding, as opposed to a mere existence assumption.
-/

namespace CriticalMixedHRT

namespace NormalizedReturnData

variable (D : NormalizedReturnData)

/-- The `j`-th translated trinomial factor of the return multiplier, as a Laurent
polynomial in `z = exp(2πi x)` (the frequency `s` is a fixed parameter folded
into the constant coefficients). -/
noncomputable def factorLaurent (s : ℝ) (j : ℕ) : LaurentPolynomial ℂ :=
  LaurentPolynomial.C D.c₀
    + LaurentPolynomial.C
        (D.c₁ * Complex.exp (-2 * ↑Real.pi * Complex.I *
          ((↑D.t₁ * (-(↑j * ↑D.a)) + ↑D.r₁ * (↑s + ↑j * (↑D.p / ↑D.m))) : ℂ)))
      * LaurentPolynomial.T (-D.t₁)
    + LaurentPolynomial.C
        (D.c₂ * Complex.exp (-2 * ↑Real.pi * Complex.I *
          ((↑D.t₂ * (-(↑j * ↑D.a)) + ↑D.r₂ * (↑s + ↑j * (↑D.p / ↑D.m))) : ℂ)))
      * LaurentPolynomial.T (-D.t₂)

/-- The nowhere-zero exponential-monomial prefactor `(-c₃⁻¹)^m · const · z^p`. -/
noncomputable def monomialLaurent : LaurentPolynomial ℂ :=
  LaurentPolynomial.C
      ((-D.c₃⁻¹) ^ D.m *
        Complex.exp (2 * ↑Real.pi * Complex.I * ((↑D.p / ↑D.m : ℂ)) *
          (∑ j ∈ Finset.range D.m, (-(↑j * ↑D.a) : ℂ))))
    * LaurentPolynomial.T D.p

/-- The concrete Laurent polynomial representing the return multiplier `B_s(·)`. -/
noncomputable def returnMultiplierLaurent (s : ℝ) : LaurentPolynomial ℂ :=
  D.monomialLaurent * ∏ j ∈ Finset.range D.m, D.factorLaurent s j

/-
Evaluation of the `j`-th Laurent factor reproduces the translated trinomial.
-/
theorem factorLaurent_eval (s : ℝ) (j : ℕ) (x : ℝ) :
    evalLaurentCircle (D.factorLaurent s j) x =
      Pfun D.c₀ D.c₁ D.c₂ D.r₁ D.t₁ D.r₂ D.t₂ (x - j * D.a) (s + j * (↑D.p / ↑D.m : ℝ)) := by
  convert evalLaurentCircle_add _ _ _ using 1;
  unfold Pfun; norm_num [ evalLaurentCircle_eq_hom ] ; ring;
  unfold evalLaurentCircleHom; norm_num [ Complex.exp_add, Complex.exp_neg, Complex.exp_int_mul ] ; ring;
  norm_num [ ← Complex.exp_int_mul, ← Complex.exp_neg ] ; ring

/-
Evaluation of the Laurent monomial prefactor reproduces the dossier's
nowhere-zero exponential monomial.
-/
theorem monomialLaurent_eval (x : ℝ) :
    evalLaurentCircle D.monomialLaurent x =
      (-D.c₃⁻¹) ^ D.m *
        Complex.exp (2 * ↑Real.pi * Complex.I * ((↑D.p / ↑D.m : ℂ)) *
          (∑ j ∈ Finset.range D.m, ((↑x - ↑j * ↑D.a : ℂ)))) := by
  unfold NormalizedReturnData.monomialLaurent;
  rw [ evalLaurentCircle_mul, evalLaurentCircle_eq_hom, evalLaurentCircle_eq_hom ];
  simp +decide [ evalLaurentCircleHom, Finset.sum_sub_distrib, mul_sub, sub_mul, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_left_comm, mul_comm, ← Complex.exp_nat_mul, ← Complex.exp_add ];
  rw [ ← Complex.exp_int_mul, ← Complex.exp_add ] ; ring;
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, D.hm.ne' ]

/-
**Part A — `normalized_return_multiplier_eval_laurent_eq_Bmult`.**

The evaluation of the constructed Laurent polynomial reproduces the return
multiplier `B_s(x)` exactly.
-/
theorem normalized_return_multiplier_eval_laurent_eq_Bmult (s x : ℝ) :
    evalLaurentCircle (D.returnMultiplierLaurent s) x = D.Bmult x s := by
  convert evalLaurentCircle_mul _ _ _ using 1;
  convert D.Bmult_eq_explicit x s using 1;
  convert congr_arg₂ ( · * · ) ( D.monomialLaurent_eval x ) ( evalLaurentCircle_eq_hom _ _ ▸ map_prod ( evalLaurentCircleHom x ) _ _ ) using 1;
  exact congrArg _ ( Finset.prod_congr rfl fun _ _ => factorLaurent_eval D s _ x ▸ rfl )

/-- **Part A — `normalized_return_multiplier_laurent_polynomial`.**

For each fixed frequency `s`, the return multiplier `x ↦ B_s(x)` is the
circle-evaluation of a concrete Laurent polynomial (built from `C`, `T`, sums and
finite products). -/
theorem normalized_return_multiplier_laurent_polynomial (s : ℝ) :
    ∃ L : LaurentPolynomial ℂ, ∀ x : ℝ, evalLaurentCircle L x = D.Bmult x s :=
  ⟨D.returnMultiplierLaurent s, fun x => D.normalized_return_multiplier_eval_laurent_eq_Bmult s x⟩

/-- **Part A (project `evalChar` form).**  The same identity stated through the
project's circle-evaluation map `evalChar`, via the
`evalChar_eq_evalLaurentCircle` adapter. -/
theorem normalized_return_multiplier_eval_char_eq_Bmult (s x : ℝ) :
    evalChar (D.returnMultiplierLaurent s) x = D.Bmult x s := by
  rw [evalChar_eq_evalLaurentCircle]
  exact D.normalized_return_multiplier_eval_laurent_eq_Bmult s x

end NormalizedReturnData

end CriticalMixedHRT