module

public import Refinery.CDFlexible
public import Refinery.CDPropertyLoss
public import Refinery.CDLossPersistence
public import Refinery.ZeroDivisorNorm
public import SpookyPrimes.Sedenion.Isotropy

@[expose] public section

/-!
# The Cayley–Dickson ladder and sedenion zero divisors: what the pasted note gets right

Report: `docs/CD_ZERO_DIVISOR_BRAID_CHERN_AUDIT_2026-10-20.md`.

## The property-loss table (correct)

`cd_ladder` collects, in one statement, the facts proved earlier in `Refinery.CDPropertyLoss`,
`Refinery.CDLossPersistence` and `Refinery.ZeroDivisorNorm`. `complex_no_compatible_order` adds the
precise form of "ℂ loses ordering": no linear order on `ℂ` makes it an ordered ring.

`cd_ladder_kept` records what the table leaves out: **every** Cayley–Dickson level, including
the sedenions, is still flexible (`(x y) x = x (y x)`) and satisfies `(x x) x = x (x x)`. So the
descent is not a loss of all structure.

## The zero divisors (partly right, partly wrong)

Here a (left) zero divisor is a nonzero real sedenion `a` with `a b = 0` for some nonzero `b`.

* `isZeroDivisor_smul`: nonzero real multiples of zero divisors are zero divisors, so the zero
  divisors (with `0`) form a **cone**. This part of the note is right.
* `zeroDivisors_not_closed_add`: `e₁ + e₁₀` and `e₁ - e₁₀` are zero divisors, but their sum `2 e₁`
  is not. So the zero divisors do not form a linear subspace.
* `zeroDivisor_mul_not_injective`: multiplying by the zero divisor `e₁ + e₁₀` sends the two
  different inputs `0` and `e₅ + e₁₄` to the same output. A zero divisor therefore **destroys**
  information; it cannot act as a lossless compression map.
-/

namespace QBX.Notes.CDClaims

open SpookyPrimes.Sedenion Refinery.CD Refinery.ZeroDiv

attribute [local instance] cdAddI cdZeroI cdNegI cdSMulI cdACG cdModule

/-! ### The ladder -/

/-- **ℂ cannot be ordered.** There is no linear order on `ℂ` compatible with its ring operations
(squares would be `≥ 0`, but `i² = -1`). -/
theorem complex_no_compatible_order :
    ¬ ∃ (o : LinearOrder ℂ), @IsStrictOrderedRing ℂ _ o.toPartialOrder := by
  rintro ⟨o, ho⟩
  letI := o
  have h1 := mul_self_nonneg Complex.I
  rw [Complex.I_mul_I, neg_nonneg] at h1
  exact absurd h1 (not_le.mpr zero_lt_one)

/-- **The property-loss column of the table is correct.** Over the reals:
level 1 (ℂ) is commutative, level 2 (ℍ) is not but is associative, level 3 (𝕆) is not
associative but is alternative and has no zero divisors, level 4 (𝕊) is not alternative and
has zero divisors; and each loss persists at every higher level. -/
theorem cd_ladder :
    (∀ x y : CD ℝ 1, cdMul 1 x y = cdMul 1 y x) ∧
    (∀ n, 2 ≤ n → ∃ x y : CD ℤ n, cdMul n x y ≠ cdMul n y x) ∧
    (∀ x y z : CD ℝ 2, cdMul 2 (cdMul 2 x y) z = cdMul 2 x (cdMul 2 y z)) ∧
    (∀ n, 3 ≤ n → ∃ x y z : CD ℤ n, cdMul n (cdMul n x y) z ≠ cdMul n x (cdMul n y z)) ∧
    (∀ x y : CD ℝ 3, cdMul 3 (cdMul 3 x x) y = cdMul 3 x (cdMul 3 x y)) ∧
    (∀ x y : CD ℝ 3, x ≠ cdZero 3 → y ≠ cdZero 3 → cdMul 3 x y ≠ cdZero 3) ∧
    (∀ n, 4 ≤ n → ∃ x y : CD ℤ n, cdMul n (cdMul n x x) y ≠ cdMul n x (cdMul n x y)) ∧
    mul (basis 1 + basis 10 : Sed ℤ) (basis 5 + basis 14) = cdZero 4 :=
  ⟨cd1_comm, fun _ hn => not_comm_of_two_le hn, cd2_assoc, fun _ hn => not_assoc_of_three_le hn,
    cd3_alternative, fun _ _ hx hy => octonion_no_zero_divisors hx hy,
    fun _ hn => not_alternative_of_four_le hn, zero_divisor_e1_e10_e5_e14.1⟩

/-- **What is not lost.** At every level `n` of the tower (sedenions `n = 4` included) the
algebra is flexible and third-power associative. -/
theorem cd_ladder_kept (n : ℕ) (x y : CD ℝ n) :
    cdMul n (cdMul n x y) x = cdMul n x (cdMul n y x) ∧
      cdMul n (cdMul n x x) x = cdMul n x (cdMul n x x) :=
  ⟨cdMul_flexible n x y, cdMul_self_mul_comm n x⟩

/-! ### Zero divisors -/

/-- A (left) zero divisor of the real sedenions: `a ≠ 0` and `a b = 0` for some `b ≠ 0`. -/
def IsZeroDivisor (a : Sed ℝ) : Prop := a ≠ 0 ∧ ∃ b : Sed ℝ, b ≠ 0 ∧ mul a b = 0

/-- The zero divisors form a cone: nonzero real multiples of zero divisors are zero divisors. -/
theorem isZeroDivisor_smul {a : Sed ℝ} (ha : IsZeroDivisor a) {c : ℝ} (hc : c ≠ 0) :
    IsZeroDivisor (c • a) := by
  obtain ⟨ha0, b, hb, hab⟩ := ha
  refine ⟨smul_ne_zero hc ha0, b, hb, ?_⟩
  rw [mul, smul_cdMul, ← mul, hab, smul_zero]

theorem isZeroDivisor_e1_add_e10 : IsZeroDivisor (basis 1 + basis 10) := by
  refine ⟨?_, basis 5 + basis 14, ?_, ?_⟩
  · simp [basis, ofFn, Pi.single, Function.update]
  · simp [basis, ofFn, Pi.single, Function.update]
  · simp [mul, cdMul, basis, ofFn, Pi.single, Function.update, cdAdd, cdNeg, cdConj]

theorem isZeroDivisor_e1_sub_e10 : IsZeroDivisor (basis 1 - basis 10) := by
  refine ⟨?_, basis 5 - basis 14, ?_, ?_⟩
  · simp [basis, ofFn, Pi.single, Function.update]
  · simp [basis, ofFn, Pi.single, Function.update]
  · simp [mul, cdMul, basis, ofFn, Pi.single, Function.update, cdAdd, cdNeg, cdConj]

/-- `2 e₁` (the sum of the two zero divisors above) lies in the octonion half, where left
multiplication scales norms, so it is not a zero divisor. -/
theorem not_isZeroDivisor_sum : ¬ IsZeroDivisor ((basis 1 + basis 10) + (basis 1 - basis 10)) := by
  rintro ⟨-, b, hb, hab⟩
  have hsum : ((basis 1 + basis 10) + (basis 1 - basis 10) : Sed ℝ) =
      ((((0, 2), (0, 0)), ((0, 0), (0, 0))), cdZero 3) := by
    simp [basis, ofFn, Pi.single, Function.update, cdZero]; norm_num
  rw [hsum] at hab
  have hb' : normSq b ≠ 0 := fun h => hb ((cdNormSq_eq_zero_iff 4 b).1 h)
  refine mul_oct_ne_zero ((((0 : ℝ), (2 : ℝ)), ((0 : ℝ), (0 : ℝ))),
    (((0 : ℝ), (0 : ℝ)), ((0 : ℝ), (0 : ℝ)))) b ?_ hb' ?_
  · simp [normSq, cdNormSq, cdZero]
  · rw [hab]; exact (cdNormSq_eq_zero_iff 4 _).2 rfl

/-- **The zero divisors are not a linear subspace**: `e₁ + e₁₀` and `e₁ - e₁₀` are zero divisors,
their sum is nonzero, and it is not a zero divisor. -/
theorem zeroDivisors_not_closed_add :
    ∃ a b : Sed ℝ, IsZeroDivisor a ∧ IsZeroDivisor b ∧ a + b ≠ 0 ∧ ¬ IsZeroDivisor (a + b) :=
  ⟨_, _, isZeroDivisor_e1_add_e10, isZeroDivisor_e1_sub_e10,
    by simp [basis, ofFn, Pi.single, Function.update], not_isZeroDivisor_sum⟩

/-- **Multiplication by a zero divisor loses information**: left multiplication by `e₁ + e₁₀`
sends the different inputs `0` and `e₅ + e₁₄` to the same output `0`. -/
theorem zeroDivisor_mul_not_injective :
    ¬ Function.Injective (mul (basis 1 + basis 10 : Sed ℝ)) := by
  intro h
  have h1 : mul (basis 1 + basis 10 : Sed ℝ) (basis 5 + basis 14) =
      mul (basis 1 + basis 10 : Sed ℝ) 0 := by
    rw [mul, mul, cdMul_zero]
    simp [cdMul, basis, ofFn, Pi.single, Function.update, cdAdd, cdNeg, cdConj]
  have := h h1
  simp [basis, ofFn, Pi.single, Function.update] at this

end QBX.Notes.CDClaims
