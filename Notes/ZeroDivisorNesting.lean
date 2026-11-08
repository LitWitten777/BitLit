module

public import QBX.Notes.CayleyDicksonClaims

@[expose] public section

/-!
# Nesting zero divisors

Report: `docs/ZERO_DIVISOR_USAGE_AUDIT_2026-10-20.md` (section "What happens if we nest them?").

Three precise readings of "nesting" a zero divisor, each checked here over `ℝ`.

1. **Nesting the algebra** (Cayley–Dickson doubling `CD ℝ n ⊂ CD ℝ (n+1)`, `a ↦ (a, 0)`).
   The inclusion is multiplicative (`cdMul_embed`), so a zero-divisor pair at one level stays a
   zero-divisor pair at every higher level (`isZDPair_embed`, `isZDPair_embed_iter`). Since the
   sedenions (level 4) contain the pair `e₁ + e₁₀`, `e₅ + e₁₄`, **every** level `m ≥ 4` has zero
   divisors (`zeroDivisors_every_level`). Nesting never removes zero divisors; it only adds more.
2. **Nesting a zero divisor in itself** (`x ↦ x · x`). Every Cayley–Dickson algebra satisfies
   `x x = t(x) x - N(x)`. For a pure imaginary `x` (trace `0`) this is the real scalar `-N(x)`,
   which is non-zero when `x ≠ 0` (`cdMul_self_of_trace_zero`, `cdMul_self_ne_zero_of_trace_zero`).
   So a pure imaginary zero divisor never annihilates itself: squaring it gives a non-zero real
   number, which is invertible. Example: `(e₁ + e₁₀)² = -2` (`sq_e1_add_e10`).
3. **Nesting the annihilation** (zero divisor times zero divisor). The product of two zero divisors
   need not be a zero divisor: `(e₁ + e₁₀)(e₁ + e₁₀) = -2` is not one (`zd_mul_zd_not_zd`).
-/

namespace QBX.Notes.ZDNesting

open SpookyPrimes.Sedenion Refinery.CD Refinery.ZeroDiv QBX.Notes.CDClaims

attribute [local instance] cdAddI cdZeroI cdNegI cdSMulI cdACG cdModule

/-- `a, b` is a zero-divisor pair at level `n`: both non-zero, with product zero. -/
def IsZDPair (n : ℕ) (a b : CD ℝ n) : Prop := a ≠ cdZero n ∧ b ≠ cdZero n ∧ cdMul n a b = cdZero n

/-- The inclusion of level `n` into level `n + 1` as the first half, `a ↦ (a, 0)`. -/
def embed (n : ℕ) (a : CD ℝ n) : CD ℝ (n + 1) := (a, cdZero n)

/-- **The Cayley–Dickson inclusion is multiplicative**: `(a, 0)(b, 0) = (a b, 0)`. -/
theorem cdMul_embed (n : ℕ) (a b : CD ℝ n) :
    cdMul (n + 1) (embed n a) (embed n b) = embed n (cdMul n a b) := by
  refine Prod.ext ?_ ?_
  · show cdAdd n (cdMul n a b) (cdNeg n (cdMul n (cdConj n (cdZero n)) (cdZero n))) = cdMul n a b
    rw [cdConj_zero, cdZero_eq, cdMul_zero, ← cdZero_eq, cdNeg_zero, cdAdd_zero]
  · show cdAdd n (cdMul n (cdZero n) a) (cdMul n (cdZero n) (cdConj n b)) = cdZero n
    rw [cdZero_eq, zero_cdMul, zero_cdMul, cdAdd_eq, add_zero]

/-- **A zero-divisor pair survives one doubling.** -/
theorem isZDPair_embed {n : ℕ} {a b : CD ℝ n} (h : IsZDPair n a b) :
    IsZDPair (n + 1) (embed n a) (embed n b) := by
  obtain ⟨ha, hb, hab⟩ := h
  refine ⟨fun h' => ha (congrArg Prod.fst h'), fun h' => hb (congrArg Prod.fst h'), ?_⟩
  rw [cdMul_embed, hab]
  rfl

/-- **A zero-divisor pair survives any number of doublings.** -/
theorem isZDPair_embed_iter {n : ℕ} {a b : CD ℝ n} (h : IsZDPair n a b) :
    ∀ k, ∃ a' b' : CD ℝ (n + k), IsZDPair (n + k) a' b'
  | 0 => ⟨a, b, h⟩
  | k + 1 => by
    obtain ⟨a', b', h'⟩ := isZDPair_embed_iter h k
    exact ⟨_, _, isZDPair_embed h'⟩

/-- The sedenion pair `e₁ + e₁₀`, `e₅ + e₁₄`. -/
theorem isZDPair_sedenion : IsZDPair 4 (basis 1 + basis 10) (basis 5 + basis 14) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [basis, ofFn, Pi.single, Function.update, cdZero]
  · simp [basis, ofFn, Pi.single, Function.update, cdZero]
  · simp [cdMul, basis, ofFn, Pi.single, Function.update, cdAdd, cdNeg, cdConj, cdZero]

/-- **Every Cayley–Dickson level from the sedenions on has zero divisors.** -/
theorem zeroDivisors_every_level (m : ℕ) (hm : 4 ≤ m) : ∃ a b : CD ℝ m, IsZDPair m a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact isZDPair_embed_iter isZDPair_sedenion k

/-- `cdScalar r n = 0` only for `r = 0`. -/
theorem cdScalar_eq_zero_iff : ∀ (n : ℕ) (r : ℝ), cdScalar r n = cdZero n ↔ r = 0
  | 0, r => by simp [cdScalar, cdZero]
  | n + 1, r => by
    constructor
    · intro h
      exact (cdScalar_eq_zero_iff n r).1 (congrArg Prod.fst h)
    · rintro rfl
      exact Prod.ext ((cdScalar_eq_zero_iff n 0).2 rfl) rfl

/-- **Squaring a pure imaginary element gives a real number**: if `t(x) = 0` then
`x x = -N(x) · 1`. -/
theorem cdMul_self_of_trace_zero (n : ℕ) (x : CD ℝ n) (ht : cdTrace n x = 0) :
    cdMul n x x = -cdScalar (cdNormSq n x) n := by
  rw [cdMul_self, ht, zero_smul, zero_sub]

/-- **A non-zero pure imaginary element never annihilates itself** (at any level). -/
theorem cdMul_self_ne_zero_of_trace_zero (n : ℕ) (x : CD ℝ n) (hx : x ≠ cdZero n)
    (ht : cdTrace n x = 0) : cdMul n x x ≠ cdZero n := by
  rw [cdMul_self_of_trace_zero n x ht]
  intro h
  have h' : cdScalar (cdNormSq n x) n = cdZero n := by
    rw [cdZero_eq] at h ⊢
    exact neg_eq_zero.mp h
  exact hx ((cdNormSq_eq_zero_iff n x).1 ((cdScalar_eq_zero_iff n _).1 h'))

/-- `(e₁ + e₁₀)² = -2`. -/
theorem sq_e1_add_e10 :
    mul (basis 1 + basis 10 : Sed ℝ) (basis 1 + basis 10) = -cdScalar 2 4 := by
  simp [mul, cdMul, basis, ofFn, Pi.single, Function.update, cdAdd, cdNeg, cdConj, cdScalar,
    cdZero]
  norm_num

/-- **A product of zero divisors need not be a zero divisor**: `e₁ + e₁₀` is a zero divisor, but
its square `-2` is not. -/
theorem zd_mul_zd_not_zd :
    IsZeroDivisor (basis 1 + basis 10) ∧
      ¬ IsZeroDivisor (mul (basis 1 + basis 10 : Sed ℝ) (basis 1 + basis 10)) := by
  refine ⟨isZeroDivisor_e1_add_e10, ?_⟩
  rintro ⟨-, b, hb, hab⟩
  rw [sq_e1_add_e10] at hab
  have h2 : mul (-cdScalar (2 : ℝ) 4) b = (-2 : ℝ) • b := by
    rw [mul, neg_cdMul, (cdMul_scalar_and_scalar_mul 4 (2 : ℝ)).2, neg_smul]
  rw [h2] at hab
  exact hb ((smul_eq_zero.mp hab).resolve_left (by norm_num))

end QBX.Notes.ZDNesting
