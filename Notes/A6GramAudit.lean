module

public import QBX.Notes.A6Doubling

@[expose] public section

/-!
# Gram-matrix audit of the 21 positive roots of `A₆`, and other checkable claims

Follow-up to `QBX.Notes.A6Doubling`. A pasted analysis proposed comparing the probe's 21 vectors
with the positive roots of `A₆` through their `21 × 21` Gram matrix, and it gave reference
values for that matrix. This file computes the reference values exactly. Several of the pasted
values are wrong; the correct ones are below. Report: `docs/A6_GRAM_AUDIT_2026-10-20.md`.

**The Gram matrix `G` of the 21 positive roots `e_i - e_j` (`i < j`) of `A₆`:**

* `gram_entries`, `gram_diag`, `gram_eq_two_iff`: the entries are `-1, 0, 1, 2`, with `2` exactly
  on the diagonal (no two positive roots are antipodal).
* `gram_counts`: off the diagonal there are **140** entries `+1`, **210** entries `0` and **70**
  entries `-1` (not 105 / 210 / 105 as claimed).
* `row_06`: rows are **not** uniform: the row of `e₀ - e₆` (the highest root) has ten `+1` and
  no `-1` (not "5 / 10 / 5 per row").
* `gram_sum`: all entries add up to `112 = |2ρ|²`, where `2ρ = (6, 4, 2, 0, -2, -4, -6)`.
* `gram_sq`: **`G² = 7 G`**, so `G / 7` is a projection. Hence (`eigen_zero_or_seven`) every
  eigenvalue is `0` or `7`; `gramQ_trace`, `gramQ_rank`, `gramQ_nullity`: trace `42`, rank `6`,
  nullity `15`. The spectrum is **`7` (six times) and `0` (fifteen times)**, not
  `{7, 3.5 ×5, 0 ×15}` (that list has trace `24.5 ≠ 42`).

**Mean angles are not a root-system test.**
* `gram_counts` gives the mean off-diagonal angle of the 21 positive roots as
  `(140·60° + 210·90° + 70·120°)/420 = 85°`, which lies outside the 60/90/120° values although
  the vectors are an honest `A₆` half-system.
* `allRoots_counts`, `allRoots_gram_sum`: for all 42 roots the inner products are symmetric
  (`420` at `±1`, `42` at `-2`), so the mean cosine is `0`; the mean angle, counting the 21
  antipodal pairs, is `92.2°`. Neither number says anything about being a root system.

**General facts used to judge the other claims.**
* `crystallographic_angle`: if `2⟨a,b⟩/⟨a,a⟩` and `2⟨a,b⟩/⟨b,b⟩` are integers `m, n`, then
  `m n = 4 cos² θ ∈ {0, 1, 2, 3, 4}`. Any two roots of a crystallographic root system meet at
  `90°, 60°, 120°, 45°, 135°, 30°, 150°` (or `0°, 180°`). A set with other angles is not a
  crystallographic root system. Testing this needs all pairwise angles, not their mean.
* `reflection_norm`: a reflection `v ↦ v - 2⟨v,a⟩/⟨a,a⟩ a` preserves the norm *exactly*, in
  every real inner-product space (no Monte-Carlo pass rate is needed).
* `reflections_generate_S7`: the 21 transpositions (the positive-root reflections, by
  `A6Doubling.refl_aroot`) generate `S₇`.
* `det_one_isUnit`: a matrix with determinant `1` is invertible, so "det = 1 (singular)" is a
  contradiction in terms.
* `golay23_perfect`, `golay24_not_perfect`, `no_perfect_length24`: the sphere-packing equality
  `2¹² · Σ_{k≤3} C(n,k) = 2ⁿ` holds for the binary Golay code of length **23**, not for the extended
  `[24, 12, 8]` code. Indeed **no** binary code of length 24 is perfect for any radius `1 … 23`.
-/

namespace QBX.Notes.A6GramAudit

open QBX.Notes.A6Doubling

/-- Index set of the 21 positive roots `e_i - e_j`, `i < j`, of `A₆`. -/
abbrev PosIdx := {p : Fin 7 × Fin 7 // p.1 < p.2}

/-- There are 21 positive roots. -/
theorem card_posIdx : Fintype.card PosIdx = 21 := by decide

/-- Closed form of the inner product of two `A`-type roots. -/
def gramF (p q : Fin 7 × Fin 7) : ℤ :=
  ((if q.1 = p.1 then 1 else 0) - (if q.1 = p.2 then 1 else 0)) -
    ((if q.2 = p.1 then 1 else 0) - (if q.2 = p.2 then 1 else 0))

/-- The closed form agrees with the inner product. -/
theorem ip_aroot_aroot (p q : Fin 7 × Fin 7) :
    ip (aroot p.1 p.2) (aroot q.1 q.2) = gramF p q := by
  rw [ip_aroot, aroot_apply, aroot_apply]; rfl

/-- The `21 × 21` Gram matrix of the positive roots. -/
def gram : Matrix PosIdx PosIdx ℤ := Matrix.of fun p q => gramF p.1 q.1

/-- `gram` is the Gram matrix of the positive roots. -/
theorem gram_apply (p q : PosIdx) :
    gram p q = ip (aroot p.1.1 p.1.2) (aroot q.1.1 q.1.2) := by
  rw [ip_aroot_aroot]; rfl

/-- **`G² = 7 G`.** -/
theorem gram_sq : gram * gram = 7 • gram := by
  decide +kernel


/-- Gram entries lie in `{-1, 0, 1, 2}`. -/
theorem gram_entries : ∀ p q : PosIdx, gram p q = -1 ∨ gram p q = 0 ∨ gram p q = 1 ∨ gram p q = 2 := by
  decide +kernel

/-- Diagonal entries are `2` (roots have length² 2). -/
theorem gram_diag : ∀ p : PosIdx, gram p p = 2 := by decide +kernel

/-- `2` occurs only on the diagonal; `-2` never occurs (no antipodal pairs). -/
theorem gram_eq_two_iff : ∀ p q : PosIdx, gram p q = 2 ↔ p = q := by decide +kernel

/-- Number of entries of `G` equal to `c`. -/
def countVal (c : ℤ) : ℕ := (Finset.univ.filter fun pq : PosIdx × PosIdx => gram pq.1 pq.2 = c).card

/-- **Entry counts of `G`:** 21 twos, 140 ones, 210 zeros, 70 minus-ones, no `-2`. -/
theorem gram_counts : countVal 2 = 21 ∧ countVal 1 = 140 ∧ countVal 0 = 210 ∧ countVal (-1) = 70 ∧
    countVal (-2) = 0 := by
  decide +kernel

/-- The mean off-diagonal angle of the positive roots, from `gram_counts`, is `85°`. -/
theorem mean_angle_85 : (140 * 60 + 210 * 90 + 70 * 120 : ℕ) = 85 * (140 + 210 + 70) := by norm_num

/-- Number of entries equal to `c` in row `p`. -/
def rowCount (p : PosIdx) (c : ℤ) : ℕ := (Finset.univ.filter fun q : PosIdx => gram p q = c).card

/-- Rows are not uniform: the row of the highest root `e₀ - e₆` has ten `+1`s and no `-1`. -/
theorem row_06 : rowCount ⟨(0, 6), by decide⟩ 1 = 10 ∧ rowCount ⟨(0, 6), by decide⟩ (-1) = 0 := by
  decide +kernel

/-- The entries add up to `112 = |2ρ|²`. -/
theorem gram_sum : ∑ p, ∑ q, gram p q = 112 := by decide +kernel

/-- `tr G = 42`. -/
theorem gram_trace : gram.trace = 42 := by decide +kernel


open Matrix

/-- The Gram matrix over `ℚ`. -/
def gramQ : Matrix PosIdx PosIdx ℚ := gram.map (Int.cast : ℤ → ℚ)

/-- `G² = 7 G` over `ℚ`. -/
theorem gramQ_sq : gramQ * gramQ = (7 : ℚ) • gramQ := by
  show gram.map (Int.castRingHom ℚ) * gram.map (Int.castRingHom ℚ) = _
  rw [← Matrix.map_mul, gram_sq]
  ext p q
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, gramQ, Matrix.map_apply]
  simp

/-- **Every eigenvalue of `G` is `0` or `7`.** -/
theorem eigen_zero_or_seven {μ : ℚ} {v : PosIdx → ℚ} (hv : v ≠ 0)
    (h : gramQ *ᵥ v = μ • v) : μ = 0 ∨ μ = 7 := by
  have h2 : (gramQ * gramQ) *ᵥ v = (μ * μ) • v := by
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, smul_smul]
  rw [gramQ_sq, Matrix.smul_mulVec, h, smul_smul] at h2
  have h3 : (μ * μ - 7 * μ) • v = 0 := by rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.1 h3 with h4 | h4
  · have : μ * (μ - 7) = 0 := by linarith
    rcases mul_eq_zero.1 this with h5 | h5
    · exact Or.inl h5
    · exact Or.inr (by linarith)
  · exact absurd h4 hv

/-- `tr G = 42` over `ℚ`. -/
theorem gramQ_trace : gramQ.trace = 42 := by
  rw [gramQ, Matrix.trace, ← Int.cast_ofNat, ← gram_trace, Matrix.trace]
  simp

/-- **`rank G = 6`** (`G/7` is a projection, whose rank is its trace `42/7`). -/
theorem gramQ_rank : gramQ.rank = 6 := by
  set f := ((1 / 7 : ℚ) • gramQ).mulVecLin with hf
  have hidem : IsIdempotentElem f := by
    rw [IsIdempotentElem, hf, Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, Matrix.smul_mul,
      Matrix.mul_smul, gramQ_sq, smul_smul, smul_smul]
    norm_num
  have htr := ((LinearMap.isProj_range_iff_isIdempotentElem f).2 hidem).trace
  rw [hf, show ((1 / 7 : ℚ) • gramQ).mulVecLin = Matrix.toLin' ((1 / 7 : ℚ) • gramQ) from rfl,
    Matrix.trace_toLin'_eq, Matrix.trace_smul, gramQ_trace] at htr
  have hr : Matrix.rank ((1 / 7 : ℚ) • gramQ) = 6 := by
    rw [Matrix.rank]; norm_num at htr; exact_mod_cast htr.symm
  have hs : ((1 / 7 : ℚ) • gramQ).mulVecLin = (1 / 7 : ℚ) • gramQ.mulVecLin := by
    ext v i; simp
  rwa [Matrix.rank, hs, LinearMap.range_smul _ _ (by norm_num)] at hr


/-- **The kernel of `G` has dimension 15.** With `rank G = 6`, `G² = 7G`: eigenvalue `7`
has multiplicity 6 and eigenvalue `0` has multiplicity 15. -/
theorem gramQ_nullity : Module.finrank ℚ (LinearMap.ker gramQ.mulVecLin) = 15 := by
  have h := LinearMap.finrank_range_add_finrank_ker gramQ.mulVecLin
  rw [← Matrix.rank, gramQ_rank, Module.finrank_fintype_fun_eq_card, card_posIdx] at h
  omega

/-- Every vector in the range of `G` is an eigenvector with eigenvalue `7`. -/
theorem range_eigen_seven (v : PosIdx → ℚ) : gramQ *ᵥ (gramQ *ᵥ v) = (7 : ℚ) • (gramQ *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, gramQ_sq, Matrix.smul_mulVec]

/-- All `A₆` roots, ordered pairs `(i, j)`, `i ≠ j`. -/
abbrev RootIdx := {p : Fin 7 × Fin 7 // p.1 ≠ p.2}

/-- Over all 42 roots the inner products sum to `0` (mean cosine `0`). -/
theorem allRoots_gram_sum : ∑ p : RootIdx, ∑ q : RootIdx, gramF p.1 q.1 = 0 := by decide +kernel

/-- Number of ordered pairs of roots of `A₆` with inner product `c`. -/
def allCount (c : ℤ) : ℕ := (Finset.univ.filter fun pq : RootIdx × RootIdx => gramF pq.1.1 pq.2.1 = c).card

/-- Inner-product counts over all ordered pairs of the 42 roots: symmetric in sign. -/
theorem allRoots_counts : allCount 2 = 42 ∧ allCount 1 = 420 ∧ allCount 0 = 840 ∧ allCount (-1) = 420 ∧
    allCount (-2) = 42 := by
  decide +kernel

open Equiv

/-- **The 21 positive-root reflections (transpositions `i ↔ j`, `i < j`) generate `S₇`.** -/
theorem reflections_generate_S7 :
    Subgroup.closure {σ : Perm (Fin 7) | ∃ i j : Fin 7, i < j ∧ σ = swap i j} = ⊤ := by
  rw [← Equiv.Perm.closure_isSwap]
  congr 1
  ext σ
  simp only [Set.mem_setOf_eq, Perm.IsSwap]
  constructor
  · rintro ⟨i, j, h, rfl⟩; exact ⟨i, j, h.ne, rfl⟩
  · rintro ⟨i, j, h, rfl⟩
    rcases lt_or_gt_of_ne h with h | h
    · exact ⟨i, j, h, rfl⟩
    · exact ⟨j, i, h, swap_comm i j⟩

section Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open RealInnerProductSpace

/-- **Reflections preserve the norm exactly.** -/
theorem reflection_norm (a v : E) (ha : a ≠ 0) :
    ‖v - (2 * ⟪v, a⟫ / ⟪a, a⟫) • a‖ = ‖v‖ := by
  have haa : ⟪a, a⟫ ≠ 0 := by simpa using ha
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    real_inner_comm a v, RCLike.conj_to_real]
  field_simp
  ring

/-- **Crystallographic angle restriction.** If both Cartan numbers of `a, b` are integers
`m, n`, then `m n = 4 cos² ∠(a, b)` and `0 ≤ m n ≤ 4`. -/
theorem crystallographic_angle (a b : E) (ha : a ≠ 0) (hb : b ≠ 0) (m n : ℤ)
    (hm : 2 * ⟪a, b⟫ = m * ⟪a, a⟫) (hn : 2 * ⟪a, b⟫ = n * ⟪b, b⟫) :
    0 ≤ m * n ∧ m * n ≤ 4 ∧ ((m * n : ℤ) : ℝ) = 4 * Real.cos (InnerProductGeometry.angle a b) ^ 2 := by
  have haa : 0 < ⟪a, a⟫ := real_inner_self_pos.2 ha
  have hbb : 0 < ⟪b, b⟫ := real_inner_self_pos.2 hb
  have hcs := real_inner_mul_inner_self_le a b
  have key : (m * n : ℝ) * (⟪a, a⟫ * ⟪b, b⟫) = 4 * ⟪a, b⟫ ^ 2 := by
    have : (m * ⟪a, a⟫) * (n * ⟪b, b⟫) = (2 * ⟪a, b⟫) * (2 * ⟪a, b⟫) := by rw [← hm, ← hn]
    nlinarith [this]
  have hpos : 0 < ⟪a, a⟫ * ⟪b, b⟫ := mul_pos haa hbb
  refine ⟨?_, ?_, ?_⟩
  · have : (0 : ℝ) ≤ m * n := by
      by_contra h; push_neg at h; nlinarith [sq_nonneg ⟪a, b⟫]
    exact_mod_cast this
  · have : (m * n : ℝ) ≤ 4 := by
      by_contra h; push_neg at h; nlinarith
    exact_mod_cast this
  · rw [InnerProductGeometry.cos_angle, div_pow, mul_pow, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    push_cast
    field_simp
    linarith [key]

end Real

/-- A matrix with determinant `1` is invertible (not singular). -/
theorem det_one_isUnit (A : Matrix (Fin 8) (Fin 8) ℝ) (h : A.det = 1) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).2 (h ▸ isUnit_one)

/-- **Perfect:** the binary Golay code of length 23 (`2¹²` words, radius 3) fills `𝔽₂²³`. -/
theorem golay23_perfect : 2 ^ 12 * (∑ k ∈ Finset.range 4, Nat.choose 23 k) = 2 ^ 23 := by decide

/-- A Hamming ball of radius 3 in `𝔽₂²⁴` has 2325 points. -/
theorem golay24_ball : (∑ k ∈ Finset.range 4, Nat.choose 24 k) = 2325 := by decide

/-- **The extended Golay code is not perfect:** no number of radius-3 balls in length 24
fills `2²⁴` points exactly (`2325` is odd). -/
theorem golay24_not_perfect (M : ℕ) : M * (∑ k ∈ Finset.range 4, Nat.choose 24 k) ≠ 2 ^ 24 := by
  rw [golay24_ball]
  intro h
  have h3 : (3 : ℕ) ∣ 2 ^ 24 := ⟨M * 775, by omega⟩
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

/-- No binary code of length 24 is perfect, for any radius `1 … 23`: the ball size never
divides `2²⁴`. -/
theorem no_perfect_length24 : ∀ r ∈ Finset.Icc 1 23,
    ¬ (∑ k ∈ Finset.range (r + 1), Nat.choose 24 k) ∣ 2 ^ 24 := by
  decide +kernel

end QBX.Notes.A6GramAudit
