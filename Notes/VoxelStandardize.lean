module

public import QBX.Notes.PipelineClaims

@[expose] public section

/-!
# The repaired voxel pipeline: guarded standardisation and non-collapsing lattice projection

Companion of the refactored `voxel_nesting.py` and `lattice_quantizers.py`
(report: `docs/VOXEL_TOPQUARK_ZD32_2026-10-20.md`).

`QBX.Notes.PipelineClaims.standardize_const` showed that the old `build_word_vectors` sent every
word to the zero vector. The repaired pipeline relies on two facts, proved here in exact arithmetic.

1. **Guarded standardisation keeps the signal.** For a non-constant vector the z-score
   `(x - mean x) / (std x + eps)` (with `eps ≥ 0`) is non-zero (`standardize_ne_zero`), has mean
   `0` (`mean_standardize`) and standard deviation `std x / (std x + eps)`
   (`std_standardize`); with `eps = 0` that is exactly `1` (`std_standardize_zero`). The guarded
   version used in the script (`standardizeSafe`, which only centres when `std x = 0`) is non-zero
   for every non-constant input (`standardizeSafe_ne_zero`).
2. **Robust scaling prevents collapse to the zero lattice point.** If every point lies within
   `ρ` of the lattice `L` (covering radius `ρ`) and `0` is a nearest lattice point to `y`, then
   `‖y‖ ≤ ρ` (`norm_le_of_zero_nearest`). Hence once a vector is scaled to norm `> ρ`, none of its
   nearest lattice points is `0` (`nearest_ne_zero_of_norm_gt`). This is what
   `scale_for_lattice` does, with `ρ = 1` for `E₈` and `ρ = √2` for the Leech lattice
   (`4` in Conway's integer coordinates).
-/

namespace QBX.Notes.VoxelStandardize

open Finset QBX.Notes.PipelineClaims

variable {n : ℕ}

/-- Guarded standardisation as in the repaired script: centre only, if the vector is constant. -/
noncomputable def standardizeSafe (eps : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  if std x = 0 then fun i => x i - mean x else standardize eps x

theorem sum_sub_mean (x : Fin n → ℝ) : ∑ i, (x i - mean x) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mean]
  field_simp
  ring

/-- A vector is constant iff it equals its mean everywhere. -/
theorem eq_mean_of_std_eq_zero (x : Fin n → ℝ) (h : std x = 0) (i : Fin n) : x i = mean x := by
  have hn : 0 < n := Fin.pos i
  have hsum : (∑ j, (x j - mean x) ^ 2) / n = 0 := by
    have h0 : 0 ≤ (∑ j, (x j - mean x) ^ 2) / n := by positivity
    rw [std, Real.sqrt_eq_zero h0] at h
    exact h
  have hsum' : ∑ j, (x j - mean x) ^ 2 = 0 := by
    rcases div_eq_zero_iff.1 hsum with h1 | h1
    · exact h1
    · exact absurd h1 (by exact_mod_cast hn.ne')
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j - mean x))).1 hsum' i
    (Finset.mem_univ _)
  nlinarith [sq_nonneg (x i - mean x)]

theorem std_nonneg (x : Fin n → ℝ) : 0 ≤ std x := Real.sqrt_nonneg _

/-- A non-constant vector has positive standard deviation. -/
theorem std_pos_of_nonconst (x : Fin n → ℝ) (h : ∃ i j, x i ≠ x j) : 0 < std x := by
  obtain ⟨i, j, hij⟩ := h
  rcases (std_nonneg x).lt_or_eq with h' | h'
  · exact h'
  · exact absurd ((eq_mean_of_std_eq_zero x h'.symm i).trans
      (eq_mean_of_std_eq_zero x h'.symm j).symm) hij

/-- **The z-score of a non-constant vector is not the zero vector** (for any `eps ≥ 0`). -/
theorem standardize_ne_zero (eps : ℝ) (heps : 0 ≤ eps) (x : Fin n → ℝ) (h : ∃ i j, x i ≠ x j) :
    standardize eps x ≠ 0 := by
  obtain ⟨i, j, hij⟩ := h
  have hs : 0 < std x + eps := by linarith [std_pos_of_nonconst x ⟨i, j, hij⟩]
  intro h0
  have hi := congrFun h0 i
  have hj := congrFun h0 j
  simp only [standardize, Pi.zero_apply, div_eq_zero_iff, hs.ne', or_false, sub_eq_zero] at hi hj
  exact hij (hi.trans hj.symm)

/-- **The guarded standardisation never kills a non-constant vector.** -/
theorem standardizeSafe_ne_zero (eps : ℝ) (heps : 0 ≤ eps) (x : Fin n → ℝ)
    (h : ∃ i j, x i ≠ x j) : standardizeSafe eps x ≠ 0 := by
  have hs := std_pos_of_nonconst x h
  rw [standardizeSafe, if_neg hs.ne']
  exact standardize_ne_zero eps heps x h

/-- The z-score has mean `0`. -/
theorem mean_standardize (eps : ℝ) (x : Fin n → ℝ) : mean (standardize eps x) = 0 := by
  unfold mean standardize
  rw [← Finset.sum_div]
  rw [sum_sub_mean, zero_div, zero_div]

/-- **The z-score has standard deviation `std x / (std x + eps)`** (so variance is kept, up to
the `eps` regulariser). -/
theorem std_standardize (eps : ℝ) (heps : 0 ≤ eps) (x : Fin n → ℝ) :
    std (standardize eps x) = std x / (std x + eps) := by
  have hm := mean_standardize eps x
  rcases (std_nonneg x).lt_or_eq with hs | hs
  · have hd : 0 < std x + eps := by linarith
    have hS : 0 ≤ (∑ i, (x i - mean x) ^ 2) / n := by positivity
    rw [std, hm]
    simp only [sub_zero, standardize, div_pow]
    rw [← Finset.sum_div, div_right_comm, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hd.le]
    rfl
  · have hconst := eq_mean_of_std_eq_zero x hs.symm
    have h0 : standardize eps x = 0 := by
      funext i
      simp [standardize, ← hconst i]
    rw [h0, ← hs, zero_div]
    have : (0 : Fin n → ℝ) = fun _ => (0 : ℝ) := rfl
    rw [this, std]
    simp [mean]

/-- With `eps = 0`, a non-constant vector is standardised to **unit** standard deviation. -/
theorem std_standardize_zero (x : Fin n → ℝ) (h : ∃ i j, x i ≠ x j) :
    std (standardize 0 x) = 1 := by
  rw [std_standardize 0 le_rfl, add_zero, div_self (std_pos_of_nonconst x h).ne']

/-! ## Robust scaling against collapse to the zero lattice point -/

section Covering

variable {E : Type*} [NormedAddCommGroup E]

/-- If every point is within `ρ` of `L` and `0` is a nearest point of `L` to `y`, then
`‖y‖ ≤ ρ`. -/
theorem norm_le_of_zero_nearest (L : Set E) (ρ : ℝ) (hcov : ∀ z : E, ∃ p ∈ L, dist z p ≤ ρ)
    (y : E) (hnear : ∀ p ∈ L, dist y 0 ≤ dist y p) : ‖y‖ ≤ ρ := by
  obtain ⟨p, hp, hd⟩ := hcov y
  rw [← dist_zero_right]
  exact (hnear p hp).trans hd

/-- **A vector of norm larger than the covering radius has no nearest lattice point equal to
`0`.** -/
theorem nearest_ne_zero_of_norm_gt (L : Set E) (ρ : ℝ) (hcov : ∀ z : E, ∃ p ∈ L, dist z p ≤ ρ)
    (y : E) (hy : ρ < ‖y‖) (q : E) (hq : q ∈ L) (hnear : ∀ p ∈ L, dist y q ≤ dist y p) :
    q ≠ 0 := by
  rintro rfl
  exact absurd (norm_le_of_zero_nearest L ρ hcov y hnear) (not_le.2 hy)

end Covering

end QBX.Notes.VoxelStandardize
