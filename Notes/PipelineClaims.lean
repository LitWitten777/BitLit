module

public import Mathlib

@[expose] public section

/-!
# Two checks on the pipeline descriptions

Report: `docs/ZERO_DIVISOR_USAGE_AUDIT_2026-10-20.md`.

## `voxel_nesting.py`: every word vector is the zero vector

`VerseVoxel.build_word_vectors` sets `base = [gematria] * dim` and then
`vector = (base - base.mean()) / (base.std() + 1e-8)`. A constant vector minus its mean is `0`, so
in exact arithmetic **every word vector is `0`**, whatever the word (`standardize_const`). Hence
every verse vector (a mean of word vectors) and every shell vector is `0` too, and the gematria never
reaches the vectors (`standardize_const_indep`). There is also no `E₈` or Leech-lattice step
anywhere in the script.

## `TopQuarkFixedPoint.lean`: the Pendleton–Ross ratio does not give 173 GeV

The module defines `R* = y_t² / g₃² = 2/9` and, separately, puts in `y_t* = 0.993` by hand.
Then it checks `0.993 · 246.22 / √2 ∈ (171, 175)`. If one actually uses `R* = 2/9`, then
`y_t = g₃ √(2/9)` and `m_t = y_t v / √2 = g₃ v / 3` (`mt_of_ratio`). For any strong coupling
`g₃ < 1.23` (the measured value at `m_Z` is about `1.22`), this is **below 101 GeV**
(`mt_of_ratio_lt`), far from the measured `≈ 172.5 GeV`. The `[171, 175]` window therefore comes
from the hand-chosen `0.993`, not from the fixed point.
-/

namespace QBX.Notes.PipelineClaims

open Finset

/-- Mean of a vector of length `n`. -/
noncomputable def mean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- Population standard deviation (`numpy.std`). -/
noncomputable def std {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt ((∑ i, (x i - mean x) ^ 2) / n)

/-- The standardisation step of `build_word_vectors`. -/
noncomputable def standardize {n : ℕ} (eps : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (x i - mean x) / (std x + eps)

/-- **Standardising a constant vector gives the zero vector.** -/
theorem standardize_const {n : ℕ} (hn : 0 < n) (eps g : ℝ) :
    standardize eps (fun _ : Fin n => g) = 0 := by
  have hm : mean (fun _ : Fin n => g) = g := by
    rw [mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  funext i
  simp [standardize, hm]

/-- So the word vector does not depend on the gematria value at all. -/
theorem standardize_const_indep {n : ℕ} (hn : 0 < n) (eps g h : ℝ) :
    standardize eps (fun _ : Fin n => g) = standardize eps (fun _ : Fin n => h) := by
  rw [standardize_const hn, standardize_const hn]

/-- Top mass from the ratio `R = y_t² / g₃²`: `m_t = √R · g₃ · v / √2`. -/
noncomputable def mtOfRatio (R g v : ℝ) : ℝ := Real.sqrt R * g * v / Real.sqrt 2

/-- With the Pendleton–Ross value `R* = 2/9`, `m_t = g₃ v / 3`. -/
theorem mt_of_ratio (g v : ℝ) : mtOfRatio (2 / 9) g v = g * v / 3 := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have h9 : Real.sqrt (2 / 9) = Real.sqrt 2 / 3 := by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 9),
      show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [mtOfRatio, h9]
  field_simp

/-- **For `g₃ < 1.23` and `v = 246.22 GeV`, the fixed-point mass is below 101 GeV.** -/
theorem mt_of_ratio_lt (g : ℝ) (hg : g < 1.23) : mtOfRatio (2 / 9) g 246.22 < 101 := by
  rw [mt_of_ratio]
  nlinarith

end QBX.Notes.PipelineClaims
