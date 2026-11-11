import Mathlib

open scoped Classical BigOperators Real
open Filter Topology

/-!
# Rotation return data (Stage 2A)

For an irrational circle rotation `R_θ : x ↦ x - θ` on `ℝ/ℤ`, the continued
fraction of `θ` provides a sequence of *best approximations* `pₙ/qₙ`, i.e. a
sequence of positive integers `qₙ` and integers `pₙ` such that
`qₙ θ - pₙ → 0`.  These are precisely the *return times* of the rotation that
the Denjoy–Koksma machinery downstream relies upon.

In this stage we do **not** construct such a sequence from the continued
fraction expansion; instead we package its defining property into a reusable
interface `RotationReturnData θ`, and prove everything conditionally on having
such data.  This keeps the Fourier-mode return-sum infrastructure independent
of any (currently missing) continued-fraction machinery in Mathlib.
-/

namespace CriticalMixedHRT

/-- A sequence of *return times* for the rotation by `θ`: positive integer
denominators `qₙ` together with integer numerators `pₙ` such that
`qₙ θ - pₙ → 0`.  (For irrational `θ` these are produced by the continued
fraction convergents; here we take their existence as data.) -/
structure RotationReturnData (θ : ℝ) where
  /-- The denominator sequence `qₙ`. -/
  q : ℕ → ℕ
  /-- The numerator sequence `pₙ`. -/
  p : ℕ → ℤ
  /-- Each denominator is positive. -/
  q_pos : ∀ n, 0 < q n
  /-- The defining return property `qₙ θ - pₙ → 0`. -/
  tendsto_return :
    Tendsto (fun n => (q n : ℝ) * θ - (p n : ℝ)) atTop (𝓝 0)

namespace RotationReturnData

variable {θ : ℝ} (R : RotationReturnData θ)

/-- The denominators are eventually positive natural numbers, hence nonzero. -/
theorem q_ne_zero (n : ℕ) : R.q n ≠ 0 :=
  (R.q_pos n).ne'

end RotationReturnData

end CriticalMixedHRT
