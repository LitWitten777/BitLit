module

public import Discovery.Kernel

/-!
# Discovery run `Run20261020_Genesis`

Claims burned in by the automated discovery loop (`python3 -m discovery.engine run`).  Entropy seed `34cd20ffa2834283cd215cdd3851e7a4af2cec6cc67f448e4167c39ba68cd648` (replay with `--seed-hex`); domains: cd_signs, quad_forms, prime_poly.  Every theorem is a closed bounded statement over `Discovery.Kernel`, decided by the Lean kernel.
-/

@[expose] public section

namespace Discovery.Ledger

open Discovery


/-- [32-dim CD, dim 32] ∀ i with i ≠ 0: σ(i, i) = -1. -/
theorem cdsign_holds_347b44802c :
    ∀ i < 32, i ≠ 0 → cdSign 5 i i = -1 :=
  by decide +kernel

/-- every prime p < 800 with p ≡ 3 (mod 8) is of the form x² + 2y². -/
theorem quadform_holds_f90d6f6a59 :
    ∀ p < 800, isPrimeB p = true → p % 8 = 3 → ∃ x < 29, ∃ y < 29, x * x + 2 * y * y = p :=
  by decide +kernel

/-- Refuted: [𝕊, dim 16] ∀ i j k with i ≠ 0, (i ^^^ j) ≠ 0, (j ^^^ k) ≠ 0: σ(i, (j ^^^ k)) · σ(j, (i ^^^ k)) · σ(k, j) · σ((i ^^^ k), k) = -1.  Counterexample: i = 1, j = 14, k = 13. -/
theorem cdsign_refute_0b9a027357 :
    ¬ (∀ i < 16, ∀ j < 16, ∀ k < 16, i ≠ 0 → (i ^^^ j) ≠ 0 → (j ^^^ k) ≠ 0 → cdSign 4 i (j ^^^ k) * cdSign 4 j (i ^^^ k) * cdSign 4 k j * cdSign 4 (i ^^^ k) k = -1) :=
  fun h => absurd (h 1 (by decide) 14 (by decide) 13 (by decide) (by decide) (by decide) (by decide)) (by decide +kernel)

/-- n² + 33n + 103 is prime for every n < 9. -/
theorem primepoly_holds_7e568ef024 :
    ∀ n < 9, isPrimeB (n * n + 33 * n + 103) = true :=
  by decide +kernel

/-- Refuted: n² + 33n + 103 is prime for every n < 10.  Counterexample: n = 9: 481 is composite. -/
theorem primepoly_refute_97efcbc759 :
    ¬ (∀ n < 10, isPrimeB (n * n + 33 * n + 103) = true) :=
  fun h => absurd (h 9 (by decide)) (by decide +kernel)

end Discovery.Ledger

end
