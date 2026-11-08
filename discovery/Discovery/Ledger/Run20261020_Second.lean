module

public import Discovery.Kernel

/-!
# Discovery run `Run20261020_Second`

Claims burned in by the automated discovery loop (`python3 -m discovery.engine run`).  Entropy seed `0826e49f0409599a7a868e92fdbc66daeb5ca10a2eca80b349af0cb28231164a` (replay with `--seed-hex`); domains: cd_signs, quad_forms, prime_poly.  Every theorem is a closed bounded statement over `Discovery.Kernel`, decided by the Lean kernel.
-/

@[expose] public section

namespace Discovery.Ledger

open Discovery


/-- every prime p < 800 with p ≡ 1 (mod 3) is of the form x² + 3y². -/
theorem quadform_holds_8737ca6f26 :
    ∀ p < 800, isPrimeB p = true → p % 3 = 1 → ∃ x < 29, ∃ y < 29, x * x + 3 * y * y = p :=
  by decide +kernel

/-- [32-dim CD, dim 32] ∀ i j with i ≠ 0: σ(j, i) · σ((i ^^^ j), i) = -1. -/
theorem cdsign_holds_31645a8c2a :
    ∀ i < 32, ∀ j < 32, i ≠ 0 → cdSign 5 j i * cdSign 5 (i ^^^ j) i = -1 :=
  by decide +kernel

/-- n² + 3n + 223 is prime for every n < 11. -/
theorem primepoly_holds_08b941054d :
    ∀ n < 11, isPrimeB (n * n + 3 * n + 223) = true :=
  by decide +kernel

/-- Refuted: n² + 3n + 223 is prime for every n < 12.  Counterexample: n = 11: 377 is composite. -/
theorem primepoly_refute_31dad9be56 :
    ¬ (∀ n < 12, isPrimeB (n * n + 3 * n + 223) = true) :=
  fun h => absurd (h 11 (by decide)) (by decide +kernel)

/-- every prime p < 800 with p ≡ 1 (mod 8) is of the form x² + 8y². -/
theorem quadform_holds_6f1e7f318d :
    ∀ p < 800, isPrimeB p = true → p % 8 = 1 → ∃ x < 29, ∃ y < 29, x * x + 8 * y * y = p :=
  by decide +kernel

/-- [32-dim CD, dim 32] ∀ i j with i ≠ 0: σ(i, j) · σ(i, (i ^^^ j)) = -1. -/
theorem cdsign_holds_1a1920a752 :
    ∀ i < 32, ∀ j < 32, i ≠ 0 → cdSign 5 i j * cdSign 5 i (i ^^^ j) = -1 :=
  by decide +kernel

/-- every prime p < 800 with p ≡ 1 (mod 4) is of the form x² + 4y². -/
theorem quadform_holds_d220bfce14 :
    ∀ p < 800, isPrimeB p = true → p % 4 = 1 → ∃ x < 29, ∃ y < 29, x * x + 4 * y * y = p :=
  by decide +kernel

/-- every prime p < 800 with p ≡ 1 (mod 8) is of the form x² + 2y². -/
theorem quadform_holds_9fe2e2111b :
    ∀ p < 800, isPrimeB p = true → p % 8 = 1 → ∃ x < 29, ∃ y < 29, x * x + 2 * y * y = p :=
  by decide +kernel

/-- every prime p < 800 with p ≡ 1 (mod 4) is of the form x² + y². -/
theorem quadform_holds_e9bb76e09c :
    ∀ p < 800, isPrimeB p = true → p % 4 = 1 → ∃ x < 29, ∃ y < 29, x * x + y * y = p :=
  by decide +kernel

/-- [32-dim CD, dim 32] ∀ i j k: σ(j, i) · σ(j, (i ^^^ j)) · σ(k, j) · σ((j ^^^ k), j) = +1. -/
theorem cdsign_holds_79fcd74642 :
    ∀ i < 32, ∀ j < 32, ∀ k < 32, cdSign 5 j i * cdSign 5 j (i ^^^ j) * cdSign 5 k j * cdSign 5 (j ^^^ k) j = 1 :=
  by decide +kernel

/-- [32-dim CD, dim 32] ∀ i j k with (i ^^^ j) ≠ 0, k ≠ 0: σ(i, j) · σ(j, (i ^^^ j)) · σ(k, (i ^^^ k)) · σ((i ^^^ k), i) = +1. -/
theorem cdsign_holds_297b2b43eb :
    ∀ i < 32, ∀ j < 32, ∀ k < 32, (i ^^^ j) ≠ 0 ∧ k ≠ 0 → cdSign 5 i j * cdSign 5 j (i ^^^ j) * cdSign 5 k (i ^^^ k) * cdSign 5 (i ^^^ k) i = 1 :=
  by decide +kernel

/-- every prime p < 800 with p ≡ 1 (mod 12) is of the form x² + 9y². -/
theorem quadform_holds_8108d16c71 :
    ∀ p < 800, isPrimeB p = true → p % 12 = 1 → ∃ x < 29, ∃ y < 29, x * x + 9 * y * y = p :=
  by decide +kernel

/-- [32-dim CD, dim 32] ∀ i j with (i ^^^ j) ≠ 0: σ((i ^^^ j), i) · σ((i ^^^ j), j) = -1. -/
theorem cdsign_holds_0a4c7cab18 :
    ∀ i < 32, ∀ j < 32, (i ^^^ j) ≠ 0 → cdSign 5 (i ^^^ j) i * cdSign 5 (i ^^^ j) j = -1 :=
  by decide +kernel

/-- Refuted: [𝕊, dim 16] ∀ i j k with i ≠ 0, (i ^^^ k) ≠ 0: σ(i, k) · σ(j, (i ^^^ k)) · σ((j ^^^ k), (i ^^^ k)) = +1.  Counterexample: i = 5, j = 14, k = 15. -/
theorem cdsign_refute_9b8dd06f65 :
    ¬ (∀ i < 16, ∀ j < 16, ∀ k < 16, i ≠ 0 ∧ (i ^^^ k) ≠ 0 → cdSign 4 i k * cdSign 4 j (i ^^^ k) * cdSign 4 (j ^^^ k) (i ^^^ k) = 1) :=
  fun h => absurd (h 5 (by decide) 14 (by decide) 15 (by decide) (by decide)) (by decide +kernel)

end Discovery.Ledger

end
