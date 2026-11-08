module

public import Discovery.Kernel

/-!
# Discovery run `Run20261020_Third`

Claims burned in by the automated discovery loop (`python3 -m discovery.engine run`).  Entropy seed `4887fe52dc82a422e860fcc22cd5fea8b24483499d687b97a843b05eb593fd1c` (replay with `--seed-hex`); domains: cd_signs, quad_forms, prime_poly.  Every theorem is a closed bounded statement over `Discovery.Kernel`, decided by the Lean kernel.
-/

@[expose] public section

namespace Discovery.Ledger

open Discovery


set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- [32-dim CD, dim 32] ∀ i j with (i ^^^ j) ≠ 0: σ(i, (i ^^^ j)) · σ(j, (i ^^^ j)) = -1. -/
theorem cdsign_holds_1dea2d3b9f :
    ∀ i < 32, ∀ j < 32, (i ^^^ j) ≠ 0 → cdSign 5 i (i ^^^ j) * cdSign 5 j (i ^^^ j) = -1 :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- [𝕆, dim 8] ∀ i j k: σ(i, j) · σ(i, (i ^^^ k)) · σ(k, (i ^^^ j ^^^ k)) · σ((i ^^^ k), i) · σ((i ^^^ k), (j ^^^ k)) = +1. -/
theorem cdsign_holds_1fb11ec25b :
    ∀ i < 8, ∀ j < 8, ∀ k < 8, cdSign 3 i j * cdSign 3 i (i ^^^ k) * cdSign 3 k (i ^^^ j ^^^ k) * cdSign 3 (i ^^^ k) i * cdSign 3 (i ^^^ k) (j ^^^ k) = 1 :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Refuted: [𝕊, dim 16] ∀ i j k: σ(i, j) · σ(i, (i ^^^ k)) · σ(k, (i ^^^ j ^^^ k)) · σ((i ^^^ k), i) · σ((i ^^^ k), (j ^^^ k)) = +1.  Counterexample: i = 2, j = 9, k = 6. -/
theorem cdsign_refute_8455ac27fb :
    ¬ (∀ i < 16, ∀ j < 16, ∀ k < 16, cdSign 4 i j * cdSign 4 i (i ^^^ k) * cdSign 4 k (i ^^^ j ^^^ k) * cdSign 4 (i ^^^ k) i * cdSign 4 (i ^^^ k) (j ^^^ k) = 1) :=
  fun h => absurd (h 2 (by decide) 9 (by decide) 6 (by decide)) (by decide +kernel)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- [𝕆, dim 8] ∀ i j k with (j ^^^ k) ≠ 0: σ(i, j) · σ(j, k) · σ(k, (i ^^^ j)) · σ(k, (i ^^^ j ^^^ k)) · σ((i ^^^ j ^^^ k), j) = -1. -/
theorem cdsign_holds_09437e4279 :
    ∀ i < 8, ∀ j < 8, ∀ k < 8, (j ^^^ k) ≠ 0 → cdSign 3 i j * cdSign 3 j k * cdSign 3 k (i ^^^ j) * cdSign 3 k (i ^^^ j ^^^ k) * cdSign 3 (i ^^^ j ^^^ k) j = -1 :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Refuted: [𝕊, dim 16] ∀ i j k with (j ^^^ k) ≠ 0: σ(i, j) · σ(j, k) · σ(k, (i ^^^ j)) · σ(k, (i ^^^ j ^^^ k)) · σ((i ^^^ j ^^^ k), j) = -1.  Counterexample: i = 5, j = 11, k = 15. -/
theorem cdsign_refute_250a2bcba1 :
    ¬ (∀ i < 16, ∀ j < 16, ∀ k < 16, (j ^^^ k) ≠ 0 → cdSign 4 i j * cdSign 4 j k * cdSign 4 k (i ^^^ j) * cdSign 4 k (i ^^^ j ^^^ k) * cdSign 4 (i ^^^ j ^^^ k) j = -1) :=
  fun h => absurd (h 5 (by decide) 11 (by decide) 15 (by decide) (by decide)) (by decide +kernel)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- [𝕆, dim 8] ∀ i j k: σ(j, i) · σ(k, i) · σ((j ^^^ k), i) = +1. -/
theorem cdsign_holds_bcdae9b451 :
    ∀ i < 8, ∀ j < 8, ∀ k < 8, cdSign 3 j i * cdSign 3 k i * cdSign 3 (j ^^^ k) i = 1 :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Refuted: [𝕊, dim 16] ∀ i j k: σ(j, i) · σ(k, i) · σ((j ^^^ k), i) = +1.  Counterexample: i = 15, j = 2, k = 11. -/
theorem cdsign_refute_398deb53c7 :
    ¬ (∀ i < 16, ∀ j < 16, ∀ k < 16, cdSign 4 j i * cdSign 4 k i * cdSign 4 (j ^^^ k) i = 1) :=
  fun h => absurd (h 15 (by decide) 2 (by decide) 11 (by decide)) (by decide +kernel)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- [32-dim CD, dim 32] ∀ i j with i ≠ 0, j ≠ 0: σ(i, (i ^^^ j)) · σ((i ^^^ j), j) = +1. -/
theorem cdsign_holds_217122f46f :
    ∀ i < 32, ∀ j < 32, i ≠ 0 ∧ j ≠ 0 → cdSign 5 i (i ^^^ j) * cdSign 5 (i ^^^ j) j = 1 :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- [𝕆, dim 8] ∀ i j k with j ≠ 0, (i ^^^ j ^^^ k) ≠ 0: σ(i, j) · σ(k, j) · σ((i ^^^ j ^^^ k), (i ^^^ k)) = +1. -/
theorem cdsign_holds_80eaf929c0 :
    ∀ i < 8, ∀ j < 8, ∀ k < 8, j ≠ 0 ∧ (i ^^^ j ^^^ k) ≠ 0 → cdSign 3 i j * cdSign 3 k j * cdSign 3 (i ^^^ j ^^^ k) (i ^^^ k) = 1 :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Refuted: [𝕊, dim 16] ∀ i j k with j ≠ 0, (i ^^^ j ^^^ k) ≠ 0: σ(i, j) · σ(k, j) · σ((i ^^^ j ^^^ k), (i ^^^ k)) = +1.  Counterexample: i = 15, j = 10, k = 11. -/
theorem cdsign_refute_d09883addc :
    ¬ (∀ i < 16, ∀ j < 16, ∀ k < 16, j ≠ 0 ∧ (i ^^^ j ^^^ k) ≠ 0 → cdSign 4 i j * cdSign 4 k j * cdSign 4 (i ^^^ j ^^^ k) (i ^^^ k) = 1) :=
  fun h => absurd (h 15 (by decide) 10 (by decide) 11 (by decide) (by decide)) (by decide +kernel)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- n² + 7n + 29 is prime for every n < 13. -/
theorem primepoly_holds_0ea5cbb2e4 :
    ∀ n < 13, isPrimeB (n * n + 7 * n + 29) = true :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Refuted: n² + 7n + 29 is prime for every n < 14.  Counterexample: n = 13: 289 is composite. -/
theorem primepoly_refute_1ed5ac6832 :
    ¬ (∀ n < 14, isPrimeB (n * n + 7 * n + 29) = true) :=
  fun h => absurd (h 13 (by decide)) (by decide +kernel)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- n² + 23n + 173 is prime for every n < 29. -/
theorem primepoly_holds_6dba5cfe9f :
    ∀ n < 29, isPrimeB (n * n + 23 * n + 173) = true :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Refuted: n² + 23n + 173 is prime for every n < 30.  Counterexample: n = 29: 1681 is composite. -/
theorem primepoly_refute_97e2ff7a3a :
    ¬ (∀ n < 30, isPrimeB (n * n + 23 * n + 173) = true) :=
  fun h => absurd (h 29 (by decide)) (by decide +kernel)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- every prime p < 800 with p ≡ 9 (mod 14) is of the form x² + 7y². -/
theorem quadform_holds_1ab0f1c080 :
    ∀ p < 800, isPrimeB p = true → p % 14 = 9 → ∃ x < 29, ∃ y < 29, x * x + 7 * y * y = p :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- [ℂ, dim 2] ∀ i j k with (j ^^^ k) ≠ 0: σ(i, k) · σ(j, (i ^^^ j)) · σ(j, (i ^^^ k)) · σ(k, (i ^^^ k)) = -1. -/
theorem cdsign_holds_a128920027 :
    ∀ i < 2, ∀ j < 2, ∀ k < 2, (j ^^^ k) ≠ 0 → cdSign 1 i k * cdSign 1 j (i ^^^ j) * cdSign 1 j (i ^^^ k) * cdSign 1 k (i ^^^ k) = -1 :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Refuted: [ℍ, dim 4] ∀ i j k with (j ^^^ k) ≠ 0: σ(i, k) · σ(j, (i ^^^ j)) · σ(j, (i ^^^ k)) · σ(k, (i ^^^ k)) = -1.  Counterexample: i = 0, j = 3, k = 1. -/
theorem cdsign_refute_99b2e9e160 :
    ¬ (∀ i < 4, ∀ j < 4, ∀ k < 4, (j ^^^ k) ≠ 0 → cdSign 2 i k * cdSign 2 j (i ^^^ j) * cdSign 2 j (i ^^^ k) * cdSign 2 k (i ^^^ k) = -1) :=
  fun h => absurd (h 0 (by decide) 3 (by decide) 1 (by decide) (by decide)) (by decide +kernel)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- [32-dim CD, dim 32] ∀ i j with j ≠ 0, (i ^^^ j) ≠ 0: σ(i, (i ^^^ j)) · σ(j, i) = +1. -/
theorem cdsign_holds_147bc8efb7 :
    ∀ i < 32, ∀ j < 32, j ≠ 0 ∧ (i ^^^ j) ≠ 0 → cdSign 5 i (i ^^^ j) * cdSign 5 j i = 1 :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- [32-dim CD, dim 32] ∀ i j with (i ^^^ j) ≠ 0: σ(i, i) · σ(i, j) · σ(j, (i ^^^ j)) = -1. -/
theorem cdsign_holds_da3877f4b3 :
    ∀ i < 32, ∀ j < 32, (i ^^^ j) ≠ 0 → cdSign 5 i i * cdSign 5 i j * cdSign 5 j (i ^^^ j) = -1 :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- every prime p < 800 with p ≡ 4 (mod 7) is of the form x² + 7y². -/
theorem quadform_holds_3cd9b9ba4e :
    ∀ p < 800, isPrimeB p = true → p % 7 = 4 → ∃ x < 29, ∃ y < 29, x * x + 7 * y * y = p :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- n² + 7n + 233 is prime for every n < 9. -/
theorem primepoly_holds_b16e5eac00 :
    ∀ n < 9, isPrimeB (n * n + 7 * n + 233) = true :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Refuted: n² + 7n + 233 is prime for every n < 10.  Counterexample: n = 9: 377 is composite. -/
theorem primepoly_refute_2d13794d43 :
    ¬ (∀ n < 10, isPrimeB (n * n + 7 * n + 233) = true) :=
  fun h => absurd (h 9 (by decide)) (by decide +kernel)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- n² + 3n + 19 is prime for every n < 15. -/
theorem primepoly_holds_f36ea0b681 :
    ∀ n < 15, isPrimeB (n * n + 3 * n + 19) = true :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Refuted: n² + 3n + 19 is prime for every n < 16.  Counterexample: n = 15: 289 is composite. -/
theorem primepoly_refute_74c57eac38 :
    ¬ (∀ n < 16, isPrimeB (n * n + 3 * n + 19) = true) :=
  fun h => absurd (h 15 (by decide)) (by decide +kernel)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- [32-dim CD, dim 32] ∀ i j with i ≠ 0, (i ^^^ j) ≠ 0: σ(j, i) · σ((i ^^^ j), j) = +1. -/
theorem cdsign_holds_f75183d210 :
    ∀ i < 32, ∀ j < 32, i ≠ 0 ∧ (i ^^^ j) ≠ 0 → cdSign 5 j i * cdSign 5 (i ^^^ j) j = 1 :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- [32-dim CD, dim 32] ∀ i j with i ≠ 0: σ(i, j) · σ(j, (i ^^^ j)) · σ((i ^^^ j), (i ^^^ j)) = -1. -/
theorem cdsign_holds_a926dff530 :
    ∀ i < 32, ∀ j < 32, i ≠ 0 → cdSign 5 i j * cdSign 5 j (i ^^^ j) * cdSign 5 (i ^^^ j) (i ^^^ j) = -1 :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- every prime p < 800 with p ≡ 1 (mod 7) is of the form x² + 7y². -/
theorem quadform_holds_118aa87a92 :
    ∀ p < 800, isPrimeB p = true → p % 7 = 1 → ∃ x < 29, ∃ y < 29, x * x + 7 * y * y = p :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- n² + 13n + 83 is prime for every n < 34. -/
theorem primepoly_holds_7d92b98ecb :
    ∀ n < 34, isPrimeB (n * n + 13 * n + 83) = true :=
  by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Refuted: n² + 13n + 83 is prime for every n < 35.  Counterexample: n = 34: 1681 is composite. -/
theorem primepoly_refute_75474dd4a0 :
    ¬ (∀ n < 35, isPrimeB (n * n + 13 * n + 83) = true) :=
  fun h => absurd (h 34 (by decide)) (by decide +kernel)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- every prime p < 800 with p ≡ 11 (mod 24) is of the form 2x² + 3y². -/
theorem quadform_holds_522bc5871d :
    ∀ p < 800, isPrimeB p = true → p % 24 = 11 → ∃ x < 21, ∃ y < 21, 2 * x * x + 3 * y * y = p :=
  by decide +kernel

end Discovery.Ledger

end
