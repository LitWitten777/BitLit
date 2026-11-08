module

public import Mathlib

@[expose] public section

/-!
# Twin primes and the four quadratic "generators" of non-twin centres

**Status: documentation note, not a theorem of the core corpus** (Lake library `QBXNotes`).
The reformulation below is exact, and it does not touch the conjecture: it is kept as a precise
record of what "generators for twin primes" amounts to, not as progress.

Every twin-prime pair other than `(3, 5)` has the form `(6k - 1, 6k + 1)`.  Call `k` a
*twin centre* when both numbers are prime.  The composites among `6k ± 1` are products of two
numbers `≡ ±1 (mod 6)`, and multiplying out gives four quadratic *generator families*

* `k = 6ab + a + b`  (`6k + 1 = (6a + 1)(6b + 1)`),
* `k = 6ab - a - b`  (`6k + 1 = (6a - 1)(6b - 1)`),
* `k = 6ab + a - b`  (`6k - 1 = (6a - 1)(6b + 1)`),
* `k = 6ab - a + b`  (`6k - 1 = (6a + 1)(6b - 1)`),

with `a, b ≥ 1`.  The main results:

* `QBX.Notes.TwinPrime.isTwinCentre_iff`: for `k ≥ 1`, `k` is a twin centre iff `k` is produced
  by none of the four generator families;
* `QBX.Notes.TwinPrime.twinPrimeConjecture_iff`: the twin prime conjecture (infinitely many
  `p` with `p` and `p + 2` prime) holds iff infinitely many `k ≥ 1` escape all four generators.

This is an exact *reformulation*, not progress on the conjecture: it moves the problem into a
statement about the complement of the union of four quadratic value sets, which is still open.
It is the precise content of "using generators to attack twin primes" that can be checked; see
`QBX/docs/design/BRAID_BIOLOGY_STEIN_TWIN.md` §5.
-/

namespace QBX.Notes.TwinPrime

/-- `k` is a twin centre: `6k - 1` and `6k + 1` are both prime. -/
def IsTwinCentre (k : ℕ) : Prop := (6 * k - 1).Prime ∧ (6 * k + 1).Prime

/-- `k` is produced by one of the four quadratic generator families (computed in `ℤ`, so that
`6ab - a - b` is never truncated). -/
def SieveGenerated (k : ℕ) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
    ((k : ℤ) = 6 * a * b + a + b ∨ (k : ℤ) = 6 * a * b - a - b ∨
     (k : ℤ) = 6 * a * b + a - b ∨ (k : ℤ) = 6 * a * b - a + b)

/-- The twin prime conjecture. -/
def TwinPrimeConjecture : Prop := Set.Infinite {p : ℕ | p.Prime ∧ (p + 2).Prime}

/-- A number `n ≥ 2` coprime to `6` is `6a ± 1` with `a ≥ 1`. -/
theorem eq_six_mul_add_or_sub {n : ℕ} (hn : 2 ≤ n) (h2 : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    ∃ a : ℕ, 1 ≤ a ∧ ((n : ℤ) = 6 * a + 1 ∨ (n : ℤ) = 6 * a - 1) := by
  have h : n % 6 = 1 ∨ n % 6 = 5 := by omega
  rcases h with h | h
  · exact ⟨n / 6, by omega, Or.inl (by omega)⟩
  · exact ⟨n / 6 + 1, by omega, Or.inr (by push_cast; omega)⟩

/-- A composite `m ≥ 2` splits as `p * q` with `2 ≤ p` and `2 ≤ q`. -/
theorem exists_factor_of_not_prime {m : ℕ} (hm : 2 ≤ m) (hp : ¬ m.Prime) :
    ∃ p q, 2 ≤ p ∧ 2 ≤ q ∧ m = p * q := by
  refine ⟨m.minFac, m / m.minFac, ?_, ?_, (Nat.mul_div_cancel' (Nat.minFac_dvd m)).symm⟩
  · exact (Nat.minFac_prime (by omega)).two_le
  · have hlt : m.minFac < m := by
      rcases Nat.lt_or_ge m.minFac m with h | h
      · exact h
      · exact absurd (Nat.prime_def_minFac.mpr ⟨hm, le_antisymm (Nat.minFac_le (by omega)) h⟩) hp
    have hpos := Nat.minFac_pos m
    have hd := Nat.mul_div_cancel' (Nat.minFac_dvd m)
    by_contra hq
    push_neg at hq
    interval_cases h : m / m.minFac
    · omega
    · omega

/-- Generated ⇒ not a twin centre (one of `6k ± 1` factors non-trivially). -/
theorem not_isTwinCentre_of_generated {k : ℕ} (h : SieveGenerated k) : ¬ IsTwinCentre k := by
  rintro ⟨hm, hp⟩
  obtain ⟨a, b, ha, hb, h | h | h | h⟩ := h
  · -- 6k + 1 = (6a+1)(6b+1)
    have he : 6 * k + 1 = (6 * a + 1) * (6 * b + 1) := by zify; rw [h]; ring
    rw [he] at hp
    have := (Nat.prime_mul_iff.mp hp)
    omega
  · -- 6k + 1 = (6a-1)(6b-1)
    have he : 6 * k + 1 = (6 * a - 1) * (6 * b - 1) := by
      zify [show 1 ≤ 6 * a by omega, show 1 ≤ 6 * b by omega]; rw [h]; ring
    rw [he] at hp
    have := (Nat.prime_mul_iff.mp hp)
    omega
  · -- 6k - 1 = (6a-1)(6b+1)
    have hk : 1 ≤ 6 * k := by
      have : (1 : ℤ) ≤ 6 * k := by rw [h]; nlinarith
      exact_mod_cast this
    have he : 6 * k - 1 = (6 * a - 1) * (6 * b + 1) := by
      zify [hk, show 1 ≤ 6 * a by omega]; rw [h]; ring
    rw [he] at hm
    have := (Nat.prime_mul_iff.mp hm)
    omega
  · -- 6k - 1 = (6a+1)(6b-1)
    have hk : 1 ≤ 6 * k := by
      have : (1 : ℤ) ≤ 6 * k := by rw [h]; nlinarith
      exact_mod_cast this
    have he : 6 * k - 1 = (6 * a + 1) * (6 * b - 1) := by
      zify [hk, show 1 ≤ 6 * b by omega]; rw [h]; ring
    rw [he] at hm
    have := (Nat.prime_mul_iff.mp hm)
    omega

/-- Not a twin centre ⇒ generated (for `k ≥ 1`). -/
theorem generated_of_not_isTwinCentre {k : ℕ} (hk : 1 ≤ k) (h : ¬ IsTwinCentre k) :
    SieveGenerated k := by
  unfold IsTwinCentre at h
  rw [not_and_or] at h
  rcases h with h | h
  · -- 6k - 1 composite
    obtain ⟨p, q, hp, hq, he⟩ := exists_factor_of_not_prime (by omega) h
    have hp2 : ¬ 2 ∣ p := fun hd => by
      have : 2 ∣ 6 * k - 1 := he ▸ Dvd.dvd.mul_right hd q
      omega
    have hp3 : ¬ 3 ∣ p := fun hd => by
      have : 3 ∣ 6 * k - 1 := he ▸ Dvd.dvd.mul_right hd q
      omega
    have hq2 : ¬ 2 ∣ q := fun hd => by
      have : 2 ∣ 6 * k - 1 := he ▸ Dvd.dvd.mul_left hd p
      omega
    have hq3 : ¬ 3 ∣ q := fun hd => by
      have : 3 ∣ 6 * k - 1 := he ▸ Dvd.dvd.mul_left hd p
      omega
    obtain ⟨a, ha, hpa⟩ := eq_six_mul_add_or_sub hp hp2 hp3
    obtain ⟨b, hb, hqb⟩ := eq_six_mul_add_or_sub hq hq2 hq3
    have hz : (6 * k : ℤ) - 1 = (p : ℤ) * q := by
      have : ((6 * k - 1 : ℕ) : ℤ) = ((p * q : ℕ) : ℤ) := by rw [he]
      push_cast [show 1 ≤ 6 * k by omega] at this
      exact this
    refine ⟨a, b, ha, hb, ?_⟩
    rcases hpa with hpa | hpa <;> rcases hqb with hqb | hqb <;> rw [hpa, hqb] at hz
    · exfalso
      have h6 : (6 : ℤ) * ((k : ℤ) - 6 * a * b - a - b) = 2 := by linear_combination hz
      generalize (k : ℤ) - 6 * a * b - a - b = t at h6
      omega
    · right; right; right; linarith
    · right; right; left; linarith
    · exfalso
      have h6 : (6 : ℤ) * ((k : ℤ) - 6 * a * b + a + b) = 2 := by linear_combination hz
      generalize (k : ℤ) - 6 * a * b + a + b = t at h6
      omega
  · -- 6k + 1 composite
    obtain ⟨p, q, hp, hq, he⟩ := exists_factor_of_not_prime (by omega) h
    have hp2 : ¬ 2 ∣ p := fun hd => by
      have : 2 ∣ 6 * k + 1 := he ▸ Dvd.dvd.mul_right hd q
      omega
    have hp3 : ¬ 3 ∣ p := fun hd => by
      have : 3 ∣ 6 * k + 1 := he ▸ Dvd.dvd.mul_right hd q
      omega
    have hq2 : ¬ 2 ∣ q := fun hd => by
      have : 2 ∣ 6 * k + 1 := he ▸ Dvd.dvd.mul_left hd p
      omega
    have hq3 : ¬ 3 ∣ q := fun hd => by
      have : 3 ∣ 6 * k + 1 := he ▸ Dvd.dvd.mul_left hd p
      omega
    obtain ⟨a, ha, hpa⟩ := eq_six_mul_add_or_sub hp hp2 hp3
    obtain ⟨b, hb, hqb⟩ := eq_six_mul_add_or_sub hq hq2 hq3
    have hz : (6 * k : ℤ) + 1 = (p : ℤ) * q := by exact_mod_cast he
    refine ⟨a, b, ha, hb, ?_⟩
    rcases hpa with hpa | hpa <;> rcases hqb with hqb | hqb <;> rw [hpa, hqb] at hz
    · left; linarith
    · exfalso
      have h6 : (6 : ℤ) * ((k : ℤ) - 6 * a * b + a - b) = -2 := by linear_combination hz
      generalize (k : ℤ) - 6 * a * b + a - b = t at h6
      omega
    · exfalso
      have h6 : (6 : ℤ) * ((k : ℤ) - 6 * a * b - a + b) = -2 := by linear_combination hz
      generalize (k : ℤ) - 6 * a * b - a + b = t at h6
      omega
    · right; left; linarith

/-- **Generator characterisation of twin centres.** -/
theorem isTwinCentre_iff {k : ℕ} (hk : 1 ≤ k) : IsTwinCentre k ↔ ¬ SieveGenerated k :=
  ⟨fun h hg => not_isTwinCentre_of_generated hg h,
   fun h => by by_contra h'; exact h (generated_of_not_isTwinCentre hk h')⟩

/-- Every twin pair with `p ≥ 5` is centred on a multiple of `6`. -/
theorem six_dvd_succ_of_twin {p : ℕ} (hp : p.Prime) (hp2 : (p + 2).Prime) (h5 : 5 ≤ p) :
    6 ∣ p + 1 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h; omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h; omega
  have h3' : ¬ 3 ∣ p + 2 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp2).mp h; omega
  have h6 := Nat.mod_add_div p 6
  have hlt := Nat.mod_lt p (show 6 > 0 by norm_num)
  generalize p % 6 = r at h6 hlt
  generalize p / 6 = q at h6
  subst h6
  interval_cases r <;> omega

/-- The lower twin primes `≥ 5` are exactly the numbers `6k - 1` with `k ≥ 1` a twin centre. -/
theorem twins_eq_image :
    {p : ℕ | p.Prime ∧ (p + 2).Prime} \ {3} =
      (fun k => 6 * k - 1) '' {k : ℕ | 1 ≤ k ∧ IsTwinCentre k} := by
  ext p
  simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_image]
  constructor
  · rintro ⟨⟨hp, hp2⟩, h3⟩
    have h5 : 5 ≤ p := by
      have := hp.two_le
      rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
      · subst h; norm_num at hp2
      · exact absurd h h3
      · subst h; norm_num at hp
      · exact h
    obtain ⟨k, hk⟩ := six_dvd_succ_of_twin hp hp2 h5
    refine ⟨k, ⟨by omega, ?_, ?_⟩, by omega⟩
    · rw [show 6 * k - 1 = p by omega]; exact hp
    · rw [show 6 * k + 1 = p + 2 by omega]; exact hp2
  · rintro ⟨k, ⟨hk, hm, hp⟩, rfl⟩
    refine ⟨⟨hm, ?_⟩, by omega⟩
    rw [show 6 * k - 1 + 2 = 6 * k + 1 by omega]; exact hp

/-- **Twin prime conjecture ⇔ infinitely many `k` escape the four generators.** -/
theorem twinPrimeConjecture_iff :
    TwinPrimeConjecture ↔ Set.Infinite {k : ℕ | 1 ≤ k ∧ ¬ SieveGenerated k} := by
  have hset : {k : ℕ | 1 ≤ k ∧ ¬ SieveGenerated k} = {k : ℕ | 1 ≤ k ∧ IsTwinCentre k} := by
    ext k
    simp only [Set.mem_setOf_eq]
    exact ⟨fun ⟨hk, h⟩ => ⟨hk, (isTwinCentre_iff hk).mpr h⟩,
      fun ⟨hk, h⟩ => ⟨hk, (isTwinCentre_iff hk).mp h⟩⟩
  have hinj : Set.InjOn (fun k : ℕ => 6 * k - 1) {k : ℕ | 1 ≤ k ∧ IsTwinCentre k} := by
    intro x hx y hy hxy
    simp only [Set.mem_setOf_eq] at hx hy hxy
    omega
  rw [hset, ← Set.infinite_image_iff hinj, ← twins_eq_image, TwinPrimeConjecture]
  exact ⟨fun h => h.diff (Set.finite_singleton 3),
    fun h hf => h (hf.subset Set.diff_subset)⟩

/-! ### Small checks -/

/-- `k = 1, 2, 3, 5, 7, 10` are twin centres: `(5,7), (11,13), (17,19), (29,31), (41,43),
(59,61)`. -/
theorem small_centres : IsTwinCentre 1 ∧ IsTwinCentre 2 ∧ IsTwinCentre 3 ∧ IsTwinCentre 5 ∧
    IsTwinCentre 7 ∧ IsTwinCentre 10 := by
  unfold IsTwinCentre; norm_num

/-- `k = 4` and `k = 6` are generated: `4 = 6·1·1 - 1 - 1` (`25 = 5·5`) and
`6 = 6·1·1 + 1 - 1` (`35 = 5·7`). -/
theorem small_generated : SieveGenerated 4 ∧ SieveGenerated 6 :=
  ⟨⟨1, 1, le_rfl, le_rfl, by norm_num⟩, ⟨1, 1, le_rfl, le_rfl, by norm_num⟩⟩

end QBX.Notes.TwinPrime
