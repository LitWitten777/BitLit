module

public import Mathlib
public import QBX.Notes.TwinPrimeConvergence

@[expose] public section

/-!
# Twin primes have density zero, and the tuple ladder is optimal

**Status: documentation note** (Lake library `QBXNotes`).  The twin prime conjecture is open and is
not proved here.  This file adds two *unconditional* results to the "convergence" picture of
`QBX.Notes.TwinPrimeConvergence`.

## 1. Twin primes have natural density zero (`twin_density_zero`)

Let `twinCountBelow N` be the number of primes `p < N` with `p + 2` prime.  Then
`twinCountBelow N / N → 0`.

The proof is the sieve of Eratosthenes–Legendre for the pair `(n, n + 2)`:

* for a finite set `S` of odd primes with product `M`, the residues `n mod M` for which no
  `p ∈ S` divides `n (n + 2)` number exactly `∏ (p - 2)` (`card_sifted`, by the Chinese remainder
  theorem, `card_filter_range_mul_coprime`, and the count `p - 2` for one prime,
  `card_avoid_two_residues`);
* every twin prime `p > M` survives the sieve, so
  `twinCountBelow N ≤ M + 1 + (N / M + 1) ∏ (p - 2)` (`twinCountBelow_le`);
* because `∑ 1/p` diverges (Mathlib: `Nat.Primes.not_summable_one_div`), the density
  `∏ (1 - 2/p) ≤ exp (-2 ∑ 1/p)` can be made as small as we like (`exists_sieve_small`).

This is much weaker than Brun's theorem (`π₂(x) ≪ x / log² x · (log log x)²`, so that
`∑ 1/p` over twin primes converges), which is not formalised here.  It is the first unconditional
"from above" statement in this development: whatever the truth of the conjecture, the twin primes
form a set of density zero.

## 2. The tuple ladder is optimal for `k = 3, 4, 5`

`boundedGaps_of_dhl` turns `DHL k 2` plus an admissible `k`-tuple of width `H` into
`BoundedGaps H`.  The rungs used in `TwinPrimeConvergence` (`H = 6` for `k = 3`, `H = 12` for
`k = 5`) and the new rung `H = 8` for `k = 4` (`boundedGaps_8_of_dhl`) are the best this method can
give: every admissible `k`-tuple fits in no window shorter than `6, 8, 12`
(`no_admissible_triple_width_lt_six`, `no_admissible_quadruple_width_lt_eight`,
`no_admissible_quintuple_width_lt_twelve`).  The finite checks are done by the kernel over all
`k`-subsets of the window, after a translation argument (`not_admissible_of_window`).
-/

namespace QBX.Notes.TwinPrime.Density

open Finset Filter Topology QBX.Notes.TwinPrime.Convergence

/-! ## Counting periodic sets -/

/-- A set of period `M` meets `[0, kM)` exactly `k` times as often as `[0, M)`. -/
theorem card_filter_range_mul_of_periodic {P : ℕ → Prop} [DecidablePred P] {M : ℕ}
    (hP : ∀ n, P (n + M) ↔ P n) (k : ℕ) :
    ((range (k * M)).filter P).card = k * ((range M).filter P).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : range ((k + 1) * M) = range (k * M) ∪ (range M).map (addLeftEmbedding (k * M)) := by
      rw [add_mul, one_mul, range_add]
    have hP' : ∀ j n, P (n + j * M) ↔ P n := by
      intro j; induction j with
      | zero => simp
      | succ j ihj => intro n; rw [add_mul, one_mul, ← add_assoc, hP, ihj]
    rw [hsplit, filter_union, card_union_of_disjoint, ih, filter_map, card_map]
    · rw [add_mul, one_mul]; congr 1
      congr 1; ext n; simp [Function.comp, add_comm (k * M) n, hP']
    · apply disjoint_filter_filter
      rw [disjoint_left]; intro a ha hb
      simp at ha hb; omega

/-- A set of period `M` meets `[0, N)` at most `(N / M + 1)` times as often as `[0, M)`. -/
theorem card_filter_range_le_of_periodic {P : ℕ → Prop} [DecidablePred P] {M : ℕ}
    (hM : 0 < M) (hP : ∀ n, P (n + M) ↔ P n) (N : ℕ) :
    ((range N).filter P).card ≤ (N / M + 1) * ((range M).filter P).card := by
  rw [← card_filter_range_mul_of_periodic hP]
  apply card_le_card
  apply filter_subset_filter
  apply range_subset_range.mpr
  have := Nat.lt_div_mul_add (a := N) hM
  nlinarith [Nat.div_add_mod N M, Nat.mod_lt N hM]

/-! ## The twin sieve -/

/-- The number of twin primes below `N`: primes `p < N` with `p + 2` also prime. -/
def twinCountBelow (N : ℕ) : ℕ :=
  ((range N).filter (fun p => p.Prime ∧ (p + 2).Prime)).card

/-- **Chinese remainder count:** for coprime `q, M`, conditions periodic modulo `q` and modulo
`M` are independent on `[0, qM)`. -/
theorem card_filter_range_mul_coprime {A B : ℕ → Prop} [DecidablePred A] [DecidablePred B]
    {q M : ℕ} (hq : 0 < q) (hM : 0 < M) (co : q.Coprime M)
    (hA : ∀ n, A n ↔ A (n % q)) (hB : ∀ n, B n ↔ B (n % M)) :
    ((range (q * M)).filter (fun n => A n ∧ B n)).card =
      ((range q).filter A).card * ((range M).filter B).card := by
  rw [← card_product]
  symm
  apply card_bij' (fun ab _ => (Nat.chineseRemainder co ab.1 ab.2 : ℕ)) (fun n _ => (n % q, n % M))
  · rintro ⟨a, b⟩ hab
    simp only [mem_product, mem_filter, mem_range] at hab ⊢
    have h1 := (Nat.chineseRemainder co a b).2.1
    have h2 := (Nat.chineseRemainder co a b).2.2
    refine ⟨Nat.chineseRemainder_lt_mul co a b hq.ne' hM.ne', ?_, ?_⟩
    · rw [hA, h1, Nat.mod_eq_of_lt hab.1.1]; exact hab.1.2
    · rw [hB, h2, Nat.mod_eq_of_lt hab.2.1]; exact hab.2.2
  · intro n hn
    simp only [mem_product, mem_filter, mem_range] at hn ⊢
    refine ⟨⟨Nat.mod_lt _ hq, (hA n).mp hn.2.1⟩, ⟨Nat.mod_lt _ hM, (hB n).mp hn.2.2⟩⟩
  · rintro ⟨a, b⟩ hab
    simp only [mem_product, mem_filter, mem_range] at hab
    have h1 := (Nat.chineseRemainder co a b).2.1
    have h2 := (Nat.chineseRemainder co a b).2.2
    simp only [Prod.mk.injEq]
    exact ⟨by rw [h1, Nat.mod_eq_of_lt hab.1.1], by rw [h2, Nat.mod_eq_of_lt hab.2.1]⟩
  · intro n hn
    simp only [mem_filter, mem_range] at hn
    have := Nat.chineseRemainder_modEq_unique co (a := n % q) (b := n % M) (z := n)
      (Nat.mod_modEq n q).symm (Nat.mod_modEq n M).symm
    have hlt := Nat.chineseRemainder_lt_mul co (n % q) (n % M) hq.ne' hM.ne'
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt hn.1, Nat.mod_eq_of_lt hlt] at this
    exact this.symm

/-- For `q ≥ 3`, exactly `q - 2` residues `n mod q` have `q ∤ n` and `q ∤ n + 2`. -/
theorem card_avoid_two_residues {q : ℕ} (h3 : 3 ≤ q) :
    ((range q).filter (fun n => ¬ q ∣ n ∧ ¬ q ∣ n + 2)).card = q - 2 := by
  have : (range q).filter (fun n => ¬ q ∣ n ∧ ¬ q ∣ n + 2) = (range q) \ {0, q - 2} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, h1, h2⟩
      refine ⟨hn, ?_⟩
      rintro (rfl | rfl)
      · exact h1 (dvd_zero q)
      · exact h2 (by rw [Nat.sub_add_cancel (by omega)])
    · rintro ⟨hn, hne⟩
      refine ⟨hn, fun h => hne (Or.inl ?_), fun h => hne (Or.inr ?_)⟩
      · exact Nat.eq_zero_of_dvd_of_lt h hn
      · obtain ⟨c, hc⟩ := h
        rcases c with _ | _ | c
        · omega
        · omega
        · nlinarith
  rw [this, card_sdiff_of_subset, card_range, card_insert_of_notMem, card_singleton]
  · simp; omega
  · intro x hx; simp at hx; simp; omega

/-- `n` survives the twin sieve by the primes in `S`: no `p ∈ S` divides `n` or `n + 2`. -/
def Sifted (S : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ S, ¬ p ∣ n ∧ ¬ p ∣ n + 2

instance (S : Finset ℕ) : DecidablePred (Sifted S) := fun n => by
  unfold Sifted; infer_instance

/-- Divisibility of `n + c` by a divisor `p` of `M` only depends on `n mod M`. -/
theorem dvd_add_iff_mod {p M : ℕ} (hp : p ∣ M) (n c : ℕ) : p ∣ n + c ↔ p ∣ n % M + c := by
  have hd : p ∣ M * (n / M) := Dvd.dvd.mul_right hp _
  conv_lhs => rw [← Nat.mod_add_div n M]
  rw [show n % M + M * (n / M) + c = (n % M + c) + M * (n / M) by ring]
  exact Nat.dvd_add_left hd

/-- Surviving the sieve only depends on `n` modulo any common multiple of the sieving primes. -/
theorem sifted_mod {S : Finset ℕ} {M : ℕ} (hM : ∀ p ∈ S, p ∣ M) (n : ℕ) :
    Sifted S n ↔ Sifted S (n % M) := by
  have key : ∀ p ∈ S, ∀ c, (p ∣ n + c ↔ p ∣ n % M + c) := fun p hp c =>
    dvd_add_iff_mod (hM p hp) n c
  unfold Sifted
  refine forall₂_congr fun p hp => ?_
  have h0 := key p hp 0
  simp only [add_zero] at h0
  rw [h0, key p hp 2]

/-- **The twin sieve count:** modulo `M = ∏_{p ∈ S} p` (odd primes), exactly `∏ (p - 2)`
residues survive. -/
theorem card_sifted (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p) :
    ((range (∏ p ∈ S, p)).filter (Sifted S)).card = ∏ p ∈ S, (p - 2) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [prod_empty, prod_empty, range_one,
      filter_true_of_mem (fun x _ p hp => absurd hp (notMem_empty p))]
    rfl
  | insert q S hqS ih =>
    have hq := hS q (mem_insert_self q S)
    have hS' : ∀ p ∈ S, p.Prime ∧ 3 ≤ p := fun p hp => hS p (mem_insert_of_mem hp)
    rw [prod_insert hqS, prod_insert hqS, ← ih hS', ← card_avoid_two_residues hq.2]
    have hMpos : 0 < ∏ p ∈ S, p := prod_pos fun p hp => (hS' p hp).1.pos
    have co : q.Coprime (∏ p ∈ S, p) := Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes hq.1 (hS' p hp).1).mpr (by rintro rfl; exact hqS hp)
    rw [← card_filter_range_mul_coprime hq.1.pos hMpos co]
    · congr 1
      apply filter_congr
      intro n _
      simp [Sifted]
    · intro n
      have h0 := dvd_add_iff_mod (dvd_refl q) n 0
      simp only [add_zero] at h0
      rw [h0, dvd_add_iff_mod (dvd_refl q) n 2]
    · exact sifted_mod (fun p hp => dvd_prod_of_mem _ hp)

/-! ## Density zero -/

/-- **Mertens-type smallness:** `∏ (1 - 2/p)` over a suitable finite set of odd primes is below
any `ε > 0`, since `∑ 1/p` diverges. -/
theorem exists_sieve_small {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ 3 ≤ p) ∧ ∏ p ∈ S, (((p : ℝ) - 2) / p) < ε := by
  set K : ℝ := 1 + (- Real.log ε) / 2
  obtain ⟨u, hu⟩ : ∃ u : Finset Nat.Primes, K < ∑ p ∈ u, 1 / ((p : ℕ) : ℝ) := by
    by_contra h
    push_neg at h
    exact Nat.Primes.not_summable_one_div
      (summable_of_sum_le (fun p => by positivity) h)
  set S := (u.map ⟨Subtype.val, Subtype.val_injective⟩).filter (· ≠ 2)
  have hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p := by
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk] at hp
    obtain ⟨⟨q, -, rfl⟩, hne⟩ := hp
    have := q.2.two_le
    exact ⟨q.2, by omega⟩
  refine ⟨S, hS, ?_⟩
  have hsum : K - 1 / 2 ≤ ∑ p ∈ S, 1 / (p : ℝ) := by
    have h1 : ∑ p ∈ u, 1 / ((p : ℕ) : ℝ) =
        ∑ p ∈ u.map ⟨Subtype.val, Subtype.val_injective⟩, 1 / (p : ℝ) := by
      rw [sum_map]; rfl
    have h2 := sum_filter_add_sum_filter_not (u.map ⟨Subtype.val, Subtype.val_injective⟩)
      (· ≠ 2) (fun p => 1 / (p : ℝ))
    have h3 : ∑ p ∈ (u.map ⟨Subtype.val, Subtype.val_injective⟩).filter (fun p => ¬ p ≠ 2),
        1 / (p : ℝ) ≤ 1 / 2 := by
      calc _ ≤ ∑ p ∈ ({2} : Finset ℕ), 1 / (p : ℝ) := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro x hx; simp at hx; simp [hx.2]
            · intros; positivity
        _ = 1 / 2 := by simp
    simp only [S]
    linarith
  calc ∏ p ∈ S, (((p : ℝ) - 2) / p) ≤ ∏ p ∈ S, Real.exp (-2 * (1 / (p : ℝ))) := by
        apply Finset.prod_le_prod
        · intro p hp
          have := (hS p hp).2
          have : (3 : ℝ) ≤ p := by exact_mod_cast this
          apply div_nonneg <;> linarith
        · intro p hp
          have h3 := (hS p hp).2
          have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
          have := Real.add_one_le_exp (-2 * (1 / (p : ℝ)))
          calc ((p : ℝ) - 2) / p = -2 * (1 / (p : ℝ)) + 1 := by field_simp; ring
            _ ≤ _ := this
    _ = Real.exp (-2 * ∑ p ∈ S, 1 / (p : ℝ)) := by rw [← Real.exp_sum, mul_sum]
    _ ≤ Real.exp (-2 * (K - 1 / 2)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = Real.exp (Real.log ε - 1) := by congr 1; simp only [K]; ring
    _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith)
    _ = ε := Real.exp_log hε

/-- **Sieve upper bound** for the twin prime count, for any finite set `S` of odd primes. -/
theorem twinCountBelow_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p) (N : ℕ) :
    twinCountBelow N ≤ (∏ p ∈ S, p) + 1 + (N / ∏ p ∈ S, p + 1) * ∏ p ∈ S, (p - 2) := by
  set M := ∏ p ∈ S, p
  have hMpos : 0 < M := prod_pos fun p hp => (hS p hp).1.pos
  have hle : ∀ q ∈ S, q ≤ M := fun q hq => Nat.le_of_dvd hMpos (dvd_prod_of_mem _ hq)
  have hsub : (range N).filter (fun p => p.Prime ∧ (p + 2).Prime) ⊆
      range (M + 1) ∪ (range N).filter (Sifted S) := by
    intro p hp
    simp only [mem_filter, mem_range, mem_union] at hp ⊢
    by_cases hpM : p < M + 1
    · exact Or.inl hpM
    · refine Or.inr ⟨hp.1, fun q hq => ⟨fun hd => ?_, fun hd => ?_⟩⟩
      · have := (Nat.prime_dvd_prime_iff_eq (hS q hq).1 hp.2.1).mp hd
        have := hle q hq; omega
      · have := (Nat.prime_dvd_prime_iff_eq (hS q hq).1 hp.2.2).mp hd
        have := hle q hq; omega
  have hper : ∀ n, Sifted S (n + M) ↔ Sifted S n := by
    intro n
    have hd : ∀ p ∈ S, p ∣ M := fun p hp => dvd_prod_of_mem _ hp
    rw [sifted_mod hd, Nat.add_mod_right, ← sifted_mod hd]
  calc twinCountBelow N ≤ (range (M + 1) ∪ (range N).filter (Sifted S)).card := card_le_card hsub
    _ ≤ (range (M + 1)).card + ((range N).filter (Sifted S)).card := card_union_le _ _
    _ ≤ M + 1 + (N / M + 1) * ((range M).filter (Sifted S)).card := by
        rw [card_range]
        exact Nat.add_le_add_left (card_filter_range_le_of_periodic hMpos hper N) _
    _ = _ := by rw [card_sifted S hS]

/-- **Twin primes have natural density zero:** `#{p < N : p, p + 2 prime} / N → 0`. -/
theorem twin_density_zero :
    Tendsto (fun N : ℕ => (twinCountBelow N : ℝ) / N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨S, hS, hρ⟩ := exists_sieve_small (half_pos hε)
  set M := ∏ p ∈ S, p
  set r := ∏ p ∈ S, (p - 2)
  have hMpos : 0 < M := prod_pos fun p hp => (hS p hp).1.pos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hrM : (r : ℝ) / M = ∏ p ∈ S, (((p : ℝ) - 2) / p) := by
    simp only [r, M, Nat.cast_prod]
    rw [← prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (by have := (hS p hp).2; omega)]
    norm_num
  set C : ℝ := M + 1 + r
  obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * C / ε)
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN0' : (N0 : ℝ) + 1 ≤ N := by exact_mod_cast hN
  have hC : C < ε / 2 * N := by
    have : 2 * C / ε < N := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  have hb := twinCountBelow_le S hS N
  have hdiv : ((N / M : ℕ) : ℝ) * M ≤ N := by exact_mod_cast Nat.div_mul_le_self N M
  have hcount : (twinCountBelow N : ℝ) ≤ C + ((N / M : ℕ) : ℝ) * r := by
    have : (twinCountBelow N : ℝ) ≤ ((M + 1 + (N / M + 1) * r : ℕ) : ℝ) := by exact_mod_cast hb
    push_cast at this
    simp only [C]; linarith
  have hq : ((N / M : ℕ) : ℝ) * r ≤ N * (r / M) := by
    rw [mul_div_assoc', le_div_iff₀ hMR]
    have hr : (0 : ℝ) ≤ r := by positivity
    nlinarith
  have hpos : (0 : ℝ) ≤ twinCountBelow N / N := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos, div_lt_iff₀ hNpos]
  rw [hrM] at hq
  nlinarith

/-! ## Optimality of the tuple ladder -/

/-- A prime `p` all of whose residues are hit by the tuple witnesses non-admissibility. -/
theorem not_admissible_of_cover {hs : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (h : ∀ r ∈ range p, ∃ x ∈ hs, p ∣ r + x) : ¬ Admissible hs := by
  intro had
  obtain ⟨r, hr⟩ := had p hp
  obtain ⟨x, hx, hd⟩ := h (r % p) (mem_range.mpr (Nat.mod_lt _ hp.pos))
  exact hr x hx ((dvd_add_iff_mod (dvd_refl p) r x).mpr hd)

/-- Admissibility is invariant under translation (the direction needed below). -/
theorem admissible_of_shift {hs : Finset ℕ} {a : ℕ} (h : Admissible (hs.image (· + a))) :
    Admissible hs := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  exact ⟨r + a, fun x hx hd => hr (x + a) (mem_image_of_mem _ hx) (by
    rw [← add_assoc, add_right_comm]; exact hd)⟩

/-- If no `k`-subset of `[0, w)` is admissible, then no `k`-tuple inside any window
`[m, m + w)` is admissible. -/
theorem not_admissible_of_window {k w : ℕ}
    (hcov : ∀ t ∈ (range w).powersetCard k, ¬ Admissible t)
    {hs : Finset ℕ} (hk : hs.card = k) {m : ℕ} (hwin : ∀ x ∈ hs, m ≤ x ∧ x < m + w) :
    ¬ Admissible hs := by
  intro had
  set t := hs.image (· - m)
  have hinj : Set.InjOn (· - m) (hs : Set ℕ) := by
    intro x hx y hy hxy
    have := (hwin x hx).1; have := (hwin y hy).1
    simp only at hxy; omega
  have ht : t ∈ (range w).powersetCard k := by
    rw [mem_powersetCard]
    refine ⟨fun y hy => ?_, by rw [card_image_of_injOn hinj, hk]⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    have := hwin x hx
    rw [mem_range]; omega
  have heq : t.image (· + m) = hs := by
    rw [image_image]
    conv_rhs => rw [← image_id (s := hs)]
    apply image_congr
    intro x hx
    have := (hwin x hx).1
    simp only [Function.comp, id]; omega
  exact hcov t ht (admissible_of_shift (heq ▸ had))

/-- A decidable certificate for `not_admissible_of_window`: every `k`-subset of `[0, w)` is
covered by some prime `p ≤ k`. -/
theorem cover_check {k w : ℕ}
    (h : ∀ t ∈ (range w).powersetCard k, ∃ p ∈ range (k + 1), p.Prime ∧
      ∀ r ∈ range p, ∃ x ∈ t, p ∣ r + x) :
    ∀ t ∈ (range w).powersetCard k, ¬ Admissible t := by
  intro t ht
  obtain ⟨p, -, hp, hc⟩ := h t ht
  exact not_admissible_of_cover hp hc

/-- No admissible triple fits in a window of length `6` (so `{0, 2, 6}` is optimal). -/
theorem no_admissible_triple_width_lt_six {hs : Finset ℕ} (hk : hs.card = 3) {m : ℕ}
    (hwin : ∀ x ∈ hs, m ≤ x ∧ x < m + 6) : ¬ Admissible hs :=
  not_admissible_of_window (cover_check (by decide)) hk hwin

/-- No admissible quadruple fits in a window of length `8` (so `{0, 2, 6, 8}` is optimal). -/
theorem no_admissible_quadruple_width_lt_eight {hs : Finset ℕ} (hk : hs.card = 4) {m : ℕ}
    (hwin : ∀ x ∈ hs, m ≤ x ∧ x < m + 8) : ¬ Admissible hs :=
  not_admissible_of_window (cover_check (by decide)) hk hwin

/-- No admissible quintuple fits in a window of length `12` (so `{0, 2, 6, 8, 12}` is
optimal). -/
theorem no_admissible_quintuple_width_lt_twelve {hs : Finset ℕ} (hk : hs.card = 5) {m : ℕ}
    (hwin : ∀ x ∈ hs, m ≤ x ∧ x < m + 12) : ¬ Admissible hs :=
  not_admissible_of_window (cover_check (by decide +kernel)) hk hwin

/-- The prime-quadruplet pattern `{0, 2, 6, 8}` is admissible. -/
theorem admissible_zero_two_six_eight : Admissible {0, 2, 6, 8} :=
  admissible_of_small (by decide +kernel)

/-- **Rung 8** from `DHL 4 2`, using the admissible quadruple `{0, 2, 6, 8}` (prime quadruplets). -/
theorem boundedGaps_8_of_dhl (hd : DHL 4 2) : BoundedGaps 8 :=
  boundedGaps_of_dhl hd (by decide) admissible_zero_two_six_eight (by decide)

/-- **The tuple ladder is optimal for `k = 3, 4, 5`.**  For each `k` the width `6, 8, 12` is
attained by an admissible tuple, and no admissible `k`-tuple fits in a shorter window.  So the
rungs `BoundedGaps 6`, `BoundedGaps 8`, `BoundedGaps 12` are the best that `DHL k 2` can give
through `boundedGaps_of_dhl`. -/
theorem tuple_ladder_optimal :
    (Admissible {0, 2, 6} ∧ ∀ hs : Finset ℕ, hs.card = 3 → ∀ m,
        (∀ x ∈ hs, m ≤ x ∧ x < m + 6) → ¬ Admissible hs) ∧
    (Admissible {0, 2, 6, 8} ∧ ∀ hs : Finset ℕ, hs.card = 4 → ∀ m,
        (∀ x ∈ hs, m ≤ x ∧ x < m + 8) → ¬ Admissible hs) ∧
    (Admissible {0, 2, 6, 8, 12} ∧ ∀ hs : Finset ℕ, hs.card = 5 → ∀ m,
        (∀ x ∈ hs, m ≤ x ∧ x < m + 12) → ¬ Admissible hs) :=
  ⟨⟨admissible_zero_two_six, fun _ hk _ hw => no_admissible_triple_width_lt_six hk hw⟩,
   ⟨admissible_zero_two_six_eight, fun _ hk _ hw => no_admissible_quadruple_width_lt_eight hk hw⟩,
   ⟨admissible_ehTuple, fun _ hk _ hw => no_admissible_quintuple_width_lt_twelve hk hw⟩⟩

end QBX.Notes.TwinPrime.Density
