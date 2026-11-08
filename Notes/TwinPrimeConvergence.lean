module

public import Mathlib
public import QBX.Notes.TwinPrimeSieve

@[expose] public section

/-!
# Twin primes as the meeting point of several conjectures

**Status: documentation note** (Lake library `QBXNotes`).  Nothing here proves the twin prime
conjecture, which is open.  What *is* proved is the web of implications between the standard
conjectures and partial results around it, so that a "convergence" strategy can be stated
precisely: which hypotheses would each be enough, and which combinations of weaker statements
would close the gap.

## The objects

* `gapSpectrum` — the set of `h` such that `p` and `p + h` are both prime for infinitely many `p`.
  The twin prime conjecture is `2 ∈ gapSpectrum` (`tpc_iff_two_mem_gapSpectrum`); Polignac's
  conjecture is "every positive even number is in it".
* `BoundedGaps H` — infinitely many primes `p` have another prime in `(p, p + H]`.  Zhang (2013),
  Maynard (2015) and Polymath 8b proved `BoundedGaps 246`; those theorems are **not** in Mathlib and
  appear here only as hypotheses.
* `Admissible hs` — the shifts `hs` avoid some residue class modulo every prime.
* `PrimeTuplesConjecture`, `DicksonConjecture`, `SchinzelH` — the classical "all forms prime
  simultaneously" conjectures.
* `DHL k m` — the Dickson–Hardy–Littlewood statement used by Maynard and Tao: every admissible
  `k`-tuple has at least `m` primes among its translates infinitely often.  Maynard and Polymath
  proved `DHL 50 2` (again: not in Mathlib, hypothesis only).
* `HardyLittlewoodTwin C` — the twin prime counting function is asymptotic to `C x / log² x`.

## What is proved (no `sorry`)

**From above (strong conjectures, each implies TPC):**
`schinzel_implies_primeTuples`, `dickson_implies_primeTuples`, `primeTuples_implies_polignac`,
`polignac_implies_tpc`, `hardyLittlewood_implies_tpc` (for any constant `C > 0`).

**From below (the bounded-gap ladder):** `BoundedGaps` is monotone (`boundedGaps_mono`), fails for
`H ≤ 1` (`not_boundedGaps_one`), and its bottom rung *is* the conjecture:
`tpc_iff_boundedGaps_two`.  Every rung pins down a concrete even gap that occurs infinitely often
(`exists_even_gap_of_boundedGaps`); in particular `polymath_consequence` turns `BoundedGaps 246`
into "some even `h ≤ 246` lies in the gap spectrum".

**Tuples:** a non-admissible tuple is prime only finitely often
(`finite_of_not_admissible`, e.g. `prime_triplets_eq` : `p, p+2, p+4` prime only for `p = 3`), and
an admissible tuple that has two primes infinitely often produces a gap in the spectrum
(`gap_of_tuple`).  `DHL 2 2` is exactly Polignac's conjecture (`dhl_two_two_iff_polignac`), and
`DHL 3 2` already forces one of the gaps `2, 4, 6` (`dhl_three_two_gap`).

**The DHL ladder:** with kernel-checked admissible tuples, `DHL 50 2` (Maynard–Polymath)
gives `BoundedGaps 246` (`boundedGaps_246_of_dhl`, using the explicit 50-tuple `polymathTuple`
of diameter 246), `DHL 5 2` (Elliott–Halberstam) gives `BoundedGaps 12`, `DHL 3 2` (generalised
EH) gives `BoundedGaps 6`, and `DHL 2 2` is Polignac.  `admissible_of_small` reduces admissibility
to the primes `p ≤ |hs|`.

**Counting:** TPC holds iff `π₂` is unbounded (`tpc_iff_twinCount_unbounded`).

**Convergence:** `tpc_of_boundedGaps_of_exclusion` — a bounded-gap theorem with bound `H`,
together with the exclusion of every even gap `4 ≤ h ≤ H` from the spectrum, gives the twin prime
conjecture.  This is the precise shape of a "squeeze" argument; the second ingredient is open for
every `H ≥ 4`.  `convergence_web` collects every arrow into one statement.
-/

namespace QBX.Notes.TwinPrime.Convergence

open QBX.Notes.TwinPrime Filter Topology

/-! ## The gap spectrum -/

/-- The primes `p` such that `p + h` is also prime. -/
def PairSet (h : ℕ) : Set ℕ := {p | p.Prime ∧ (p + h).Prime}

/-- The gaps `h` that occur infinitely often between (not necessarily consecutive) primes. -/
def gapSpectrum : Set ℕ := {h | (PairSet h).Infinite}

/-- Polignac's conjecture: every positive even number is a prime gap infinitely often. -/
def Polignac : Prop := ∀ k, 1 ≤ k → 2 * k ∈ gapSpectrum

/-- **The twin prime conjecture is `2 ∈ gapSpectrum`.** -/
theorem tpc_iff_two_mem_gapSpectrum : TwinPrimeConjecture ↔ 2 ∈ gapSpectrum := Iff.rfl

theorem polignac_implies_tpc : Polignac → TwinPrimeConjecture := fun h => by
  simpa using h 1 le_rfl

/-- `0` is in the spectrum (Euclid). -/
theorem zero_mem_gapSpectrum : 0 ∈ gapSpectrum := by
  simpa [gapSpectrum, PairSet] using Nat.infinite_setOf_prime

/-- Odd gaps occur at most once (one of `p`, `p + h` is even), so the spectrum is even. -/
theorem even_of_mem_gapSpectrum {h : ℕ} (hh : h ∈ gapSpectrum) : Even h := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  apply hh
  refine (Set.finite_Iic 2).subset ?_
  rintro p ⟨hp, hph⟩
  simp only [Set.mem_Iic]
  rcases Nat.even_or_odd p with he | ho
  · have := (Nat.Prime.even_iff hp).mp he; omega
  · have := (Nat.Prime.even_iff hph).mp (ho.add_odd hodd); omega

/-! ## The bounded-gap ladder -/

/-- `BoundedGaps H`: infinitely many primes `p` have another prime in `(p, p + H]`. -/
def BoundedGaps (H : ℕ) : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ ∃ q, q.Prime ∧ p < q ∧ q ≤ p + H}

theorem boundedGaps_mono {H H' : ℕ} (hle : H ≤ H') (h : BoundedGaps H) : BoundedGaps H' := by
  refine h.mono ?_
  rintro p ⟨hp, q, hq, hpq, hqH⟩
  exact ⟨hp, q, hq, hpq, by omega⟩

/-- A gap `h ≥ 1` in the spectrum gives the rung `BoundedGaps h`. -/
theorem boundedGaps_of_mem_gapSpectrum {h : ℕ} (h1 : 1 ≤ h) (hh : h ∈ gapSpectrum) :
    BoundedGaps h := by
  refine Set.Infinite.mono ?_ hh
  rintro p ⟨hp, hph⟩
  exact ⟨hp, p + h, hph, by omega, le_rfl⟩

/-- The ladder has no rung below `2`: only `p = 2` has a prime at distance `1`. -/
theorem not_boundedGaps_one : ¬ BoundedGaps 1 := by
  intro hb
  apply hb
  refine (Set.finite_singleton 2).subset ?_
  rintro p ⟨hp, q, hq, hpq, hq1⟩
  obtain rfl : q = p + 1 := by omega
  rcases Nat.even_or_odd p with he | ho
  · exact (Nat.Prime.even_iff hp).mp he
  · have := (Nat.Prime.even_iff hq).mp ho.add_one
    have := hp.two_le
    omega

/-- **The bottom rung of the ladder is the twin prime conjecture.** -/
theorem tpc_iff_boundedGaps_two : TwinPrimeConjecture ↔ BoundedGaps 2 := by
  constructor
  · exact boundedGaps_of_mem_gapSpectrum (by norm_num)
  · intro hb
    unfold BoundedGaps at hb
    refine (hb.diff (Set.finite_singleton 2)).mono ?_
    rintro p ⟨⟨hp, q, hq, hpq, hq2⟩, hp2⟩
    simp only [Set.mem_singleton_iff] at hp2
    refine ⟨hp, ?_⟩
    rcases (show q = p + 1 ∨ q = p + 2 by omega) with rfl | rfl
    · exfalso
      rcases Nat.even_or_odd p with he | ho
      · exact hp2 ((Nat.Prime.even_iff hp).mp he)
      · have := (Nat.Prime.even_iff hq).mp ho.add_one
        have := hp.two_le
        omega
    · exact hq

/-- **Pigeonhole:** a rung `BoundedGaps H` pins down one specific gap `1 ≤ h ≤ H` that occurs
infinitely often. -/
theorem exists_gap_of_boundedGaps {H : ℕ} (hb : BoundedGaps H) :
    ∃ h, 1 ≤ h ∧ h ≤ H ∧ h ∈ gapSpectrum := by
  by_contra hne
  push_neg at hne
  apply hb
  have hfin : (⋃ h ∈ Set.Icc 1 H, PairSet h).Finite :=
    Set.Finite.biUnion (Set.finite_Icc 1 H) fun h hm =>
      Set.not_infinite.mp (hne h hm.1 hm.2)
  refine hfin.subset ?_
  rintro p ⟨hp, q, hq, hpq, hqH⟩
  simp only [Set.mem_iUnion]
  exact ⟨q - p, ⟨by omega, by omega⟩, hp, by rwa [show p + (q - p) = q by omega]⟩

/-- The gap found by the pigeonhole is even, so it is at least `2`. -/
theorem exists_even_gap_of_boundedGaps {H : ℕ} (hb : BoundedGaps H) :
    ∃ h, Even h ∧ 2 ≤ h ∧ h ≤ H ∧ h ∈ gapSpectrum := by
  obtain ⟨h, h1, hH, hm⟩ := exists_gap_of_boundedGaps hb
  have he := even_of_mem_gapSpectrum hm
  refine ⟨h, he, ?_, hH, hm⟩
  obtain ⟨r, rfl⟩ := he
  omega

/-- **Polymath 8b, as a hypothesis.**  The bounded-gap theorem with `H = 246` (proved by
Maynard and Polymath, not formalised in Mathlib) yields an explicit even gap `≤ 246` that occurs
infinitely often. -/
theorem polymath_consequence (h246 : BoundedGaps 246) :
    ∃ h, Even h ∧ 2 ≤ h ∧ h ≤ 246 ∧ h ∈ gapSpectrum :=
  exists_even_gap_of_boundedGaps h246

/-- **Convergence from below.**  A bounded-gap theorem with bound `H`, together with the
exclusion of every gap `4 ≤ h ≤ H` from the spectrum, forces the twin prime conjecture. -/
theorem tpc_of_boundedGaps_of_exclusion {H : ℕ} (hb : BoundedGaps H)
    (hex : ∀ h, 4 ≤ h → h ≤ H → h ∉ gapSpectrum) : TwinPrimeConjecture := by
  obtain ⟨h, he, h2, hH, hm⟩ := exists_even_gap_of_boundedGaps hb
  rcases (show h = 2 ∨ h = 3 ∨ 4 ≤ h by omega) with rfl | rfl | h4
  · exact hm
  · exact absurd he (by decide)
  · exact absurd hm (hex h h4 hH)

/-! ## Admissible tuples -/

/-- A finite set of shifts is admissible if, modulo every prime, it misses some residue class. -/
def Admissible (hs : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ h ∈ hs, ¬ p ∣ r + h

/-- The `n` for which every translate `n + h`, `h ∈ hs`, is prime. -/
def TupleSet (hs : Finset ℕ) : Set ℕ := {n | ∀ h ∈ hs, (n + h).Prime}

/-- **A non-admissible tuple is prime only finitely often**: some prime divides one of the
translates of every `n`, so that translate must equal the prime. -/
theorem finite_of_not_admissible {hs : Finset ℕ} (hna : ¬ Admissible hs) :
    (TupleSet hs).Finite := by
  unfold Admissible at hna
  push_neg at hna
  obtain ⟨p, hp, hcov⟩ := hna
  refine (Set.finite_Iic p).subset ?_
  intro n hn
  obtain ⟨h, hh, hdvd⟩ := hcov n
  have := (Nat.prime_dvd_prime_iff_eq hp (hn h hh)).mp hdvd
  simp only [Set.mem_Iic]
  omega

/-- `p, p + 2, p + 4` are all prime only for `p = 3` (the tuple `{0, 2, 4}` covers every residue
modulo `3`). -/
theorem prime_triplets_eq : TupleSet {0, 2, 4} = {3} := by
  ext n
  simp only [TupleSet, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Set.mem_setOf_eq, Set.mem_singleton_iff, add_zero]
  constructor
  · rintro ⟨h0, h2, h4⟩
    rcases (show 3 ∣ n ∨ 3 ∣ n + 2 ∨ 3 ∣ n + 4 by omega) with h | h | h
    · exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h0).mp h).symm
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h2).mp h
      obtain rfl : n = 1 := by omega
      exact absurd h0 Nat.not_prime_one
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h4).mp h
      omega
  · rintro rfl
    norm_num

/-- `{0, h}` is admissible exactly when `h` is even. -/
theorem admissible_pair_iff (h : ℕ) : Admissible {0, h} ↔ Even h := by
  constructor
  · intro ha
    obtain ⟨r, hr⟩ := ha 2 Nat.prime_two
    have h0 := hr 0 (by simp)
    have h1 := hr h (by simp)
    rw [Nat.even_iff]
    omega
  · rintro ⟨k, rfl⟩ p hp
    have hp2 := hp.two_le
    by_cases h2 : p = 2
    · subst h2
      refine ⟨1, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      omega
    · by_cases hd : p ∣ 1 + (k + k)
      · refine ⟨2, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
          add_zero]
        refine ⟨fun h => h2 ?_, fun h => ?_⟩
        · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
        · have := Nat.dvd_sub h hd
          rw [show 2 + (k + k) - (1 + (k + k)) = 1 by omega] at this
          exact hp.one_lt.ne' (Nat.dvd_one.mp this)
      · refine ⟨1, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
          add_zero]
        exact ⟨fun h => hp.one_lt.ne' (Nat.dvd_one.mp h), hd⟩

/-- `{0, 2, 6}` is admissible. -/
theorem admissible_zero_two_six : Admissible {0, 2, 6} := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, add_zero]
  by_cases h3 : p = 3
  · subst h3; exact ⟨2, by decide⟩
  by_cases h7 : p = 7
  · subst h7; exact ⟨2, by decide⟩
  refine ⟨1, fun h => hp.one_lt.ne' (Nat.dvd_one.mp h), fun h => h3 ?_, fun h => h7 ?_⟩
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h

/-! ## The classical conjectures from above -/

/-- The prime `k`-tuples conjecture (qualitative Hardy–Littlewood): every admissible tuple is
simultaneously prime infinitely often. -/
def PrimeTuplesConjecture : Prop := ∀ hs : Finset ℕ, Admissible hs → (TupleSet hs).Infinite

/-- Dickson's conjecture for linear forms `a n + b` (`a ≥ 1`) with no fixed prime divisor. -/
def DicksonConjecture : Prop :=
  ∀ L : Finset (ℕ × ℕ), (∀ f ∈ L, 1 ≤ f.1) →
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ f ∈ L, ¬ p ∣ f.1 * n + f.2) →
    {n : ℕ | ∀ f ∈ L, (f.1 * n + f.2).Prime}.Infinite

open Polynomial in
/-- Schinzel's Hypothesis H: finitely many irreducible integer polynomials with positive leading
coefficients whose product has no fixed prime divisor take prime values (in absolute value)
simultaneously infinitely often. -/
def SchinzelH : Prop :=
  ∀ fs : Finset ℤ[X], (∀ f ∈ fs, Irreducible f ∧ 0 < f.leadingCoeff) →
    (∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ (p : ℤ) ∣ ∏ f ∈ fs, f.eval n) →
    {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}.Infinite

theorem dickson_implies_primeTuples : DicksonConjecture → PrimeTuplesConjecture := by
  intro hd hs ha
  have key := hd (hs.image fun h => (1, h)) (by simp) (by
    intro p hp
    obtain ⟨r, hr⟩ := ha p hp
    exact ⟨r, by simpa using hr⟩)
  refine key.mono ?_
  intro n hn h hh
  simpa using hn (1, h) (Finset.mem_image_of_mem _ hh)

open Polynomial in
theorem schinzel_implies_primeTuples : SchinzelH → PrimeTuplesConjecture := by
  intro hS hs ha
  have key := hS (hs.image fun h : ℕ => X + C (h : ℤ))
    (by
      simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro h _
      exact ⟨(monic_X_add_C _).irreducible_of_degree_eq_one (degree_X_add_C _),
        by rw [leadingCoeff_X_add_C]; norm_num⟩)
    (by
      intro p hp
      obtain ⟨r, hr⟩ := ha p hp
      refine ⟨r, fun hdvd => ?_⟩
      obtain ⟨f, hf, hpf⟩ := ((Nat.prime_iff_prime_int.mp hp).dvd_finset_prod_iff _).mp hdvd
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hf
      apply hr h hh
      have : ((p : ℕ) : ℤ) ∣ ((r + h : ℕ) : ℤ) := by simpa using hpf
      exact Int.natCast_dvd_natCast.mp this)
  refine key.mono ?_
  intro n hn h hh
  have := hn _ (Finset.mem_image_of_mem _ hh)
  rwa [eval_add, eval_X, eval_C, ← Nat.cast_add, Int.natAbs_natCast] at this

theorem primeTuples_implies_polignac : PrimeTuplesConjecture → Polignac := by
  intro hpt k _
  refine (hpt {0, 2 * k} ((admissible_pair_iff _).mpr ⟨k, by ring⟩)).mono ?_
  intro n hn
  exact ⟨by simpa using hn 0 (by simp), hn (2 * k) (by simp)⟩

theorem primeTuples_implies_tpc : PrimeTuplesConjecture → TwinPrimeConjecture :=
  fun h => polignac_implies_tpc (primeTuples_implies_polignac h)

/-! ## Dickson–Hardy–Littlewood `DHL(k, m)` (Maynard–Tao) -/

/-- `DHL k m`: every admissible `k`-tuple has at least `m` prime translates infinitely often. -/
def DHL (k m : ℕ) : Prop :=
  ∀ hs : Finset ℕ, hs.card = k → Admissible hs →
    {n : ℕ | m ≤ (hs.filter fun h => (n + h).Prime).card}.Infinite

/-- **Pigeonhole on pairs:** if a tuple has two prime translates infinitely often, then some
difference of two of its shifts lies in the gap spectrum. -/
theorem gap_of_tuple {hs : Finset ℕ}
    (hinf : {n : ℕ | 2 ≤ (hs.filter fun h => (n + h).Prime).card}.Infinite) :
    ∃ a ∈ hs, ∃ b ∈ hs, a < b ∧ b - a ∈ gapSpectrum := by
  by_contra hne
  push_neg at hne
  apply hinf
  have hfin : ∀ x ∈ ((hs ×ˢ hs).filter fun x => x.1 < x.2 : Set (ℕ × ℕ)),
      {n : ℕ | (n + x.1).Prime ∧ (n + x.2).Prime}.Finite := by
    rintro ⟨a, b⟩ hx
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hx
    obtain ⟨⟨ha, hb⟩, hab⟩ := hx
    have hP := Set.not_infinite.mp (hne a ha b hb hab)
    refine Set.Finite.of_finite_image (f := fun n => n + a) (hP.subset ?_)
      (fun x _ y _ h => by simpa using h)
    rintro _ ⟨n, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, by rwa [show n + a + (b - a) = n + b by omega]⟩
  refine (Set.Finite.biUnion (Finset.finite_toSet _) hfin).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hn
  rw [Finset.mem_filter] at ha hb
  simp only [Set.mem_iUnion]
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨(a, b), by simp [ha.1, hb.1, h], ha.2, hb.2⟩
  · exact ⟨(b, a), by simp [ha.1, hb.1, h], hb.2, ha.2⟩

/-- `DHL k 2` applied to an admissible tuple of diameter `≤ H` gives the rung `BoundedGaps H`. -/
theorem boundedGaps_of_dhl {k H : ℕ} (hd : DHL k 2) {hs : Finset ℕ} (hk : hs.card = k)
    (ha : Admissible hs) (hH : ∀ h ∈ hs, h ≤ H) : BoundedGaps H := by
  obtain ⟨a, ha', b, hb', hab, hm⟩ := gap_of_tuple (hd hs hk ha)
  exact boundedGaps_mono (by have := hH b hb'; omega)
    (boundedGaps_of_mem_gapSpectrum (by omega) hm)

/-- **`DHL 2 2` is exactly Polignac's conjecture.** -/
theorem dhl_two_two_iff_polignac : DHL 2 2 ↔ Polignac := by
  constructor
  · intro hd k hk
    have hcard : ({0, 2 * k} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
    refine (hd _ hcard ((admissible_pair_iff _).mpr ⟨k, by ring⟩)).mono ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have heq := Finset.eq_of_subset_of_card_le
      (Finset.filter_subset (fun h => (n + h).Prime) ({0, 2 * k} : Finset ℕ)) (by omega)
    have hall := Finset.filter_eq_self.mp heq
    exact ⟨by simpa using hall 0 (by simp), hall (2 * k) (by simp)⟩
  · intro hpol hs hcard ha
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    wlog hlt : x < y generalizing x y
    · rw [Finset.pair_comm] at ha hcard ⊢
      exact this y x (Ne.symm hxy) hcard ha (by omega)
    obtain ⟨r, hr⟩ := ha 2 Nat.prime_two
    have h1 := hr x (by simp)
    have h2 := hr y (by simp)
    obtain ⟨k, hk⟩ : ∃ k, y - x = 2 * k := ⟨(y - x) / 2, by omega⟩
    have hP : (PairSet (y - x)).Infinite := by
      rw [hk]; exact hpol k (by omega)
    have hP' := hP.diff (Set.finite_Iio x)
    have hinj : Set.InjOn (fun p => p - x) (PairSet (y - x) \ Set.Iio x) := by
      intro a ha b hb hab
      simp only [Set.mem_diff, Set.mem_Iio, not_lt] at ha hb
      simp only at hab
      omega
    refine ((Set.infinite_image_iff hinj).mpr hP').mono ?_
    rintro _ ⟨p, ⟨⟨hp, hpy⟩, hpx⟩, rfl⟩
    simp only [Set.mem_Iio, not_lt] at hpx
    simp only [Set.mem_setOf_eq]
    have hfilt : (({x, y} : Finset ℕ).filter fun h => (p - x + h).Prime) = {x, y} := by
      refine Finset.filter_eq_self.mpr ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      refine ⟨by rwa [show p - x + x = p by omega], ?_⟩
      rwa [show p - x + y = p + (y - x) by omega]
    rw [hfilt, Finset.card_pair hxy]

/-- `DHL 3 2` (applied to `{0, 2, 6}`) forces one of the gaps `2, 4, 6` into the spectrum. -/
theorem dhl_three_two_gap (hd : DHL 3 2) :
    2 ∈ gapSpectrum ∨ 4 ∈ gapSpectrum ∨ 6 ∈ gapSpectrum := by
  obtain ⟨a, ha, b, hb, hab, hm⟩ :=
    gap_of_tuple (hd {0, 2, 6} (by decide) admissible_zero_two_six)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | omega | simp_all

/-! ## Hardy–Littlewood asymptotics -/

/-- The twin prime counting function `π₂(x) = #{p ≤ x : p, p + 2 prime}`. -/
noncomputable def twinCount (x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ (p + 2).Prime).card

/-- The Hardy–Littlewood twin prime asymptotic `π₂(x) ~ C x / log² x` (conjecturally with
`C = 2 C₂ ≈ 1.3203`, `C₂` the twin prime constant). -/
def HardyLittlewoodTwin (C : ℝ) : Prop :=
  Tendsto (fun x : ℝ => (twinCount x : ℝ) / (x / Real.log x ^ 2)) atTop (𝓝 C)

/-- **Any positive Hardy–Littlewood constant implies the twin prime conjecture.** -/
theorem hardyLittlewood_implies_tpc {C : ℝ} (hC : 0 < C) (hl : HardyLittlewoodTwin C) :
    TwinPrimeConjecture := by
  by_contra hfin
  have hS : {p : ℕ | p.Prime ∧ (p + 2).Prime}.Finite := Set.not_infinite.mp hfin
  set N := hS.toFinset.card
  have hbound : ∀ x, twinCount x ≤ N := fun x =>
    Finset.card_le_card fun p hp => by
      simp only [Finset.mem_filter] at hp
      simpa using hp.2
  have hlim : Tendsto (fun x : ℝ => (twinCount x : ℝ) / (x / Real.log x ^ 2)) atTop (𝓝 0) := by
    have hg : Tendsto (fun x : ℝ => (N : ℝ) * (Real.log x ^ 2 / (1 * x + 0))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).const_mul (N : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      positivity
    · filter_upwards [eventually_gt_atTop 0] with x hx
      rw [div_div_eq_mul_div, one_mul, add_zero, mul_div_assoc]
      gcongr
      exact_mod_cast hbound x
  exact hC.ne' (tendsto_nhds_unique hl hlim)

/-- The twin prime conjecture is exactly the unboundedness of `π₂`. -/
theorem tpc_iff_twinCount_unbounded : TwinPrimeConjecture ↔ ∀ N : ℕ, ∃ x : ℝ, N < twinCount x := by
  constructor
  · intro h N
    obtain ⟨t, hts, htc⟩ := h.exists_subset_card_eq (N + 1)
    refine ⟨(t.sup id : ℕ), ?_⟩
    have hsub : t ⊆ (Finset.range (⌊((t.sup id : ℕ) : ℝ)⌋₊ + 1)).filter
        fun p => p.Prime ∧ (p + 2).Prime := by
      intro p hp
      rw [Finset.mem_filter, Nat.floor_natCast, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hp), hts hp⟩
    have := Finset.card_le_card hsub
    unfold twinCount
    omega
  · intro h hS
    obtain ⟨x, hx⟩ := h hS.toFinset.card
    have : twinCount x ≤ hS.toFinset.card :=
      Finset.card_le_card fun p hp => by
        simp only [Finset.mem_filter] at hp
        simpa using hp.2
    omega

/-! ## The DHL ladder with explicit admissible tuples

Maynard's sieve proves `DHL k 2` for large `k`; the bound `H` then comes from the narrowest
admissible `k`-tuple.  The known (cited, **not** formalised) inputs are:

| input                         | `DHL k 2` for | narrowest tuple used here    | rung              |
|-------------------------------|---------------|------------------------------|-------------------|
| Maynard–Polymath (theorem)    | `k = 50`      | `polymathTuple`, diameter 246 | `BoundedGaps 246` |
| Elliott–Halberstam (conj.)    | `k = 5`       | `{0, 2, 6, 8, 12}`           | `BoundedGaps 12`  |
| generalised EH (conj.)        | `k = 3`       | `{0, 2, 6}`                  | `BoundedGaps 6`   |
| Polignac = `DHL 2 2` (conj.)  | `k = 2`       | `{0, 2}`                     | `BoundedGaps 2` = TPC |

The sieve-theoretic *parity barrier* (Selberg; cited) is why the method stops at `k = 3`: the
last rung needs an input of a different kind.  Each row below is a proved implication
"`DHL k 2` ⇒ rung"; the admissibility of each tuple is checked by the Lean kernel.
-/

/-- **Only small primes matter for admissibility:** a prime `p > |hs|` can never be covered,
because `hs` meets at most `|hs| < p` residue classes. -/
theorem admissible_of_small {hs : Finset ℕ}
    (h : ∀ p ∈ Finset.range (hs.card + 1), p.Prime →
      ∃ r ∈ Finset.range p, ∀ x ∈ hs, ¬ p ∣ r + x) :
    Admissible hs := by
  intro p hp
  by_cases hle : p ≤ hs.card
  · obtain ⟨r, -, hr⟩ := h p (Finset.mem_range.mpr (by omega)) hp
    exact ⟨r, hr⟩
  · push_neg at hle
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hcard : (hs.image fun x : ℕ => -(x : ZMod p)).card <
        (Finset.univ : Finset (ZMod p)).card := by
      rw [Finset.card_univ, ZMod.card]
      exact Finset.card_image_le.trans_lt hle
    obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨z.val, fun x hx hdvd => hz ?_⟩
    rw [Finset.mem_image]
    refine ⟨x, hx, ?_⟩
    have : ((z.val + x : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at this
    rw [ZMod.natCast_zmod_val] at this
    linear_combination -this

/-- An admissible 50-tuple of diameter 246 (found by a residue-class sieve search; its
admissibility is checked below by the kernel). -/
def polymathTuple : Finset ℕ :=
  [0, 4, 6, 10, 16, 22, 24, 30, 34, 36, 42, 46, 52, 60, 64, 66, 70, 72, 76, 90, 94, 100, 102,
    112, 114, 120, 126, 130, 136, 142, 144, 154, 156, 160, 162, 174, 186, 190, 192, 196, 202, 204,
    214, 220, 226, 232, 234, 240, 244, 246].toFinset

theorem polymathTuple_card : polymathTuple.card = 50 := by decide

theorem polymathTuple_le : ∀ h ∈ polymathTuple, h ≤ 246 := by decide

theorem admissible_polymathTuple : Admissible polymathTuple :=
  admissible_of_small (by decide +kernel)

theorem admissible_ehTuple : Admissible {0, 2, 6, 8, 12} :=
  admissible_of_small (by decide +kernel)

/-- **Rung 246** from `DHL 50 2` (the Maynard–Polymath theorem, taken as a hypothesis). -/
theorem boundedGaps_246_of_dhl (hd : DHL 50 2) : BoundedGaps 246 :=
  boundedGaps_of_dhl hd polymathTuple_card admissible_polymathTuple polymathTuple_le

/-- **Rung 12** from `DHL 5 2` (Maynard's consequence of Elliott–Halberstam). -/
theorem boundedGaps_12_of_dhl (hd : DHL 5 2) : BoundedGaps 12 :=
  boundedGaps_of_dhl hd (by decide) admissible_ehTuple (by decide)

/-- **Rung 6** from `DHL 3 2` (Polymath's consequence of generalised Elliott–Halberstam). -/
theorem boundedGaps_6_of_dhl (hd : DHL 3 2) : BoundedGaps 6 :=
  boundedGaps_of_dhl hd (by decide) admissible_zero_two_six (by decide)

/-! ## The whole web in one statement -/

/-- **Convergence web.**  Every arrow into the twin prime conjecture that is proved in this file,
collected in one place:

1. Schinzel's Hypothesis H ⇒ TPC;
2. Dickson's conjecture ⇒ TPC;
3. the prime `k`-tuples conjecture ⇒ Polignac ⇒ TPC, and Polignac ⇔ `DHL 2 2`;
4. a Hardy–Littlewood asymptotic with any positive constant ⇒ TPC;
5. TPC ⇔ `BoundedGaps 2` ⇔ `2 ∈ gapSpectrum` ⇔ `π₂` unbounded;
6. `DHL 3 2` ⇒ one of the gaps `2, 4, 6` occurs infinitely often;
7. any rung `BoundedGaps H` plus the exclusion of the gaps `4, …, H` ⇒ TPC. -/
theorem convergence_web :
    (SchinzelH → TwinPrimeConjecture) ∧
    (DicksonConjecture → TwinPrimeConjecture) ∧
    (PrimeTuplesConjecture → Polignac) ∧ (Polignac → TwinPrimeConjecture) ∧
    (DHL 2 2 ↔ Polignac) ∧
    (∀ C : ℝ, 0 < C → HardyLittlewoodTwin C → TwinPrimeConjecture) ∧
    (TwinPrimeConjecture ↔ BoundedGaps 2) ∧ (TwinPrimeConjecture ↔ 2 ∈ gapSpectrum) ∧
    (TwinPrimeConjecture ↔ ∀ N : ℕ, ∃ x : ℝ, N < twinCount x) ∧
    (DHL 3 2 → 2 ∈ gapSpectrum ∨ 4 ∈ gapSpectrum ∨ 6 ∈ gapSpectrum) ∧
    (∀ H, BoundedGaps H → (∀ h, 4 ≤ h → h ≤ H → h ∉ gapSpectrum) → TwinPrimeConjecture) :=
  ⟨fun h => primeTuples_implies_tpc (schinzel_implies_primeTuples h),
   fun h => primeTuples_implies_tpc (dickson_implies_primeTuples h),
   primeTuples_implies_polignac, polignac_implies_tpc, dhl_two_two_iff_polignac,
   fun _ hC hl => hardyLittlewood_implies_tpc hC hl,
   tpc_iff_boundedGaps_two, tpc_iff_two_mem_gapSpectrum, tpc_iff_twinCount_unbounded,
   dhl_three_two_gap, fun _ hb hex => tpc_of_boundedGaps_of_exclusion hb hex⟩

end QBX.Notes.TwinPrime.Convergence
