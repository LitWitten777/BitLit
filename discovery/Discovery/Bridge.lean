import Mathlib
import Discovery.Kernel
import RequestProject.SedenionCocycle

/-!
# Bridge: what the discovery vocabulary means

The automated discovery loop states its claims with the import-free definitions of
`Discovery.Kernel`, so that staging a claim is fast.  This file proves, once and for all, that
those definitions mean what they are named after:

* `Discovery.cdSign_eq` — `Discovery.cdSign` is the sign cochain
  `SovereignEngine.CayleyDickson.cdSign` of the Cayley–Dickson development, hence
  (`Discovery.cdMul_basis`) for every commutative ring `R` the Cayley–Dickson product of basis
  vectors of `CD R n` is `e_i ⋆ e_j = (cdSign n i j) • e_{i ⊕ j}`.  Every staged sign law is
  therefore a statement about the actual Cayley–Dickson multiplication.
* `Discovery.isPrimeB_iff` — `isPrimeB n = true ↔ Nat.Prime n`.
-/

namespace Discovery

open SovereignEngine.CayleyDickson

/-- The discovery kernel's sign function is the Cayley–Dickson sign cochain. -/
theorem cdSign_eq : Discovery.cdSign = SovereignEngine.CayleyDickson.cdSign := by
  funext n
  induction n with
  | zero => funext i j; rfl
  | succ n ih =>
      funext i j
      simp only [Discovery.cdSign, SovereignEngine.CayleyDickson.cdSign, ih]

/-- Products of canonical basis vectors in the Cayley–Dickson algebra `CD R n`, expressed with
the discovery kernel's sign: `e_i ⋆ e_j = cdSign n i j • e_{i ⊕ j}`. -/
theorem cdMul_basis {R : Type*} [CommRing R] (n i j : ℕ) (hi : i < 2 ^ n) (hj : j < 2 ^ n) :
    cdMul R n (sbasis R n 1 i) (sbasis R n 1 j)
      = sbasis R n ((Discovery.cdSign n i j : ℤ) : R) (i ^^^ j) := by
  rw [cdMul_sbasis n 1 1 i j hi hj, cdSign_eq, one_mul, one_mul]

theorem noDivisorFrom_iff (n : ℕ) :
    ∀ k d, noDivisorFrom n d k = true ↔ ∀ m, d ≤ m → m < d + k → n % m ≠ 0 := by
  intro k
  induction k with
  | zero => intro d; simp [noDivisorFrom]; intro m h1 h2; omega
  | succ k ih =>
      intro d
      simp only [noDivisorFrom, Bool.and_eq_true, bne_iff_ne, ne_eq, ih]
      constructor
      · rintro ⟨h0, h⟩ m hm1 hm2
        rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
        · exact h0
        · exact h m (by omega) (by omega)
      · intro h
        exact ⟨h d le_rfl (by omega), fun m hm1 hm2 => h m (by omega) (by omega)⟩

/-- The trial-division test of the discovery kernel decides primality. -/
theorem isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ Nat.Prime n := by
  rw [Nat.prime_def_lt]
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, noDivisorFrom_iff]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hdvd => ?_⟩
    by_contra hne
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hdvd
      omega
    exact h m (by omega) (by omega) (Nat.mod_eq_zero_of_dvd hdvd)
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm1 hm2 hmod => ?_⟩
    have := h m (by omega) (Nat.dvd_of_mod_eq_zero hmod)
    omega

end Discovery
