import Discovery.Bridge
import Discovery.Ledger.Run20261020_Genesis
import Discovery.Ledger.Run20261020_Second

/-!
# Reading burned claims as mathematics

The discovery loop burns closed, bounded statements about the vocabulary of
`Discovery.Kernel`.  Combined with the bridge theorems of `Discovery.Bridge`, each of them is a
statement about standard objects.  This file carries out that translation for a few claims
burned by the runs `Run20261020_Genesis` and `Run20261020_Second`:

* `Discovery.fermat_two_squares_below_800` — every prime `p < 800` with `p ≡ 1 (mod 4)` is a sum
  of two squares (burned claim `quadform_holds_e9bb76e09c`, with `isPrimeB_iff`);
* `Discovery.cd32_basis_sq` — in the 32-dimensional Cayley–Dickson algebra over any commutative
  ring, every imaginary basis vector squares to `-1` (burned claim `cdsign_holds_347b44802c`);
* `Discovery.cd32_left_alternative_basis`, `Discovery.cd32_right_alternative_basis` —
  `e_i (e_i e_j) = -e_j` and `(e_j e_i) e_i = -e_j` for every imaginary basis vector `e_i` and
  every basis vector `e_j` of the 32-dimensional Cayley–Dickson algebra (burned claims
  `cdsign_holds_1a1920a752` and `cdsign_holds_31645a8c2a`).
-/

namespace Discovery

open SovereignEngine.CayleyDickson

/-- Every prime `p < 800` with `p ≡ 1 (mod 4)` is a sum of two squares. -/
theorem fermat_two_squares_below_800 (p : ℕ) (hp : p < 800) (hprime : p.Prime)
    (hmod : p % 4 = 1) : ∃ x y : ℕ, x ^ 2 + y ^ 2 = p := by
  obtain ⟨x, -, y, -, h⟩ :=
    Ledger.quadform_holds_e9bb76e09c p hp ((isPrimeB_iff p).2 hprime) hmod
  exact ⟨x, y, by rw [← h]; ring⟩

/-- In the 32-dimensional Cayley–Dickson algebra over a commutative ring, every imaginary
basis vector squares to `-1`. -/
theorem cd32_basis_sq {R : Type*} [CommRing R] (i : ℕ) (hi : i < 32) (h0 : i ≠ 0) :
    cdMul R 5 (sbasis R 5 1 i) (sbasis R 5 1 i) = sbasis R 5 (-1) 0 := by
  have hi' : i < 2 ^ 5 := by norm_num; exact hi
  rw [cdMul_basis 5 i i hi' hi', Ledger.cdsign_holds_347b44802c i hi h0, Nat.xor_self]
  simp

/-- Left alternativity on the basis of the 32-dimensional Cayley–Dickson algebra:
`e_i (e_i e_j) = -e_j` for `i ≠ 0`. -/
theorem cd32_left_alternative_basis {R : Type*} [CommRing R] (i j : ℕ) (hi : i < 32)
    (hj : j < 32) (h0 : i ≠ 0) :
    cdMul R 5 (sbasis R 5 1 i) (cdMul R 5 (sbasis R 5 1 i) (sbasis R 5 1 j))
      = sbasis R 5 (-1) j := by
  have hi' : i < 2 ^ 5 := by norm_num; exact hi
  have hj' : j < 2 ^ 5 := by norm_num; exact hj
  have hij : i ^^^ j < 2 ^ 5 := Nat.xor_lt_two_pow hi' hj'
  rw [cdMul_basis 5 i j hi' hj', cdMul_sbasis 5 1 _ i (i ^^^ j) hi' hij]
  have h := Ledger.cdsign_holds_1a1920a752 i hi j hj h0
  have hx : i ^^^ (i ^^^ j) = j := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hx, one_mul, ← cdSign_eq, ← Int.cast_mul, h]
  simp

/-- Right alternativity on the basis of the 32-dimensional Cayley–Dickson algebra:
`(e_j e_i) e_i = -e_j` for `i ≠ 0`. -/
theorem cd32_right_alternative_basis {R : Type*} [CommRing R] (i j : ℕ) (hi : i < 32)
    (hj : j < 32) (h0 : i ≠ 0) :
    cdMul R 5 (cdMul R 5 (sbasis R 5 1 j) (sbasis R 5 1 i)) (sbasis R 5 1 i)
      = sbasis R 5 (-1) j := by
  have hi' : i < 2 ^ 5 := by norm_num; exact hi
  have hj' : j < 2 ^ 5 := by norm_num; exact hj
  have hji : j ^^^ i < 2 ^ 5 := Nat.xor_lt_two_pow hj' hi'
  rw [cdMul_basis 5 j i hj' hi', cdMul_sbasis 5 _ 1 (j ^^^ i) i hji hi']
  have h := Ledger.cdsign_holds_31645a8c2a i hi j hj h0
  have hx : j ^^^ i ^^^ i = j := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hx, mul_one, Nat.xor_comm j i, ← cdSign_eq, ← Int.cast_mul, h]
  simp

end Discovery
