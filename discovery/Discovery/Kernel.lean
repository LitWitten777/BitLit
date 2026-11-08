module

/-!
# Discovery kernel: the decidable vocabulary of the automated discovery loop

Every claim that the automated discovery loop (`discovery/engine/`) stages for the Lean kernel
is a closed, bounded statement written only in terms of the definitions of this file and of Lean
core.  The file deliberately imports nothing, so a staged claim elaborates in about a second.

* `cdSign n i j` — the sign `σ(i, j) ∈ {±1}` of the product of canonical basis vectors of the
  Cayley–Dickson algebra of dimension `2ⁿ`: `e_i e_j = σ(i, j) e_{i ⊕ j}` (`⊕` = bitwise xor).
  The definition is a verbatim copy of `SovereignEngine.CayleyDickson.cdSign`
  (`sovereign/RequestProject/SedenionCocycle.lean`); `Discovery/Bridge.lean` proves the two equal
  and therefore ties every staged sign law to the actual Cayley–Dickson product.
* `isPrimeB n` — trial-division primality test; `Discovery/Bridge.lean` proves
  `isPrimeB n = true ↔ Nat.Prime n`.
-/

@[expose] public section

namespace Discovery

/-- Sign of `e_i e_j` in the Cayley–Dickson algebra of dimension `2ⁿ`:
`e_i e_j = cdSign n i j • e_{i ^^^ j}` (copy of `SovereignEngine.CayleyDickson.cdSign`). -/
def cdSign : Nat → Nat → Nat → Int
  | 0, _, _ => 1
  | n + 1, i, j =>
      if i < 2 ^ n then
        (if j < 2 ^ n then cdSign n i j else cdSign n (j - 2 ^ n) i)
      else
        (if j < 2 ^ n then (if j = 0 then cdSign n (i - 2 ^ n) j else -cdSign n (i - 2 ^ n) j)
         else -(if j - 2 ^ n = 0 then cdSign n (j - 2 ^ n) (i - 2 ^ n)
                else -cdSign n (j - 2 ^ n) (i - 2 ^ n)))

/-- `noDivisorFrom n d k`: no divisor `d' ∈ [d, d + k)` with `2 ≤ d'` divides `n`
(structural recursion on the fuel `k`, so the kernel evaluates it directly). -/
def noDivisorFrom (n : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | d, k + 1 => (n % d != 0) && noDivisorFrom n (d + 1) k

/-- Trial-division primality test: `n ≥ 2` and no `d ∈ [2, n)` divides `n`. -/
def isPrimeB (n : Nat) : Bool :=
  decide (2 ≤ n) && noDivisorFrom n 2 (n - 2)

end Discovery

end
