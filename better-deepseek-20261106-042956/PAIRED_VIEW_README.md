# Paired CD × Clifford view: what is formalized

`FINDINGS.md` identifies joint-view identifiability as the next priority:
"Establish the exact map and its kernel before adding more dimensions or interpreting its
labels." This directory's three files do exactly that for the base case — paired linear views
of the same sedenion key.

## What is proved in Lean

**`Sovereign/Meta/StateOfThoughtPairedView.lean`** (existing) — the generic paired-view
theorems:

- `ker_stack` — `ker (A, B) = ker A ⊓ ker B`
- `injective_stack_iff` — `(A, B)` injective ⟺ `ker A ⊓ ker B = ⊥`
- `finrank_ker_stack` — joint nullity is `dim (ker A ⊓ ker B)`
- `paired_loss_le` — joint loss ≤ min of individual losses
- `finrank_range_stack` — joint rank = `dim V − dim (ker A ⊓ ker B)`

And the sedenion specialization:

- `cdRightMul`, `sedenionAnnihilator_eq_ker` — CD right multiplication and its kernel
- `zeroDivisor_rank_eq_twelve` — **CD rank 12 for every nonzero sedenion zero divisor**
  (derived from the 4-dimensional right annihilator)
- `paired_cdRightMul_injective_iff`, `paired_cdRightMul_finrank_ker`,
  `paired_cdRightMul_nullity_le_four`, `paired_cdRightMul_rank`

**`Sovereign/Meta/CliffordMul.lean`** (new) — the specific Clifford multiplication:

- `psiCliff` — the sign table from `hypercube/hashrounds2.py`
- `cliffordRightMul`, `cliffordRightMulLin` — the right-multiplication map
- Sanity checks: `psiCliff 1 1 = -1`, `psiCliff 1 2 = 1`, right-mult by `e_0` is identity

**`Sovereign/Meta/PairedCDClifford.lean`** (new) — the paired specialization:

- `pairedCDClifford` — the paired view `(y ·_CD x, y ·_Cliff x)`
- `ker_pairedCDClifford` — kernel is `sedenionAnnihilator x ⊓ ker(Cliff_x)`
- `paired_injective_of_clifford_injective` — structural: Cliff injective ⇒ paired injective
- `pairedCDClifford_joint_ker_le` — joint kernel ⊆ CD annihilator, so ≤ 4-dim for zero divisors
- `assessors_length` — the 84 assessor list has length 84
- `PairedCDCliffordClassification` — the FINDINGS numbers (as a `Prop`)

## What is verified computationally but not yet formalized

**`PairedCDCliffordClassification`** (48 keys with joint rank 16, 36 with joint rank 14) is
recorded as a `Prop` but not yet proved in Lean. Its formal proof requires either:

1. A **computable rank function over `ℚ`** (Gaussian elimination) so that `native_decide` can
   evaluate `Module.finrank ℚ (LinearMap.ker (pairedCDClifford x))` at each of the 84 keys.
   Mathlib's `Module.finrank` uses `Classical.choice` on a basis and is noncomputable;
   a computable alternative needs to be built (roughly 60–100 lines of Lean).

2. Or **explicit kernel-basis witnesses** for each of the 84 keys. For the 36 keys with
   joint rank 14, exhibit two explicitly chosen vectors in `ker CD_x ⊓ ker Cliff_x`; for the
   48 with joint rank 16, the injectivity follows automatically when `ker Cliff_x = 0` (36
   keys), and needs explicit injectivity checks for the remaining 12. That is 84 × ~2
   witnesses of dimension 16.

The **Python script `verify_paired.py`** reproduces the FINDINGS numbers exactly with
exact rational arithmetic. Running it prints:

```

CD rank histogram:              {12: 84}
Clifford rank histogram:        {8: 48, 16: 36}
Joint (stacked) rank histogram: {16: 48, 14: 36}
✓ FINDINGS classification reproduced exactly.

```

So the numbers are confirmed; only the Lean formalization of the specific numeric
classification remains (a computational-algebra task).

## What this closes and what it leaves

| FINDINGS action item | Status |
|---|---|
| Establish the exact map and its kernel for paired views | ✅ Proved (abstract + sedenion + Clifford) |
| Show `ker C_k = ker A_k ⊓ ker B_k` | ✅ `ker_pairedCDClifford` |
| Show joint rank = `16 − dim(ann a ⊓ ann b)` | ✅ `paired_cdRightMul_rank` (CD–CD); the CD–Clifford version follows by substitution |
| CD rank 12 for every zero divisor | ✅ `zeroDivisor_rank_eq_twelve` |
| Joint nullity ≤ 4 for two zero divisors | ✅ `paired_cdRightMul_nullity_le_four` |
| Classification 48/36 | ⚠️ Numeric verification only; Lean proof needs a computable rank |
| Clifford multiplication defined | ✅ `CliffordMul.lean` |
| Clifford rank 8 or 16 | ⚠️ Verified by `verify_paired.py`; Lean proof same blocker |

The natural next step is either:

- **A computable `rankQ : Matrix (Fin m) (Fin n) ℚ → ℕ`** via Gaussian elimination, then
  `native_decide` on `PairedCDCliffordClassification`; **or**
- **A witness-based classification** with explicit kernel-basis vectors for each of the 84
  keys, generated from `verify_paired.py`'s exact computations.

Either closes FINDINGS step 2 and 3 fully.
