#!/usr/bin/env python3
"""Generates the body of QBX/Formal/Streams/WeylLongestD.lean (D4-D6 positive roots and the
unique-longest-element theorems). Nothing here is trusted; Lean re-checks everything."""
def cox(n):
    M=[[1 if i==j else 2 for j in range(n)] for i in range(n)]
    edges=[(i,i+1) for i in range(n-2)]+[(n-3,n-1)]
    for i,j in edges: M[i][j]=M[j][i]=3
    return M
def cart(n):
    M=cox(n); return [[2 if i==j else (-1 if M[i][j]==3 else 0) for j in range(n)] for i in range(n)]
def refl(C,i,v):
    s=sum(C[i][b]*v[b] for b in range(len(v))); w=list(v); w[i]-=s; return tuple(w)
def roots(C):
    n=len(C); simple=[tuple(1 if a==i else 0 for a in range(n)) for i in range(n)]
    R=list(simple); seen=set(R); fr=list(simple)
    while fr:
        new=[]
        for r in fr:
            for i in range(n):
                if r==simple[i]: continue
                w=refl(C,i,r); assert min(w)>=0
                if w not in seen: seen.add(w); R.append(w); new.append(w)
        fr=new
    return R
out=[]
H={4:6,5:8,6:10}
for n in (4,5,6):
    C=cart(n); R=roots(C); N=len(R); assert N==n*(n-1)
    x=f"d{n}"; X=f"D{n}"
    rows="; ".join(", ".join(str(c) for c in row) for row in C)
    rl=",\n".join("  !["+", ".join(map(str,r))+"]" for r in R)
    T=f"coxD{n}.Group"
    s=f'''/-! ## `D{n}` -/

/-- The (symmetric) Cartan matrix of `D{n}`, realising `coxD{n}`. -/
def {x}Cartan : Matrix (Fin {n}) (Fin {n}) ℤ := !![{rows}]

theorem {x}_isCartanFor : IsCartanFor coxD{n} {x}Cartan where
  diag := by decide +kernel
  liftable := by unfold CoxeterMatrix.IsLiftable; decide +kernel
  finite := by decide
  rankTwo := by decide +kernel

/-- The {N} positive roots of `D{n}` in simple-root coordinates. -/
def {x}PosRoots : List (Fin {n} → ℤ) := [
{rl}]

/-- The positive roots as a finite set. -/
def {x}Pos : Finset (Fin {n} → ℤ) := {x}PosRoots.toFinset

theorem {x}Pos_card : {x}Pos.card = {N} := by decide +kernel

theorem {x}Pos_isPositiveRootSet : IsPositiveRootSet {x}Cartan {x}Pos where
  closed := by decide +kernel
  simple_mem := by decide +kernel
  nonneg := by decide +kernel
  zero_not_mem := by decide +kernel

/-- The reflection representation of `W(D{n})` defined by `{x}Cartan`. -/
abbrev {x}Crep : {T} →* Matrix (Fin {n}) (Fin {n}) ℤ := crep {x}_isCartanFor

/-- **Faithfulness**: the reflection representation of `W(D{n})` is injective. -/
theorem {x}Crep_injective : Function.Injective {x}Crep := crep_injective {x}_isCartanFor

/-- `ℓ(w)` is the number of positive roots of `D{n}` that `w` sends to negative roots. -/
theorem {x}_length_eq_escapes (w : {T}) :
    coxD{n}.toCoxeterSystem.length w = Cartan.escapes {x}Pos ({x}Crep w) :=
  length_eq_escapes {x}_isCartanFor {x}Pos_isPositiveRootSet w

/-- Every element of `W(D{n})` has length at most `{N}`. -/
theorem {x}_length_le (w : {T}) : coxD{n}.toCoxeterSystem.length w ≤ {N} :=
  {x}Pos_card ▸ length_le_card {x}_isCartanFor {x}Pos_isPositiveRootSet w

/-- The image `w₀ = toCoxeter Δ` of the Garside element of `ArtinD{n}` in `W(D{n})`. -/
def {x}W0 : {T} := toCoxeter {x}Delta

/-- `ρ(w₀)` sends every positive root to a non-positive one. -/
theorem {x}Mat_delta_escapes :
    ∀ r ∈ {x}Pos, ({x}DeltaWordAB.map (natCMat {x}Cartan)).prod *ᵥ r ∉ {x}Pos := by
  decide +kernel

/-- **`w₀` is the unique longest element of `W(D{n})`**: `ℓ(w) = {N}` iff `w = w₀`. -/
theorem {x}_length_eq_iff (w : {T}) :
    coxD{n}.toCoxeterSystem.length w = {N} ↔ w = {x}W0 := by
  rw [← {x}Pos_card]
  refine length_eq_card_iff {x}_isCartanFor {x}Pos_isPositiveRootSet ?_ w
  rw [{x}W0, {x}Delta, crep_toCoxeter_natLift]
  exact {x}Mat_delta_escapes
'''
    out.append(s)
print("\n".join(out))
