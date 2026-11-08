"""Generate the E6/E7 braid-move certificates in QBX/Formal/Streams/ArtinE6/ and ArtinE7/.

Same method as gen_e8_artin_certificates.py (constructive Matsumoto theorem), plus a search for a
short conjugating word between the bipartite and the standard Coxeter word, and the E6 twisted
right-division Delta = X * sigma_{eps s}.  Output is only a hint: Lean re-checks every move
(QBX.Formal.Streams.checkCode_sound).  Usage: python3 QBX/scripts/gen_e67_artin_certificates.py
(run from the repository root; overwrites the generated Lean files).
"""
import sys, functools, itertools, pickle, os
sys.setrecursionlimit(100000)
sys.set_int_max_str_digits(10000000)
EDGES=[(0,2),(1,3),(2,3),(3,4),(4,5),(5,6),(6,7)]
def setup(n):
    global N,M,C
    N=n
    edges=[e for e in EDGES if max(e)<n]
    M=[[2]*n for _ in range(n)]
    for i in range(n): M[i][i]=1
    for a,b in edges: M[a][b]=M[b][a]=3
    C=[[0]*n for _ in range(n)]
    for i in range(n): C[i][i]=2
    for a,b in edges: C[a][b]=C[b][a]=-1
def refl(i,v):
    c=sum(C[i][j]*v[j] for j in range(N)); v=list(v); v[i]-=c; return tuple(v)
def act(word,v):
    for i in reversed(word): v=refl(i,v)
    return v
def unit(i): return tuple(1 if j==i else 0 for j in range(N))
def neg(v): return all(x<=0 for x in v)
def elem(word): return tuple(act(word,unit(i)) for i in range(N))
def apply_elem(e,v):
    r=[0]*N
    for i in range(N):
        for j in range(N): r[j]+=v[i]*e[i][j]
    return tuple(r)
def reduced_word(word):
    e=elem(word); res=[]
    while True:
        for j in range(N):
            if neg(e[j]): break
        else: break
        res.append(j)
        e=tuple(apply_elem(e,refl(j,unit(i))) for i in range(N))
    return list(reversed(res))
def alt(s,t,m): return [s if k%2==0 else t for k in range(m)]
@functools.lru_cache(maxsize=None)
def transform(u,v):
    if u==v: return ()
    if u[0]==v[0]:
        return tuple((p+1,i,j) for (p,i,j) in transform(u[1:],v[1:]))
    s,t=u[0],v[0]; m=M[s][t]
    a=alt(s,t,m)
    r=tuple(reduced_word(list(reversed(a))+list(u)))
    A=tuple(a)+r; B=tuple(alt(t,s,m))+r
    assert len(A)==len(u)
    return transform(u,A)+((0,s,t),)+transform(B,v)
def check(u,v,moves):
    w=list(u)
    for p,i,j in moves:
        m=M[i][j]; assert w[p:p+m]==alt(i,j,m); w[p:p+m]=alt(j,i,m)
    assert w==list(v)
def enc(mv):
    c=0
    for (p,i,j) in reversed(mv):
        assert p<128 and i<8 and j<8
        c=c*8192+(p*64+i*8+j)
    return c
def trace_eq(u,v):
    if sorted(u)!=sorted(v): return False
    for a in range(N):
        for b in range(N):
            if M[a][b]!=2:
                if [x for x in u if x in (a,b)]!=[x for x in v if x in (a,b)]: return False
    return True
def comm_moves(u,v):
    w=list(u); mv=[]
    for k in range(len(v)):
        p=w.index(v[k],k)
        while p>k:
            i,j=w[p-1],w[p]; assert M[i][j]==2
            mv.append((p-1,i,j)); w[p-1],w[p]=j,i; p-=1
    assert w==list(v); return mv

import pickle
res={}
for n,A,B,half,eps in [(6,[0,3,5],[1,2,4],6,{0:5,5:0,2:4,4:2,1:1,3:3}),(7,[0,3,5],[1,2,4,6],9,{i:i for i in range(7)})]:
    setup(n); transform.cache_clear()
    D1=tuple((A+B)*half); D2=tuple((B+A)*half)
    assert len(reduced_word(list(D1)))==len(D1)
    out={}
    mv=transform(D1,D2); check(D1,D2,mv); out['ab']=mv
    for s in range(n):
        X=tuple(reduced_word([s]+list(D1)))
        m1=transform(D1,(s,)+X); m2=transform(D1,X+(eps[s],))
        check(D1,(s,)+X,m1); check(D1,X+(eps[s],),m2)
        out[s]=(X,m1,m2)
    std=list(range(n)); bip=A+B
    # search conj word g
    found=None
    for L in range(0,11):
        for g in itertools.product(range(n),repeat=L):
            if trace_eq(bip+list(g), list(g)+std): found=list(g); break
        if found is not None: break
    cm=comm_moves(bip+found, found+std)
    out['conj']=(found,cm)
    res[n]=out
    print(n, len(mv), [(len(out[s][1]),len(out[s][2])) for s in range(n)], found, len(cm))


import pickle, os

ROOT='QBX/Formal/Streams'
cfg={6:dict(A=[0,3,5],B=[1,2,4],half=6,eps={0:5,5:0,2:4,4:2,1:1,3:3},groups=[list(range(6))]),
     7:dict(A=[0,3,5],B=[1,2,4,6],half=9,eps={i:i for i in range(7)},groups=[[0,1,2],[3,4],[5,6]])}
def L(w): return "["+", ".join(map(str,w))+"]"
for n,c in cfg.items():
    T=f"e{n}"; TT=f"E{n}"; sub="₆" if n==6 else "₇"
    out=res[n]; setup(n)
    A,B,half,eps=c['A'],c['B'],c['half'],c['eps']
    os.makedirs(f"{ROOT}/Artin{TT}",exist_ok=True)
    g,cm=out['conj']
    rest_cases="\n".join(f"  | {s} => {L(out[s][0])}" for s in range(n-1))+f"\n  | _ => {L(out[n-1][0])}"
    words=f'''module

public import QBX.Formal.Streams.ArtinE8.Words

@[expose] public section

/-!
# Words for the `E{sub}` Garside element

Indices follow Mathlib's `CoxeterMatrix.E{sub}`, whose diagram is the restriction of the `E₈` diagram
(`QBX.Formal.Streams.e8Edge`) to `{{0, …, {n-1}}}`; so the `E₈` exponents `e8Exp` are used with bound
`{n}`.

* `{T}WordA = {L(A)}` and `{T}WordB = {L(B)}`: the two colour classes of the diagram.
* `{T}DeltaWordAB = (AB)^{half}` ({n*half} letters, the number of positive roots of `E{sub}`).
* `{T}RestWord s`: a word `X` with `Δ = σₛ X = X σ_{{ε s}}` (certified in `Artin{TT}.Cert*`), where
  `ε` is {"the diagram automorphism `0 ↔ 5`, `2 ↔ 4`" if n==6 else "the identity"}.
* `{T}ConjWord`, `{T}StdWord`: a conjugating word and the standard Coxeter word `[0, 1, …, {n-1}]`.

Generated by `QBX/scripts/gen_e67_artin_certificates.py`.
-/

namespace QBX.Formal.Streams

/-- First colour class of the `E{sub}` diagram. -/
def {T}WordA : List ℕ := {L(A)}

/-- Second colour class of the `E{sub}` diagram. -/
def {T}WordB : List ℕ := {L(B)}

/-- `(AB)^{half}`. -/
def {T}DeltaWordAB : List ℕ := (List.replicate {half} ({T}WordA ++ {T}WordB)).flatten

/-- `(BA)^{half}`. -/
def {T}DeltaWordBA : List ℕ := (List.replicate {half} ({T}WordB ++ {T}WordA)).flatten

/-- A word `X` with `Δ = σₛ X = X σ_{{ε s}}` (a reduced word for `s · w₀`). -/
def {T}RestWord : ℕ → List ℕ
{rest_cases}

/-- A word `g` with `c_bip · g = g · c_std` (commutation moves only). -/
def {T}ConjWord : List ℕ := {L(g)}

/-- The standard-order Coxeter word `[0, 1, …, {n-1}]`. -/
def {T}StdWord : List ℕ := {L(list(range(n)))}

end QBX.Formal.Streams
'''
    open(f"{ROOT}/Artin{TT}/Words.lean","w").write(words)
    hdr=lambda title: f'''module

public import QBX.Formal.Streams.Artin{TT}.Words

@[expose] public section

/-! # {title}

Machine-generated braid-move certificates (see `QBX.Formal.Streams.checkCode`): each number packs
the moves, one base-`2^13` digit `p * 64 + i * 8 + j` per move, and the theorem checks in the
kernel that applying them transforms the first word into the second.
-/

namespace QBX.Formal.Streams
'''
    def thm(name, u, v, mv, doc):
        D1u=None
        return f'''
/-- Packed moves for `{name}`. -/
def {name}Code : ℕ :=
  {enc(mv)}

/-- {doc} -/
theorem {name} :
    checkCode e8Exp {n} {u} {v} {len(mv)}
      {name}Code = true := by
  decide +kernel
'''
    D1=tuple((A+B)*half)
    # check rev cert
    rv=list(reversed(A+B)); rmv=comm_moves(rv,B+A)
    body=hdr(f"`(AB)^{half} = (BA)^{half}` and conjugacy of Coxeter words in the `E{sub}` Artin group")
    check(D1,tuple((B+A)*half),out['ab'])
    body+=thm(f"{T}Cert_AB",f"{T}DeltaWordAB",f"{T}DeltaWordBA",out['ab'],"`(AB)^"+str(half)+" = (BA)^"+str(half)+"`.")
    check(tuple(A+B+g),tuple(g+list(range(n))),cm)
    body+=thm(f"{T}Cert_cox",f"({T}WordA ++ {T}WordB ++ {T}ConjWord)",f"({T}ConjWord ++ {T}StdWord)",cm,"`c_bip · g` and `g · c_std` are related by commutation moves.")
    check(tuple(rv),tuple(B+A),rmv)
    body+=thm(f"{T}Cert_rev",L(rv),f"({T}WordB ++ {T}WordA)",rmv,"The reversed bipartite word commutes into `B ++ A`.")
    body+="\nend QBX.Formal.Streams\n"
    open(f"{ROOT}/Artin{TT}/CertAB.lean","w").write(body)
    for gi,grp in enumerate(c['groups']):
        body=hdr(f"`Δ = σₛ X = X σ_{{ε s}}` in the `E{sub}` Artin group, `s ∈ {L(grp)}`")
        for s in grp:
            X,m1,m2=out[s]
            check(D1,(s,)+X,m1); check(D1,X+(eps[s],),m2)
            body+=thm(f"{T}Cert_left{s}",f"{T}DeltaWordAB",f"({s} :: {T}RestWord {s})",m1,f"`Δ = σ{s} X`.")
            body+=thm(f"{T}Cert_right{s}",f"{T}DeltaWordAB",f"({T}RestWord {s} ++ [{eps[s]}])",m2,f"`Δ = X σ{eps[s]}`.")
        body+="\nend QBX.Formal.Streams\n"
        open(f"{ROOT}/Artin{TT}/CertGen{gi}.lean","w").write(body)
print("ok")
