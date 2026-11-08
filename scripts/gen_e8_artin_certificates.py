"""Generate the E8 braid-move certificates in QBX/Formal/Streams/ArtinE8/ (CertAB, CertGen0-7).

Implements the constructive proof of Matsumoto's theorem: two reduced words of the same element
of W(E8) are connected by braid moves.  Output is only a hint; Lean re-checks every move
(QBX.Formal.Streams.checkCode_sound).  Usage: python3 QBX/scripts/gen_e8_artin_certificates.py
(prints move counts; writes certs.pkl).  The Lean files were then emitted from certs.pkl by
packing each move (p, i, j) as the base-2^13 digit p*64 + i*8 + j, least significant first.
"""
import sys, functools
sys.setrecursionlimit(100000)
n=8
edges=[(0,2),(1,3),(2,3),(3,4),(4,5),(5,6),(6,7)]
M=[[2]*n for _ in range(n)]
for i in range(n): M[i][i]=1
for a,b in edges: M[a][b]=M[b][a]=3
C=[[0]*n for _ in range(n)]
for i in range(n): C[i][i]=2
for a,b in edges: C[a][b]=C[b][a]=-1
def refl(i,v):
    c=sum(C[i][j]*v[j] for j in range(n))
    v=list(v); v[i]-=c; return tuple(v)
def act(word,v):
    for i in reversed(word): v=refl(i,v)
    return v
def unit(i): return tuple(1 if j==i else 0 for j in range(n))
def neg(v): return all(x<=0 for x in v)
# element as tuple of images of simple roots
def elem(word): return tuple(act(word,unit(i)) for i in range(n))
def apply_elem(e,v):
    r=[0]*n
    for i in range(n):
        for j in range(n): r[j]+=v[i]*e[i][j]
    return tuple(r)
def reduced_word(word):
    # reduced word for element via right descents
    e=elem(word); res=[]
    while True:
        for j in range(n):
            if neg(e[j]): break
        else: break
        res.append(j)
        # e := e * s_j
        e=tuple(apply_elem(e,refl(j,unit(i))) for i in range(n))
    return list(reversed(res))
def alt(s,t,m): return [s if k%2==0 else t for k in range(m)]
@functools.lru_cache(maxsize=None)
def transform(u,v):
    if u==v: return ()
    if u[0]==v[0]:
        return tuple((p+1,i,j) for (p,i,j) in transform(u[1:],v[1:]))
    s,t=u[0],v[0]; m=M[s][t]
    a=alt(s,t,m)
    # w' = a^{-1} u ; a^{-1} = reversed a
    r=tuple(reduced_word(list(reversed(a))+list(u)))
    A=tuple(a)+r; B=tuple(alt(t,s,m))+r
    assert len(A)==len(u)
    return transform(u,A)+((0,s,t),)+transform(B,v)
def check(u,v,moves):
    w=list(u)
    for p,i,j in moves:
        m=M[i][j]; assert w[p:p+m]==alt(i,j,m); w[p:p+m]=alt(j,i,m)
    assert w==list(v)

import pickle
A=[0,3,5,7];B=[1,2,4,6]
D1=tuple((A+B)*15); D2=tuple((B+A)*15)
def enc(mv):
    c=0
    for (p,i,j) in reversed(mv):
        assert p<128
        c=c*8192+(p*64+i*8+j)
    return c
out={}
mv=transform(D1,D2); check(D1,D2,mv); out['ab']=(D1,D2,mv)
for s in range(n):
    X=tuple(reduced_word([s]+list(D1)))
    m1=transform(D1,(s,)+X); m2=transform(D1,X+(s,))
    out[s]=(X,m1,m2)
pickle.dump(out,open('certs.pkl','wb'))
for k,v in out.items(): print(k, len(v[2]) if k=="ab" else (len(v[1]), len(v[2])))
