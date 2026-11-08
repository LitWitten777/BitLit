import sys, functools, itertools, math
sys.setrecursionlimit(100000)
sys.set_int_max_str_digits(10000000)
TYPES = {
 # name: (n, weighted edges, A, B, half, eps)
 'B3': (3, [(0,1,3),(1,2,4)], [0,2],[1], 3, None),
 'B4': (4, [(0,1,3),(1,2,3),(2,3,4)], [0,2],[1,3], 4, None),
 'B5': (5, [(0,1,3),(1,2,3),(2,3,3),(3,4,4)], [0,2,4],[1,3], 5, None),
 'D4': (4, [(0,1,3),(1,2,3),(1,3,3)], [0,2,3],[1], 3, None),
 'D5': (5, [(0,1,3),(1,2,3),(2,3,3),(2,4,3)], [0,2],[1,3,4], 4, {3:4,4:3}),
 'D6': (6, [(0,1,3),(1,2,3),(2,3,3),(3,4,3),(3,5,3)], [0,2,4,5],[1,3], 5, None),
 'F4': (4, [(0,1,3),(1,2,4),(2,3,3)], [0,2],[1,3], 6, None),
 'H3': (3, [(0,1,3),(1,2,5)], [0,2],[1], 5, None),
 'H4': (4, [(0,1,3),(1,2,3),(2,3,5)], [0,2],[1,3], 15, None),
}
def setup(name):
    global N,M,C
    n,edges,A,B,half,eps=TYPES[name]
    N=n
    M=[[2]*n for _ in range(n)]
    for i in range(n): M[i][i]=1
    for a,b,k in edges: M[a][b]=M[b][a]=k
    C=[[-2*math.cos(math.pi/M[i][j]) if i!=j else 2.0 for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            if abs(C[i][j])<1e-12: C[i][j]=0.0
EPS=1e-9
def refl(i,v):
    c=sum(C[i][j]*v[j] for j in range(N)); v=list(v); v[i]-=c; return tuple(v)
def act(word,v):
    for i in reversed(word): v=refl(i,v)
    return v
def unit(i): return tuple(1.0 if j==i else 0.0 for j in range(N))
def neg(v): return all(x<=EPS for x in v)
def elem(word): return tuple(act(word,unit(i)) for i in range(N))
def reduced_word(word):
    # repeatedly strip right descents
    w=list(word); res=[]
    e=elem(w)
    cur=list(word)
    while True:
        e=elem(cur)
        for j in range(N):
            if neg(e[j]): break
        else: break
        res.append(j); cur=cur+[j]
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
    assert len(A)==len(u), (u,v,A)
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
            if M[a][b]!=2 and a!=b:
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
def compute(name):
    setup(name); transform.cache_clear()
    n,edges,A,B,half,eps=TYPES[name]
    eps=eps or {}
    E=lambda s: eps.get(s,s)
    D1=tuple((A+B)*half); D2=tuple((B+A)*half)
    assert len(reduced_word(list(D1)))==len(D1)
    out={}
    mv=transform(D1,D2); check(D1,D2,mv); out['ab']=mv
    for s in range(n):
        X=tuple(reduced_word([s]+list(D1)))
        m1=transform(D1,(s,)+X); m2=transform(D1,X+(E(s),))
        check(D1,(s,)+X,m1); check(D1,X+(E(s),),m2)
        out[s]=(X,m1,m2)
    std=list(range(n)); bip=A+B
    found=None
    for L in range(0,12):
        for g in itertools.product(range(n),repeat=L):
            if trace_eq(bip+list(g), list(g)+std): found=list(g); break
        if found is not None: break
    cm=comm_moves(bip+found, found+std)
    out['conj']=(found,cm)
    return out
if __name__=='__main__':
    import time
    for name in TYPES:
        t=time.time(); out=compute(name)
        n=TYPES[name][0]
        print(name, len(out['ab']), [(len(out[s][1]),len(out[s][2])) for s in range(n)], out['conj'][0], round(time.time()-t,1))
