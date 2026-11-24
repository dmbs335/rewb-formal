"""Audit only: bounded enumeration of projected target variables, not a fast QE implementation."""
from itertools import product
from random import Random

# DFA = (transition table over {0,1}, start, accept set)
def walk(d, s, q=None):
    q=d[1] if q is None else q
    for x in s: q=d[0][q][int(x)]
    return q

def acc(d,s): return walk(d,s) in d[2]
def unary_period(s):
    return next(q for q in range(1,len(s)+1) if s[q:]==s[:-q])
def runs(w):
    n=len(w); ret=[]
    for l in range(n):
        for r in range(l+2,n+1):
            q=unary_period(w[l:r])
            if r-l<2*q: continue
            if l>0 and w[l-1]==w[l-1+q]: continue
            if r<n and w[r]==w[r-q]: continue
            ret.append((l,r,q))
    return ret

def tab(w, ds):
    n=len(w)
    return [[[acc(d,w[i:j]) for j in range(n+1)] for i in range(n+1)] for d in ds]

def oracle(w,ds,lim=None,Q=None):
    A,B,C,D,F,G,H=tab(w,ds); n=len(w); rr=runs(w) if Q is not None else None
    for p in range(n+1):
        for e in range(p,n+1):
            L=e-p
            if lim is not None and L>lim: continue
            for k in range(e,n-L+1):
                f=k+L
                if Q is not None and not any(q<=Q and l<=p and f<=r and k>p and (k-p)%q==0 for l,r,q in rr): continue
                if w[p:e]!=w[k:f] or not G[e][k] or not H[f][n]: continue
                for j in range(p,e+1):
                    if not D[p][j]: continue
                    for t in range(j,e+1):
                        if not B[j][t] or not F[t][e]: continue
                        u=w[j:t]; h=len(u)
                        for a in range(h,p+1):
                            i=a-h
                            if A[0][i] and C[a][p] and w[i:a]==u: return True
    return False

def batch_direct(w,ds,p,u):
    A,_,C,*_=ds; h=len(u)
    return any(acc(A,w[:a-h]) and acc(C,w[a:p]) and w[a-h:a]==u for a in range(h,p+1))

def short_algo(w,ds,L0):
    A,B,C,D,F,G,H=tab(w,ds); n=len(w); queries=set()
    # Vok is computed by direct comparison in this audit, rather than the suffix-array sweep.
    for p in range(n+1):
        m=min(n,p+L0)
        ok=[False]*(m-p+1)
        for e in range(p,m+1):
            L=e-p
            ok[L]=any(w[p:e]==w[k:k+L] and G[e][k] and H[k+L][n] for k in range(e,n-L+1))
        possible=set()
        for t in range(m,p-1,-1):
            if t<m: possible={q for q in range(len(ds[4][0])) if ds[4][0][q][int(w[t])] in possible}
            if ok[t-p]: possible |= ds[4][2]
            if ds[4][1] not in possible: continue
            for j in range(p,t+1):
                if D[p][j] and B[j][t]: queries.add((p,w[j:t]))
    return any(batch_direct(w,ds,p,u) for p,u in queries)

def source_records(w,A,l,r,q,a,rho):
    h=l+(a-rho-l)%q
    M=(a-rho-h)//q
    if M<3: return None,set()
    V=w[h:h+q]; state=walk(A,w[:h]); seen={}; path=[]
    while state not in seen:
        seen[state]=len(path); path.append(state); state=walk(A,V,state)
    mu=seen[state]; lam=len(path)-mu
    # Expand the exact values and upper-tail congruences just for auditing.
    out=set()
    for c in range(mu):
        if path[c] in A[2] and M-c>=3: out.add(M-c)
    for c in range(mu,len(path)):
        if path[c] in A[2]:
            out.update(m for m in range(3,M-mu+1) if (M-m-c)%lam==0)
    return V,out

def periodic_acc(d,V,rx,zx,ry,zy,suffix=''):
    if zy<zx or (zy==zx and ry<rx): return False
    if zy==zx: return acc(d,V[rx:ry]+suffix)
    q=walk(d,V[rx:]); g=[walk(d,V,i) for i in range(len(d[0]))]
    for _ in range(zy-zx-1): q=g[q]
    return walk(d,V[:ry]+suffix,q) in d[2]

def periodic_algo(w,ds,Q):
    A,B,C,D,F,G,H=ds; rr=runs(w); n=len(w)
    src={}; checks=0; short=[]; long=[]
    for l,r,q in rr:
        if q>Q: continue
        V=w[l:l+q]; N,eta=divmod(r-l,q)
        if r-l>=3*q:
            for a in range(l,r+1):
                for rho in range(q):
                    key,ms=source_records(w,A,l,r,q,a,rho)
                    if not ms: continue
                    for m in ms:
                        i=a-q*m-rho
                        assert l<=i<=a<=r and acc(A,w[:i])
                        assert w[i:i+q]==key
                    expected={m for m in range(3,(a-l-rho)//q+1) if acc(A,w[:a-q*m-rho])}
                    assert ms==expected
                    checks+=1
                    src.setdefault((q,key,rho),[]).append((a,ms))
        for p in range(l,r+1):
            zp,rp=divmod(p-l,q)
            # Enumerate block coordinates to audit projection of the fixed Presburger formula.
            for rj,re,rho in product(range(q),repeat=3):
                rt=(rj+rho)%q; carry=(rj+rho)//q
                phase=V[rj:]+V[:rj]; poss=set()
                for zj in range(N+1):
                    j=l+q*zj+rj
                    if not p<=j<=r or not periodic_acc(D,V,rp,zp,rj,zj): continue
                    for m in range(N+1):
                        zt=zj+m+carry; t=l+q*zt+rt
                        if not j<=t<=r or not periodic_acc(B,V,rj,zj,rt,zt): continue
                        for ze in range(N+1):
                            e=l+q*ze+re
                            if not t<=e<=r or not periodic_acc(F,V,rt,zt,re,ze): continue
                            for zk in range(zp+1,N+1):
                                k=l+q*zk+rp; zf=ze-zp+zk; f=l+q*zf+re
                                if not e<=k<=f<=r: continue
                                if periodic_acc(G,V,re,ze,rp,zk) and periodic_acc(H,V,re,zf,eta,N,w[r:]):
                                    assert w[p:e]==w[k:f]
                                    poss.add(m)
                for m in poss:
                    ell=q*m+rho
                    if m<3:
                        u=(phase*4)[:ell]
                        short.append((p,u))
                    else:
                        long.append((p,(q,phase,rho),m))
    a=any(batch_direct(w,ds,p,u) for p,u in short)
    b=any(any(e<=p and m in ms and acc(C,w[e:p]) for e,ms in src.get(key,[])) for p,key,m in long)
    return a or b,checks,len(short),len(long)

def main():
    rng=Random(73119); all_=( ((0,0),),0,{0}); eps=(((1,1),(1,1)),0,{0})
    def randdfa():
        if rng.random()<.35: return all_
        if rng.random()<.12: return eps
        k=rng.randint(1,3)
        return tuple(tuple(rng.randrange(k) for _ in range(2)) for _ in range(k)),rng.randrange(k),{i for i in range(k) if rng.randrange(2)}
    short_count=per_count=pos_s=pos_p=rec_count=shortq=longq=0
    for _ in range(420):
        n=rng.randint(0,12); q=rng.randint(1,3)
        V=''.join(rng.choice('01') for _ in range(q))
        if rng.random()<.65:
            w=(V*(n+q))[:n]
            if n and rng.random()<.5:
                z=rng.randrange(n); w=w[:z]+str(1-int(w[z]))+w[z+1:]
        else: w=''.join(rng.choice('01') for _ in range(n))
        ds=tuple(randdfa() for _ in range(7)); L0=rng.randrange(n+1); Q=rng.randint(1,3)
        expected=oracle(w,ds,lim=L0); actual=short_algo(w,ds,L0)
        assert expected==actual,(w,ds,L0,expected,actual)
        short_count+=1;pos_s+=expected
        expected=oracle(w,ds,Q=Q);actual,c,s,l=periodic_algo(w,ds,Q)
        assert expected==actual,(w,ds,Q,expected,actual)
        per_count+=1;pos_p+=expected;rec_count+=c;shortq+=s;longq+=l
    # Deliberate external source and non-empty long capture witnesses.
    for w in ('0001000000','111011111111','010101001010101010101'):
        ds=(eps,all_,all_,eps,eps,eps,eps)
        expected=oracle(w,ds,Q=2);actual,c,s,l=periodic_algo(w,ds,2)
        assert expected==actual,(w,expected,actual)
        per_count+=1;pos_p+=expected;rec_count+=c;shortq+=s;longq+=l
    print(dict(short_cases=short_count,short_positive=pos_s,periodic_cases=per_count,periodic_positive=pos_p,nonempty_source_records=rec_count,short_target_records=shortq,long_target_records=longq))
if __name__=='__main__': main()
