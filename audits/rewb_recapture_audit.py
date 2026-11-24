"""Checks algebraic reductions for all-start one-use REWB matching.
Not an implementation of the dynamic suffix-tree data structure or runs enumeration.
Run: python rewb_recapture_audit.py
"""
from itertools import product
from random import Random
from math import lcm
from collections import defaultdict

rng=Random(314159)
# monoid operation: read f then g.
def comp(f,g): return tuple(g[x] for x in f)
def ident(k): return tuple(range(k))
def tau(d, s):
    f=ident(len(d[0]));
    for x in s: f=comp(f,d[x])
    return f

def dfa(k):
    return (tuple(tuple(rng.randrange(k) for _ in range(k)) for _ in range(2)), frozenset(i for i in range(k) if rng.randrange(2)))

def accept(D,s): return tau(D[0],s)[0] in D[1]

def orbit(g):
    seen={}; vals=[]; cur=ident(len(g))
    while cur not in seen:
        seen[cur]=len(vals); vals.append(cur); cur=comp(cur,g)
    return vals,seen[cur],len(vals)-seen[cur]

def powers(g,min_z=0):
    """Each power value -> union of singleton (a,0) or progression (a,d)."""
    vals,mu,lam=orbit(g)
    out=[]
    for i,v in enumerate(vals):
        if i<mu:
            if i>=min_z: out.append((v,i,0))
        else:
            a=i+max(0,(min_z-i+lam-1)//lam)*lam
            out.append((v,a,lam))
    return out

def sum_ok(target, records, coeffs):
    a=sum(c*x[0] for c,x in zip(coeffs,records))
    rem=target-a
    if rem<0:return False
    steps=[c*x[1] for c,x in zip(coeffs,records) if x[1]]
    if not steps:return rem==0
    # convert each AP to a finite union of APs of common step.
    K=lcm(*steps)
    return any(rem>=b and (rem-b)%K==0 for b in map(sum, product(*(range(0,K,d) for d in steps))))

def run_formula(w,p,R,q,B,C,E):
    if R-p<4*q:return False
    V=w[p:p+q]; N,eta=divmod(R-p,q)
    gb,gc,ge=(tau(D[0],V) for D in (B,C,E))
    EB=tau(E[0],w[R:])
    EF=comp(tau(E[0],V[:eta]),EB)
    PB=powers(gb,2); PC=powers(gc); PE=powers(ge)
    # rho=0
    for (b,a,ad),(c,z,zd),(e,j,jd) in product(PB,PC,PE):
        if b[0] in B[1] and c[0] in C[1] and EF[e[0]] in E[1] and sum_ok(N,[(a,ad),(z,zd),(j,jd)],[2,1,1]):return True
    # 0<rho<q; deduplicate finite transition triples.
    triples={(tau(B[0],V[:rho]),tau(C[0],V[rho:]),tau(E[0],V[rho:])) for rho in range(1,q)}
    for bp,cs,es in triples:
        for (b,a,ad),(c,z,zd),(e,j,jd) in product(PB,PC,PE):
            if bp[b[0]] in B[1] and c[cs[0]] in C[1] and EF[e[es[0]]] in E[1] and sum_ok(N-2,[(a,ad),(z,zd),(j,jd)],[2,1,1]):return True
    triples={(tau(B[0],V[:rho]),tau(C[0],V[rho:]),tau(E[0],V[rho:eta])) for rho in range(1,eta+1)}
    for bp,cs,es in triples:
        for (b,a,ad),(c,z,zd) in product(PB,PC):
            if bp[b[0]] in B[1] and c[cs[0]] in C[1] and EB[es[0]] in E[1] and sum_ok(N-1,[(a,ad),(z,zd)],[2,1]):return True
    return False

def run_oracle(w,p,R,q,B,C,E):
    return any(accept(B,w[p:p+L]) and accept(C,w[p+L:i]) and accept(E,w[i+L:]) for L in range(2*q,(R-p)//2+1) for i in range(p+((L+q-1)//q)*q,R-L+1,q))

# DFA union of stages. Stage 0 loops (only marks restrict first jump).
def stage_dfa(C,E):
    d=tuple((0,)+tuple(1+x for x in C[0][a])+tuple(1+len(C[0][0])+x for x in E[0][a]) for a in range(2))
    j1={(0,1)}; j2={(1+x,1+len(C[0][0])) for x in C[1]}
    F={1+len(C[0][0])+x for x in E[1]}
    return d,j1,j2,F

def cluster_partition(occ,H):
    groups=[]
    for p in occ:
        if groups and 2*(p-groups[-1][-1])<=H: groups[-1].append(p)
        else:groups.append([p])
    return groups

def valid_distinct(w,groups,L,marks,C,E):
    return any(p in marks and p+L<=i and accept(C,w[p+L:i]) and accept(E,w[i+L:]) for t,g in enumerate(groups) for p in g for h in groups[t+1:] for i in h)

def type_of(x,T,K):return (0,x) if x<T else (1,x%K)

def representative(ty,T,K):return ty[1] if ty[0]==0 else T+(ty[1]-T)%K

def type_query(c,u,v,T,K,marks,only_last=False):
    """Represent possible exponent type pairs. Enumeration is only an oracle for rank query.
    In the proof the intersection of two types is an interval + residue constraint.
    """
    return {(type_of(t-u,T,K),type_of(v-t,T,K)) for t in range(u,v+1) if t in marks and (not only_last or t==v)}

def cluster_formula(w,X,H,L,occ,marks,C,E):
    groups=cluster_partition(occ,H); d,J1,J2,F=stage_dfa(C,E); m=len(d[0]);
    if not groups:return False
    # Uniform bounds for transformation powers: each individual orbit, not full monoid.
    q=next((g[1]-g[0] for g in groups if len(g)>1),None)
    if q:
        V=X[:q]; rho=H%q; U=V[rho:]+V[:rho]; gv=tau(d,V); gu=tau(d,U)
        ovs=[orbit(gv),orbit(gu)]; T=max(o[1] for o in ovs); K=lcm(*(o[2] for o in ovs))
    Ttail=tau(d,X[L:H])
    active={0:{0},1:set()}
    for idx,g in enumerate(groups):
        s=g[0]; c=len(g); t=g[-1]; nxt=groups[idx+1][0] if idx+1<len(groups) else len(w)
        prev=groups[idx-1][-1] if idx else None
        in1=prev is not None and prev+H>s
        out1=idx+1<len(groups) and t+H>nxt
        new={0:set(),1:set()}
        for im in (0,1):
            if im and not in1:continue
            I=prev+H if im else s
            if I>nxt:raise AssertionError('bad skip boundary')
            new[0].update(tau(d,w[I:nxt])[state] for state in active[im])
            u=1 if im else 0
            for om in (0,1):
                if om and not out1:continue
                v=c-1 if om or not out1 else c-2
                if u>v:continue
                if c==1:
                    for jumps,allow in [(J1,s in marks),(J2,True)]:
                        if not allow:continue
                        a=tau(d,w[I:s]); b=ident(m) if om else tau(d,w[s+H:nxt]);
                        for state in active[im]:
                            for x,y in jumps:
                                if a[state]==x:new[om].add(b[Ttail[y]])
                    continue
                assert all(g[i]==s+i*q for i in range(c))
                a=tau(d,w[I:g[u]]); b=ident(m) if om else tau(d,w[g[v]+H:nxt]);
                for jumps,inds in [(J1,{j for j,p in enumerate(g) if p in marks}),(J2,set(range(c)))]:
                    for t1,t2 in type_query(c,u,v,T,K,inds,bool(om)):
                        i1,i2=representative(t1,T,K),representative(t2,T,K)
                        f1=ident(m);f2=ident(m)
                        for _ in range(i1):f1=comp(f1,gv)
                        for _ in range(i2):f2=comp(f2,gu)
                        for state in active[im]:
                            for x,y in jumps:
                                if f1[a[state]]==x:new[om].add(b[f2[Ttail[y]]])
        active=new
    return bool(active[0]&F)

def brute_starts(w,B,C,E):
    return {p for p in range(len(w)+1) if any(w[p:p+L]==w[i:i+L] and accept(B,w[p:p+L]) and accept(C,w[p+L:i]) and accept(E,w[i+L:]) for L in range((len(w)-p)//2+1) for i in range(p+L,len(w)-L+1))}

def main():
    runchecks=0
    for _ in range(1800):
        q=rng.randrange(1,7); V=tuple(rng.randrange(2) for _ in range(q)); size=rng.randrange(4*q,11*q+1)
        R=size; w=(V*((size+q-1)//q))[:size]+tuple(rng.randrange(2) for _ in range(rng.randrange(6)))
        B,C,E=[dfa(rng.randrange(1,5)) for _ in range(3)]
        for p in set([0,rng.randrange(size),rng.randrange(size)]):
            a=run_formula(w,p,R,q,B,C,E); b=run_oracle(w,p,R,q,B,C,E)
            assert a==b,(w,p,R,q,B,C,E,a,b)
            runchecks+=1
    clchecks=0; shortened=0
    for _ in range(1800):
        n=rng.randrange(1,31); base=tuple(rng.randrange(2) for _ in range(rng.randrange(1,9)))
        if rng.randrange(2):w=tuple(rng.randrange(2) for _ in range(n))
        else:
            w=list((base*((n+len(base)-1)//len(base)))[:n]);
            for _ in range(rng.randrange(4)):w[rng.randrange(n)]^=1
            w=tuple(w)
        C,E=[dfa(rng.randrange(1,5)) for _ in range(2)]
        marks={p for p in range(n) if rng.randrange(2)}
        p=rng.randrange(n); H=rng.randrange(1,n-p+1); X=w[p:p+H]
        occ=[i for i in range(n-H+1) if w[i:i+H]==X]
        groups=cluster_partition(occ,H)
        for L in range(1,H+1):
            if [i for i in range(n-L+1) if w[i:i+L]==X[:L]]!=occ:continue
            if cluster_partition(occ,L)!=groups:continue
            if any((y-x<H)!=(y-x<L) for x,y in zip(occ,occ[1:]) if 2*(y-x)>H):continue
            a=cluster_formula(w,X,H,L,occ,marks,C,E); b=valid_distinct(w,groups,L,marks,C,E)
            assert a==b,(w,X,H,L,occ,marks,C,E,a,b)
            clchecks+=1; shortened+=int(L<H)
    print('run-local arithmetic cases:',runchecks)
    print('cross-cluster transfer cases:',clchecks,'(shortened:',shortened,')')
def reverse_dfa(D):
    tr, F=D; states=[F]; ids={F:0}; rows=[]
    for S in states:
        row=[]
        for a in range(2):
            T=frozenset(i for i,v in enumerate(tr[a]) if v in S)
            if T not in ids:ids[T]=len(states);states.append(T)
            row.append(ids[T])
        rows.append(row)
    return tuple(tuple(row[a] for row in rows) for a in range(2)),frozenset(i for i,S in enumerate(states) if 0 in S)

def all_starts_test(w,B,C,E):
    """Full semantic simulation using deliberately slow run/substring enumeration.
    The proof uses a suffix tree and dynamic rank/transfer trees instead.
    """
    n=len(w); good=set()
    if accept(B,()):
        good.update(p for p in range(n+1) if any(accept(C,w[p:j]) and accept(E,w[j:]) for j in range(p,n+1)))
    # maximal runs, naive enumeration. Only exponent >=4 relevant.
    for q in range(1,n//4+1):
        for l in range(n-4*q+1):
            if l and w[l-1]==w[l-1+q]:continue
            R=l+q
            while R<n and w[R]==w[R-q]:R+=1
            if R-l<4*q:continue
            if any(all(w[j]==w[j-d] for j in range(l+d,R)) for d in range(1,q)):continue
            for p in range(l,R-4*q+1):
                if run_formula(w,p,R,q,B,C,E):good.add(p)
    fam=defaultdict(list)
    for X in {w[i:j] for i in range(n) for j in range(i+1,n+1)}:
        L=len(X);occ=tuple(i for i in range(n-L+1) if w[i:i+L]==X)
        groups=tuple(tuple(g) for g in cluster_partition(occ,L))
        flags=tuple(y[0]-x[-1]<L for x,y in zip(groups,groups[1:]))
        fam[(occ,groups,flags)].append(X)
    for (occ,groups,flags),words in fam.items():
        if len(groups)<2:continue
        X=max(words,key=len);H=len(X)
        for L in set(len(z) for z in words if accept(B,z)):
            assert any(z==X[:L] for z in words)
            for p in occ:
                if p not in good and cluster_formula(w,X,H,L,occ,{p},C,E):good.add(p)
    return good

def sequential_brute(w,A,B,C,D,F,G,H):
    n=len(w)
    left={e for e in range(n+1) if any(accept(A,w[:p]) and w[p:p+L]==w[e-L:e] and accept(B,w[p:p+L]) and accept(C,w[p+L:e-L]) for p in range(e+1) for L in range((e-p)//2+1))}
    right=brute_starts(w,F,G,H)
    return any(e<=j and accept(D,w[e:j]) for e in left for j in right)

def extra():
    count=0;seq=0
    for _ in range(1100):
        n=rng.randrange(0,16)
        w=tuple(rng.randrange(2) for _ in range(n))
        A,B,C,D,F,G,H=[dfa(rng.randrange(1,4)) for _ in range(7)]
        a=all_starts_test(w,B,C,A); b=brute_starts(w,B,C,A)
        assert a==b,(w,B,C,A,a,b)
        count+=1
        if _<420:
            left={n-p for p in all_starts_test(w[::-1],reverse_dfa(B),reverse_dfa(C),reverse_dfa(A))}
            right=all_starts_test(w,F,G,H)
            Q=set(); ans=False
            for j in range(n+1):
                if j in left:Q.add(0)
                if j in right and Q&D[1]:ans=True
                if j<n:Q={D[0][w[j]][q] for q in Q}
            exp=sequential_brute(w,A,B,C,D,F,G,H)
            assert ans==exp,(w,ans,exp,left,right)
            seq+=1
    print('all-start semantic simulations:',count)
    print('sequential recapture simulations:',seq)
if __name__=='__main__':
    main();extra()
