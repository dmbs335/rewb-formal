"""Audit for block-packed fixed two-use 1-REWB matching.

This is a reference correctness checker, NOT a benchmark of the claimed
asymptotic running time. It uses direct LCE/LCS and emulates universal
microblock lookup by computing products on demand. The short-REWB branch
is checked by direct decomposition rather than the ICALP 2026 algorithm.
Alphabet: 0,1. Run with Python 3.10+.
"""
from dataclasses import dataclass
from itertools import product
import random

@dataclass(frozen=True)
class DFA:
    trans: tuple
    finals: int
    start: int = 0
    @property
    def size(self): return len(self.trans)
    def state(self,w,q=None):
        if q is None: q=self.start
        for c in w: q=self.trans[q][c]
        return q
    def accepts(self,w): return bool(self.finals>>self.state(w)&1)

def bits(m):
    while m:
        b=m&-m; yield b.bit_length()-1; m-=b

def revmask(D,states,w):
    return sum(1<<q for q in range(D.size) if states>>D.state(w,q)&1)

def lcs(w,a,t):
    d=0
    while a>d and t>d and w[a-d-1]==w[t-d-1]: d+=1
    return d

def lce(w,a,t):
    d=0; n=len(w)
    while a+d<n and t+d<n and w[a+d]==w[t+d]: d+=1
    return d

def run_family(w,lo,hi,delta,b):
    """First-copy END a in [lo,hi]; second end t=a+delta.
    Return at most two intervals (a_low,a_high,l,cap) for d>b.
    The interval width must be <=b; l is maximal equal-run start.
    """
    n=len(w); lo=max(lo,0); hi=min(hi,n-delta)
    assert hi-lo+1<=b
    if delta<=b or lo>hi or lo==0: return []
    i=lo-1
    if w[i]!=w[i+delta]: return []
    l=i-lcs(w,i,i+delta); r=i+lce(w,i,i+delta)
    a0=max(lo,l+b+1); a1=min(hi,r)
    if a0>a1: return []
    out=[]
    if a0<=min(a1,l+delta): out.append((a0,min(a1,l+delta),l,False))
    if max(a0,l+delta+1)<=a1: out.append((max(a0,l+delta+1),a1,l,True))
    return out

def mask_interval(lo,hi,T,W):
    a=max(0,lo-T); b=min(W-1,hi-T)
    return 0 if a>b else ((1<<(b-a+1))-1)<<a

def shear_tile(rows,W):
    """Reference for the universal W x W diagonal-shear lookup."""
    out=[0]*(2*W-1)
    for i,row in enumerate(rows):
        for j in bits(row): out[j-i+W-1] |= 1<<j
    return out

def transpose_rows(rows,W):
    """Transpose n rows of W bits into W columns, packed by W."""
    n=len(rows); cols=[[0]*((n+W-1)//W) for _ in range(W)]
    for off in range(0,n,W):
        for i,row in enumerate(rows[off:off+W]):
            for j in bits(row): cols[j][off//W]|=1<<i
    return cols

def transpose_cols(cols,n,W):
    out=[0]*n
    for j,col in enumerate(cols):
        for h,word in enumerate(col):
            for i in bits(word):
                if h*W+i<n: out[h*W+i]|=1<<j
    return out

def short_outer(w,G,H,b):
    """One band word per start p, bit L for L<=b."""
    n=len(w); out=[0]*(n+1)
    for L in range(min(b,n)+1):
        groups={}
        for p in range(n-L+1): groups.setdefault(w[p:p+L],[]).append(p)
        for occ in groups.values():
            # descending order; insert eligible second starts before checking
            events=[(p+L,0,p) for p in occ]+[(k,1,k) for k in occ if H.accepts(w[k+L:])]
            events.sort(reverse=True); active=0; prev=n
            for x,typ,p in events:
                active=revmask(G,active,w[x:prev]); prev=x
                if typ: active|=G.finals
                elif active>>G.start&1: out[p]|=1<<L
    return out

def outer_blocks(w,G,H,F,W,b):
    """Yield packed rows of O and R, processing end blocks right-to-left."""
    n=len(w); N=n+1; band=short_outer(w,G,H,b)
    Hgood=[H.accepts(w[f:]) for f in range(N)]
    P=(N+W-1)//W; v=[[0]*P for _ in range(F.size)]
    for T in reversed(range(0,N,W)):
        U=min(n,T+W-1); inject=[[0]*G.size for _ in range(N)]; cap=[0]*N
        for delta in range(b+1,N):
            for lo,hi,l,is_cap in run_family(w,T,U,delta,b):
                for a in range(lo,hi+1):  # emulates constant-time mask lookup
                    if not Hgood[a+delta]: continue
                    if is_cap: cap[delta]|=1<<(a-T)
                    else: inject[l][G.state(w[a:l+delta])]|=1<<(a-T)
        for D in range(0,N,W):
            row=cap[D:D+W]+[0]*max(0,D+W-N)
            for k,mask in enumerate(shear_tile(row,W)):
                p=T-D+k-(W-1)
                if mask:
                    assert 0<=p<N; inject[p][G.start]|=mask
        active=[0]*G.size; O=[0]*N
        for p in range(N):
            for q in range(G.size): active[q]|=inject[p][q]
            for q in bits(G.finals): O[p]|=active[q]
            O[p]&=mask_interval(p,n,T,W)
            shift=T-p
            small=(band[p]>>shift) if shift>=0 else (band[p]<<(-shift))
            O[p]|=small & ((1<<(U-T+1))-1)
            if p<n:
                new=[0]*G.size
                for q in range(G.size): new[G.trans[q][w[p]]]|=active[q]
                active=new
        Ocols=transpose_rows(O,W); Rcols=[[0]*P for _ in range(W)]
        for t in range(U,T-1,-1):
            nxt=[]
            for q in range(F.size):
                base=v[F.trans[q][w[t]]] if t<n else [0]*P
                nxt.append([x|y for x,y in zip(base,Ocols[t-T])] if F.finals>>q&1 else base.copy())
            v=nxt; Rcols[t-T]=v[F.start].copy()
        R=transpose_cols(Rcols,N,W)
        yield T,U,O,R

def scalar_outer(w,G,H,F):
    n=len(w); O=[[False]*(n+1) for _ in range(n+1)]; R=[[False]*(n+1) for _ in range(n+1)]
    for p in range(n+1):
        for e in range(p,n+1):
            L=e-p
            O[p][e]=any(w[p:e]==w[k:k+L] and G.accepts(w[e:k]) and H.accepts(w[k+L:]) for k in range(e,n-L+1))
        for t in range(n+1): R[p][t]=any(O[p][e] and F.accepts(w[t:e]) for e in range(t,n+1))
    return O,R

# Each entry of a Boolean transition matrix is a W-bit mask.
def mat_ident(s,W): return tuple(tuple(((1<<W)-1) if i==j else 0 for j in range(s)) for i in range(s))
def mat_zero(s): return tuple((0,)*s for _ in range(s))
def mat_mul(a,b):
    s=len(a); c=[[0]*s for _ in range(s)]
    for i in range(s):
        for k,x in enumerate(a[i]):
            if x:
                for j,y in enumerate(b[k]): c[i][j]|=x&y
    return tuple(map(tuple,c))
def scalar_mul(a,b):
    out=[]
    for row in a:
        x=0
        for k in bits(row): x|=b[k]
        out.append(x)
    return tuple(out)
def pack_matrices(zero,one,m,W):
    allmask=(1<<W)-1; s=len(zero)
    return tuple(tuple(((allmask^m) if zero[i]>>j&1 else 0)|(m if one[i]>>j&1 else 0) for j in range(s)) for i in range(s))

def two_stage(D,C):
    d=D.size; N=d+C.size; E=[]
    for flag in (0,1):
        E.append(tuple((1<<i)|((1<<(d+C.start)) if flag and i<d and D.finals>>i&1 else 0) for i in range(N)))
    T=[tuple((1<<D.trans[i][c]) if i<d else (1<<(d+C.trans[i-d][c])) for i in range(N)) for c in (0,1)]
    return E,T,C.finals<<d

def combined(A,B,C,D):
    a=A.size; cd=(C.size+D.size)*a; n=cd+B.size; E=[]
    for flag in (0,1):
        rows=[1<<i for i in range(n)]
        for q in bits(D.finals):
            for r in bits(A.finals): rows[(C.size+q)*a+r]|=1<<(cd+B.start)
        if flag:
            for q in bits(C.finals):
                for r in range(a): rows[q*a+r]|=rows[(C.size+D.start)*a+r]
        E.append(tuple(rows))
    T=[]
    for c in (0,1):
        row=[]
        for U,off in ((C,0),(D,C.size)):
            for q in range(U.size):
                for r in range(a): row.append(1<<((off+U.trans[q][c])*a+A.trans[r][c]))
        row.extend(1<<(cd+B.trans[q][c]) for q in range(B.size)); T.append(tuple(row))
    return E,T,B.finals<<cd

class AuditPackedIndex:
    """Emulates universal microblock lookups using local cached products.
    The actual proof uses direct-address tables and two-level DSTs.
    """
    def __init__(self,w,marks,W,E,T):
        self.n=len(w); self.W=W; self.s=len(E[0]); self.I=mat_ident(self.s,W)
        self.E=[pack_matrices(*E,m,W) for m in marks]
        self.X=[pack_matrices(scalar_mul(E[0],T[c]),scalar_mul(E[1],T[c]),marks[i],W) for i,c in enumerate(w)]
        self.blocks={}; self.full={}
    def local(self,block,a,b):
        key=(block,a,b)
        if key not in self.blocks:
            cur=self.I
            for i in range(block*self.W+a,block*self.W+b): cur=mat_mul(cur,self.X[i])
            self.blocks[key]=cur
        return self.blocks[key]
    def select_local(self,block,coords,which,closure=False):
        # coords = {column: (local left,local right)}
        z=[[0]*self.s for _ in range(self.s)]
        for j,(a,b) in coords.items():
            m=self.local(block,a,b)
            if closure: m=mat_mul(m,self.E[block*self.W+b])
            for q in range(self.s):
                for r in range(self.s): z[q][r]|=m[q][r]&(1<<j)
        return tuple(map(tuple,z))
    def middle(self,l,r):
        if (l,r) not in self.full:
            cur=self.I
            for h in range(l,r): cur=mat_mul(cur,self.local(h,0,self.W))
            self.full[l,r]=cur
        return self.full[l,r]
    def family(self,coords,closure=False):
        """coords = {column: (left,right)}. Split by endpoint blocks."""
        groups={}; W=self.W
        for j,(l,r) in coords.items():
            assert 0<=l<=r<=self.n
            a,x=divmod(l,W); b,y=divmod(r,W)
            groups.setdefault((a,b),{})[j]=(x,y)
        out=[[0]*self.s for _ in range(self.s)]
        for (a,b),co in groups.items():
            if a==b: M=self.select_local(a,co,None,closure)
            else:
                L=self.select_local(a,{j:(x,W) for j,(x,y) in co.items()},None)
                R=self.select_local(b,{j:(0,y) for j,(x,y) in co.items()},None,closure)
                M=mat_mul(mat_mul(L,self.middle(a+1,b)),R)
            for q in range(self.s):
                for r in range(self.s): out[q][r]|=M[q][r]
        return tuple(map(tuple,out))

def first_eligible(w,B,R,A,W):
    n=len(w); M=[0]*(n+1); states=[0]*B.size; qA=A.start
    for i in range(n+1):
        if A.finals>>qA&1: states[B.start]|=R[i]
        for q in bits(B.finals): M[i]|=states[q]
        if i<n:
            ns=[0]*B.size
            for q in range(B.size): ns[B.trans[q][w[i]]]|=states[q]
            states=ns; qA=A.trans[qA][w[i]]
    return M

def family_answers(w,ds,T,U,R,W,b):
    """Return packed per-pair booleans and independent scalar checks.
    A pair is checked iff min(LCS(a,t), t-a)>b (capture lengths within it
    need not exceed b; short answers are also sound).
    """
    A,B,C,D,F,G,H=ds; n=len(w)
    E1,T1,_=two_stage(C,D); E2,T2,fin1=combined(A,B,C,D)
    E3,T3,fin2=two_stage(D,C); M=first_eligible(w,B,R,A,W)
    I1=AuditPackedIndex(w,R,W,E1,T1); I2=AuditPackedIndex(w,R,W,E2,T2)
    I3=AuditPackedIndex(w,M,W,E3,T3)
    checked=0; pos=[0,0]
    for delta in range(b+1,U+1):
        expected_a={a for a in range(max(0,T-delta),U-delta+1) if min(lcs(w,a,a+delta),delta)>b}
        fam=run_family(w,T-delta,U-delta,delta,b)
        assert set(a for lo,hi,l,cap in fam for a in range(lo,hi+1))==expected_a
        for lo,hi,l,cap in fam:
            records={}
            for a in range(lo,hi+1):
                t=a+delta; d=delta if cap else a-l; z=t-d
                records[t-T]=(a,t,d,z)
            L1=I1.family({j:(a,z) for j,(a,t,d,z) in records.items()})
            L2=I2.family({j:(z,t) for j,(a,t,d,z) in records.items()},True)
            L3=I3.family({j:(a-d,a) for j,(a,t,d,z) in records.items()},True)
            answer1=answer2=0
            for j,(a,t,d,z) in records.items():
                qa=A.state(w[:a-d]); qd=D.state(w[a:z]); flag=1<<j
                for q in range(C.size+D.size):
                    for f in bits(fin1):
                        answer1|=L1[C.start][q]&L2[q*A.size+qa][f]&flag
                for f in bits(fin2): answer2|=L3[qd][f]&flag
            for j,(a,t,d,z) in records.items():
                want1=want2=False
                for L in range(d+1):
                    i=a-L; k=t-L
                    if A.accepts(w[:i]) and B.accepts(w[i:a]):
                        want1 |= any(R[p]>>j&1 and C.accepts(w[a:p]) and D.accepts(w[p:k]) for p in range(a,k+1))
                    if M[i]>>j&1 and C.accepts(w[i:a]) and D.accepts(w[a:k]): want2=True
                assert bool(answer1>>j&1)==want1,(1,w,ds,a,t,d)
                assert bool(answer2>>j&1)==want2,(2,w,ds,a,t,d)
                checked+=1; pos[0]+=want1; pos[1]+=want2
    return checked,pos

def audit():
    rng=random.Random(20261124); anyD=DFA(((0,0),),1); eps=DFA(((1,1),(1,1)),1)
    def rd():
        s=rng.randint(1,3); return DFA(tuple(tuple(rng.randrange(s) for _ in range(2)) for _ in range(s)),rng.randrange(1<<s),rng.randrange(s))
    counts={'family_coverage':0,'outer_bits':0,'marked_bits':0,'long_pair_checks':0,'positive_p1':0,'positive_p2':0,'transpose_checks':0,'shear_checks':0}
    for n in range(1,10):
        for w in product((0,1),repeat=n):
            for W in (1,2,3):
                b=2*W
                for T in range(0,n+1,W):
                    U=min(n,T+W-1)
                    for delta in range(b+1,n+1):
                        for lo,hi in ((T,U),(T-delta,U-delta)):
                            fam=run_family(w,lo,hi,delta,b)
                            got={a for x,y,l,c in fam for a in range(x,y+1)}
                            want={a for a in range(max(0,lo),min(n-delta,hi)+1) if min(lcs(w,a,a+delta),delta)>b}
                            assert got==want
                            for x,y,l,cap in fam:
                                for a in range(x,y+1): assert (delta if cap else a-l)==min(lcs(w,a,a+delta),delta)
                            counts['family_coverage']+=1
    for W in (1,2,3,4,5):
        for _ in range(100):
            rows=[rng.randrange(1<<W) for i in range(W)]
            assert transpose_cols(transpose_rows(rows,W),W,W)==rows; counts['transpose_checks']+=1
            out=shear_tile(rows,W)
            for i in range(W):
                for j in range(W): assert (rows[i]>>j&1)==(out[j-i+W-1]>>j&1)
            counts['shear_checks']+=1
    for z in range(360):
        W=rng.choice((1,2,3,4)); b=2*W; n=rng.randint(0,25)
        # Include long periodic strings, not only random noise.
        root=tuple(rng.randrange(2) for _ in range(rng.randint(1,4)))
        w=tuple(root[i%len(root)] for i in range(n)) if z%3 else tuple(rng.randrange(2) for _ in range(n))
        ds=tuple(rng.choice((anyD,eps,rd())) for _ in range(7)) if z%6 else (anyD,)*7
        A,B,C,D,F,G,H=ds; O0,R0=scalar_outer(w,G,H,F)
        for T,U,O,R in outer_blocks(w,G,H,F,W,b):
            for p in range(n+1):
                for t in range(T,U+1):
                    assert bool(O[p]>>(t-T)&1)==O0[p][t]; counts['outer_bits']+=1
                    assert bool(R[p]>>(t-T)&1)==R0[p][t]; counts['marked_bits']+=1
            k,pos=family_answers(w,ds,T,U,R,W,b)
            counts['long_pair_checks']+=k; counts['positive_p1']+=pos[0]; counts['positive_p2']+=pos[1]
    print(counts)

if __name__=='__main__': audit()
