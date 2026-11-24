"""Fixed two-use nested REWB: O_P(n^2) time, O_P(n) workspace.
Alphabet in this reference implementation: integers 0,1.  All ordinary
regular languages are given as DFAs.  Run this file to compare with a
separate decomposition oracle. Microblock codes use direct addressing.
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
    def step(self,q,c): return self.trans[q][c]
    def state(self,w):
        q=self.start
        for c in w: q=self.step(q,c)
        return q
    def accepts(self,w): return bool(self.finals & (1<<self.state(w)))
    def move(self,mask,c):
        return sum({1<<self.step(q,c) for q in bits(mask)})
    def pre(self,mask,c):
        return sum(1<<q for q in range(self.size) if mask & (1<<self.step(q,c)))

def bits(m):
    while m:
        b=m&-m; yield b.bit_length()-1; m-=b

def apply(m,rel):
    out=0
    for q in bits(m): out |= rel[q]
    return out

def mul(a,b): return tuple(apply(row,b) for row in a)
def ident(n): return tuple(1<<i for i in range(n))
def pre(m,rel): return sum(1<<i for i,row in enumerate(rel) if row&m)

def z_array(s):
    z=[0]*len(s); l=r=0
    for i in range(1,len(s)):
        if i<r: z[i]=min(r-i,z[i-l])
        while i+z[i]<len(s) and s[z[i]]==s[i+z[i]]: z[i]+=1
        if i+z[i]>r: l,r=i,i+z[i]
    return z

def lcs_row(w,t):
    n=len(w); rev=w[::-1]; pat=rev[n-t:]
    z=z_array(pat+(-1,)+rev)
    return [0 if j==0 else z[t+1+n-j] for j in range(n+1)]

class RangeProduct:
    """Finite alphabet microblocks and a disjoint sparse table.
    Uses O_s(n+1) preprocessing/space and O(1) product queries for fixed s.
    Symbols are integers from 0 to len(table)-1; table maps symbols to relations.
    """
    def __init__(self,word,table):
        n=len(word); s=max(2,len(table)); self.I=ident(len(table[0])); self.n=n
        b=1; p=s
        while p*p<=n+2: b+=1; p*=s
        self.b=max(1,b-1); b=self.b
        cache=[None]*(2*s**b); self.micro=[]; block=[]
        for i in range(0,n,b):
            key=tuple(word[i:i+b]); l=len(key)
            code=1
            for c in key: code=code*s+c
            if cache[code] is None:
                rows=[]
                for a in range(l+1):
                    row=[self.I]; cur=self.I
                    for c in key[a:]: cur=mul(cur,table[c]); row.append(cur)
                    rows.append(row)
                cache[code]=rows
            r=cache[code]; self.micro.append(r); block.append(r[0][l])
        self.block=block; m=len(block); self.dst=[]
        for k in range((m-1).bit_length() if m else 0):
            h=1<<k; level=[self.I]*m
            for l in range(0,m,2*h):
                mid=min(l+h,m); end=min(l+2*h,m)
                cur=self.I
                for x in range(mid-1,l-1,-1): cur=mul(block[x],cur); level[x]=cur
                cur=self.I
                for x in range(mid,end): cur=mul(cur,block[x]); level[x]=cur
            self.dst.append(level)
    def full(self,l,r):
        if l==r: return self.I
        if l+1==r: return self.block[l]
        k=(l^(r-1)).bit_length()-1
        return mul(self.dst[k][l],self.dst[k][r-1])
    def query(self,l,r):
        assert 0<=l<=r<=self.n
        if l==r: return self.I
        b=self.b; L,x=divmod(l,b); R,y=divmod(r-1,b); y+=1
        if L==R: return self.micro[L][x][y-x]
        left=self.micro[L][x][b-x]; right=self.micro[R][0][y]
        return mul(mul(left,self.full(L+1,R)),right)

def pref(w,D):
    out=[D.start]
    for c in w: out.append(D.step(out[-1],c))
    return out

def suff(w,D):
    out=[0]*(len(w)+1); out[-1]=D.finals
    for i in range(len(w)-1,-1,-1): out[i]=D.pre(out[i+1],w[i])
    return out

def outer_columns(w,G,H,F,A=None):
    """Yield (t, LCS(t,*), R[*,t], raw_outer[*,t]) right-to-left."""
    n=len(w); h=suff(w,H); aa=pref(w,A) if A else None
    active=[0]*(n+1)
    for t in range(n,-1,-1):
        lcs=lcs_row(w,t)
        g=pref(w[t:],G); inject=[0]*(t+1)
        for f in range(t,n+1):
            if h[f] & (1<<H.start):
                d=min(lcs[f],f-t)
                inject[t-d]|=1<<g[f-d-t]
        raw=[False]*(n+1); states=0
        for p in range(t+1):
            states|=inject[p]
            raw[p]=bool(states&G.finals) and (A is None or bool(A.finals&(1<<aa[p])))
            if p<t: states=G.move(states,w[p])
        for p in range(n+1):
            if t<n: active[p]=F.pre(active[p],w[t])
            if raw[p]: active[p]|=F.finals
        mark=[p<=t and bool(active[p]&(1<<F.start)) for p in range(n+1)]
        yield t,lcs,mark,raw

def two_stage(D,C):
    """Read D, switch at marked position in accepting D state, then read C."""
    d=D.size; N=d+C.size
    E=[]
    for flag in (0,1):
        E.append(tuple((1<<i)|((1<<(d+C.start)) if flag and i<d and D.finals&(1<<i) else 0) for i in range(N)))
    T=[tuple((1<<D.step(i,c)) if i<d else (1<<(d+C.step(i-d,c))) for i in range(N)) for c in (0,1)]
    table=[mul(E[f],T[c]) for c in (0,1) for f in (0,1)]
    return E,table,C.finals<<d

def p2(w,A,B,C,D,F,G,H):
    """A (B (C)_x D \\x F)_x G \\x H."""
    n=len(w); E,table,final=two_stage(D,C)
    dt=[tuple(1<<D.step(q,c) for q in range(D.size)) for c in (0,1)]
    gap=RangeProduct(w,dt)
    for t,lcs,R,_ in outer_columns(w,G,H,F,A):
        M=[False]*(n+1); active=0
        for i in range(t+1):
            if R[i]: active|=1<<B.start
            M[i]=bool(active&B.finals)
            if i<t: active=B.move(active,w[i])
        idx=RangeProduct([2*c+M[i] for i,c in enumerate(w)],table)
        for a in range(t+1):
            d=min(lcs[a],t-a); b=t-d
            qmask=gap.query(a,b)[D.start]
            out=apply(apply(qmask,idx.query(a-d,a)),E[M[a]])
            if out&final: return True
    return False

def combined(A,B,C,D):
    """C and D track A in parallel; C->D at a marked boundary;
    D->B at an unmarked boundary if A and D both accept."""
    a=A.size; cd=(C.size+D.size)*a; n=cd+B.size
    E=[]
    for flag in (0,1):
        rows=[1<<i for i in range(n)]
        for q in range(D.size):
            for r in range(a):
                if D.finals&(1<<q) and A.finals&(1<<r): rows[(C.size+q)*a+r]|=1<<(cd+B.start)
        if flag:
            for q in bits(C.finals):
                for r in range(a): rows[q*a+r]|=rows[(C.size+D.start)*a+r]
        E.append(tuple(rows))
    T=[]
    for c in (0,1):
        row=[]
        for U,offset in ((C,0),(D,C.size)):
            for q in range(U.size):
                for r in range(a): row.append(1<<((offset+U.step(q,c))*a+A.step(r,c)))
        row.extend(1<<(cd+B.step(q,c)) for q in range(B.size)); T.append(tuple(row))
    table=[mul(E[f],T[c]) for c in (0,1) for f in (0,1)]
    return E,table,B.finals<<cd

def p1(w,A,B,C,D,F,G,H):
    """A (B)_x C (D \\x F)_x G \\x H."""
    n=len(w); aa=pref(w,A); _,cd,_=two_stage(C,D); E,table,final=combined(A,B,C,D)
    for t,lcs,R,_ in outer_columns(w,G,H,F):
        idx=RangeProduct([2*c+R[i] for i,c in enumerate(w)],cd)
        accept=[0]*(t+1); accept[t]=pre(final,E[R[t]])
        for b in range(t-1,-1,-1): accept[b]=pre(accept[b+1],table[2*w[b]+R[b]])
        for a in range(t+1):
            d=min(lcs[a],t-a); b=t-d; qa=aa[a-d]
            m=idx.query(a,b)[C.start]
            if any(accept[b] & (1<<(q*A.size+qa)) for q in bits(m)): return True
    return False

def brute_outer(w,G,H,F,A=None):
    n=len(w); raw=[[False]*(n+1) for _ in range(n+1)]; R=[[False]*(n+1) for _ in range(n+1)]
    for p in range(n+1):
        for e in range(p,n+1):
            if A and not A.accepts(w[:p]): continue
            L=e-p
            raw[p][e]=any(w[p:e]==w[k:k+L] and G.accepts(w[e:k]) and H.accepts(w[k+L:]) for k in range(e,n-L+1))
        for t in range(p,n+1): R[p][t]=any(raw[p][e] and F.accepts(w[t:e]) for e in range(t,n+1))
    return raw,R

def brute_p1(w,A,B,C,D,F,G,H):
    n=len(w)
    for i in range(n+1):
        if not A.accepts(w[:i]): continue
        for a in range(i,n+1):
            u=w[i:a]; L=a-i
            if not B.accepts(u): continue
            for p in range(a,n+1):
                if not C.accepts(w[a:p]): continue
                for j in range(p,n-L+1):
                    if not D.accepts(w[p:j]) or u!=w[j:j+L]: continue
                    for e in range(j+L,n+1):
                        if not F.accepts(w[j+L:e]): continue
                        v=w[p:e]; m=len(v)
                        for k in range(e,n-m+1):
                            if G.accepts(w[e:k]) and v==w[k:k+m] and H.accepts(w[k+m:]): return True
    return False

def brute_p2(w,A,B,C,D,F,G,H):
    n=len(w)
    for p in range(n+1):
        if not A.accepts(w[:p]): continue
        for i in range(p,n+1):
            if not B.accepts(w[p:i]): continue
            for a in range(i,n+1):
                u=w[i:a]; L=a-i
                if not C.accepts(u): continue
                for j in range(a,n-L+1):
                    if not D.accepts(w[a:j]) or u!=w[j:j+L]: continue
                    for e in range(j+L,n+1):
                        if not F.accepts(w[j+L:e]): continue
                        v=w[p:e]; m=len(v)
                        for k in range(e,n-m+1):
                            if G.accepts(w[e:k]) and v==w[k:k+m] and H.accepts(w[k+m:]): return True
    return False

def rnddfa(r):
    n=r.randint(1,4)
    return DFA(tuple(tuple(r.randrange(n) for _ in range(2)) for _ in range(n)),r.randrange(1<<n),r.randrange(n))

def audit():
    rng=random.Random(2031); total=[0,0]; positive=[0,0]; cols=0; lcs_count=0; monoid_q=0
    anyD=DFA(((0,0),),1); eps=DFA(((1,1),(1,1)),1)
    def check(w,ds):
        for z,(fast,slow) in enumerate(((p1,brute_p1),(p2,brute_p2))):
            a=fast(w,*ds); b=slow(w,*ds)
            assert a==b,(z,w,ds,a,b)
            total[z]+=1; positive[z]+=a
    for n in range(7):
        for w in product((0,1),repeat=n):
            for k in range(8):
                ds=tuple(rng.choice((eps,anyD,rnddfa(rng))) for _ in range(7))
                check(w,ds)
    for _ in range(1500):
        n=rng.randrange(0,11); w=tuple(rng.randrange(2) for _ in range(n)); ds=tuple(rnddfa(rng) for _ in range(7))
        check(w,ds)
    for _ in range(500):
        n=rng.randrange(0,15); w=tuple(rng.randrange(2) for _ in range(n)); G,H,F,A=[rnddfa(rng) for _ in range(4)]
        for A in (None,A):
            raw,R=brute_outer(w,G,H,F,A)
            for t,lcs,mark,col in outer_columns(w,G,H,F,A):
                assert col==[raw[p][t] for p in range(n+1)]
                assert mark==[R[p][t] for p in range(n+1)]
                cols+=1
                for j,L in enumerate(lcs):
                    expected=0
                    while expected<min(j,t) and w[j-expected-1]==w[t-expected-1]: expected+=1
                    assert L==expected; lcs_count+=1
    for _ in range(100):
        n=rng.randrange(0,1024); s=rng.randrange(2,6); N=4
        tab=[tuple(rng.randrange(1<<N) for _ in range(N)) for _ in range(s)]
        w=[rng.randrange(s) for _ in range(n)]; idx=RangeProduct(w,tab)
        for k in range(100):
            l=rng.randrange(n+1); r=rng.randrange(l,n+1); a=ident(N)
            for x in w[l:r]: a=mul(a,tab[x])
            assert a==idx.query(l,r); monoid_q+=1
    print('nested comparisons:',total,'positive:',positive)
    print('outer columns:',cols,'LCS entries:',lcs_count,'range products:',monoid_q)
if __name__=='__main__': audit()
