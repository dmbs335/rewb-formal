"""Independent checks for affine packed range products and rare inner-copy triples.
The triple checker uses a finite-state split scan, not an O(1) range index.
This file is a correctness audit, not an end-to-end complexity benchmark.
Python 3.10+; no third-party dependencies.
"""
import random
from itertools import product
from dataclasses import dataclass
@dataclass(frozen=True)
class DFA:
    trans: tuple
    finals: int
    start: int=0
    @property
    def size(self):return len(self.trans)
    def state(self,w,q=None):
        q=self.start if q is None else q
        for c in w:q=self.trans[q][c]
        return q
    def accepts(self,w):return bool(self.finals>>self.state(w)&1)
def lcs(w,a,t):
    d=0
    while a>d and t>d and w[a-d-1]==w[t-d-1]:d+=1
    return d
def lce(w,a,t):
    d=0
    while a+d<len(w) and t+d<len(w) and w[a+d]==w[t+d]:d+=1
    return d
def bits(m):
    while m:
        b=m&-m;yield b.bit_length()-1;m-=b
def mat_ident(s,W):return tuple(tuple(((1<<W)-1) if i==j else 0 for j in range(s)) for i in range(s))
def mat_mul(a,b):
    s=len(a);c=[[0]*s for _ in range(s)]
    for i in range(s):
        for k,x in enumerate(a[i]):
            for j,y in enumerate(b[k]):c[i][j]|=x&y
    return tuple(map(tuple,c))


def transpose(rows,W):
    a=list(rows); assert W>0 and W&(W-1)==0 and len(a)==W
    s=1
    while s<W:
        m=sum(((1<<s)-1)<<k for k in range(0,W,2*s))
        for i in range(W):
            if i&s==0:
                t=((a[i]>>s)^a[i+s])&m
                a[i]^=t<<s; a[i+s]^=t
        s*=2
    return a


def shear(rows,W):
    """output[r-j+W-1][j] = input[r][j], padded with zero."""
    col=transpose(rows,W); mask=(1<<W)-1
    low=[]; high=[]
    for j,c in enumerate(col):
        z=c<<(W-1-j); low.append(z&mask); high.append(z>>W)
    return transpose(low,W)+transpose(high,W)[:-1]


def shear_matrices(rows,W):
    s=len(rows[0]); out=[[[0]*s for _ in range(s)] for _ in range(2*W-1)]
    for a in range(s):
        for b in range(s):
            vals=shear([x[a][b] for x in rows],W)
            for k,v in enumerate(vals):out[k][a][b]=v
    return [tuple(map(tuple,x)) for x in out]


def mat_mask(a,mask):return tuple(tuple(v&mask for v in r) for r in a)
def mat_or(a,b):return tuple(tuple(x|y for x,y in zip(r,s)) for r,s in zip(a,b))

class DST:
    def __init__(self,a,I):
        self.a=a;self.I=I;self.tab=[]; n=len(a)
        for k in range(max(0,n-1).bit_length()):
            h=1<<k;t=[I]*n
            for l in range(0,n,2*h):
                m=min(l+h,n);r=min(l+2*h,n);x=I
                for i in range(m-1,l-1,-1):x=mat_mul(a[i],x);t[i]=x
                x=I
                for i in range(m,r):x=mat_mul(x,a[i]);t[i]=x
            self.tab.append(t)
    def query(self,l,r):
        assert 0<=l<=r<=len(self.a)
        if l==r:return self.I
        if l+1==r:return self.a[l]
        k=(l^(r-1)).bit_length()-1
        return mat_mul(self.tab[k][l],self.tab[k][r-1])

class BlockDST:
    """O(N log W + (N/W)log N) build, O(1) fixed range query."""
    def __init__(self,a,W,I):
        self.W=W;self.I=I;self.n=len(a);self.local=[];whole=[]
        for k in range(0,len(a),W):
            sub=DST(a[k:k+W],I);self.local.append(sub);whole.append(sub.query(0,len(sub.a)))
        self.top=DST(whole,I)
    def query(self,l,r):
        assert 0<=l<=r<=self.n
        if l==r:return self.I
        W=self.W; b,x=divmod(l,W); c,y=divmod(r-1,W);y+=1
        if b==c:return self.local[b].query(x,y)
        return mat_mul(mat_mul(self.local[b].query(x,len(self.local[b].a)),self.top.query(b+1,c)),self.local[c].query(0,y))

class AffineIndex:
    """Both fixed / both moving / long mixed interval products.
    Endpoints are (intercept,slope), slope in {0,1}, lane j.
    Short mixed intervals use scalar lanes (charged separately in proof).
    """
    def __init__(self,a,W):
        self.n=len(a);self.W=W;self.I=mat_ident(len(a[0]),W);I=self.I
        self.zero=mat_mask(I,0); self.mask=(1<<W)-1
        # Add padding so endpoint n belongs to a block.
        A=a+[I]*((W-len(a)%W)%W+W);self.A=A
        self.base=BlockDST(A,W,I)
        self.pref=[];self.suff=[]
        diag=[self.zero]*(len(A)+W-1)
        for b in range(0,len(A),W):
            tile=A[b:b+W];d=shear_matrices(tile,W)
            for k,x in enumerate(d):diag[b+k]=mat_or(diag[b+k],x)
            p=[I];s=[I]*(W+1)
            for x in tile:p.append(mat_mul(p[-1],x))
            for k in range(W-1,-1,-1):s[k]=mat_mul(tile[k],s[k+1])
            self.pref.append(shear_matrices(p[:-1],W));self.suff.append(shear_matrices(s[:-1],W))
        self.diag=BlockDST(diag,W,I)
    def query(self,L,R,mask=None):
        W=self.W;I=self.I; mask=self.mask if mask is None else mask
        l,ls=L;r,rs=R
        assert all(0<=l+ls*j<=r+rs*j<=self.n for j in bits(mask))
        if ls==rs:
            if ls: res=self.diag.query(l+W-1,r+W-1)
            else: res=self.base.query(l,r)
            return mat_mask(res,mask)
        out=self.zero
        # In the implementation, masks for these constant-many groups can be
        # obtained by interval intersection; this audit uses explicit masks.
        groups={}
        for j in bits(mask):
            a=l+ls*j;b=r+rs*j
            if b-a<W:
                out=mat_or(out,mat_mask(self.base.query(a,b),1<<j));continue
            key=(a if ls else b)//W
            groups[key]=groups.get(key,0)|(1<<j)
        for g,m in groups.items():
            z=g*W
            if ls:
                q=self.suff[g][l-z+W-1];x=mat_mul(q,self.base.query(z+W,r))
            else:
                q=self.pref[g][r-z+W-1];x=mat_mul(self.base.query(l,z),q)
            out=mat_or(out,mat_mask(x,m))
        return out


def random_dfa(rng):
    k=rng.randrange(1,4)
    return DFA(tuple(tuple(rng.randrange(k) for _ in range(2)) for _ in range(k)),rng.randrange(1<<k),rng.randrange(k))

def triple_oracle(w,ds,typ,a,t,f,Lmin=1,Lmax=None):
    """a,t: two inner-copy ends. f: corresponding end in outer copy 2.
    For type 1 f corresponds to t; for type 2 f corresponds to a.
    """
    A,B,C,D,F,G,H=ds;n=len(w);delta=f-(t if typ==1 else a)
    if not (0<=a<=t<=n and delta>0 and f<=n):return False
    for ell in range(Lmin,min(a,t-a,n if Lmax is None else Lmax)+1):
        if w[a-ell:a]!=w[t-ell:t]:continue
        i=a-ell;j=t-ell
        if typ==1 and not (A.accepts(w[:i]) and B.accepts(w[i:a])):continue
        if typ==2 and not (C.accepts(w[i:a]) and D.accepts(w[a:j])):continue
        for p in range((a if typ==1 else 0),(j if typ==1 else i)+1):
            if typ==1 and not (C.accepts(w[a:p]) and D.accepts(w[p:j])):continue
            if typ==2 and not (A.accepts(w[:p]) and B.accepts(w[p:i])):continue
            for e in range(t,min(n-delta,p+delta)+1):
                if F.accepts(w[t:e]) and G.accepts(w[e:p+delta]) and H.accepts(w[e+delta:]) and w[p:e]==w[p+delta:e+delta]:return True
    return False


def triple_reduce(w,ds,typ,a,t,f,Lmin=1,Lmax=None):
    """The finite-state range reduction, checked by direct split enumeration.
    All remaining choices are ordered positions e <= z <= x in ONE text.
    """
    A,B,C,D,F,G,H=ds;n=len(w);base=t if typ==1 else a;delta=f-base
    if not (0<=a<=t<=n and delta>0 and f<=n):return False
    l=base-lcs(w,base,f);r=base+lce(w,base,f)
    d=min(lcs(w,a,t),t-a,base-l,n if Lmax is None else Lmax)
    if r<t or d<Lmin:return False
    if typ==1:
        l0=max(a,l);g0=C.state(w[a:l0]);a0=A.state(w[:a-d]);xlo=f-d;xhi=f-Lmin
        # e in [t,r], z=p+delta in [l0+delta,f], x=j+delta in [xlo,xhi].
        for e in range(t,r+1):
            if not (F.accepts(w[t:e]) and H.accepts(w[e:r]+w[r+delta:])):continue
            for z in range(max(e,l0+delta),f+1):
                if not (C.finals>>C.state(w[l0+delta:z],g0)&1 and G.accepts(w[e:z])):continue
                for x in range(max(z,xlo),xhi+1):
                    if A.finals>>A.state(w[f-d:x],a0)&1 and D.accepts(w[z:x]) and B.accepts(w[x:f]):return True
    else:
        a0=A.state(w[:l]);d0=D.state(w[a:t-d]);xlo=f-d;xhi=f-Lmin
        for e in range(t,r+1):
            if not (F.accepts(w[t:e]) and H.accepts(w[e:r]+w[r+delta:])):continue
            for z in range(max(e,l+delta),f+1):
                if not (A.finals>>A.state(w[l+delta:z],a0)&1 and G.accepts(w[e:z])):continue
                for x in range(max(z,xlo),xhi+1):
                    if D.finals>>D.state(w[f-d:x],d0)&1 and B.accepts(w[z:x]) and C.accepts(w[x:f]):return True
    return False


def literal_chain_audit(rng, trials=450):
    """Check the prefix/suffix cut identities used in the monoid size proof."""
    checks=0
    for _ in range(trials):
        k=rng.randrange(1,4);us=[tuple(rng.randrange(2) for _ in range(rng.randrange(2,8))) for _ in range(k)]
        # Fixed regular components (two states), separated by one-way literal chains.
        edges=[];eps=[];cores=[];chains=[];N=0
        def state():
            nonlocal N
            q=N;N+=1;return q
        prev=None
        for i in range(k+1):
            core=[state(),state()];cores+=core
            if prev is not None:eps.append((prev,core[0]))
            for q in core:
                for c in (0,1):
                    for v in core:
                        if rng.random()<.55:edges.append((q,c,v))
            if i<k:
                chain=[state() for _ in range(len(us[i])+1)];cores.extend([chain[0],chain[-1]]);chains.append(chain)
                for q in core:
                    if rng.random()<.8:eps.append((q,chain[0]))
                for j,c in enumerate(us[i]):edges.append((chain[j],c,chain[j+1]))
                prev=chain[-1]
        def rel(z,allowed):
            def close(S):
                S=set(S);changed=True
                while changed:
                    changed=False
                    for a,b in eps:
                        if a in S and b in allowed and b not in S:S.add(b);changed=True
                return S
            out=[]
            for i in range(N):
                S=close({i}) if i in allowed else set()
                for c in z:S=close({b for a,d,b in edges if a in S and d==c and b in allowed})
                out.append(S)
            return out
        allq=set(range(N));z=tuple(rng.randrange(2) for _ in range(rng.randrange(18)))
        full=rel(z,allq)
        for u,ch in zip(us,chains):
            inside=ch[1:-1];before=set(range(ch[0]+1));after=set(range(ch[-1],N))
            sl=max(i for i in range(min(len(u),len(z))+1) if i==0 or u[-i:]==z[:i]);tl=max(i for i in range(min(len(u),len(z))+1) if i==0 or u[:i]==z[-i:])
            left=rel(z[:sl],allq);right=rel(z[sl:],after)
            for i in inside:
                actual=full[i]&after;pred=set().union(*(right[j] for j in left[i]&after))
                assert actual==pred
                checks+=1
            cut=len(z)-tl;left=rel(z[:cut],before);right=rel(z[cut:],allq)
            for i in set(cores)&before:
                actual=full[i]&set(inside);pred=set().union(*(right[j] for j in left[i]))&set(inside)
                assert actual==pred
                checks+=1
    return checks

def main():
    rng=random.Random(6432); counts=[0]*4
    for W in (1,2,4,8,16,32):
        for _ in range(70):
            rows=[rng.getrandbits(W) for _ in range(W)]
            tr=transpose(rows,W);sh=shear(rows,W)
            for i in range(W):
                for j in range(W):
                    assert (rows[i]>>j&1)==(tr[j]>>i&1)==(sh[i-j+W-1]>>j&1)
                    counts[0]+=1
    for W in (2,4,8,16):
        for _ in range(22):
            n=rng.randrange(W,5*W+1);s=2
            rows=[tuple(tuple(rng.getrandbits(W) for _ in range(s)) for _ in range(s)) for _ in range(n)]
            ix=AffineIndex(rows,W)
            for _ in range(90):
                L=(rng.randrange(-W,n+1),rng.randrange(2));R=(rng.randrange(-W,n+1),rng.randrange(2))
                valid=sum(1<<j for j in range(W) if 0<=L[0]+L[1]*j<=R[0]+R[1]*j<=n)
                if not valid:continue
                mask=valid&rng.getrandbits(W)
                # avoid undefined global query endpoints for a zero mask or a
                # fixed/moving all-outside base; keep a fallback direct subset.
                if not mask:continue
                if L[1]==R[1]==1 and not (-W+1<=L[0]<=R[0]<=len(ix.A)):continue
                out=ix.query(L,R,mask);expected=ix.zero
                for j in bits(mask):
                    x=mat_ident(s,W)
                    for M in rows[L[0]+L[1]*j:R[0]+R[1]*j]:x=mat_mul(x,M)
                    expected=mat_or(expected,mat_mask(x,1<<j))
                assert out==expected,(W,n,L,R,mask)
                counts[1]+=1
    for _ in range(12000):
        n=rng.randrange(3,19);w=tuple(rng.randrange(2) for _ in range(n))
        ds=[random_dfa(rng) for _ in range(7)]
        # Include more accepting languages to get nontrivial YES cases.
        ds=[DFA(((0,0),),1) if rng.random()<.3 else D for D in ds]
        a,t,f=sorted(rng.sample(range(1,n+1),3));Lmin=rng.randrange(1,3);Lmax=rng.choice([None,2,3,5])
        for typ in (1,2):
            # For type 2 the third copy's first-inner end can precede t only
            # if outer copies overlap, which is excluded, so sorted suffices.
            x=triple_oracle(w,ds,typ,a,t,f,Lmin,Lmax);y=triple_reduce(w,ds,typ,a,t,f,Lmin,Lmax)
            assert x==y,(w,ds,typ,a,t,f,Lmin,Lmax,x,y)
            counts[2]+=1;counts[3]+=int(x)
    seeded=0;rare_checks=0
    def randword(k):return tuple(rng.randrange(2) for _ in range(k))
    def lit(x):
        k=len(x);return DFA(tuple(tuple((i+1 if i<k and c==x[i] else k+1) for c in range(2)) for i in range(k+2)),1<<k)
    for _ in range(600):
        u=randword(rng.randrange(1,7)); a0,b0,c0,d0,f0,g0,h0=[randword(rng.randrange(4)) for _ in range(7)]
        for typ in (1,2):
            if typ==1:
                v=d0+u+f0;w=a0+u+c0+v+g0+v+h0;a=len(a0)+len(u);t=a+len(c0)+len(d0)+len(u);f=t+len(v)+len(g0)
                parts=[a0,u,c0,d0,f0,g0,h0]
            else:
                v=b0+u+d0+u+f0;w=a0+v+g0+v+h0;a=len(a0)+len(b0)+len(u);t=a+len(d0)+len(u);f=a+len(v)+len(g0)
                parts=[a0,b0,u,d0,f0,g0,h0]
            ds=[lit(x) if rng.random()<.6 else DFA(((0,0),),1) for x in parts]
            assert triple_oracle(w,ds,typ,a,t,f,len(u),len(u))
            assert triple_reduce(w,ds,typ,a,t,f,len(u),len(u))
            seeded+=1
    for _ in range(300):
        w=randword(rng.randrange(1,24));n=len(w);h=rng.randrange(1,n+1)
        occ={}
        for j in range(1,n+1):
            for L in range(1,j+1):occ.setdefault(w[j-L:j],[]).append(j)
        groups={x:es for x,es in occ.items() if len(es)<=h and (len(x)==1 and n>h or len(x)>1 and len(occ[x[1:]])>h or len(x)==1 and n<=h)}
        seen=set()
        for x,es in groups.items():
            assert not (seen&set(es));seen.update(es)
        for x,es in occ.items():
            if len(es)<=h:
                anc=[y for y in groups if len(y)<=len(x) and x[-len(y):]==y]
                assert len(anc)==1 and set(es)<=set(groups[anc[0]])
                rare_checks+=1
    print('literal-chain relation cut checks:',literal_chain_audit(rng))
    print('seeded positive triple checks:',seeded)
    print('rare suffix family coverage checks:',rare_checks)
    print('transpose/shear bit comparisons:',counts[0])
    print('packed affine interval comparisons:',counts[1])
    print('triple reduction comparisons:',counts[2],'; YES cases:',counts[3])

if __name__=='__main__':main()
