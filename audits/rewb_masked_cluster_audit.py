"""Audit of masked 1-use components. Explicit length/exponent enumeration; not the fast DS."""
from random import Random
from itertools import product

from rewb_boundary_index_audit import run, acc, rnddfa, states

def groups(occ,H):
    out=[]
    for p in occ:
        if out and 2*(p-out[-1][-1])<=H:out[-1].append(p)
        else:out.append([p])
    return out

def masked_cluster(w,X,H,L,occ,m1,m2,C,E):
    G=groups(occ,H); q=next((g[1]-g[0] for g in G if len(g)>1),None)
    if q:
        V=X[:q]; rho=H%q; U=V[rho:]+V[:rho]
    # Stage 0 waits, stage 1 reads C, stage 2 reads E.
    def read(st,z):
        stage,a=st
        return (stage,run(C if stage==1 else E,z,a)) if stage else st
    def jump(st):
        stage,a=st
        if stage==0:return (1,C[1])
        if stage==1 and a in C[2]:return (2,E[1])
        return None
    live={0:{(0,0)},1:set()}
    for i,g in enumerate(G):
        s,t=g[0],g[-1];c=len(g);b=G[i+1][0] if i+1<len(G) else len(w)
        p=G[i-1][-1] if i else None
        ov0=p is not None and p+H>s;ov1=t+H>b
        new={0:set(),1:set()}
        for im in [0,1]:
            if im and not ov0:continue
            I=p+H if im else s
            assert I<=b
            new[0]|={read(st,w[I:b]) for st in live[im]}
            u=im
            for om in [0,1]:
                if om and not ov1:continue
                v=c-1 if om or not ov1 else c-2
                if u>v:continue
                for k in range(u,v+1):
                    if om and k!=v:continue
                    for st in live[im]:
                        x=read(st,w[I:g[u]])
                        if c>1:x=read(x,V*(k-u))
                        assert x==read(st,w[I:g[k]])
                        if g[k] not in (m1 if x[0]==0 else m2):continue
                        y=jump(x)
                        if y is None:continue
                        y=read(y,X[L:H]);y0=y
                        if not om:
                            if c>1:y=read(y,U*(v-k))
                            y=read(y,w[g[v]+H:b])
                            assert y==read(y0,w[g[k]+H:b])
                        new[om].add(y)
        live=new
    return any(st==2 and a in E[2] for st,a in live[0])

def mask_run(w,s,R,q,B,C,E,m2):
    # Exact expansion of the constant number of arithmetic families in the proof.
    V=w[s:s+q];N,eta=divmod(R-s,q);tail=w[R:];ks=set()
    for rho in range(q):
        for a in range(2,N+1):
            if not acc(B,V*a+V[:rho]):continue
            for k in range(a+(rho>0),N+1):
                if k+a>N or (k+a==N and rho>eta):continue
                gap=(V*(k-a)) if rho==0 else V[rho:]+V*(k-a-1)
                if not acc(C,gap):continue
                if not rho:suf=V*(N-k-a)+V[:eta]+tail
                elif k+a==N:suf=V[rho:eta]+tail
                else:suf=V[rho:]+V*(N-k-a-1)+V[:eta]+tail
                if acc(E,suf):ks.add(k)
    return any(s+k*q in m2 for k in ks)

def main():
    rng=Random(61124);cl=shr=rn=pos=0
    for _ in range(3500):
        n=rng.randrange(1,35);v=''.join(rng.choice('01') for _ in range(rng.randrange(1,9)))
        w=(v*((n+len(v)-1)//len(v)))[:n] if rng.randrange(2) else ''.join(rng.choice('01') for _ in range(n))
        p=rng.randrange(n);H=rng.randrange(1,n-p+1);X=w[p:p+H]
        occ=[i for i in range(n-H+1) if w[i:i+H]==X];G=groups(occ,H)
        C,E=rnddfa(rng),rnddfa(rng);m1={i for i in range(n+1) if rng.randrange(2)};m2={i for i in range(n+1) if rng.randrange(2)}
        for L in range(1,H+1):
            if [i for i in range(n-L+1) if w[i:i+L]==X[:L]]!=occ:continue
            if groups(occ,L)!=G:continue
            if any((y[0]-x[-1]<H)!=(y[0]-x[-1]<L) for x,y in zip(G,G[1:])):continue
            want=any(a in m1 and j in m2 and a+L<=j and acc(C,w[a+L:j]) and acc(E,w[j+L:]) for k,g in enumerate(G) for a in g for h in G[k+1:] for j in h)
            got=masked_cluster(w,X,H,L,occ,m1,m2,C,E)
            assert got==want,(w,H,L,occ,m1,m2);cl+=1;shr+=L<H;pos+=want
        q=rng.randrange(1,8);V=''.join(rng.choice('01') for _ in range(q));R=rng.randrange(4*q,12*q+1)
        w=(V*((R+q-1)//q))[:R]+''.join(rng.choice('01') for _ in range(rng.randrange(5)));s=rng.randrange(R-4*q+1)
        m2={i for i in range(len(w)+1) if rng.randrange(2)};B,C,E=[rnddfa(rng) for _ in range(3)]
        want=any(j in m2 and acc(B,w[s:s+L]) and acc(C,w[s+L:j]) and acc(E,w[j+L:]) for L in range(2*q,(R-s)//2+1) for j in range(s+((L+q-1)//q)*q,R-L+1,q))
        assert mask_run(w,s,R,q,B,C,E,m2)==want,(w,s,R,q,m2);rn+=1
    print('masked cross-cluster families',cl,'shortened',shr,'positive',pos,'masked periodic cases',rn)
if __name__=='__main__':main()
