import random,itertools, functools
R=random.Random(483029)
# DFA phases: A,C,D,E, state 0 initial

def aut():
    n=R.choice([1,2,3]); return (tuple(tuple(R.randrange(n) for _ in range(2)) for i in range(n)), frozenset(i for i in range(n) if R.randrange(2)))
def step(A,q,z):
    for c in z:q=A[0][q][c]
    return q

def occ(w,x):return [i for i in range(len(w)-len(x)+1) if w[i:i+len(x)]==x]
def comp(S,m):
    if m==1:
        if S>=0: yield (S,)
    else:
        for i in range(S+1):
            for rest in comp(S-i,m-1):yield (i,)+rest

def solve(w,X,L,As,debug=False):
    H=len(X); n=len(w); os=occ(w,X); tail=X[L:]
    # build maximal q clusters
    groups=[]
    for p in os:
        if not groups or 2*(p-groups[-1][-1])>H:groups.append([p])
        else:groups[-1].append(p)
    qs={g[1]-g[0] for g in groups if len(g)>1};assert len(qs)<=1
    for g in groups:
        if len(g)>1:assert all(y-x==g[1]-g[0] for x,y in zip(g,g[1:]))
    # Require overlap relation between selected occurrences unchanged.
    if any((b-a>=L)!=(b-a>=H) for a,b in itertools.combinations(os,2)):return None
    def read(st,z):p,q=st; return p,step(As[p],q,z)
    def jump(st):
        p,q=st
        if p==3 or q not in As[p][1]:return None
        return read((p+1,0),tail)
    states={(0,read((0,0),w[:os[0]]))}
    for idx,g in enumerate(groups):
        s=g[0]; c=len(g); b=groups[idx+1][0] if idx+1<len(groups) else n
        ov=g[-1]+H>b
        new=set()
        for mode,st in states:
            entry=groups[idx-1][-1]+H if mode else s
            assert entry<=b
            new.add((0,read(st,w[entry:b])))
            if c==1:
                if not mode:
                    z=jump(st)
                    if z is not None:new.add((1,z) if ov else (0,read(z,w[s+H:b])))
                continue
            q=g[1]-g[0];h=(H+q-1)//q;V=X[:q]; rem=H%q; rr=V[rem:] if rem else (); U=V[rem:]+V[:rem]
            u=mode
            assert entry<=s+u*q
            for out in (0,1):
                if out and not ov:continue
                v=c-1-(ov and not out)
                for k in range(1,4-st[0]+1):
                    S=v-u-(k-1)*h
                    for rs0 in comp(S,k if out else k+1):
                        rs=rs0+(0,) if out else rs0
                        z=read(st,w[entry:s+u*q]); z=read(z,V*rs[0]); z=jump(z)
                        for i in range(1,k):
                            if z is None:break
                            z=read(z,rr+V*rs[i]);z=jump(z)
                        if z is None:continue
                        if not out:z=read(read(z,U*rs[k]),w[s+v*q+H:b])
                        new.add((out,z))
        states=new
    ans=any(not m and p==3 and x in As[3][1] for m,(p,x) in states)
    brute=False
    for i,j,k in itertools.combinations(os,3):
        if i+L>j or j+L>k:continue
        z=[w[:i],w[i+L:j],w[j+L:k],w[k+L:]]
        if all(step(A,0,t) in A[1] for A,t in zip(As,z)):brute=True;break
    assert ans==brute,(w,X,L,As,groups,states,ans,brute)
    return ans

count=0; mixed=0; short=0; yes=0
for it in range(8000):
    n=R.randrange(3,55)
    if it%3==0:
        v=tuple(R.randrange(2) for _ in range(R.randrange(1,7)))
        w=(v*n)[:n]
        w=tuple(1-x if R.random()<.06 else x for x in w)
    else:w=tuple(R.randrange(2) for _ in range(n))
    As=[aut() for _ in range(4)]
    i=R.randrange(n);H=R.randrange(1,min(n-i,14)+1); X=w[i:i+H]
    os=occ(w,X)
    if len(os)<2:continue
    for L in range(1,H+1):
        if occ(w,X[:L])!=os:continue
        ans=solve(w,X,L,As)
        if ans is not None:
            count+=1; short+=L<H; yes+=ans
            ds=[b-a for a,b in zip(os,os[1:])]; mixed+=any(2*d<=H for d in ds) and any(2*d>H for d in ds)
print(dict(family_checks=count,shorter_length_checks=short,mixed_clusters=mixed,accepted=yes))
# Audit actual suffix-trie edge families and critical lengths, including changes
# when an occurrence set is extended by moving from one edge to its parent.
edge_checks=stable_checks=period_switch_checks=0
for n in range(1,11):
  for w in itertools.product(range(2), repeat=n):
    dct={}
    for i in range(n):
      for j in range(i+1,n+1):dct.setdefault(w[i:j],[]).append(i)
    # A maximal chain of identical occurrence sets corresponds to a compact edge.
    families={}
    for x,ps in dct.items():families.setdefault(tuple(ps),[]).append(x)
    for ps,xs in families.items():
      xs.sort(key=len); lo=len(xs[0]); hi=len(xs[-1]); X=xs[-1]
      assert [len(x) for x in xs]==list(range(lo,hi+1))
      assert all(X[:len(x)]==x for x in xs)
      gaps=[j-i for i,j in zip(ps,ps[1:])]
      def sig(L):
        dense=tuple(2*d<=L for d in gaps); ov=tuple(d<L for d in gaps)
        qs={d for d,b in zip(gaps,dense) if b};assert len(qs)<=1
        q=next(iter(qs),0); h=(L+q-1)//q if q else 0
        if q:assert all(d==q or d>L-q for d in gaps)
        return dense,ov,q,h
      top=sig(hi)
      if top[2]:assert hi-lo<top[2]
      prior={}
      for L in range(lo,hi+1):
        s=sig(L); rel=tuple(j-i>=L for i,j in itertools.combinations(ps,2))
        if s in prior: assert rel==prior[s];stable_checks+=1
        prior[s]=rel
      edge_checks+=1
      # A surviving dense adjacency forces the same period after moving to parent.
      if lo>1:
        pps=dct[X[:lo-1]]; pgaps=[b-a for a,b in zip(pps,pps[1:])]
        pp={d for d in pgaps if 2*d<=lo-1};assert len(pp)<=1
        old={d for d in gaps if 2*d<=lo-1};assert len(old)<=1
        if old and pp and old!=pp:
          pset=set(zip(pps,pps[1:]));assert all((i,j) not in pset for i,j in zip(ps,ps[1:]) if 2*(j-i)<=lo-1);period_switch_checks+=1
print(dict(compact_edges=edge_checks,stable_interval_checks=stable_checks,period_switch_checks=period_switch_checks))
