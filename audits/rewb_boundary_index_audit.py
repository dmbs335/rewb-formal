"""Logical audit of the new boundary index. Explicit tries / direct sets, not the fast persistent implementation."""
from random import Random
from itertools import product

# DFA (transitions, start, accepting states)
def run(d,s,q=None):
    if q is None:q=d[1]
    for x in s:q=d[0][q][int(x)]
    return q
def acc(d,s,q=None):return run(d,s,q) in d[2]
def mod(d,q=None,F=None):return (d[0],d[1] if q is None else q,d[2] if F is None else F)
def states(d):return range(len(d[0]))

class Node:
    def __init__(self,X=''):
        self.X=X;self.ch={};self.src=[];self.tar=[];self.S=[];self.T=[];self.heavy=None;self.up=None
        self.R=set();self.path={};self.mark=set()

def add(root,X,t,target):
    u=root
    for c in X:
        if c not in u.ch:
            v=Node(u.X+c);v.up=u;u.ch[c]=v
        u=u.ch[c]
    (u.tar if target else u.src).append(t)
    return u

def tree(w,g0,g1,rev=False):
    r=Node();sl={};tl={}
    if rev:
        for a in range(g0+1):sl[a]=add(r,w[:a][::-1],a,False)
        for t in range(g1,len(w)+1):tl[t]=add(r,w[g1:t][::-1],t,True)
    else:
        for i in range(g0+1):sl[i]=add(r,w[i:g0],i,False)
        for j in range(g1,len(w)+1):tl[j]=add(r,w[j:],j,True)
    def post(u):
        u.S=u.src[:];u.T=u.tar[:]
        for v in u.ch.values():post(v);u.S+=v.S;u.T+=v.T
        if u.ch:u.heavy=max(u.ch.values(),key=lambda v:len(v.S)+len(v.T))
    post(r);return r,sl,tl

def fixed_end_index(w,g,A,B,D,E):
    root,sl,_=tree(w,g,g,True)
    def post(u):
        X=u.X;h=len(X)
        for alpha,delta in product(states(A),states(D)):
            if any(acc(B,X[:L][::-1]) and acc(A,X[L:][::-1],alpha) and acc(D,X[L:][::-1],delta) for L in range(h+1)):
                u.R.add((alpha,delta))
        # direct target colors, checked by relabel formula
        u.colors={t:run(D,w[g:t-h]) for t in u.T}
        for v in u.ch.values():
            post(v)
            for t,delta in v.colors.items():assert run(D,v.X[h:][::-1],delta)==u.colors[t]
    post(root)
    def path(u,old=None):
        h=len(u.X);ret={}
        if old is not None:
            edge=u.X[len(u.up.X):][::-1]
            for t,S in old.items():ret[t]={alpha for alpha in states(A) if run(A,edge,alpha) in S}
        # terminals are inserted here too, safely (shared full prefix)
        light=u.tar[:]
        for v in u.ch.values():
            if v is not u.heavy:light+=v.T
        for t in light:
            assert t not in ret
            ret[t]={alpha for alpha in states(A) if (alpha,u.colors[t]) in u.R}
        u.path=ret
        for v in u.ch.values():path(v,ret if v is u.heavy else None)
    path(root)
    def query(a,r):
        # collect the bottom node of each heavy-path segment on the root-leaf path
        u=sl[a];ends=[u]
        while u.up is not None:
            v=u.up
            if v.heavy is not u:ends.append(v)
            u=v
        for v in ends:
            alpha=run(A,w[:a-len(v.X)])
            if any(t<=r and alpha in S and acc(E,w[t:r]) for t,S in v.path.items()):return True
            if any(t<=r and (alpha,delta) in v.R and acc(E,w[t:r]) for t,delta in v.colors.items()):return True
        return False
    return query

def fixed_start_index(w,g,A,B,C,E):
    root,_,tl=tree(w,g,g,False)
    def dfs(u,old=()):
        h=len(u.X)
        # The accepted cuts for this edge (in explicit trie, a single length).
        ok=acc(B,u.X) and any(acc(A,w[:i]) and acc(C,w[i+h:g]) for i in u.S)
        depths=old+((h,) if ok else ())
        u.cuts=depths
        for v in u.ch.values():dfs(v,depths)
    dfs(root)
    def query(j,r):
        return any(L<=r-j and acc(E,w[j+L:r]) for L in tl[j].cuts)
    return query

def separated(w,g0,g1,A,B,C,D):
    root,_,tl=tree(w,g0,g1,True)
    def post(u):
        h=len(u.X)
        S={run(A,w[:a-h]) for a in u.src if acc(C,w[a:g0])}
        for v in u.ch.values():
            post(v);S|={run(A,v.X[h:][::-1],alpha) for alpha in v.colors}
        assert S=={run(A,w[:a-h]) for a in u.S if acc(C,w[a:g0])}
        u.colors=S
        u.local={d for d in states(D) if acc(B,u.X[::-1]) and d in D[2] and any(a in A[2] for a in S)}
    post(root)
    def dfs(u,up=set()):
        if u.up is not None:up={d for d in states(D) if run(D,u.X[len(u.up.X):][::-1],d) in up}
        u.mark=up|u.local
        for v in u.ch.values():dfs(v,u.mark)
    dfs(root)
    return {t for t,v in tl.items() if D[1] in v.mark}

def boundary_oracle(w,l,r,ds):
    A,B,C,K,D,E=ds
    for a in range(r+1):
      for p in range(max(l,a),r+1):
       if not acc(C,w[a:p]) or not acc(K,w[l:p]):continue
       for j in range(p,r+1):
        if not acc(D,w[p:j]):continue
        for L in range(min(a,r-j)+1):
         if w[a-L:a]==w[j:j+L] and acc(A,w[:a-L]) and acc(B,w[j:j+L]) and acc(E,w[j+L:r]):return True
    return False

def boundary(w,l,r,ds,s):
    A,B,C,K,D,E=ds;n=len(w);g0=(l//s)*s;g=min(n,g0+s)
    # Far-p branch, audited as its two logical cases (separated and fixed second-start masks).
    if g<=r:
        q=run(K,w[l:g]);KK=mod(K,q)
        # a<=g: crossing split at g, enumerating states of C there
        for c in states(C):
            for a in range(g+1):
             if run(C,w[a:g])!=c:continue
             for p in range(g,r+1):
              if not acc(C,w[g:p],c) or not acc(KK,w[g:p]):continue
              for j in range(p,r+1):
               if not acc(D,w[p:j]):continue
               for L in range(min(a,r-j)+1):
                if w[a-L:a]==w[j:j+L] and acc(A,w[:a-L]) and acc(B,w[j:j+L]) and acc(E,w[j+L:r]):return True
        # a>=g: choose actual K state at a; the regular gap is C_q' D.
        for a in range(g,r+1):
         k=run(KK,w[g:a])
         for p in range(a,r+1):
          if not acc(C,w[a:p]) or not acc(K,w[a:p],k):continue
          for j in range(p,r+1):
           if not acc(D,w[p:j]):continue
           for L in range(min(a,r-j)+1):
            if w[a-L:a]==w[j:j+L] and acc(A,w[:a-L]) and acc(B,w[j:j+L]) and acc(E,w[j+L:r]):return True
    # Near-p branch. Four configurations.
    for p in range(l,min(g,r+1)):
        if not acc(K,w[l:p]):continue
        CC=mod(C,F={c for c in states(C) if acc(C,w[g0:p],c)})
        if g<=r:
            DD=mod(D,q=run(D,w[p:g]))
            if any(t<=r and acc(E,w[t:r]) for t in separated(w,g0,g,A,B,CC,DD)):return True
            idx=fixed_end_index(w,g,A,B,DD,E)
            for a in range(g0+1,p+1):
                if acc(C,w[a:p]) and idx(a,r):return True
        idx=fixed_start_index(w,g0,A,B,CC,E)
        for j in range(p,min(g,r+1)):
            if acc(D,w[p:j]) and idx(j,r):return True
    for a in range(g0+1,min(g,r+1)):
        for j in range(max(a,l),min(g,r+1)):
            if not any(acc(C,w[a:p]) and acc(K,w[l:p]) and acc(D,w[p:j]) for p in range(max(a,l),j+1)):continue
            if any(w[a-L:a]==w[j:j+L] and acc(A,w[:a-L]) and acc(B,w[j:j+L]) and acc(E,w[j+L:r]) for L in range(min(a,r-j)+1)):return True
    return False

def rnddfa(rng):
    k=rng.randrange(1,5);return ([[rng.randrange(k) for _ in range(2)] for _ in range(k)],rng.randrange(k),{i for i in range(k) if rng.randrange(2)})

def main():
    rng=Random(20261124);nf=ns=nt=nb=0;yes=0
    for _ in range(400):
        n=rng.randrange(0,14);w=''.join(rng.choice('01') for _ in range(n));g=rng.randrange(n+1)
        A,B,C,K,D,E=ds=[rnddfa(rng) for _ in range(6)]
        q=fixed_end_index(w,g,A,B,D,E)
        for a in range(g+1):
            for r in range(g,n+1):
                want=any(w[a-L:a]==w[j:j+L] and acc(A,w[:a-L]) and acc(B,w[j:j+L]) and acc(D,w[g:j]) and acc(E,w[j+L:r]) for j in range(g,r+1) for L in range(min(a,r-j)+1))
                assert q(a,r)==want,(w,g,a,r,'end');nf+=1
        q=fixed_start_index(w,g,A,B,C,E)
        for j in range(g,n+1):
            for r in range(j,n+1):
                want=any(w[i:a]==w[j:j+a-i] and acc(A,w[:i]) and acc(B,w[i:a]) and acc(C,w[a:g]) and acc(E,w[j+a-i:r]) for a in range(g+1) for i in range(a+1) if j+a-i<=r)
                assert q(j,r)==want,(w,g,j,r,'start');ns+=1
        g1=rng.randrange(g,n+1);got=separated(w,g,g1,A,B,C,D)
        for t in range(g1,n+1):
            want=any(w[a-L:a]==w[t-L:t] and acc(A,w[:a-L]) and acc(B,w[t-L:t]) and acc(C,w[a:g]) and acc(D,w[g1:t-L]) for a in range(g+1) for L in range(min(a,t-g1)+1))
            assert (t in got)==want,(w,g,g1,t,'sep');nt+=1
        for __ in range(10):
            l=rng.randrange(n+1);r=rng.randrange(l,n+1);s=rng.randrange(1,n+2)
            want=boundary_oracle(w,l,r,ds);got=boundary(w,l,r,ds,s)
            assert got==want,(w,l,r,s,ds,got,want);nb+=1;yes+=want
    print('fixed-source-end queries',nf,'fixed-target-start queries',ns,'separated endpoint bits',nt,'boundary queries',nb,'positive',yes)
if __name__=='__main__':main()
