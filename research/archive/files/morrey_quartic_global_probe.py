#!/usr/bin/env python3
"""Exploratory only: tests degree<=4 positive Hessian moment quadratures
for multiple random 2x2 periodic gradient laws. Not a proof of Morrey.
"""
import numpy as np
from scipy.optimize import linprog
from itertools import product
import time,sys
EXPS=np.array([z for z in product(range(5),repeat=4) if 2 <= sum(z) <= 4],dtype=np.int16)
assert len(EXPS)==65

def feats(X,H):
    X=np.asarray(X,float);H=np.asarray(H,float)
    out=np.zeros((X.shape[0],len(EXPS)))
    for i in range(4):
      for j in range(4):
        coeff = EXPS[:,i]*EXPS[:,j] - (i==j)*EXPS[:,i]
        if not np.any(coeff): continue
        powers=EXPS.copy();powers[:,i]-=1;powers[:,j]-=1
        valid=(powers.min(axis=1)>=0)&(coeff>0)
        if not np.any(valid):continue
        val=np.ones((len(X),np.count_nonzero(valid)))
        for k in range(4):
          val*=X[:,k:k+1]**powers[valid,k]
        out[:,valid]+=val*(coeff[valid]*H[:,i:i+1]*H[:,j:j+1])
    return out

def mons(X):
    out=np.ones((len(X),len(EXPS)))
    for i in range(4):out*=X[:,i:i+1]**EXPS[:,i]
    return out

def grads(U,V):
    N=U.shape[0];G=[]
    for i in range(N):
      for j in range(N):
        for k in (0,1):
          def g(A):
            q=lambda x,y:A[x%N,y%N]
            if k==0: return [q(i+1,j)-q(i,j),q(i,j+1)-q(i,j)]
            else: return [q(i+1,j+1)-q(i,j+1),q(i+1,j+1)-q(i+1,j)]
          G.append(g(U)+g(V))
    return np.array(G,float)

def screen(N=4, seed=0, nsamp=12000):
    rng=np.random.default_rng(seed)
    U=rng.integers(-2,3,(N,N));V=rng.integers(-2,3,(N,N))
    G=grads(U,V)
    assert np.linalg.norm(G.mean(axis=0))<1e-9
    b=mons(G).mean(axis=0)
    # A convex combos of actual gradient support: more likely useful
    k=rng.integers(1,7,size=nsamp)
    X=np.zeros((nsamp,4))
    for i in range(6):
        ids=rng.integers(0,len(G),size=nsamp)
        use=(i<k).astype(float)
        X+=G[ids]*(use/k)[:,None]
    X=np.rint(X*4)/4
    a=rng.integers(-2,3,size=(nsamp,2));n=rng.integers(-2,3,size=(nsamp,2))
    a=np.where(np.linalg.norm(a,axis=1)[:,None]==0,np.array([[1,0]]),a)
    n=np.where(np.linalg.norm(n,axis=1)[:,None]==0,np.array([[1,0]]),n)
    H=np.stack((a[:,0]*n[:,0],a[:,0]*n[:,1],a[:,1]*n[:,0],a[:,1]*n[:,1]),axis=1).astype(float)
    H/=np.linalg.norm(H,axis=1)[:,None]
    C=feats(X,H)
    scales=np.maximum(np.max(np.abs(C),axis=0),np.abs(b));scales=np.maximum(scales,1e-10)
    C/=scales;b/=scales
    start=time.time()
    res=linprog(np.zeros(nsamp),A_eq=C.T,b_eq=b,bounds=(0,None),method='highs',options={'time_limit':27,'primal_feasibility_tolerance':1e-8,'dual_feasibility_tolerance':1e-8})
    if res.success:
      supp=np.flatnonzero(res.x>1e-7)
      resid=np.max(abs(C.T@res.x-b))
      print('N=',N,'seed=',seed,'sample=',nsamp,'status=feasible','support=',len(supp),'residual=',resid,'runtime=',round(time.time()-start,2),flush=True)
    else:
      print('N=',N,'seed=',seed,'sample=',nsamp,'status=',res.status,res.message,'runtime=',round(time.time()-start,2),flush=True)

if __name__=='__main__':
 for n,seed in [(4,200),(4,201),(4,202),(8,203)]:screen(n,seed,nsamp=9000)
