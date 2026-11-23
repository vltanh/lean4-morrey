#!/usr/bin/env python3
"""Noncertifying periodic PL Jensen search for the exact hybrid-cone separator.

Run with NumPy, SciPy, PyTorch (CPU):
    python research/experiments/2026-11-22/iwaniec_hybrid_pl_search.py

Not a proof of QC and not an exhaustive counterexample search.
"""
import numpy as np
import torch
from scipy.optimize import minimize
from numpy.polynomial import Chebyshev

torch.set_num_threads(1)
COEFF=np.array([37676885,55559819,22507846,3634764,1122809,
 1068027,57237,275379,623336,96945,-261804,-126467,-6991],
 dtype=float)/(2**24)
CC=torch.tensor(COEFF,dtype=torch.float64)
HP=Chebyshev(COEFF)

def density(A):
 a,b,c,d=(A[...,0,0],A[...,0,1],A[...,1,0],A[...,1,1])
 trace=a*a+b*b+c*c+d*d
 det=a*d-b*c
 disc=torch.clamp(trace*trace-4*det*det,min=0)
 top2=(trace+torch.sqrt(disc+1e-30))/2
 r=torch.clamp(det/(top2+1e-24),-1,1)
 t0=torch.ones_like(r);t1=r
 h=CC[0]*t0+CC[1]*t1
 for j in range(2,len(CC)):
  t2=2*r*t1-t0
  h=h+CC[j]*t2
  t0,t1=t1,t2
 return top2*top2*h

def gradients(x,n):
 """Two actual periodic nodal PL gradients per square; rows=output components."""
 v=x.reshape(n,n,2)
 v10=v.roll(-1,0);v01=v.roll(-1,1);v11=v10.roll(-1,1)
 gx1=n*(v10-v);gy1=n*(v11-v10)
 gx2=n*(v11-v01);gy2=n*(v01-v)
 return torch.stack((gx1,gy1),dim=-1),torch.stack((gx2,gy2),dim=-1)

def energy(x,n,base_r):
 d1,d2=gradients(x,n)
 A=torch.tensor([[1.,0.],[0.,base_r]],dtype=torch.float64)
 return .5*(density(A+d1).mean()+density(A+d2).mean())

def check_compatibility(n):
 rng=np.random.default_rng(555+n)
 x=torch.tensor(rng.standard_normal(n*n*2),dtype=torch.float64)
 G1,G2=gradients(x,n)
 det=lambda G:G[...,0,0]*G[...,1,1]-G[...,0,1]*G[...,1,0]
 gm=.5*(G1.mean((0,1))+G2.mean((0,1)))
 dm=.5*(det(G1).mean()+det(G2).mean())
 assert gm.abs().max().item()<1e-9
 assert abs(dm.item())<1e-9

def run(seed=209):
 rng=np.random.default_rng(seed)
 trials=[]
 for base_r,meshes,starts in [
   (0.,(3,4,6),25),
   (-.6,(4,6),9),(-.3,(4,6),9),
   (.3,(4,6),9),(.6,(4,6),9),
 ]:
  for n in meshes:
   check_compatibility(n)
   target=float(HP(base_r))
   best=target
   for i in range(starts):
    scale=(.05,.2,.4,.7,1.,2.)[i%6]
    x=rng.normal(0,scale/n,(n,n,2))
    x-=x.mean((0,1),keepdims=True)
    def fg(z):
     xx=torch.tensor(z,dtype=torch.float64,requires_grad=True)
     E=energy(xx,n,base_r)
     g=torch.autograd.grad(E,xx)[0]
     return E.item(),g.detach().numpy().ravel()
    opt=minimize(fg,x.ravel(),jac=True,method='L-BFGS-B',
                 options={'maxiter':200,'ftol':2e-12})
    best=min(best,opt.fun)
   trials.append((base_r,n,starts,best-target))
   print(f"base_r={base_r:+.1f}, n={n}, starts={starts}, "
         f"best_observed_gap={best-target:+.12g}",flush=True)
 return trials

if __name__=="__main__":
 run()
