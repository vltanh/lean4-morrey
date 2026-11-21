"""2x2-specific SOS search in Cassese q + alpha L² + beta LP + gamma P².
Floating semidefinite solutions are candidates, NOT exact certificates.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np, cvxpy as cp,sys,json
from pathlib import Path
from scipy.optimize import minimize
from lh_sos_core import SOS,PeriodicFE
ROOT=Path(__file__).parent

def wedge(a,b,c,d):return (np.outer(a,d)+np.outer(d,a)-np.outer(b,c)-np.outer(c,b))/2

def forms(B):
 e=np.eye(6);a,b,c,d,ee,f=e
 x0=(a-c-ee)/2;x1=(b+d+f)/2;y0=d-f;y1=ee;u0=b;u1=-a-c;z0=(a-c+ee)/2;z1=(b-d-f)/2
 T=np.zeros((6,4));T[:3,0]=B[0];T[:3,1]=B[1];T[3:,2]=B[0];T[3:,3]=B[1]
 ss=[wedge(y0,y1,u0,u1),wedge(x0,x1,u0,u1),wedge(x0,x1,y0,y1),2*(np.outer(x0,x0)+np.outer(x1,x1))+sum(np.outer(v,v) for v in [y0,y1,u0,u1]),2*(np.outer(z0,z0)+np.outer(z1,z1))]
 return [T.T@s@T for s in ss]

def polyquad(S):
 d={}
 for i in range(4):
  for j in range(4):
   e=[0]*4;e[i]+=1;e[j]+=1;t=tuple(e);d[t]=d.get(t,0)+S[i,j]
 return d

def product(p,q):
 d={}
 for a,c in p.items():
  for b,cc in q.items():
   e=tuple(x+y for x,y in zip(a,b));d[e]=d.get(e,0)+c*cc
 return d

class Penalty:
 def __init__(self,B,eps=1e-9,sign=1,free_mixed=False):
  self.B=B;self.s=SOS();s=self.s
  fs=[polyquad(S) for S in forms(B)]
  p0=product(fs[0],fs[0]);p01=product(fs[1],fs[2])
  for e,c in p01.items():p0[e]=p0.get(e,0)-4*c
  polys=[p0,product(fs[3],fs[3]),product(fs[3],fs[4]),product(fs[4],fs[4])]
  co=np.zeros((len(s.e),4))
  for j,p in enumerate(polys):
   for e,c in p.items():co[s.lookup[e],j]=c
  self.scales=np.linalg.norm(co,axis=0);co/=self.scales
  co[:,0]*=sign
  self.co=co
  self.pen=cp.Variable(3);self.free_mixed=free_mixed;self.Q=cp.Variable((16,16),symmetric=True);self.mom=cp.Parameter(len(s.e))
  cs=s.C[:,[i+20*j for j in range(4,20) for i in range(4,20)]]
  self.C=cs;self.p=co[:,0]+co[:,1:]@self.pen
  self.prob=cp.Problem(cp.Minimize(self.mom@self.p+1e-10*cp.trace(self.Q)),[cs@cp.vec(self.Q,order='F')==s.D@self.p,self.Q >> eps*np.eye(16),self.pen[[0,2]]>=0]+([] if free_mixed else [self.pen[1]>=0]))
 def solve(self,A,F):
  s=self.s;self.mom.value=s.moments(A+F)-s.values(F[None,:])[0]
  try:
   self.prob.solve(solver='CLARABEL',tol_gap_abs=1e-9,tol_feas=1e-9,tol_gap_rel=1e-9,max_iter=300)
  except cp.error.SolverError as exc:
   return None,None,dict(status='solver_error',message=str(exc))
  if self.p.value is None:return None,None,dict(status=self.prob.status)
  p=self.p.value.copy();Q=self.Q.value.copy()
  meta=dict(status=self.prob.status,gap=float(self.mom.value@p),coefficient_residual=float(np.max(np.abs(self.C@Q.ravel(order='F')-s.D@p))),gram_min_eig=float(np.linalg.eigvalsh(Q)[0]),penalty_normalized=self.pen.value.tolist(),penalty_raw=(self.pen.value*self.scales[0]/self.scales[1:]).tolist())
  return p,Q,meta
 def hess(self,A,p):
  e=self.s.e;hh=np.zeros((len(A),4,4))
  for i in range(4):
   for j in range(4):
    fac=e[:,i]*(e[:,j]-(i==j));use=fac!=0;ee=e[use].copy();ee[:,i]-=1;ee[:,j]-=1
    hh[:,i,j]=np.prod(A[:,None,:]**ee[None,:,:],axis=2)@(p[use]*fac[use])
  return hh
 def base(self,A,p):
  val,g=self.s.fgrad(A,p);l=g.mean(0);Q=.5*self.hess(A,p).mean(0)
  ev,U=np.linalg.eigh(Q);cut=1e-10*max(1,ev.max());F=-.5*U@(np.where(ev>cut,(U.T@l)/np.maximum(ev,cut),0))
  return F,float(val.mean()+.5*l@F),ev
 def objective(self,x,p,fe):
  A,scale=fe.normalized(x);F,gap,ev=self.base(A,p)
  _,d=self.s.fgrad(A+F,p);_,df=self.s.fgrad(F[None,:],p);d-=df
  dg=(d-A*np.mean(np.sum(d*A,axis=1)))/(scale*len(A))
  return gap,fe.back(dg)

def main():
 rng=np.random.default_rng(534243);fe=PeriodicFE(5,2);records=[];best=np.inf
 Bs=[np.array([[1.,0,0],[0,1,0]]),np.array([[1,0,1],[0,1,1]])]
 # The r=.01 plane failed in the recorded run and is excluded here.
 for r in [.5,.1]:
  Bs.append(np.array([[1-r*r,2*r,1+r*r],[1-r*r,-2*r,1+r*r]])/(1+r*r))
 for pi,B in enumerate(Bs):
  pc=Penalty(B)
  for trial in range(4):
   x=rng.normal(size=50);F=rng.normal(size=4)*.2
   for iteration in range(5):
    A,_=fe.normalized(x);p,Q,meta=pc.solve(A,F)
    if p is None:
     print(pi,trial,iteration,meta,flush=True);break
    opt=minimize(lambda z:pc.objective(z,p,fe),x,jac=True,method='L-BFGS-B',options=dict(maxiter=250,ftol=1e-13,gtol=1e-10,maxls=40))
    x=opt.x;A,_=fe.normalized(x);F,gap,ev=pc.base(A,p)
    row=dict(plane=pi,trial=trial,round=iteration,optimized_gap=gap,field_iterations=opt.nit,Qbase_min_eig=float(ev.min()),**meta)
    records.append(row);print(json.dumps(row),flush=True)
    if gap<best:
     best=gap;np.savez(ROOT/'penalty_sos_best.npz',p=p,Q=Q,F=F,A=A,B=B,x=x,exponents=pc.s.e,coefficients=pc.co,scales=pc.scales,normalized_penalty=pc.pen.value)
    (ROOT/'penalty_sos_results.json').write_text(json.dumps(records,indent=2))
    if gap< -1e-6:
     print('NEGATIVE CANDIDATE requiring exact certificate',flush=True);return
 print('BEST',best,flush=True)

if __name__=='__main__':main()
