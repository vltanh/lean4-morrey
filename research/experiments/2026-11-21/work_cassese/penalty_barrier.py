import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import numpy as np,json
from scipy.optimize import minimize
from pathlib import Path
from penalty_sos import Penalty,PeriodicFE
ROOT=Path(__file__).parent
rng=np.random.default_rng(921834);fe=PeriodicFE(5,2);records=[];best=np.inf
Bs=[np.array([[1.,0,0],[0,1,0]]),np.array([[1,0,1],[0,1,1]])]
for r in [.5,.1]:Bs.append(np.array([[1-r*r,2*r,1+r*r],[1-r*r,-2*r,1+r*r]])/(1+r*r))
for sign in [1,-1]:
 for pi,B in enumerate(Bs):
  pc=Penalty(B,sign=sign,free_mixed=True)
  for trial in range(3):
   x=rng.normal(size=50);F=rng.normal(size=4)*.3
   for iteration in range(4):
    A,_=fe.normalized(x);p,Q,meta=pc.solve(A,F)
    if p is None:
     records.append(dict(sign=sign,plane=pi,trial=trial,round=iteration,**meta));break
    def objective(y):
     A,s=fe.normalized(y);cov=A.T@A/len(A)+1e-5*np.eye(4)
     F,v,ev=pc.base(A,p);_,d=pc.s.fgrad(A+F,p);_,df=pc.s.fgrad(F[None,:],p);d-=df
     mu=.001;v-=mu*np.linalg.slogdet(cov)[1];d-=2*mu*A@np.linalg.inv(cov)
     dg=(d-A*np.mean(np.sum(d*A,axis=1)))/(s*len(A))
     return v,fe.back(dg)
    opt=minimize(objective,x,jac=True,method='L-BFGS-B',options=dict(maxiter=250,ftol=1e-13,gtol=1e-9,maxls=40))
    x=opt.x;A,_=fe.normalized(x);F,gap,ev=pc.base(A,p)
    row=dict(sign=sign,plane=pi,trial=trial,round=iteration,optimized_gap=gap,field_iterations=opt.nit,Qbase_min_eig=float(ev.min()),covariance_eigenvalues=np.linalg.eigvalsh(A.T@A/len(A)).tolist(),**meta)
    records.append(row);print(json.dumps(row),flush=True)
    if gap<best:
     best=gap;np.savez(ROOT/'penalty_barrier_best.npz',p=p,Q=Q,F=F,A=A,B=B,x=x,exponents=pc.s.e,coefficients=pc.co,scales=pc.scales,normalized_penalty=pc.pen.value)
    (ROOT/'penalty_barrier_results.json').write_text(json.dumps(records,indent=2))
    if gap< -1e-6:
     print('NEGATIVE CANDIDATE requiring exact certificate',flush=True);raise SystemExit
print('BEST',best,flush=True)
