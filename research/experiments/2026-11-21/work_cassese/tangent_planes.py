import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import numpy as np,json
from scipy.optimize import minimize
from pathlib import Path
from search import Search
ROOT=Path(__file__).parent
class Tangent(Search):
 def __init__(self,delta,modes,theta):
  self.B0=np.array([[np.cos(theta),np.sin(theta),1],[np.cos(theta),-np.sin(theta),1]])/np.sqrt(2)
  super().__init__(delta,modes)
 def embed(self,rot):
  B=self.B0;ns=self.modes@B;mats=[]
  for n in ns:
   T=np.zeros((6,2));T[:3,0]=n;T[3:,1]=n
   V=self.Rh@T
   ev,U=np.linalg.eigh(V.T@V)
   inv=(U*(1/np.sqrt(ev)))@U.T
   mats.append(V@inv)
  return np.stack(mats),B
rng=np.random.default_rng(848372)
modes=[(1,0),(0,1),(1,1),(1,-1),(2,1),(1,2),(2,-1),(1,-2)]
results=[]
for delta in [.1,.01,.001]:
 for theta in [.5,.1,.01,.001]:
  se=Tangent(delta,modes,theta)
  def fun(c):
   val,g=se.value(np.r_[np.zeros(3),c],rotdiff=False)
   return val,g[3:]
  for trial in range(3):
   c=rng.normal(size=4*len(modes))
   rr=minimize(fun,c,jac=True,method='L-BFGS-B',options=dict(maxiter=700,gtol=1e-9,ftol=1e-13,maxls=50))
   x=np.r_[np.zeros(3),rr.x];rep=se.value(x,report=True)
   rep.update(theta=theta,trial=trial,success=bool(rr.success),iterations=rr.nit,gradient_norm=float(np.linalg.norm(rr.jac)),message=str(rr.message))
   results.append(rep)
   print(delta,theta,trial,rep['gap_scaled'],rr.nit,rep['gradient_norm'],flush=True)
   (ROOT/'tangent_planes_results.json').write_text(json.dumps(results,indent=2))
