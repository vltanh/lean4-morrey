import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import numpy as np,json
from scipy.optimize import minimize
from scipy.spatial.transform import Rotation
from pathlib import Path
from search import Search
ROOT=Path(__file__).parent
rng=np.random.default_rng(532271)
modes=[(1,0),(0,1),(1,1),(1,-1),(2,1),(1,2),(2,-1),(1,-2)]
planes=[np.array([[1,0,1],[-1,0,1],[0,-np.sqrt(2),0]])/np.sqrt(2),np.eye(3),Rotation.from_rotvec([.5,.3,.7]).as_matrix()]
results=[]
for delta in [1,.1,.01,.001]:
 se=Search(delta,modes)
 for pi,B in enumerate(planes):
  rot=Rotation.from_matrix(B).as_rotvec()
  def fun(c):
   val,g=se.value(np.r_[rot,c],rotdiff=False)
   return val,g[3:]
  best=None
  for trial in range(3):
   c=rng.normal(size=4*len(modes))
   rr=minimize(fun,c,jac=True,method='L-BFGS-B',options=dict(maxiter=600,gtol=1e-9,ftol=1e-13,maxls=50))
   x=np.r_[rot,rr.x];rep=se.value(x,report=True)
   rep.update(plane=pi,trial=trial,success=bool(rr.success),iterations=rr.nit,gradient_norm=float(np.linalg.norm(rr.jac)),message=str(rr.message))
   results.append(rep)
   if best is None or rep['gap_scaled']<best: best=rep['gap_scaled']
   print(delta,pi,trial,rep['gap_scaled'],rr.nit,rep['gradient_norm'],flush=True)
   (ROOT/'fixed_planes_results.json').write_text(json.dumps(results,indent=2))
