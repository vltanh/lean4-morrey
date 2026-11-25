"""Target sharp-LH degeneracy with large u1(x) gradients and mixed modes."""
import json,time
import numpy as np
from scipy.optimize import minimize
from pathlib import Path
from pbeta_fourier_search import Search,mode_set
s=Search(mode_set('3'),2,'transverse');rng=np.random.default_rng(7731);m=len(s.modes);out=[];tm=time.time()
for scale in [3.,10.,30.,100.,300.]:
 for j in range(12):
  c=rng.normal(size=(2*m,2));mask=s.dirs[:,1]==0;c[mask,0]*=scale
  r=minimize(s.eval,c.ravel(),jac=True,method='L-BFGS-B',options={'maxiter':1600,'gtol':1e-10,'ftol':1e-14,'maxls':40})
  aux=s.eval(r.x,True);aux.update(scale=scale,start=j,nit=r.nit,success=bool(r.success),message=str(r.message),gradient_norm=float(np.linalg.norm(r.jac)));out.append(aux)
  print('scale',scale,j,'gap',aux['gap'],'base',np.linalg.norm(aux['base']),'eigmin',min(aux['eigenvalues']),'var',aux['variance'],'nit',r.nit,'time',round(time.time()-tm,2),flush=True)
  (Path(__file__).resolve().parent/'targeted_results.json').write_text(json.dumps({'modes':s.modes.tolist(),'beta':2,'normalization':'transverse','results':out,'best':min(out,key=lambda x:x['gap'])},indent=2))
