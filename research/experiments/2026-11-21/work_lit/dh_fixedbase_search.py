import json,time,argparse
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from dh_fem_search import N_STRONG,N_ORIGINAL,objective,init,gradient,checks

def main(args):
 rng=np.random.default_rng(args.seed)
 out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
 records=[];best=1e100
 for family,N in [('strong',N_STRONG),('original',N_ORIGINAL)]:
  for n in args.grids:
   for rho in args.scales:
    for typ in ['identity','anisotropic','rotated']:
     if typ=='identity':F=rho*np.eye(2)
     elif typ=='anisotropic':F=rho*np.diag([1.,.3])
     else:
      th=np.pi/6;F=rho*np.array([[np.cos(th),-np.sin(th)],[np.sin(th),np.cos(th)]])
     def fun(u):
      val,g=objective(np.r_[u,F.ravel()],n,N)
      return val,g[:-4]
     for i in range(args.starts):
      u=init(n,rng,i)[:-4]
      t=time.time()
      res=minimize(fun,u,jac=True,method='L-BFGS-B',
         options={'maxiter':args.maxiter,'ftol':1e-14,'gtol':1e-9,'maxls':40})
      U=res.x.reshape(n,n,2);G=gradient(U)
      U/=np.sqrt(np.mean(np.sum(G*G,axis=(-2,-1))))
      row=dict(family=family,n=n,rho=rho,base_type=typ,start=i,gap=float(res.fun),
          iters=int(res.nit),success=bool(res.success),message=res.message,seconds=time.time()-t)
      records.append(row)
      if res.fun<best:
       best=float(res.fun);np.savez(out/'best.npz',U=U,F=F,N=N,gap=best)
      print(json.dumps(row),flush=True)
      (out/'results.json').write_text(json.dumps(records,indent=2))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--seed',type=int,default=99012)
 p.add_argument('--grids',type=int,nargs='+',default=[4,8,16]);p.add_argument('--scales',type=float,nargs='+',default=[.25,.5,1,2,4])
 p.add_argument('--starts',type=int,default=4);p.add_argument('--maxiter',type=int,default=800)
 p.add_argument('--output',default=str(Path(__file__).with_name('dh_fixed_results')))
 main(p.parse_args())
