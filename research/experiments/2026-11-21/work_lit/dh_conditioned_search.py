"""Optimize full-rank bases with singular value ratio >= (1-.85)/(1+.85)."""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from dh_fem_search import N_STRONG,N_ORIGINAL,objective,init,gradient

def base(p,sign):
 rho,theta,phi,r=p
 ct,st=np.cos(theta),np.sin(theta); cp,sp=np.cos(phi),np.sin(phi)
 s=rho/np.sqrt(2*(1+r*r))
 F=s*np.array([ct+r*cp,-st+r*sp,st+r*sp,ct-r*cp])
 J=np.column_stack((F/rho,s*np.array([-st,-ct,ct,-st]),
                    s*np.array([-r*sp,r*cp,r*cp,r*sp]),
                    -r*F/(1+r*r)+s*np.array([cp,sp,sp,-cp])))
 F[2:]*=sign;J[2:]*=sign
 return F,J

def fun(z,n,N,sign):
 F,J=base(z[-4:],sign)
 val,g=objective(np.r_[z[:-4],F],n,N)
 return val,np.r_[g[:-4],g[-4:]@J]

def main(args):
 rng=np.random.default_rng(args.seed);out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
 z=init(4,rng,1);z[-4:]=[1.5,.7,.9,.4]
 v,g=fun(z,4,N_STRONG,-1)
 errs=[]
 for j in range(len(z)-4,len(z)):
  zp=z.copy();zm=z.copy();zp[j]+=1e-5;zm[j]-=1e-5
  errs.append(abs((fun(zp,4,N_STRONG,-1)[0]-fun(zm,4,N_STRONG,-1)[0])/2e-5-g[j]))
 assert max(errs)<1e-8
 print('parameter gradient check',max(errs),flush=True)
 records=[];best=1e100
 for family,N in [('strong',N_STRONG),('original',N_ORIGINAL)]:
  for n in args.grids:
   for sign in [1,-1]:
    for i in range(args.starts):
     z=init(n,rng,i);z[-4:]=[rng.uniform(.3,5),rng.uniform(-np.pi,np.pi),rng.uniform(-np.pi,np.pi),rng.uniform(0,.8)]
     t=time.time()
     res=minimize(fun,z,args=(n,N,sign),jac=True,method='L-BFGS-B',
        bounds=[(None,None)]*(2*n*n)+[(.2,6),(None,None),(None,None),(0,.85)],
        options={'maxiter':args.maxiter,'ftol':1e-14,'gtol':1e-9,'maxls':40})
     U=res.x[:-4].reshape(n,n,2);G=gradient(U);U/=np.sqrt(np.mean(np.sum(G*G,axis=(-2,-1))))
     F=base(res.x[-4:],sign)[0].reshape(2,2)
     row=dict(family=family,n=n,sign=sign,start=i,gap=float(res.fun),base_parameters=res.x[-4:].tolist(),
          F=F.tolist(),iters=int(res.nit),success=bool(res.success),message=res.message,seconds=time.time()-t)
     records.append(row)
     if res.fun<best:
      best=float(res.fun);np.savez(out/'best.npz',U=U,F=F,N=N,gap=best)
     print(json.dumps(row),flush=True)
     (out/'results.json').write_text(json.dumps(records,indent=2))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--seed',type=int,default=329410)
 p.add_argument('--grids',type=int,nargs='+',default=[8,16]);p.add_argument('--starts',type=int,default=8)
 p.add_argument('--maxiter',type=int,default=1000)
 p.add_argument('--output',default=str(Path(__file__).with_name('dh_conditioned_results')))
 main(p.parse_args())
