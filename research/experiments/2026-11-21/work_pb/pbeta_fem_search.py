"""Piecewise affine periodic fields on exact equal area triangulation.
Optimize the base via quadratic completion and normalize transverse gradient energy.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from pbeta_fourier_search import base_min,val_grad
class FEM:
 def __init__(self,n,beta=2):self.n=n;self.beta=beta
 def field(self,u):
  n=self.n;u=u.reshape(n,n,2)
  xp=np.roll(u,-1,axis=0);yp=np.roll(u,-1,axis=1);xy=np.roll(xp,-1,axis=1)
  low=np.stack([xp-u,yp-u],axis=-1)*n
  hi=np.stack([xy-yp,xy-xp],axis=-1)*n
  return np.stack([low,hi],axis=0).reshape(-1,4)
 def adjoint(self,v):
  n=self.n;v=v.reshape(2,n,n,2,2);lo,hi=v
  gx,gy=lo[...,0],lo[...,1]
  out=np.roll(gx,1,axis=0)-gx+np.roll(gy,1,axis=1)-gy
  gx,gy=hi[...,0],hi[...,1]
  out+=np.roll(np.roll(gx+gy,1,axis=0),1,axis=1)-np.roll(gx,1,axis=1)-np.roll(gy,1,axis=0)
  return (out*n).ravel()
 def eval(self,raw,aux=False):
  X=self.field(raw);Y=X.copy();Y[:,0]=0
  var=np.mean(np.sum(Y*Y,axis=1));scale=np.sqrt(var);X/=scale
  gap,gx,F,ev,h,K,c0=base_min(X,self.beta)
  Y/=scale
  gx=(gx-Y*np.mean(np.sum(gx*X,axis=1)))/scale
  gr=self.adjoint(gx)/len(X)
  if aux:
   return {'gap':float(gap),'base':F.tolist(),'eigenvalues':ev.tolist(),'nodal':(raw/scale).reshape(self.n,self.n,2).tolist(),'variance_transverse':float(np.mean(np.sum(X[:,1:]**2,axis=1))),'gradient_variance':float(np.mean(np.sum(X*X,axis=1))),'mean_det':float(np.mean(X[:,0]*X[:,3]-X[:,1]*X[:,2]))}
  return gap,gr
 def check(self):
  rng=np.random.default_rng(516);u=rng.normal(size=2*self.n*self.n);val,g=self.eval(u);err=[]
  for _ in range(8):
   z=rng.normal(size=len(u));z/=np.linalg.norm(z);eps=1e-5
   fd=(self.eval(u+eps*z)[0]-self.eval(u-eps*z)[0])/(2*eps)
   err.append(abs(fd-g@z))
  if max(err)>1e-6:raise RuntimeError(err)
  print('gradient_check',max(err),flush=True)
  aux=self.eval(u,True);X=self.field(np.array(aux['nodal']));F=np.array(aux['base'])
  dr=np.mean(val_grad(X+F,self.beta)[0])-val_grad(F.reshape(1,4),self.beta)[0][0]
  print('direct_gap_check',abs(dr-val),'mean_det',aux['mean_det'],flush=True)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=4);ap.add_argument('--starts',type=int,default=30);ap.add_argument('--maxiter',type=int,default=800);ap.add_argument('--seed',type=int,default=453);ap.add_argument('--output',default='fem.json');a=ap.parse_args()
 s=FEM(a.n);s.check();rng=np.random.default_rng(a.seed);res=[];best=None;t=time.time()
 for k in range(a.starts):
  if k%3==2 and best is not None:raw=np.array(best['nodal']).ravel()+rng.normal(scale=.1/a.n,size=2*a.n*a.n)
  else:raw=rng.normal(size=2*a.n*a.n)
  r=minimize(s.eval,raw,jac=True,method='L-BFGS-B',options={'maxiter':a.maxiter,'gtol':1e-10,'ftol':1e-14,'maxls':40})
  aux=s.eval(r.x,True);aux.update(start=k,nit=r.nit,success=bool(r.success),message=str(r.message),gradient_norm=float(np.linalg.norm(r.jac)))
  res.append(aux)
  if best is None or aux['gap']<best['gap']:best=aux
  print(k,'gap',aux['gap'],'eigmin',min(aux['eigenvalues']),'base',np.linalg.norm(aux['base']),'nit',r.nit,'seconds',round(time.time()-t,1),flush=True)
  Path(a.output).write_text(json.dumps({'n':a.n,'beta':2,'normalization':'transverse','results':res,'best':best,'note':'Float local search only.'},indent=2))
if __name__=='__main__':main()
