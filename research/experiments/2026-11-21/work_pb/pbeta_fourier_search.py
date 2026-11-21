"""Periodic gradient search for P_beta, eliminating every base F analytically.
No sampled rank-one convexity: use the exact beta>=2 certificate in beta2_certificate.py.
Quadrature grid >4*max|frequency| makes quartic trigonometric averages exact.
Float arithmetic is search evidence only.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize, check_grad
G=np.array([[0,0,0,.5],[0,0,-1,0],[0,-1,0,0],[.5,0,0,0.]])
E=np.diag([0.,1.,1.,1.])

def val_grad(X,beta):
 a,b,c,d=X.T; g=a*d-2*b*c;r=b*b+c*c+d*d
 V=np.column_stack([d,-2*c,-2*b,a])
 Y=X.copy();Y[:,0]=0
 val=g*g+beta*r*r
 grad=2*g[:,None]*V+4*beta*r[:,None]*Y
 return val,grad

def base_min(X,beta):
 n=len(X); a,b,c,d=X.T;gx=a*d-2*b*c;rx=b*b+c*c+d*d
 V=np.column_stack([d,-2*c,-2*b,a]);Y=X.copy();Y[:,0]=0
 K=V.T@V/n+2*gx.mean()*G+beta*(2*rx.mean()*E+4*Y.T@Y/n)
 h=np.mean(V*gx[:,None],axis=0)+2*beta*np.mean(Y*rx[:,None],axis=0)
 c0=np.mean(gx*gx+beta*rx*rx)
 ev,U=np.linalg.eigh(K)
 if ev.min() < -1e-8: raise RuntimeError(('quadratic gap not PSD',ev))
 inv=np.where(ev>1e-13,1/np.maximum(ev,1e-30),0.)
 F=-U@(inv*(U.T@h))
 gap=c0+h@F
 # Stable difference of gradients at F+X and F.
 af,bf,cf,df=F;gf=af*df-2*bf*cf;yf=F.copy();yf[0]=0;rf=yf@yf
 vf=np.array([df,-2*cf,-2*bf,af]);l=X@vf;dy=Y@yf
 dg=2*gf*V+2*(l+gx)[:,None]*vf+2*(l+gx)[:,None]*V+4*beta*(rf*Y+(2*dy+rx)[:,None]*yf+(2*dy+rx)[:,None]*Y)
 return gap,dg,F,ev,h,K,c0

class Search:
 def __init__(self,modes,beta=2,normalization="full"):
  self.modes=np.asarray(modes,dtype=float);self.beta=beta;self.normalization=normalization
  self.n=int(4*np.max(np.abs(self.modes))+1)
  x=np.arange(self.n)*2*np.pi/self.n; xx,yy=np.meshgrid(x,x,indexing='ij')
  points=np.stack([xx.ravel(),yy.ravel()],axis=1)
  angles=points@self.modes.T
  self.basis=np.concatenate([np.cos(angles),np.sin(angles)],axis=1)
  nhat=self.modes/np.linalg.norm(self.modes,axis=1)[:,None]
  self.dirs=np.concatenate([nhat,nhat])
  self.weights=np.ones(self.basis.shape[1]*2)
  if normalization=="transverse":self.weights[::2]=self.dirs[:,1]**2
 def eval(self,raw,aux=False):
  norm=np.sqrt(np.dot(self.weights*raw,raw));c=np.sqrt(2)*raw/norm;c=c.reshape(-1,2)
  X=np.einsum('ni,ik,ij->nkj',self.basis,c,self.dirs,optimize=True).reshape(-1,4)
  gap,dg,F,ev,h,K,c0=base_min(X,self.beta)
  dc=np.einsum('nkj,ni,ij->ik',dg.reshape(-1,2,2),self.basis,self.dirs,optimize=True)/len(X)
  dc=dc.ravel();gh=np.sqrt(2)/norm*(dc-self.weights*raw*(raw@dc)/norm**2)
  if aux: return {'gap':float(gap),'base':F.tolist(),'eigenvalues':ev.tolist(),'linear':h.tolist(),'variance':float(np.mean(X*X)*4),'coefficients':c.tolist(),'raw_norm':float(norm),'c0':float(c0),'mean_det':float(np.mean(X[:,0]*X[:,3]-X[:,1]*X[:,2]))}
  return gap,gh
 def gradcheck(self,seed=713):
  rng=np.random.default_rng(seed);raw=rng.normal(size=self.basis.shape[1]*2)
  v,g=self.eval(raw);errs=[]
  for k in range(8):
   z=rng.normal(size=len(raw));z/=np.linalg.norm(z);eps=1e-5
   fd=(self.eval(raw+eps*z)[0]-self.eval(raw-eps*z)[0])/(2*eps)
   errs.append(abs(fd-z@g))
  print('gradient_check',max(errs),flush=True)
  if max(errs)>1e-6:raise RuntimeError(errs)
  aux=self.eval(raw,True)
  coeff=np.array(aux['coefficients']);X=np.einsum('ni,ik,ij->nkj',self.basis,coeff,self.dirs).reshape(-1,4);F=np.array(aux['base'])
  direct=np.mean(val_grad(X+F,self.beta)[0])-val_grad(F.reshape(1,4),self.beta)[0][0]
  print('direct_gap_check',abs(direct-v),'mean_det',aux['mean_det'],flush=True)

def mode_set(tag):
 if tag=='four':return [(1,0),(0,1),(2,-1),(-1,2)]
 if tag=='six':return [(1,0),(0,1),(1,1),(1,-1),(2,1),(1,2)]
 K=int(tag)
 return [(i,j) for i in range(0,K+1) for j in range(-K,K+1) if (i>0 or j>0)]

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--modes',default='six');ap.add_argument('--starts',type=int,default=20);ap.add_argument('--maxiter',type=int,default=700);ap.add_argument('--seed',type=int,default=104);ap.add_argument('--beta',type=float,default=2.);ap.add_argument('--output',default='search.json');ap.add_argument('--normalization',choices=['full','transverse'],default='full');a=ap.parse_args()
 s=Search(mode_set(a.modes),a.beta,a.normalization);s.gradcheck();rng=np.random.default_rng(a.seed);best=None;results=[];t=time.time()
 for k in range(a.starts):
  if k and k%3==2 and best is not None:
   raw=np.array(best['coefficients']).ravel()+rng.normal(scale=.2,size=s.basis.shape[1]*2)
  else:raw=rng.normal(size=s.basis.shape[1]*2)
  r=minimize(s.eval,raw,jac=True,method='L-BFGS-B',options={'maxiter':a.maxiter,'gtol':1e-10,'ftol':1e-14,'maxls':40})
  aux=s.eval(r.x,True);aux.update(start=k,nit=r.nit,success=bool(r.success),message=str(r.message),gradient_norm=float(np.linalg.norm(r.jac)))
  results.append(aux)
  if best is None or aux['gap']<best['gap']:best=aux
  print(k, 'gap',aux['gap'],'eigmin',min(aux['eigenvalues']),'base',np.linalg.norm(aux['base']),'nit',r.nit,'seconds',round(time.time()-t,1),flush=True)
  Path(a.output).write_text(json.dumps({'beta':a.beta,'normalization':a.normalization,'modes':s.modes.tolist(),'grid':s.n,'results':results,'best':best,'note':'Float search only; positive/zero outcomes prove no quasiconvexity statement.'},indent=2))
if __name__=='__main__':main()
