"""Search globally rank-one-convex planar pullbacks of Cassese's 2x3 quartic.
No finite sampling of rank-one directions: ROC is inherited from published Lean theorem.
Any negative energy must be independently certified.
"""
import argparse,numpy as np,sympy as sy
from scipy.optimize import minimize
ap=argparse.ArgumentParser();ap.add_argument('--seeds',type=int,default=10);ap.add_argument('--iters',type=int,default=190);ap.add_argument('--N',type=int,default=16);ap.add_argument('--delta',type=float,default=1);ap.add_argument('--mode',type=int,default=0);args=ap.parse_args()
a,b,c,d,e,f=sy.symbols('a b c d e f',real=True)
# A23=[[a,b,c],[d,e,f]], embedding [[a-c,b,b,-a-c],[d-f,e,e,-d-f]]
x0=(a-c-e)/2; x1=(b+d+f)/2
y0=d-f;y1=e;u0=b;u1=-a-c
z0=(a-c+e)/2;z1=(b-d-f)/2
W=lambda x,y,z,t:x*t-y*z
q=W(y0,y1,u0,u1)**2-4*W(x0,x1,u0,u1)*W(x0,x1,y0,y1)
LS=2*(x0*x0+x1*x1)+y0*y0+y1*y1+u0*u0+u1*u1
PS=2*(z0*z0+z1*z1)
delta=sy.Rational(str(args.delta));lam=22/delta
h=sy.expand(q+delta*(LS+lam**2*PS)**2)
coords=[a,b,c,d,e,f];hf=sy.lambdify(coords,h,'numpy');hgrad=sy.lambdify(coords,[sy.diff(h,u) for u in coords],'numpy')
print('quartic monomials',len(sy.Poly(h,coords).terms()),'delta',args.delta,'lambda',float(lam),flush=True)
N=args.N;x,y=np.meshgrid(np.arange(N)/N,np.arange(N)/N,indexing='ij')
waves=[(1,0),(0,1),(1,1),(2,-1),(-1,2)] if args.mode==0 else [(1,0),(0,1),(1,1),(2,-1),(-1,2),(2,1),(1,-2),(3,2),(-2,3)]
mode=[]
for kx,ky in waves:
 phase=2*np.pi*(kx*x+ky*y)
 for wave in [np.cos(phase),np.sin(phase)]:
  for comp in range(2):
   g=np.zeros((N,N,2,2));g[:,:,comp,0]=kx*wave;g[:,:,comp,1]=ky*wave
   mode.append(g.reshape(-1,2,2))
T=np.stack(mode);T/=np.sqrt(np.mean(np.sum(T*T,axis=(2,3)),axis=1))[:,None,None,None]
K=len(T);rng=np.random.default_rng(3423)
def obj(raw,retinfo=False):
 # sphere normalization prevents scale-collapse of quartic integrand
 zz=raw[:K]; BB=raw[K:].reshape(2,3)
 zz/=1e0 # avoid in-place modification of views
 zz=zz/(np.linalg.norm(zz)+1e-12); BB=BB/(np.linalg.norm(BB)+1e-12)
 U=np.einsum('k,kacd->acd',zz,T,optimize=True);X=np.einsum('nrc,cs->nrs',U,BB,optimize=True)
 sarr=[X[:,i,j] for i in range(2) for j in range(3)]
 qvals=hf(*sarr);val=np.mean(qvals)
 grads=np.stack(hgrad(*sarr),axis=-1).reshape(-1,2,3)
 gx=np.einsum('nrs,knrc,cs->k',grads,T,BB,optimize=True)/len(grads)
 gb=np.einsum('nrc,nrs->cs',U,grads,optimize=True)/len(grads)
 # normalize gradients via chain rule
 normz=np.linalg.norm(raw[:K])+1e-12;normb=np.linalg.norm(raw[K:])+1e-12
 gx=(gx-zz*np.dot(zz,gx))/normz
 gb=(gb-BB*np.sum(BB*gb))/normb
 if retinfo:return val,zz,BB,X,np.mean(LS) if False else None
 return float(val),np.r_[gx,gb.ravel()]
# Sanity: finite difference gradients, avoid tiny at near zero
z=np.r_[rng.normal(size=K),rng.normal(size=6)]
f0,g0=obj(z)
for j in [0,K//2,K-1,K,K+5]:
 eps=1e-5; t=z.copy();t[j]+=eps; fp=obj(t)[0];t=z.copy();t[j]-=eps;fm=obj(t)[0]
 assert abs((fp-fm)/(2*eps)-g0[j])<max(1e-3,1e-3*abs(g0[j])),(j,(fp-fm)/(2*eps),g0[j])
print('exact analytic gradients checked by finite differences',flush=True)
best=1e99
for k in range(args.seeds):
 start=np.r_[rng.normal(size=K),rng.normal(size=6)]
 res=minimize(obj,start,jac=True,method='L-BFGS-B',options={'maxiter':args.iters,'ftol':1e-13,'gtol':1e-7})
 if res.fun<best:
  best=res.fun
  _,zz,BB,X,_=obj(res.x,True)
  np.savez('/mnt/data/morrey_cassese_pullback_best.npz',z=zz,B=BB,waves=waves,val=res.fun,delta=args.delta)
 print('seed',k,'normalized quartic gap',f'{res.fun:+.8g}','best',f'{best:+.8g}','iterations',res.nit,flush=True)
print('BEST',best,flush=True)
