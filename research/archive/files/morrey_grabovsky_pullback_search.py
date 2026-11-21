"""Constructive search for 2x2 Morrey counterexample by rank-one-preserving pullbacks
of the proven rank-one-convex quaternionic 2x6 energy of Agazzi et al. 2026.
G(M) = sqrt(|u|²|t|²+|s|²|v|²-2(u.s)(v.t)-2(u.v)(s.t)+2(u.t)(s.v))
for rows of M split as [u,v],[s,t] with 3-vectors.
Every f(A)=G(M0+A B) is globally rank-one convex for ANY B (2x6).
Only a strictly negative periodic Jensen gap would refute Morrey.
This is an exploratory optimizer: negative results require independent validation.
"""
import argparse, numpy as np
from scipy.optimize import minimize
ap=argparse.ArgumentParser();ap.add_argument('--seeds',type=int,default=25);ap.add_argument('--maxiter',type=int,default=280);ap.add_argument('--N',type=int,default=16);ap.add_argument('--mode',type=int,default=0);ap.add_argument('--save',default='/mnt/data/morrey_grabovsky_best.npz');args=ap.parse_args()
N=args.N;x,y=np.meshgrid(np.arange(N)/N,np.arange(N)/N,indexing='ij');waves=[(1,0),(0,1),(2,-1),(-1,2)]
if args.mode==1:waves=[(1,0),(0,1),(1,1),(2,1),(-1,2),(1,-2)]
if args.mode==2:waves=[(1,0),(0,1),(1,1),(2,1),(-1,2),(1,-2),(3,1),(1,3),(-2,3),(3,-2)]
mode=[]
for kx,ky in waves:
 ph=2*np.pi*(kx*x+ky*y)
 for der in [np.cos(ph),-np.sin(ph)]:
  for comp in range(2):
   h=np.zeros((N,N,2,2));h[:,:,comp,0]=kx*der;h[:,:,comp,1]=ky*der
   mode.append(h.reshape(-1,2,2))
T=np.stack(mode)
T/=np.sqrt(np.mean(np.sum(T*T,axis=(-2,-1)),axis=1))[:,None,None,None]
K=len(T);M=np.zeros((2,6));M[0,0]=-2;M[1,3]=-2

def G_and_dG(X):
 u,v,s,t=X[:,0,:3],X[:,0,3:],X[:,1,:3],X[:,1,3:]
 uu=np.sum(u*u,axis=1);vv=np.sum(v*v,axis=1);ss=np.sum(s*s,axis=1);tt=np.sum(t*t,axis=1)
 us=np.sum(u*s,axis=1);vt=np.sum(v*t,axis=1);uv=np.sum(u*v,axis=1);st=np.sum(s*t,axis=1);ut=np.sum(u*t,axis=1);sv=np.sum(s*v,axis=1)
 g2=uu*tt+ss*vv-2*us*vt-2*uv*st+2*ut*sv
 g2=np.maximum(g2,1e-24)
 sqrt=np.sqrt(g2)
 dg=np.empty_like(X)
 dg[:,0,:3]=(2*u*tt[:,None]-2*s*vt[:,None]-2*v*st[:,None]+2*t*sv[:,None])/(2*sqrt[:,None])
 dg[:,0,3:]=(2*v*ss[:,None]-2*t*us[:,None]-2*u*st[:,None]+2*s*ut[:,None])/(2*sqrt[:,None])
 dg[:,1,:3]=(2*s*vv[:,None]-2*u*vt[:,None]-2*t*uv[:,None]+2*v*ut[:,None])/(2*sqrt[:,None])
 dg[:,1,3:]=(2*t*uu[:,None]-2*v*us[:,None]-2*s*uv[:,None]+2*u*sv[:,None])/(2*sqrt[:,None])
 return sqrt,dg

assert np.max(np.abs(G_and_dG(M[None,:,:])[0]-4))<1e-12
rng=np.random.default_rng(638)
def objective(z):
 a=z[:K];B=z[K:].reshape(2,6)
 U=np.einsum('i,injk->njk',a,T,optimize=True)
 X=M+U@B
 val,dg=G_and_dG(X)
 grad_B=np.einsum('nij,nik->jk',U,dg)/len(U)
 grad_a=np.einsum('nij,knil,lj->k',dg,T,B)/len(U)
 # equivalently derivative to alpha = sum over samples, coords of dG (T_i B)
 return float(np.mean(val)-4.),np.r_[grad_a,grad_B.ravel()]

# gradient finite-difference sanity check
z=np.r_[rng.normal(scale=.1,size=K),rng.normal(scale=.5,size=12)]
f,g=objective(z)
for k in [0,1,K-1,K,K+6,K+11]:
 eps=1e-6;zz=z.copy();zz[k]+=eps;ff=objective(zz)[0];zz[k]-=2*eps;bb=objective(zz)[0]
 assert abs((ff-bb)/(2*eps)-g[k])<4e-6,(k,(ff-bb)/(2*eps),g[k])
print('gradient independent finite-difference check PASS; N',N,'waves',len(waves),'vars',len(z),flush=True)

best=1e9
for seed in range(args.seeds):
  # random scale B and Fourier coefficients chosen to begin in genuine nonlinear regime
  amp=rng.normal(size=K)
  amp/=np.linalg.norm(amp)
  B=rng.normal(size=(2,6));B/=np.linalg.norm(B)
  if seed%3==0:amp*=.3
  if seed%3==1:amp*=2.
  if seed%3==2:amp*=5.
  z=np.r_[amp,B.ravel()]
  res=minimize(objective,z,jac=True,method='L-BFGS-B',options={'maxiter':args.maxiter,'ftol':2e-13,'gtol':1e-9,'maxls':24})
  v=res.fun
  if v<best:
    best=v
    np.savez(args.save,polynomial=False,waves=waves,alpha=res.x[:K],B=res.x[K:].reshape(2,6),M=M,N=N,objective=v)
  print('seed',seed,'gap',f'{v:+.12g}','best',f'{best:+.12g}','iterations',res.nit,'status',res.message,flush=True)
print('best',best,flush=True)
