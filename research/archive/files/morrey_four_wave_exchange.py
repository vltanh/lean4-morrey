"""Exchange LP against the matrix-valued rank-one Hessian of homogeneous quartics.
Finds negative Hessian witnesses; NO positive proof without separate continuum certification.
"""
import numpy as np, itertools, math, argparse
from scipy.optimize import linprog
p=argparse.ArgumentParser();p.add_argument('--steps',type=int,default=65);p.add_argument('--angular',type=int,default=32);p.add_argument('--init',type=int,default=4000);args=p.parse_args()
rng=np.random.default_rng(123)
R=np.load('/mnt/data/morrey_four_wave_best.npz');e=R['polynomial_exponents'];Q=len(e)
coeff=R['gradient_coeff'];F=R['base_matrix'];waves=R['wavevectors']
N=32;x,y=np.meshgrid(np.arange(N)/N,np.arange(N)/N,indexing='ij');T=[]
for k in waves:
 ph=2*np.pi*(k[0]*x+k[1]*y)
 for g in [2*np.pi*np.cos(ph),-2*np.pi*np.sin(ph)]:
  for c in range(2):
   J=np.zeros((N,N,4));J[:,:,c*2]=k[0]*g;J[:,:,c*2+1]=k[1]*g;T.append(J)
T=np.array(T);T/=np.sqrt(np.mean(T*T,axis=(1,2,3)))[:,None,None,None]
U=np.einsum('i,ixyj->xyj',coeff,T);U/=np.sqrt(np.mean(np.sum(U**2,axis=2)))
field=F+U;mom=(np.mean(np.prod(field.reshape(-1,4)[:,None,:]**e[None,:,:],axis=-1),axis=0)-np.prod(F[None,:]**e,axis=-1))

def dhess(X,H):
 ret=np.zeros((len(X),Q))
 for i in range(4):
  for j in range(4):
   z=e[:,i]*(e[:,j]-(i==j));nz=z!=0
   if not np.any(nz):continue
   exp=e[nz].copy();exp[:,i]-=1;exp[:,j]-=1
   ret[:,nz]+=(H[:,i]*H[:,j])[:,None]*z[nz]*np.prod(X[:,None,:]**exp[None,:,:],axis=2)
 return ret

# Tensor G[q,i,j,k,l]: D²(A^e)[H,H] = sum_ij,kl G[q,i,j,k,l] A_i A_j H_k H_l
G=np.zeros((Q,4,4,4,4));factorials=np.array([[math.factorial(int(a)) for a in ex] for ex in e]).prod(axis=1)
for idx,(i,j,k,l) in enumerate(itertools.product(range(4),repeat=4)):
 cnt=np.bincount([i,j,k,l],minlength=4)
 ix=np.flatnonzero(np.all(e==cnt,axis=1))
 if len(ix):G[ix[0],i,j,k,l]=factorials[ix[0]]/2

grid=np.linspace(0,np.pi,args.angular,endpoint=False)
TH,PH=np.meshgrid(grid,grid,indexing='ij');uu=np.stack([np.cos(TH.ravel()),np.sin(TH.ravel())],axis=-1);vv=np.stack([np.cos(PH.ravel()),np.sin(PH.ravel())],axis=-1)
HH=np.column_stack([uu[:,0]*vv[:,0],uu[:,0]*vv[:,1],uu[:,1]*vv[:,0],uu[:,1]*vv[:,1]])
# initial random sampled Hess
X=rng.normal(size=(args.init,4));X/=np.linalg.norm(X,axis=1)[:,None]
u=rng.normal(size=(args.init,2));u/=np.linalg.norm(u,axis=1)[:,None]
v=rng.normal(size=(args.init,2));v/=np.linalg.norm(v,axis=1)[:,None]
h=np.column_stack([u[:,0]*v[:,0],u[:,0]*v[:,1],u[:,1]*v[:,0],u[:,1]*v[:,1]])
A=dhess(X,h);normal=A.mean(axis=0)
print('initial moment norm',np.linalg.norm(mom),'degrees',len(e),'init constraints',len(A),flush=True)
best=1e9
for step in range(args.steps):
 res=linprog(mom,A_ub=-A,b_ub=np.zeros(len(A)),A_eq=normal[None,:],b_eq=[1.],bounds=[(None,None)]*Q,method='highs',options={'time_limit':15})
 if not res.success:
  print('solve failed',res.message);break
 c=res.x; mat=np.einsum('q,qijkl,mk,ml->mij',c,G,HH,HH,optimize=True)
 values,evectors=np.linalg.eigh(mat);idx=np.argsort(values[:,0])[:16]
 worst=values[idx[0],0]
 if res.fun<best:best=res.fun
 print('iter',step,'J',float(res.fun),'worst_rankone_hessian',float(worst),'numconstraints',len(A),flush=True)
 if res.fun>0:
  print('NONNEGATIVE lower bound over sampled cone; rigorous negative candidate eliminated.');break
 if worst>-1e-8:
  print('NO NEGATIVE EIGENVALUE FOUND on grid; refinement necessary.');break
 Xnew=np.array([evectors[k,:,0] for k in idx]);Hnew=HH[idx]
 A=np.vstack([A,dhess(Xnew,Hnew)])
 np.savez('/mnt/data/morrey_four_wave_exchange_last.npz',coef=c,exps=e,J=res.fun,worst_hessian=worst,iteration=step,moment=mom)
