"""Certified necessary condition: homogeneous quartic ROC iff 4x4 M(u⊗v) PSD for all angles.
This program searches for *negative* eigenvalues only; nonnegative sampled eigenvalues do NOT certify ROC.
"""
import numpy as np, itertools
from scipy.optimize import minimize
from math import pi, factorial
R=np.load('/mnt/data/morrey_four_wave_best.npz')
E=R['polynomial_exponents'];c=R['polynomial_coeff']
# coefficient tensors: Hessian in H, quadratic in A
B=np.zeros((4,4,4,4))
for ex,z in zip(E,c):
 for i,j,k,l in itertools.product(range(4),repeat=4):
  e=list(map(int,ex))
  for h in (i,j,k,l):
   if e[h]==0:break
   z1=1
  else: pass
  # common direct coefficient
  residual=e.copy(); mult=1
  for h in (i,j,k,l):
   mult*=residual[h];residual[h]-=1
  if min(residual)<0 or sum(residual)!=0:continue
  B[i,j,k,l]+=float(z)*mult/2
# numerical M(H) = B_ij,kl H_k H_l

def mat(theta_phi):
  t,s=theta_phi
  u=np.array([np.cos(t),np.sin(t)]);v=np.array([np.cos(s),np.sin(s)])
  h=np.outer(u,v).ravel()
  return np.einsum('ijkl,k,l->ij',B,h,h),h

def f(x):return np.linalg.eigvalsh(mat(x)[0])[0]
G=64;gs=np.linspace(0,pi,G,endpoint=False)
samples=np.array([[t,s] for t in gs for s in gs]);evals=np.array([f(x) for x in samples])
idx=np.argsort(evals)[:16]
results=[]
for i in idx:
  r=minimize(f,samples[i],method='BFGS',options={'gtol':1e-11,'maxiter':70})
  results.append((r.fun,r.x,r))
results.sort(key=lambda x:x[0]);worst=results[0]
print('min gridded eigenvalue',min(evals),'min refined eigenvalue',worst[0]);
for val,x,r in results[:4]:
 m,h=mat(x); w,evec=np.linalg.eigh(m)
 print('angle',x,'lambda_min',w[0],'X',evec[:,0],'H',h,'minD2',w[0])
print('polynomial:',[(tuple(map(int,e)),round(float(cc),8)) for e,cc in zip(E,c) if abs(cc)>1e-6])
np.savez('/mnt/data/morrey_four_wave_hessian_witness.npz',angles=worst[1],H=mat(worst[1])[1],X=np.linalg.eigh(mat(worst[1])[0])[1][:,0],min_eigenvalue=worst[0])
