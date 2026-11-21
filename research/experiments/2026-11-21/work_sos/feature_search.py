"""SOS search avoiding concentration on low-degree algebraic wells.

The barrier uses centered polynomial-feature covariance, not just covariance
of A. For degree 4 use all monomials of degree 1,2; for degree 6 add degree3.
It is a search aid, not a mathematical restriction in any claimed theorem.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
from pathlib import Path
import argparse,json,math
import numpy as np
from scipy.optimize import minimize
from sos_search import SOS,PeriodicFE,exps

class Features:
    def __init__(self,degree):
        self.e=np.array([e for d in range(1,degree//2+1) for e in exps(4,d)],int)
        self.scale=np.array([math.sqrt(math.factorial(sum(e))/math.prod(math.factorial(k) for k in e)) for e in self.e])
    def calc(self,A):return np.prod(A[:,None,:]**self.e[None,:,:],axis=2)*self.scale
    def cost_grad(self,A):
        V=self.calc(A);Z=V-V.mean(axis=0);C=Z.T@Z/len(A)
        eig=np.linalg.eigvalsh(C);C=C+1e-12*np.eye(len(self.e))
        L=np.linalg.cholesky(C);cost=-2*np.log(np.diag(L)).sum()/len(self.e)
        D=-2*np.linalg.solve(C,Z.T).T/len(self.e)
        grad=np.zeros_like(A)
        for j in range(4):
            use=self.e[:,j]>0;e=self.e[use].copy();e[:,j]-=1
            derivative=np.prod(A[:,None,:]**e[None,:,:],axis=2)*self.scale[use]*self.e[use,j]
            grad[:,j]=np.sum(D[:,use]*derivative,axis=1)
        return cost,grad,float(eig[0])

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,default=4);ap.add_argument('--starts',type=int,default=6)
    ap.add_argument('--rounds',type=int,default=4);ap.add_argument('--seed',type=int,default=21386);ap.add_argument('--out',required=True)
    args=ap.parse_args();out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
    rng=np.random.default_rng(args.seed);fe=PeriodicFE(8,2);sos=SOS(degree=args.degree,eps=1e-7);features=Features(args.degree)
    mu=0.0005
    def objective(x,p):
        A,s=fe.normalized(x);val,d=sos.fgrad(A,p);b,bd,_=features.cost_grad(A);d+=mu*bd
        gradA=(d-A*np.mean(np.sum(d*A,axis=1)))/(s*len(A))
        return val.mean()+mu*b,fe.back(gradA)
    xx=rng.normal(size=128);p=rng.normal(size=len(sos.e));direction=rng.normal(size=128);direction/=np.linalg.norm(direction)
    eps=1e-5;v,g=objective(xx,p)
    fd=(objective(xx+eps*direction,p)[0]-objective(xx-eps*direction,p)[0])/(2*eps)
    err=abs(fd-g@direction)/(1+abs(fd));assert err<1e-7,err
    print(json.dumps(dict(check='augmented feature barrier gradient',error=err)),flush=True)
    best=float('inf');rows=[]
    for seed in range(args.starts):
        x=rng.normal(size=128)
        for r in range(args.rounds):
            A,_=fe.normalized(x);p,Q,meta=sos.solve(A)
            opt=minimize(lambda x:objective(x,p),x,jac=True,method='L-BFGS-B',
                         options=dict(maxiter=220,ftol=1e-13,gtol=1e-9,maxls=40))
            x=opt.x;A,_=fe.normalized(x);gap=float(sos.moments(A)@p);_,_,cov_min=features.cost_grad(A)
            row=dict(seed=seed,round=r,optimized_gap=gap,feature_covariance_min_eig=cov_min,
                     mean_det_squared=float(np.mean((A[:,0]*A[:,3]-A[:,1]*A[:,2])**2)),
                     field_iterations=opt.nit,field_converged=bool(opt.success),**meta)
            rows.append(row);print(json.dumps(row),flush=True)
            if gap<best:
                best=gap;np.savez(out/'best.npz',p=p,Q=Q,A=A,x=x,exponents=sos.e,zexponents=sos.z,k=8)
            (out/'results.json').write_text(json.dumps(rows,indent=2))
            if gap < -1e-7:
                print('NEGATIVE CANDIDATE REQUIRES EXACT CERTIFICATION',flush=True);return
    print(json.dumps(dict(best=best,steps=len(rows))),flush=True)

if __name__=='__main__':main()
