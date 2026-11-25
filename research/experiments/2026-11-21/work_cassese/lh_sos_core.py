"""Numerical Morrey search with a global SOS Legendre--Hadamard ansatz.

This is a search program, not a proof. Negative candidates must be rationalized
and independently certified before they can be called counterexamples.

f has degree 2..4. For all A,a,b, impose exactly at the coefficient level
  D^2 f(A)[a tensor b,a tensor b] = z(A,a,b)^T Q z(A,a,b),
where z=(1,A_1,...,A_mn) tensor a tensor b and Q >= 0.
An exact identity and PSD Q imply global rank-one convexity. A floating SDP
solution supplies only a candidate for that exact identity.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import itertools, json, argparse, time
from pathlib import Path
import numpy as np
from scipy import sparse
from scipy.optimize import minimize
import cvxpy as cp

def exps(n,d):
    if n==1:
        yield (d,)
    else:
        for i in range(d+1):
            for tail in exps(n-1,d-i): yield (i,)+tail

class SOS:
    def __init__(self,m=2,n=2,eps=0,degree=4):
        self.m,self.n,self.N=m,n,m*n
        N=self.N
        assert degree in (4,6)
        self.e=np.array([e for d in range(2,degree+1) for e in exps(N,d)],int)
        self.lookup={tuple(e):i for i,e in enumerate(self.e)}
        zero=(0,)*(N+m+n)
        z=[]
        for aa in (e for d in range(degree//2) for e in exps(N,d)):
            for i in range(m):
                for j in range(n):
                    e=list(zero)
                    e[:N]=aa
                    e[N+i]=e[N+m+j]=1
                    z.append(tuple(e))
        self.z=np.array(z,int);self.nz=len(z)
        keys=sorted(set(tuple(a+b) for a in self.z for b in self.z))
        idx={e:i for i,e in enumerate(keys)}
        self.keys=keys
        ri=[];ci=[];data=[]
        for i,a in enumerate(self.z):
            for j,b in enumerate(self.z):
                ri.append(idx[tuple(a+b)]);ci.append(i+self.nz*j);data.append(1.)
        self.C=sparse.csc_matrix((data,(ri,ci)),shape=(len(keys),self.nz**2))
        D=np.zeros((len(keys),len(self.e)))
        for k,alpha in enumerate(self.e):
            for i in range(N):
                for j in range(N):
                    fac=alpha[i]*(alpha[j]-(i==j))
                    if not fac: continue
                    ee=np.r_[alpha.copy(),np.zeros(m+n,int)]
                    ee[i]-=1;ee[j]-=1
                    ee[N+i//n]+=1;ee[N+j//n]+=1
                    ee[N+m+i%n]+=1;ee[N+m+j%n]+=1
                    D[idx[tuple(ee)],k]+=fac
        self.D=sparse.csc_matrix(D)
        self.p=cp.Variable(len(self.e));self.Q=cp.Variable((self.nz,self.nz),symmetric=True)
        self.moment=cp.Parameter(len(self.e))
        cons=[self.C@cp.vec(self.Q,order='F')==self.D@self.p,
              self.Q >> eps*np.eye(self.nz),cp.trace(self.Q)==1]
        for i,j in itertools.combinations(range(m),2):
            for k,l in itertools.combinations(range(n),2):
                e1=np.zeros(N,int);e1[i*n+k]+=1;e1[j*n+l]+=1
                e2=np.zeros(N,int);e2[i*n+l]+=1;e2[j*n+k]+=1
                cons.append(self.p[self.lookup[tuple(e1)]]==self.p[self.lookup[tuple(e2)]])
        self.prob=cp.Problem(cp.Minimize(self.moment@self.p),cons)
        self.eps=eps

    def values(self,A):
        return np.prod(A[:,None,:]**self.e[None,:,:],axis=2)

    def fgrad(self,A,p):
        val=self.values(A)@p
        out=np.zeros_like(A)
        for j in range(self.N):
            use=self.e[:,j]>0
            ej=self.e[use].copy();ej[:,j]-=1
            out[:,j]=np.prod(A[:,None,:]**ej[None,:,:],axis=2)@(p[use]*self.e[use,j])
        return val,out

    def moments(self,A):return self.values(A).mean(axis=0)

    def solve(self,A):
        self.moment.value=self.moments(A)
        self.prob.solve(solver='CLARABEL',tol_gap_abs=2e-10,tol_feas=2e-10,
                        tol_gap_rel=2e-9,max_iter=200,verbose=False)
        if self.p.value is None:raise RuntimeError(self.prob.status)
        p=self.p.value.copy();Q=self.Q.value.copy()
        resid=float(np.max(np.abs(self.C@Q.ravel(order='F')-self.D@p)))
        eig=float(np.linalg.eigvalsh(Q)[0])
        return p,Q,dict(gap=float(self.moment.value@p),status=self.prob.status,
                        gram_min_eig=eig,coefficient_residual=resid)

    def sanity(self):
        rng=np.random.default_rng(1729)
        p=rng.normal(size=len(self.e));A=rng.normal(size=self.N)
        a=rng.normal(size=self.m);b=rng.normal(size=self.n);H=np.outer(a,b).ravel()
        e=np.r_[A,a,b]
        expected=sum(c*np.prod(e**key) for c,key in zip(self.D@p,self.keys))
        eps=2e-4
        f=lambda t:float((self.values((A+t*H)[None,:])@p)[0])
        actual=(f(eps)-2*f(0)+f(-eps))/eps**2
        assert abs(expected-actual)<2e-4*(1+abs(expected)),(expected,actual)
        print(json.dumps(dict(check='LH coefficient map',relative_error=abs(expected-actual)/(1+abs(expected)))),flush=True)

class PeriodicFE:
    def __init__(self,k=4,m=2):
        self.k,self.m=k,m
        G=np.zeros((2*k*k,2,k*k))
        def at(a,b):return (a%k)*k+b%k
        for a in range(k):
            for b in range(k):
                t=2*(a*k+b)
                G[t,0,at(a+1,b)]=k;G[t,0,at(a,b)]=-k
                G[t,1,at(a,b+1)]=k;G[t,1,at(a,b)]=-k
                G[t+1,0,at(a+1,b+1)]=k;G[t+1,0,at(a,b+1)]=-k
                G[t+1,1,at(a+1,b+1)]=k;G[t+1,1,at(a+1,b)]=-k
        self.G=G
    def raw(self,x):return np.einsum('tjn,in->tij',self.G,x.reshape(self.m,-1)).reshape(-1,2*self.m)
    def normalized(self,x):
        A=self.raw(x);s=np.sqrt(np.mean(np.sum(A*A,axis=1)))
        if s<1e-12: raise ValueError('zero field')
        return A/s,s
    def back(self,d):return np.einsum('tjn,tij->in',self.G,d.reshape(-1,self.m,2)).ravel()
    def obj(self,x,sos,p,barrier=0):
        A,s=self.normalized(x)
        val,d=sos.fgrad(A,p)
        cost=val.mean()
        if barrier:
            cov=A.T@A/len(A)
            sign,ldet=np.linalg.slogdet(4*cov)
            if sign<=0: raise ValueError('singular gradient covariance')
            cost-=barrier*ldet
            d-=2*barrier*(A@np.linalg.inv(cov))
        gradA=(d-A*np.mean(np.sum(d*A,axis=1)))/(s*len(A))
        return cost,self.back(gradA)

def check_gradient(fe,sos,x):
    rng=np.random.default_rng(42);p=rng.normal(size=len(sos.e));v=rng.normal(size=x.size);v/=np.linalg.norm(v)
    val,g=fe.obj(x,sos,p);eps=1e-5
    numeric=(fe.obj(x+eps*v,sos,p)[0]-fe.obj(x-eps*v,sos,p)[0])/(2*eps)
    err=abs(numeric-g@v)/(1+abs(numeric))
    assert err<1e-7,err
    print(json.dumps(dict(check='periodic field gradient',relative_error=err)),flush=True)

