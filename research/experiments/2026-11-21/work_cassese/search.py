"""Cassese planar pullback search, exact (bandlimited) quadrature and base elimination.
Not a proof unless a negative candidate is independently certified.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import numpy as np
from scipy.optimize import minimize
from scipy.spatial.transform import Rotation
from pathlib import Path
import json, sys
ROOT=Path(__file__).parent

def quadcross(a,b,c,d):
    return (np.outer(a,d)+np.outer(d,a)-np.outer(b,c)-np.outer(c,b))/2

def setup(delta):
    e=np.eye(6)
    a,b,c,d,ee,f=e
    x0=(a-c-ee)/2;x1=(b+d+f)/2
    y0=d-f;y1=ee;u0=b;u1=-a-c
    z0=(a-c+ee)/2;z1=(b-d-f)/2
    ss=[quadcross(y0,y1,u0,u1),quadcross(x0,x1,u0,u1),quadcross(x0,x1,y0,y1)]
    lam=22/delta
    R=2*(np.outer(x0,x0)+np.outer(x1,x1)) +sum(np.outer(v,v) for v in [y0,y1,u0,u1])+2*lam**2*(np.outer(z0,z0)+np.outer(z1,z1))
    ev,U=np.linalg.eigh(R)
    Ri=(U*(1/np.sqrt(ev)))@U.T
    Rh=(U*np.sqrt(ev))@U.T
    S=np.stack([Ri@s@Ri/np.sqrt(delta) for s in ss]+[np.eye(6)])
    K=np.diag([1.,0.,0.,1.]);K[1,2]=K[2,1]=-2
    return S,K,Rh,Ri

class Search:
 def __init__(self,delta,modes,grid=16):
    self.delta=delta;self.S,self.K,self.Rh,self.Ri=setup(delta)
    self.modes=np.asarray(modes,float)
    xy=np.array(np.meshgrid(np.arange(grid)*2*np.pi/grid,np.arange(grid)*2*np.pi/grid,indexing='ij')).reshape(2,-1).T
    ph=xy@self.modes.T
    self.trig=np.stack([np.cos(ph),np.sin(ph)],axis=2)
    self.n=len(xy);self.k=len(modes)
 def diff(self,w):
    sw=np.einsum('iab,nb->nia',self.S,w,optimize=True)
    r=np.einsum('na,nia->ni',w,sw)
    kr=r@self.K
    val=np.einsum('ni,ni->n',r,kr)
    grad=4*np.einsum('ni,nia->na',kr,sw)
    hess=8*np.einsum('nia,ij,njb->nab',sw,self.K,sw,optimize=True)+4*np.einsum('ni,iab->nab',kr,self.S)
    return val,grad,hess
 def embed(self,rot):
    B=Rotation.from_rotvec(rot).as_matrix()[:2,:]
    ns=self.modes@B
    mats=[]
    for n in ns:
      T=np.zeros((6,2));T[:3,0]=n;T[3:,1]=n
      V=self.Rh@T
      ev,U=np.linalg.eigh(V.T@V)
      inv=(U*(1/np.sqrt(ev)))@U.T
      mats.append(V@inv)
    return np.stack(mats),B
 def value(self,x,gradient=True,rotdiff=True,report=False):
    rot=x[:3];coef=x[3:].reshape(self.k,2,2)
    norm=np.linalg.norm(coef);coef=coef*np.sqrt(2)/norm
    E,B=self.embed(rot)
    w=np.einsum('nkp,kjp,kaj->na',self.trig,coef,E,optimize=True)
    val,grad,hess=self.diff(w)
    c=val.mean();l=grad.mean(0);Q=.5*hess.mean(0)
    ev,U=np.linalg.eigh(Q)
    if ev.min() < -1e-7*max(1,ev.max()):
      raise ValueError(('bad Q',ev))
    cutoff=1e-11*max(1,ev.max());il=U.T@l
    mi=-.5*np.where(ev>cutoff,il/np.maximum(ev,cutoff),0)
    m=U@mi
    gap=c+.5*l@m
    if report:
      physical_m=self.Ri@m;physical_w=w@self.Ri.T
      variance=np.mean(np.sum(physical_w**2,axis=1))
      return dict(delta=self.delta,gap_scaled=float(gap),gap_original=float(gap*self.delta),gradient_variance=float(variance),gap_unit_physical_variance=float(gap*self.delta/variance**2),base=physical_m.tolist(),B=B.tolist(),normalized_coefficients=coef.tolist(),rotation=rot.tolist(),Q_eigenvalues=ev.tolist(),linear_kernel_residual=float(np.linalg.norm(il[ev<=cutoff])),c=float(c),base_correction=float(.5*l@m),actual_min_norm=float(np.linalg.norm(w)),modes=self.modes.tolist(),x=x.tolist())
    if not gradient:return gap
    gp=self.diff(w+m)[1]-self.diff(m[None,:])[1]
    gc=np.einsum('na,kaj,nkp->kjp',gp,E,self.trig,optimize=True)/self.n
    gc=(gc-coef*np.sum(gc*coef)/2)*np.sqrt(2)/norm
    gr=np.zeros(3)
    if rotdiff:
      for i in range(3):
        h=1e-5;xx=x.copy();xx[i]+=h;v1=self.value(xx,gradient=False)
        xx[i]-=2*h;v0=self.value(xx,gradient=False);gr[i]=(v1-v0)/(2*h)
    return gap,np.r_[gr,gc.ravel()]

if __name__=='__main__':
    delta=float(sys.argv[1]) if len(sys.argv)>1 else .05
    runs=int(sys.argv[2]) if len(sys.argv)>2 else 8
    modes=[(1,0),(0,1),(1,1),(1,-1),(2,1),(1,2),(2,-1),(1,-2)]
    se=Search(delta,modes)
    rng=np.random.default_rng(20261121+int(delta*1000))
    allres=[]
    x=np.r_[rng.normal(size=3),rng.normal(size=4*len(modes))]
    v,g=se.value(x)
    fd=[]
    for i in rng.choice(len(x),8,replace=False):
      h=1e-5;xx=x.copy();xx[i]+=h;vp=se.value(xx,gradient=False);xx[i]-=2*h;vm=se.value(xx,gradient=False)
      fd.append(abs(g[i]-(vp-vm)/(2*h))/max(1,abs(g[i])))
    print('gradient max relative error',max(fd),flush=True)
    for trial in range(runs):
      x=np.r_[rng.normal(size=3),rng.normal(size=4*len(modes))]
      if trial%2==0:
        # plane n2=0 with two characteristic lines on coordinate axes
        B=np.array([[1,0,1],[-1,0,1],[0,-np.sqrt(2),0]])/np.sqrt(2)
        x[:3]=Rotation.from_matrix(B).as_rotvec()
      r=minimize(se.value,x,jac=True,method='L-BFGS-B',options=dict(maxiter=400,gtol=1e-9,ftol=1e-12,maxls=40))
      rep=se.value(r.x,report=True);rep['iterations']=r.nit;rep['success']=bool(r.success);rep['message']=str(r.message)
      allres.append(rep)
      print(trial,'gap',rep['gap_scaled'],'physical unit',rep['gap_unit_physical_variance'],'nit',r.nit,'var',rep['gradient_variance'],'grad',np.linalg.norm(r.jac),flush=True)
      (ROOT/f'results_delta_{delta:g}.json').write_text(json.dumps(dict(gradient_relative_error=max(fd),runs=allres),indent=2))
