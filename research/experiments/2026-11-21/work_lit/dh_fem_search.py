"""Periodic piecewise-affine search for Dacorogna--Haeberly energies.

Real candidates use the published rank-one-convex parameter range.  Objective
quadrature is exact for piecewise-affine maps: it is a finite sum over triangles.
The integral values are floating point, not certified interval enclosures.
"""
import argparse, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize


N_STRONG = np.array([[8,0,0,2],[0,5,1,0],[0,1,5,0],[2,0,0,8]], dtype=float)/10
N_ORIGINAL = np.array([[10,0,0,1],[0,7,2,0],[0,2,7,0],[1,0,0,10]], dtype=float)/10

def energy(A, N):
    shape=A.shape
    X=A.reshape(-1,4)
    r=np.linalg.norm(X,axis=1)
    NX=X@N
    q=np.sum(X*NX,axis=1)
    nz=r>1e-14
    f=np.zeros(len(X)); df=np.zeros_like(X)
    f[nz]=q[nz]/r[nz]
    df[nz]=2*NX[nz]/r[nz,None]-q[nz,None]*X[nz]/r[nz,None]**3
    return f.reshape(shape[:-2]), df.reshape(shape)

def gradient(U):
    n=U.shape[0]
    X=np.roll(U,-1,axis=0); Y=np.roll(U,-1,axis=1)
    XY=np.roll(X,-1,axis=1)
    lo=np.stack((X-U,Y-U),axis=-1)*n
    hi=np.stack((XY-Y,XY-X),axis=-1)*n
    return np.stack((lo,hi),axis=0)

def adjoint(V):
    n=V.shape[1]
    lx,ly=V[0,...,0],V[0,...,1]
    hx,hy=V[1,...,0],V[1,...,1]
    return (np.roll(lx,1,axis=0)-lx+np.roll(ly,1,axis=1)-ly
            +np.roll(np.roll(hx+hy,1,axis=0),1,axis=1)
            -np.roll(hx,1,axis=1)-np.roll(hy,1,axis=0))/(2*n)

def objective(z,n,N):
    U=z[:-4].reshape(n,n,2)
    F=z[-4:].reshape(2,2)
    G0=gradient(U)
    scale=np.sqrt(np.mean(np.sum(G0*G0,axis=(-2,-1))))
    if scale<1e-14:
        return 1e10,np.zeros_like(z)
    G=G0/scale
    vals,der=energy(F+G,N)
    f0,df0=energy(F,N)
    val=float(vals.mean()-f0)
    radial=np.mean(np.sum(der*G,axis=(-2,-1)))
    dU=adjoint(der-radial*G)/scale
    dF=der.mean(axis=(0,1,2))-df0
    return val,np.r_[dU.ravel(),dF.ravel()]

def checks():
    rng=np.random.default_rng(9371); n=4
    z=rng.normal(size=2*n*n+4)
    f,g=objective(z,n,N_STRONG)
    errs=[]
    for j in rng.choice(len(z),size=20,replace=False):
        h=1e-5
        zz=z.copy();zz[j]+=h
        zr=z.copy();zr[j]-=h
        fd=(objective(zz,n,N_STRONG)[0]-objective(zr,n,N_STRONG)[0])/(2*h)
        errs.append(abs(fd-g[j]))
    U=z[:-4].reshape(n,n,2); G=gradient(U)
    detmean=np.linalg.det(G).mean()
    # Exact one-wave control: increasing the largest eigenvalue destroys RC.
    U=np.zeros((n,n,2)); U[:,:,0]=np.array([0,.25,.5,.25])[None,:]
    zz=np.r_[U.ravel(),[3,0,0,3]]
    Nbad=N_STRONG.copy();Nbad[np.ix_([0,3],[0,3])]+=.025
    good=objective(zz,n,N_STRONG)[0]; bad=objective(zz,n,Nbad)[0]
    ans=dict(gradient_max_error=max(errs),gradient_mean=G.mean(axis=(0,1,2)).tolist(),
             determinant_mean=float(detmean),rank_one_wave_control_good=good,
             rank_one_wave_control_bad=bad)
    assert max(errs)<1e-7
    assert np.linalg.norm(G.mean(axis=(0,1,2)))<1e-13
    assert abs(detmean)<1e-12
    assert good>0 and bad<0
    return ans

def init(n,rng,i):
    # Smooth trigonometric initial fields, nodal degrees of freedom unrestricted.
    x=np.arange(n)/n
    X,Y=np.meshgrid(x,x,indexing='ij')
    U=np.zeros((n,n,2))
    for k,l in [(1,0),(0,1),(1,1),(1,-1),(2,1),(1,2)]:
        U+=np.sin(2*np.pi*(k*X+l*Y)+rng.uniform(0,2*np.pi))[...,None]*rng.normal(size=2)/(k*k+l*l)
    if i%4==0:
        F=np.eye(2)*[.3,.7,1.5,3][(i//4)%4]
    else:
        F=rng.normal(size=(2,2));F*=rng.uniform(.2,3)/np.linalg.norm(F)
    return np.r_[U.ravel(),F.ravel()]

def run(args):
    result={'method':'periodic affine triangles; unit gradient L2; L-BFGS-B',
            'checks':checks(),'runs':[], 'seed':args.seed}
    print(json.dumps(result['checks']),flush=True)
    out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
    rng=np.random.default_rng(args.seed)
    best=1e100
    for family,N in [('strong',N_STRONG),('original',N_ORIGINAL)]:
      for n in args.grids:
       for i in range(args.starts):
        z=init(n,rng,i)
        t=time.time()
        res=minimize(objective,z,args=(n,N),jac=True,method='L-BFGS-B',
                     bounds=[(None,None)]*(2*n*n)+[(-args.base_bound,args.base_bound)]*4,
                     options={'maxiter':args.maxiter,'ftol':1e-14,'gtol':1e-9,'maxls':40})
        U=res.x[:-4].reshape(n,n,2);G=gradient(U)
        scale=np.sqrt(np.mean(np.sum(G*G,axis=(-2,-1))));U/=scale
        F=res.x[-4:].reshape(2,2)
        row={'family':family,'n':n,'start':i,'gap':float(res.fun),'iters':int(res.nit),
             'success':bool(res.success),'message':res.message,'seconds':time.time()-t,
             'F':F.tolist(),'min_matrix_norm':float(np.min(np.linalg.norm(F+gradient(U),axis=(-2,-1)))),
             'gradient_variance':float(np.mean(np.sum(gradient(U)**2,axis=(-2,-1))))}
        result['runs'].append(row)
        if res.fun<best:
            best=float(res.fun)
            np.savez(out/'best.npz',U=U,F=F,N=N,gap=best)
        print(json.dumps(row),flush=True)
        (out/'results.json').write_text(json.dumps(result,indent=2))
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--seed',type=int,default=75391)
    p.add_argument('--grids',type=int,nargs='+',default=[4,8,16]);p.add_argument('--starts',type=int,default=8)
    p.add_argument('--maxiter',type=int,default=600);p.add_argument('--base-bound',type=float,default=4)
    p.add_argument('--output',default=str(Path(__file__).with_name('dh_results')))
    run(p.parse_args())
