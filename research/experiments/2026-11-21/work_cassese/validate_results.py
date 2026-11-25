"""Independent original-formula quadrature checks of saved searches."""
import numpy as np,json,hashlib
from pathlib import Path
from search import setup
ROOT=Path(__file__).parent

def coords(m):
 a,b,c,d,e,f=m.T
 return np.stack([(a-c-e)/2,(b+d+f)/2,d-f,e,b,-a-c,(a-c+e)/2,(b-d-f)/2],axis=-1)

def qforms(m,delta):
 x0,x1,y0,y1,u0,u1,z0,z1=coords(m).T
 return np.stack([y0*u1-y1*u0,x0*u1-x1*u0,x0*y1-x1*y0,2*(x0*x0+x1*x1)+y0*y0+y1*y1+u0*u0+u1*u1+2*(22/delta)**2*(z0*z0+z1*z1)],axis=-1)

def original_gap(rec,grid=27):
 delta=rec['delta'];B=np.array(rec['B']);coef=np.array(rec['normalized_coefficients']);modes=np.array(rec['modes']);m=np.array(rec['base'])
 _,_,Rh,_=setup(delta)
 xy=np.array(np.meshgrid(np.arange(grid)*2*np.pi/grid,np.arange(grid)*2*np.pi/grid,indexing='ij')).reshape(2,-1).T
 ph=xy@modes.T;tr=np.stack([np.cos(ph),np.sin(ph)],axis=-1)
 maps=[]
 for n in modes@B:
  T=np.zeros((6,2));T[:3,0]=n;T[3:,1]=n
  V=Rh@T;ev,U=np.linalg.eigh(V.T@V);maps.append(T@((U*(1/np.sqrt(ev)))@U.T))
 g=np.einsum('nkp,kjp,kaj->na',tr,coef,np.array(maps),optimize=True)
 rg=qforms(g,delta);rm=qforms(m[None,:],delta)[0]
 rl=qforms(g+m,delta)-rg-rm
 K=np.diag([1.,0.,0.,delta]);K[1,2]=K[2,1]=-2
 # Stable quartic polarization; mean linear term exactly vanishes analytically.
 gap=np.mean(2*(rg@K@rm)+np.einsum('ni,ij,nj->n',rl,K,rl)+2*np.einsum('ni,ij,nj->n',rl,K,rg)+np.einsum('ni,ij,nj->n',rg,K,rg))
 return float(gap),float(np.linalg.norm(g.mean(0))),float(np.mean(np.sum(g*g,axis=1)))

files=['results_delta_0.1.json','results_delta_0.01.json','fixed_planes_results.json','tangent_planes_results.json']
summary=[]
for name in files:
 obj=json.loads((ROOT/name).read_text());runs=obj['runs'] if isinstance(obj,dict) else obj
 errors=[];gaps=[];means=[]
 for r in runs:
  g,mean,var=original_gap(r)
  errors.append(abs(g-r['gap_original'])/max(1,abs(g)))
  gaps.append(g);means.append(mean)
 summary.append(dict(file=name,runs=len(runs),min_gap_scaled=min(r['gap_scaled'] for r in runs),min_direct_original_gap=min(gaps),max_abs_error=max(errors),max_mean_gradient=max(means),converged=sum(r['success'] for r in runs)))
print(json.dumps(summary,indent=2))
(ROOT/'validation_summary.json').write_text(json.dumps(summary,indent=2))
