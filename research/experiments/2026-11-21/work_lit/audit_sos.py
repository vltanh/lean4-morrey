"""Independent physical-direction and normalized-FE checks for ../work_sos."""
import sys,json,random,math
from fractions import Fraction as F
from pathlib import Path
import numpy as np

ROOT=Path(__file__).resolve().parents[1]/'work_sos'
sys.path.insert(0,str(ROOT))
from sos_search import SOS,PeriodicFE

def main():
 c=json.loads((ROOT/'control_run/exact_control_certificate.json').read_text())
 assert(c['m'],c['n'],c['degree'])==(3,2,4)
 p,exps,Q=c['polynomial_numerators'],c['exponents'],c['gram_numerators']
 def ev(x):
  return sum(v*math.prod(xx**e for xx,e in zip(x,a)) for v,a in zip(p,exps))
 rng=random.Random(7517)
 for trial in range(30):
  A=[rng.randrange(-3,4) for _ in range(6)]
  u=[rng.randrange(-2,3) for _ in range(3)];v=[rng.randrange(-2,3) for _ in range(2)]
  H=[x*y for x in u for y in v]
  vals={t:ev([a+t*h for a,h in zip(A,H)]) for t in [-2,-1,0,1,2]}
  # Exact second derivative for degree-four polynomial in t, unlike lhs() loop.
  LH=F(-vals[2]+16*vals[1]-30*vals[0]+16*vals[-1]-vals[-2],12)
  z=[s*x*y for s in [1]+A[::-1] for x in u for y in v]
  rhs=sum(z[i]*Q[i][j]*z[j] for i in range(42) for j in range(42))
  assert LH==rhs
 r=np.random.default_rng(1842);fe=PeriodicFE(4,2);x=r.normal(size=32)
 A,s=fe.normalized(x)
 assert np.linalg.norm(A.mean(0))<1e-14
 assert abs(np.linalg.det(A.reshape(-1,2,2)).mean())<1e-14
 assert abs(np.mean(np.sum(A*A,1))-1)<1e-14
 sos=SOS(degree=6);p=r.normal(size=len(sos.e))
 errors={}
 for bar in [1e-4,.01]:
  val,g=fe.obj(x,sos,p,bar);es=[]
  for _ in range(8):
   v=r.normal(size=len(x));v/=np.linalg.norm(v);h=1e-5
   fd=(fe.obj(x+h*v,sos,p,bar)[0]-fe.obj(x-h*v,sos,p,bar)[0])/(2*h)
   es.append(abs(fd-g@v)/(1+abs(fd)))
  assert max(es)<1e-8
  errors[str(bar)]=max(es)
 result={'exact_directional_control_checks':30,'control_dimension':'3x2',
          'fe_mean_gradient_and_det_zero':True,'fe_variance_one':True,
          'degree_six_barrier_gradient_errors':errors}
 print(json.dumps(result,indent=2))
 Path(__file__).with_name('sos_audit_results.json').write_text(json.dumps(result,indent=2))

if __name__=='__main__':main()
