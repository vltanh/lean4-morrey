"""Independent 60-digit audit of base-eliminated gaps, including ill-conditioned cases.
Uses explicit periodic gradients and high-precision direct energy, not floating
quadratic completion for the final gap. No proof over unsearched fields.
"""
import json
from pathlib import Path
import numpy as np
import mpmath as mp
mp.mp.dps=60
ROOT=Path(__file__).resolve().parent
G=mp.matrix([[0,0,0,mp.mpf('.5')],[0,0,-1,0],[0,-1,0,0],[mp.mpf('.5'),0,0,0]])
E=mp.diag([0,1,1,1]);basis_cache={}
def field(data,row):
 if 'nodal' in row:
  u=[[[mp.mpf(str(v)) for v in a] for a in l] for l in row['nodal']];n=len(u);xs=[]
  for i in range(n):
   for j in range(n):
    p=u[i][j];q=u[(i+1)%n][j];r=u[i][(j+1)%n];s=u[(i+1)%n][(j+1)%n]
    xs.append([n*(q[0]-p[0]),n*(r[0]-p[0]),n*(q[1]-p[1]),n*(r[1]-p[1])])
    xs.append([n*(s[0]-r[0]),n*(s[0]-q[0]),n*(s[1]-r[1]),n*(s[1]-q[1])])
  return xs
 modes=[tuple(map(int,k)) for k in data['modes']];key=tuple(modes);n=4*max(max(abs(k[0]),abs(k[1])) for k in modes)+1
 if key not in basis_cache:
  dirs=[(mp.mpf(i)/mp.sqrt(i*i+j*j),mp.mpf(j)/mp.sqrt(i*i+j*j)) for i,j in modes];dirs+=dirs
  basis=[]
  for x in range(n):
   for y in range(n):
    angles=[2*mp.pi*(x*i+y*j)/n for i,j in modes]
    b=[mp.cos(z) for z in angles]+[mp.sin(z) for z in angles]
    basis.append([(z*dx,z*dy) for z,(dx,dy) in zip(b,dirs)])
  basis_cache[key]=basis
 coeff=[[mp.mpf(str(v)) for v in a] for a in row['coefficients']]
 return [[sum(z[d]*c[o] for z,c in zip(b,coeff)) for o,d in [(0,0),(0,1),(1,0),(1,1)]] for b in basis_cache[key]]
def P(x):
 a,b,c,d=x;return (a*d-2*b*c)**2+2*(b*b+c*c+d*d)**2
def audit(data,row):
 xs=field(data,row);n=len(xs);K=mp.zeros(4);h=mp.zeros(4,1);c0=0;meandet=0;var=0
 for X in xs:
  a,b,c,d=X;g=a*d-2*b*c;r=b*b+c*c+d*d;v=mp.matrix([d,-2*c,-2*b,a]);y=mp.matrix([0,b,c,d])
  K+=v*v.T+2*g*G+2*(2*r*E+4*y*y.T)
  h+=v*g+4*y*r;c0+=g*g+2*r*r;meandet+=a*d-b*c;var+=r
 K/=n;h/=n;c0/=n;meandet/=n;var/=n
 F=-mp.lu_solve(K,h);gap=c0+(h.T*F)[0]
 direct=sum(P([x[k]+F[k] for k in range(4)]) for x in xs)/n-P(list(F))
 return {'high_precision_gap':mp.nstr(gap,30),'direct_gap':mp.nstr(direct,30),'gap_discrepancy':mp.nstr(abs(direct-gap),8),'mean_det':mp.nstr(meandet,8),'transverse_variance':mp.nstr(var,30),'high_precision_base':[mp.nstr(v,25) for v in F]}
results=[]
for filename in ['six_transverse_results.json','k3_transverse_results.json','fem8_results.json','targeted_results.json']:
 data=json.loads((ROOT/filename).read_text());rows=data['results']
 selected=set([min(range(len(rows)),key=lambda i:rows[i]['gap'])])
 for i,r in enumerate(rows):
  ev=r['eigenvalues']
  if min(ev)/max(ev)<1e-10:selected.add(i)
 for i in sorted(selected):
  row=rows[i];v=audit(data,row);v.update(source=filename,index=i,double_gap=row['gap'],condition_indicator=min(row['eigenvalues'])/max(row['eigenvalues']))
  results.append(v);print(filename,i,'double',row['gap'],'mp',v['high_precision_gap'],'direct_error',v['gap_discrepancy'],flush=True)
(ROOT/'high_precision_audit.json').write_text(json.dumps({'digits':60,'results':results,'note':'Independent high precision numerical evaluations, not a theorem.'},indent=2))
