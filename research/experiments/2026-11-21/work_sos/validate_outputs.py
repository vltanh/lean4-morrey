"""Audit stored floating candidates, with explicit monomial-order metadata."""
from pathlib import Path
import json
import numpy as np
from certify_control import lhs,rhs,zexps

root=Path(__file__).resolve().parent
rows=[]
for filename in sorted(root.glob('*/best.npz')):
    old=np.load(filename);d={k:old[k] for k in old.files}
    degree=int(d['exponents'].sum(axis=1).max());m=n=2
    if 'zexponents' not in d:
        if filename.parent.name=='search4':
            # This first run preceded the generalized polynomial-order routine.
            z=[]
            for k in range(5):
                for i in range(2):
                    for j in range(2):
                        t=[0]*8
                        if k:t[k-1]=1
                        t[4+i]=1;t[6+j]=1;z.append(t)
        else:z=zexps(m,n,degree)
        d['zexponents']=np.array(z,int);np.savez(filename,**d)
    p,Q,A,e,z=d['p'],d['Q'],d['A'],d['exponents'],d['zexponents']
    L=lhs(p,e,m,n);R=rhs(Q,z)
    error=max(abs(L[k]-R[k]) for k in set(L)|set(R))
    gap=float(np.mean(np.prod(A[:,None,:]**e[None,:,:],axis=2)@p))
    row=dict(file=str(filename.relative_to(root)),degree=degree,actual_gap=gap,
             coefficient_residual=float(error),gram_min_eig=float(np.linalg.eigvalsh(Q)[0]),
             mean_gradient_max=float(np.abs(A.mean(axis=0)).max()),
             mean_determinant=float(np.mean(A[:,0]*A[:,3]-A[:,1]*A[:,2])),
             gradient_variance=float(np.mean(np.sum(A*A,axis=1))))
    assert error<1e-5,('wrong metadata or unacceptable candidate',row)
    assert row['mean_gradient_max']<1e-9
    assert abs(row['mean_determinant'])<1e-9
    rows.append(row)
(root/'floating_output_audit.json').write_text(json.dumps(rows,indent=2))
print(json.dumps(rows,indent=2))
