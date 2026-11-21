"""Exact rational verification of the KNOWN 3x2 control, not a 2x2 result.

Build: python certify_control.py --build
Verify: python certify_control.py
Verification uses only Python's standard library, exact integers and fractions.
"""
from fractions import Fraction as F
from pathlib import Path
from collections import defaultdict
import json, itertools, argparse

HERE=Path(__file__).resolve().parent
CERT=HERE/'control_run'/'exact_control_certificate.json'

def exp(n,d):
    if n==1:yield(d,)
    else:
        for k in range(d+1):
            for e in exp(n-1,d-k):yield(k,)+e

def zexps(m,n,degree):
    N=m*n;out=[]
    for d in range(degree//2):
        for e in exp(N,d):
            for i in range(m):
                for j in range(n):
                    a=list(e)+[0]*(m+n);a[N+i]=a[N+m+j]=1;out.append(tuple(a))
    return out

def lhs(p,e,m,n):
    N=m*n;result=defaultdict(int)
    for coeff,aa in zip(p,e):
        if not coeff:continue
        for i in range(N):
            for j in range(N):
                c=coeff*aa[i]*(aa[j]-(i==j))
                if not c:continue
                a=list(aa)+[0]*(m+n);a[i]-=1;a[j]-=1
                a[N+i//n]+=1;a[N+j//n]+=1;a[N+m+i%n]+=1;a[N+m+j%n]+=1
                result[tuple(a)]+=c
    return result

def rhs(Q,z):
    result=defaultdict(int)
    for i,a in enumerate(z):
        for j in range(i,len(z)):
            key=tuple(x+y for x,y in zip(a,z[j]))
            result[key]+=(1 if i==j else 2)*Q[i][j]
    return result

def exact_pd(Q):
    n=len(Q);L=[[F(int(i==j)) for j in range(n)] for i in range(n)];d=[]
    for j in range(n):
        t=F(Q[j][j])-sum(L[j][k]**2*d[k] for k in range(j))
        if t<=0:raise AssertionError(('not positive definite at pivot',j))
        d.append(t)
        for i in range(j+1,n):L[i][j]=(Q[i][j]-sum(L[i][k]*L[j][k]*d[k] for k in range(j)))/t
    return min(d)

def control_moment(e):
    # Dw=(cos x,0;0,cos y;cos(x+y),cos(x+y)).
    if e[1] or e[2]:return F(0)
    factors=[(1,0)]*e[0]+[(0,1)]*e[3]+[(1,1)]*(e[4]+e[5])
    count=0
    for signs in itertools.product((-1,1),repeat=len(factors)):
        if all(sum(s*k[j] for s,k in zip(signs,factors))==0 for j in (0,1)):count+=1
    return F(count,2**len(factors))

def build():
    import numpy as np
    a=np.load(HERE/'control_run'/'control.npz');den=10**12;m,n,degree=3,2,4
    e=a['exponents'].tolist();p=(np.rint(a['p']*den).astype(np.int64)*2).tolist()
    Q=(np.rint(a['Q']*den).astype(np.int64)*2).tolist();z=zexps(m,n,degree)
    for i in range(len(Q)):
        for j in range(i):Q[i][j]=Q[j][i]
    want=lhs(p,e,m,n);have=rhs(Q,z);chosen={}
    # Every Gram entry contributes to just one monomial, allowing exact repairs.
    for i,a in enumerate(z):
        for j in range(i,len(z)):
            key=tuple(x+y for x,y in zip(a,z[j]));chosen.setdefault(key,(i,j))
    for key in set(want)|set(have):
        delta=want[key]-have[key]
        if not delta:continue
        i,j=chosen[key]
        if i!=j:
            assert delta%2==0;delta//=2
        Q[i][j]+=delta;Q[j][i]=Q[i][j]
    cert=dict(title='Known 3x2 negative control; NOT a 2x2 counterexample',m=m,n=n,degree=degree,
              denominator=2*den,exponents=e,polynomial_numerators=p,gram_numerators=Q,
              field='w(x,y)=(sin(x),sin(y),sin(x+y)) on the 2pi-periodic torus')
    CERT.write_text(json.dumps(cert,separators=(',',':')))

def verify():
    c=json.loads(CERT.read_text());m,n,degree=c['m'],c['n'],c['degree'];assert(m,n,degree)==(3,2,4)
    p,e,Q=c['polynomial_numerators'],c['exponents'],c['gram_numerators'];den=c['denominator']
    z=zexps(m,n,degree);left=lhs(p,e,m,n);right=rhs(Q,z)
    assert all(left[k]==right[k] for k in set(left)|set(right))
    assert all(Q[i][j]==Q[j][i] for i in range(len(Q)) for j in range(len(Q)))
    pivot=exact_pd(Q)/den
    gap=sum((F(v,den)*control_moment(a) for v,a in zip(p,e)),F(0))
    assert gap<0
    result=dict(dimension='3x2',exact_polynomial_identity=True,exact_positive_gram=True,
                gram_size=len(Q),gap=str(gap),gap_float=float(gap),min_LDL_pivot_float=float(pivot),
                status='Known higher-dimensional mechanism validated; no 2x2 conclusion.')
    (HERE/'control_run'/'exact_verification.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--build',action='store_true');args=ap.parse_args()
    if args.build:build()
    verify()
