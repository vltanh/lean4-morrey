#!/usr/bin/env python3
"""Exact rational controls for common-energy false critical laws and adaptive L.
Not an actual gradient law or a proof of Morrey.
"""
from fractions import Fraction as Q
from itertools import product
from math import prod

K=1026
L=10000
C=40002
sigma=Q(1,4)
m=Q(1,2048)
Mh=4*10**10

# Base trap: diagonal matrices, determinant relation det=trace.
atoms=[(-Q(1),Q(1,2)),(Q(1,2),-Q(1)),(Q(2),Q(2))]
w=[Q(4,9),Q(4,9),Q(1,9)]
def avg(vals, weights=w): return sum((p*v for p,v in zip(weights,vals)),Q(0))
assert sum(w)==1 and avg(x for x,y in atoms)==avg(y for x,y in atoms)==0
assert avg(x*y for x,y in atoms)==0
assert avg(x*x for x,y in atoms)==avg(y*y for x,y in atoms)==1
assert avg((x*x+y*y)**2 for x,y in atoms)==Q(17,2)

# Piecewise polynomial common constitutive energy H.
def huber(s):
    return s*s if abs(s)<=1 else 2*abs(s)-1

def smax(a,b):
    d=a-b
    if abs(d)>=sigma: return max(a,b)
    return (a+b+(d*d+sigma*sigma)/(2*sigma))/2

def branches(x,u,v,y):
    q=(x*x+u*u+v*v+y*y)/2
    B=u*u+v*v
    s=x*y-u*v-x-y
    z=huber(s)
    return z+B,q+K*z-5,q+K*B-5,L*q-C

def energy(x,u,v,y):
    h0,h1,h2,h3=branches(x,u,v,y)
    return smax(smax(smax(h0,h1),h2),h3)
for x,y in [(Q(0),Q(0))]+atoms:
    h0,h1,h2,h3=branches(x,0,0,y)
    assert h0==0 and h1<=-1 and h2<=-1 and h3<=-2
    assert energy(x,0,0,y)==0
# If h0 participates in the final smooth maximum, then all h_i<=h0+1.
# The sum of inequalities for h1 and h2 gives the stated active bound.
assert 13*sigma/4<1  # three stages: sigma + two costs 5*sigma/4 = 3.5*sigma <1
assert 7*sigma/2<1
assert Q(12,K-2)<Q(1,64)
assert (C+1+Q(1,64))/L<5
# In active region |X|<4; |s|<=1/8, B<=1/64.
assert 1-Q(1,8)-Q(1,128)>Q(3,4)
assert Q(3,4)/5>Q(1,8)
t=Q(1,64)
assert 1-Q(3,2)*t*t>Q(1,4)
assert Q(1,16)-5*t*t-Q(1,8)*t>Q(1,32)
assert 2*t*t==m
assert 2*Q(1,32)**2>=m
# Outside |X|>=4 the quadratic tail dominates every other branch.
# phi(s)<=2|s|<=2Q+3|X|, B<=2Q.
r=Q(4)
assert (L-(1+2*K))*r*r/2-3*K*r-C+5>1
assert (L-(1+2*K))*r-3*K>0
assert (L-4)*r*r/2-3*r-C>1
assert (L-4)*r-3>0
# Full Hessian bound on B4 from |Ds|<=6, |phi'|<=2, |phi''|<=2.
Hbounds=[74+2,1+K*74,1+2*K,L]
Dbounds=[2*6+8,4+K*12,4+K*8,4*L]
assert max(Dbounds)<=40000
assert max(Hbounds)+3*2*(80000**2)<Mh
print('Exact common-energy construction: trap moments, contact, active curvature, tail and global Hessian budgets passed.')

# Exact detector of the unscaled trap: K_r(Z-rI), Z=I-X, r=4.
# K_r=(s-r)_+*(r-delta), delta=det/s. Base Z=I.
def trunc_K(x,y,r):
    s=max(abs(x),abs(y))
    if s<=r: return Q(0)
    return (s-r)*(r-x*y/s)
rr=Q(4)
assert trunc_K(1-rr,1-rr,rr)==0
assert [trunc_K(1-x-rr,1-y-rr,rr) for x,y in atoms]==[0,0,-1]
assert avg(trunc_K(1-x-rr,1-y-rr,rr) for x,y in atoms)==-Q(1,9)

# After anisotropic degeneration, large amplitude and dilution to E=1,
# covariance whitening followed by fourth-moment scale extraction
# exactly restores the base trap up to signed permutations of eigenvectors.
# For a generic gradient, the same scale statistic defines a valid
# adaptive QC test (not an assertion that it is universally separating).
count=0
for delta,r in product([Q(1,2),Q(1,10),Q(1,100),Q(1,10000)], [Q(1),Q(3),Q(12)]):
    weight=1/(r*r*(1+delta*delta))
    assert 0<weight<=1
    wd=[weight*p for p in w]+[1-weight]
    X=[(r*x,r*delta*y) for x,y in atoms]+[(Q(0),Q(0))]
    assert avg((x*x+y*y for x,y in X),wd)==1
    covx=avg((x*x for x,y in X),wd)
    covy=avg((y*y for x,y in X),wd)
    assert covx==weight*r*r and covy==weight*r*r*delta*delta
    assert covy/covx==delta*delta
    # Undo covariance anisotropy first, then recover r via fourth moments.
    Z=[(x,y/delta) for x,y in X]
    e2=avg((x*x+y*y for x,y in Z),wd)
    e4=avg(((x*x+y*y)**2 for x,y in Z),wd)
    assert e4/e2==Q(17,4)*r*r
    r2=Q(4,17)*e4/e2
    assert r2==r*r
    Y=[(x/r,y/r) for x,y in Z]
    assert Y==atoms+[(Q(0),Q(0))]
    gap=avg((trunc_K(1-x-rr,1-y-rr,rr) for x,y in Y),wd)
    assert gap==-weight/9<0
    # f_delta=(h after inverse transform - kappa Q)/M; normalized
    # b=kappa/(2M), critical stabilized H and DH vanish on support.
    kappa=m/(2*r*r)
    Mf=Q(Mh+1)/(r*r*delta*delta)
    b=kappa/(2*Mf)
    assert 0<b<Q(1,8)
    assert b==m*delta*delta/(4*(Mh+1))
    assert (Q(Mh)/(r*r*delta*delta)+kappa)<=Mf
    gapf=avg((-b*(x*x+y*y) for x,y in X),wd)
    assert gapf==-b
    count+=1
print(count,'exact anisotropy/dilution, normalized defect and adaptive-detector controls passed.')
print('No actual gradient realization, unrestricted proof, or finite infeasibility certificate claimed.')

# The one-scale covariance detector is not a universal trap detector.
# Larger contrast a=5 still gives a valid minor-compatible hyperbola law.
a=Q(5); y=a/(1+a); p=2/(a-y+4); p3=1-2*p
atoms2=[(-a,y),(y,-a),(Q(2),Q(2))]; w2=[p,p,p3]
assert avg((x for x,y in atoms2),w2)==avg((y for x,y in atoms2),w2)==0
assert avg((x*y for x,y in atoms2),w2)==0
assert all(x*y==x+y for x,y in atoms2)
e2=avg((x*x+y*y for x,y in atoms2),w2)
e4=avg(((x*x+y*y)**2 for x,y in atoms2),w2)
rho2=Q(4,17)*e4/e2
assert rho2==Q(769,153)>4
# At each scaled atom, at least one diagonal entry has absolute value
# <=1. Consequently K_4(-3I - sign*Y) >=0 for every sign choice:
# if the larger singular value exceeds 4, the smaller is <=4.
assert all(min(x*x,y*y)<=rho2 for x,y in atoms2)
# Common PC strongly RC energy of the same type, with expanded constants.
K2=2050; C02=14; L2=50000; C32=700000; R2=8
assert max((x*x+y*y)/2 for x,y in atoms2)<C02-1
assert all(L2*(x*x+y*y)/2-C32<=-2 for x,y in atoms2)
assert Q(2*C02+2,K2-2)<Q(1,64)
assert (C32+1+Q(1,64))/L2<15<R2*R2/2
assert (L2-(1+2*K2))*R2**2/2-3*K2*R2-C32+C02>1
assert (L2-(1+2*K2))*R2-3*K2>0
assert (L2-4)*R2**2/2-3*R2-C32>1
assert (L2-4)*R2-3>0
t2=Q(1,16*(R2+1)**2)
assert 1-Q(3,2)*t2*t2>Q(1,4)
assert Q(3,8*(R2+1))-(R2+1)*t2*t2-t2/8>Q(1,4*(R2+1))
# In contrast, the determinant-relation detector with r greater than
# sup ||I-X|| detects both exact traps without covariance amplitude fitting.
for at,wt,rr in [(atoms,w,Q(4)),(atoms2,w2,Q(8))]:
    assert all(max(abs(1-x),abs(1-y))<rr for x,y in at)
    assert avg((trunc_K(1-x-rr,1-y-rr,rr) for x,y in at),wt)==-wt[-1]
print('Second exact trap defeats the one-scale covariance detector; determinant-relation adaptive detector rejects both.')
# Regression condition: span of (x,y,det X) is graph d=x+y;
# its d=0 kernel consists of (x,-x) and is rank-one-free.
for at in [atoms,atoms2]:
    assert all(x*y==x+y for x,y in at)
    assert at[0][0]*at[1][1]-at[0][1]*at[1][0]!=0
# Adding an arbitrarily small minor-compatible rank-one component
# makes the existential split condition hold; it does not cure the
# negative detector. So nonblocked alone is not a closed test.
for eps in [Q(1,10),Q(1,100),Q(1,10000)]:
    aa=atoms+[(Q(1),Q(0)),(-Q(1),Q(0))]
    ww=[(1-eps)*v for v in w]+[eps/2,eps/2]
    assert avg((x for x,y in aa),ww)==avg((y for x,y in aa),ww)==avg((x*y for x,y in aa),ww)==0
    assert avg((trunc_K(1-x-4,1-y-4,4) for x,y in aa),ww)==-(1-eps)/9<0
print('Exact blocked-regression and small nonblocked perturbation controls passed.')

# The proposed finite baseline (adaptive covariance scale + nonblocked)
# still allows approximate PC-critical laws at a fixed positive b.
d0=Q(1,2)
weight=1/avg((x*x+(d0*y)**2 for x,y in atoms2),w2)
baseX=[(x,d0*y) for x,y in atoms2]+[(Q(0),Q(0))]
basew=[weight*p for p in w2]+[1-weight]
assert avg((x*x+y*y for x,y in baseX),basew)==1
for eps in [Q(1,10),Q(1,100),Q(1,10000),Q(1,10**8)]:
    X=baseX+[(Q(1),Q(0)),(-Q(1),Q(0))]
    ww=[(1-eps)*p for p in basew]+[eps/2,eps/2]
    assert avg((x*x+y*y for x,y in X),ww)==1
    cx=avg((x*x for x,y in X),ww); cy=avg((y*y for x,y in X),ww)
    assert cx>cy>0 and avg((x*y for x,y in X),ww)==0
    d2=cy/cx
    m2=avg((x*x+y*y/d2 for x,y in X),ww)
    m4=avg(((x*x+y*y/d2)**2 for x,y in X),ww)
    rho2=Q(4,17)*m4/m2
    assert all(min(x*x,y*y/d2)<rho2 for x,y in X)
    # Regression of det X on the two diagonal entries. No matrix
    # square roots are needed to recover the approximate trap center.
    alpha=avg((x*x*y for x,y in X),ww)/cx
    gamma=avg((x*y*y for x,y in X),ww)/cy
    assert gamma==1 and alpha>0
    rr=Q(10)
    assert avg((trunc_K(1-x/gamma-rr,1-y/alpha-rr,rr) for x,y in X),ww)<0
print('4 exact near-critical controls pass covariance-scale and nonblocked tests; regression-adaptive detector excludes them.')
