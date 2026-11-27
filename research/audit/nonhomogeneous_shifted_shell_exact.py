"""Exact finite algebra for the shifted-truncated-determinant obstruction.
The analytic QC and all-radius proofs are in the companion note.
"""
from fractions import Fraction as Q
from itertools import product


def L(x, y, r=Q(1)):
    return x*x-y*y if x+y<=r else 2*r*x-r*r


def F(s,d):
    x,y=(s+d)/2,(s-d)/2
    return L(x,abs(y-1))


def K(s,d,r,e):
    return max(s-r,0)*(r+e*d)


law=[(Q(0),Q(0),Q(3,8)),(Q(2),Q(-2),Q(1,2)),(Q(4),Q(2),Q(1,8))]
s0,d0=Q(1),Q(-1)
E=lambda f:sum(w*f(s,d) for s,d,w in law)
assert E(lambda s,d:1)==1
assert E(lambda s,d:s*d)==s0*d0==-1
assert E(lambda s,d:(s+d)/2)==Q(3,8)
assert E(lambda s,d:(s-d)/2)==Q(9,8)
assert [F(s,d) for s,d,w in law]==[-1,-1,5]
assert F(s0,d0)==0 and E(F)==-Q(1,4)
# Exact matrix lift: diagonal with complex coordinates z,w.
atoms=[(Q(0),Q(0),Q(3,8)),(Q(0),Q(2),Q(1,2))]+[(Q(3*z),Q(w),Q(1,32)) for z,w in product((-1,1),repeat=2)]
assert sum(p*z for z,w,p in atoms)==0 and sum(p*w for z,w,p in atoms)==1
assert sum(p*(z*z-w*w) for z,w,p in atoms)==-1
assert sum(p*L(abs(z),abs(abs(w)-1)) for z,w,p in atoms)==-Q(1,4)
# On [1,2] two exact quadratics: (2-r)(5r+4)/8 and (-5r²+18r-8)/8.
# The latter is concave with both endpoint values positive.
for r in (Q(1),Q(5,4),Q(3,2),Q(7,4),Q(2)):
    assert E(lambda s,d:K(s,d,r,-1))==(2-r)*(5*r+4)/8
    assert E(lambda s,d:K(s,d,r,1))==(-5*r*r+18*r-8)/8
assert E(lambda s,d:K(s,d,Q(1),1))==Q(5,8)
assert E(lambda s,d:K(s,d,Q(2),1))==1
# Endpoint and lower-radius controls. The companion proof handles every radius.
for r in [Q(i,16) for i in range(1,81)]:
    for e in (-1,1):
        assert E(lambda s,d:K(s,d,r,e))>=K(s0,d0,r,e)
# Strictification bound before smoothing: E||X||_F²-||A||_F².
var=E(lambda s,d:s*s+d*d)-(s0*s0+d0*d0)
assert var==Q(9,2)
assert E(F)+var/36==-Q(1,8)
print('Exact three-radius witness: all moments, matrix lift, shifted-L gap -1/4, kernel polynomial identities, strictification: passed')
