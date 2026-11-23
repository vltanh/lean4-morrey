#!/usr/bin/env python3
"""Exact SOS derivation of the 59/60 operator-norm moment obstruction.

For a>=0:
a <= 3/4 + a^2/3
a <= 3/4 - a^2/3 + (2/3)a^4.
Their differences have explicit sum-of-squares identities.
No floating point or external packages.
"""
from fractions import Fraction as Q
def polyadd(a,b):
    return tuple((a[i] if i<len(a) else Q(0))+
                 (b[i] if i<len(b) else Q(0))
                 for i in range(max(len(a),len(b))))
def scale(a,c):return tuple(c*x for x in a)
def mul(a,b):
    z=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]+=x*y
    return tuple(z)
a=(Q(0),Q(1))
a2=mul(a,a);a4=mul(a2,a2)
one=(Q(1),)
minus=polyadd(polyadd(scale(one,Q(3,4)),scale(a2,Q(1,3))),scale(a,-1))
minus_sos=scale(mul(polyadd(a,scale(one,-Q(3,2))),
                    polyadd(a,scale(one,-Q(3,2)))),Q(1,3))
plus=polyadd(polyadd(polyadd(scale(one,Q(3,4)),scale(a2,-Q(1,3))),
                     scale(a4,Q(2,3))),scale(a,-1))
plus_sos=polyadd(
    scale(mul(polyadd(a2,scale(one,-Q(3,4))),
              polyadd(a2,scale(one,-Q(3,4)))),Q(2,3)),
    scale(mul(polyadd(a,scale(one,-Q(3,4))),
              polyadd(a,scale(one,-Q(3,4)))),Q(2,3)))
def pad(x,n):return tuple(x)+(Q(0),)*(n-len(x))
assert pad(minus,5)==pad(minus_sos,5)
assert pad(plus,5)==pad(plus_sos,5)
assert Q(3,4)+Q(2,3)*Q(7,20)==Q(59,60)<1
assert Q(7,20)<Q(3,8)
print("PASS: exact two SOS identities, separator violates matrix-moment bound 59/60")
