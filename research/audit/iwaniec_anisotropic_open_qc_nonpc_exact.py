#!/usr/bin/env python3
"""Exact rational four-atom stability margin for an infinite-dimensional C²
anisotropic/nonhomogeneous QC, non-PC class.

Quasiconvexity of the quartic core is an EXTERNAL 2026 preprint result,
not checked in this script. No Morrey counterexample is claimed.
"""
from fractions import Fraction as Q
gamma=Q(9,8)
assert 3*(9**2)<4*(8**2)  # gamma² < 4/3
I=((Q(1),Q(0)),(Q(0),Q(1)))
K=((Q(1,5),Q(0)),(Q(0),-Q(1,5)))
weights=(Q(1,52),Q(1,52),Q(25,52),Q(25,52))
atoms=(I,tuple(tuple(-z for z in row) for row in I),
       K,tuple(tuple(-z for z in row) for row in K))
def values(a):
 x,y=a
 s=sum(z*z for row in a for z in row)
 det=x[0]*y[1]-x[1]*y[0]
 return s,det,s*s-Q(9,4)*s*det
assert sum(weights)==1
assert all(sum(weights[i]*atoms[i][r][c] for i in range(4))==0
           for r in range(2) for c in range(2))
assert sum(weights[i]*values(atoms[i])[1] for i in range(4))==0
assert values(I)[2]==-Q(1,2)
assert values(K)[2]==Q(17,1250)
assert sum(weights[i]*values(atoms[i])[0] for i in range(4))==Q(2,13)
assert Q(19705,19728)+Q(1,6500)==Q(32025557,32058000)
assert Q(1)-Q(32025557,32058000)==Q(32443,32058000)
residual=Q(32443,32058000)-Q(2,10000)
assert residual==Q(130157,160290000)>0
print('PASS: exact global four-atom gap after any allowed C² perturbation:',residual)
