#!/usr/bin/env python3
"""Exact global positive isotropic rank-one convex non-polyconvex obstruction.

W=exp(q), q=||A||_F^4-(9/4)||A||_F^2 det(A).
Checks the rank-one Hessian SOS, four minors moments and rational exp bounds.
Requires SymPy for one symbolic polynomial identity.
"""
from fractions import Fraction as Q
import sympy as s

a,b,c,d=s.symbols("a b c d",real=True)
sq=a*a+b*b+c*c+d*d
q=s.expand(sq*sq-s.Rational(9,4)*sq*(a*d-b*c))
SOS=4*(3*(a-s.Rational(9,16)*d)**2+
    s.Rational(13,256)*d*d+
    (b+s.Rational(9,16)*c)**2+
    s.Rational(175,256)*c*c)
assert s.expand(s.diff(q,a,2)-SOS)==0
print("PASS: exact rank-one Hessian SOS after SO(2) rotations")

atoms=[(Q(1,52),Q(1),Q(1)),(Q(1,52),Q(-1),Q(-1)),
       (Q(25,52),Q(1,5),Q(-1,5)),(Q(25,52),Q(-1,5),Q(1,5))]
assert sum(w for w,x,y in atoms)==1
assert sum(w*x for w,x,y in atoms)==0
assert sum(w*y for w,x,y in atoms)==0
assert sum(w*x*y for w,x,y in atoms)==0

def qdiag(x,y):
    norm=x*x+y*y
    return norm*norm-Q(9,4)*norm*x*y

assert qdiag(Q(1),Q(1))==-Q(1,2)
assert qdiag(Q(1,5),Q(-1,5))==Q(17,1250)
assert sum(w*qdiag(x,y) for w,x,y in atoms)==-Q(2,325)

# From 1+1/2+1/8=13/8>8/5, e^-1/2<5/8.
# From e^x<=1/(1-x), 0<x<1, e^(17/1250)<1250/1233.
assert Q(13,8)>Q(8,5) and Q(8,13)<Q(5,8)
upper=Q(1,26)*Q(5,8)+Q(25,26)*Q(1250,1233)
assert upper==Q(19705,19728) and upper<1
print("PASS: exact 4-atom minors-law W-Jensen violation, upper",upper)
