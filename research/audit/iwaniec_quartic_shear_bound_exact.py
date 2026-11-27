#!/usr/bin/env python3
"""Exact algebra regression: quartic shear bounds and high-coupling PC identity.

Requires SymPy for symbolic coefficient identities.
PC of Q_e is a cited analytic theorem, not checked by this script.
"""
import sympy as s
a,b,c,t,r,g,d,z,e=s.symbols("a b c t r g d z e", real=True)
F=lambda S,D:a*S**2+b*S*D+c*D**2
assert s.diff(F(2+t*t,1),t,2).subs(t,0)==8*a+2*b
assert s.diff(F(2+t*t,-1),t,2).subs(t,0)==8*a-2*b
h=F(1+r*r,r)
h2=s.diff(h,r,2)
assert s.simplify(h2-(12*a*(r+b/(4*a))**2+4*a+2*c-3*b*b/(4*a)))==0
Q=z*(z-2*e*d)
R=(z-2*e*d)**2
identity=a*(2-g)*Q+a*(g-1)*R+(c-4*a*(g-1))*d*d
target=a*z*z-2*e*a*g*z*d+c*d*d
assert s.simplify((identity-target).subs(e**2,1))==0
for E in (-1,1):
    assert s.expand((identity-target).subs(e,E))==0
print("PASS: exact shear, diagonal curvature, and high-coupling decomposition")
