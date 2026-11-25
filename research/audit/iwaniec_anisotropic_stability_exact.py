#!/usr/bin/env python3
"""Exact quantitative isotropic-to-anisotropic QC stability controls.

ISO_p: nonnegative isotropic p-homogeneous RC=>PC, p>=2, is the USER'S
ASSUMED mathematical input, not proved by this checker. The analytic
Bregman uniform-convexity estimate is proved in the research note.
"""
from fractions import Fraction as Q
from sympy import symbols, hessian, Rational, Matrix

def cp(p):
    return Q(p,1)/(Q(p-1,1)*Q(4)**(p-1)*Q(3)**(p-2))
assert cp(2)==Q(1,2)
assert cp(4)==Q(1,432)

p=4
alpha=Q(1,100);mu=Q(1,25)
c=min(alpha,mu/Q(p*(p-1)))/2
eta=c*cp(p)
assert c==Q(1,600)
assert eta==Q(1,259200)

# Explicitly nonconvex polynomial isotropic core:
# F0=||A||^2(||A||^2-2det A)+||A||^4/100.
# On A=diag((y+x)/2,(y-x)/2), exactly:
x,y=symbols('x y', real=True)
q=(x**4+x*x*y*y)/2
squared_norm4=(x*x+y*y)**2/4
f=q+Rational(1,100)*squared_norm4
M=hessian(f,[x,y]).subs({x:1,y:2})
assert M==Matrix([[Rational(1007,100),Rational(101,25)],
                 [Rational(101,25),Rational(113,100)]])
assert M.det()==-Rational(1977,400)
print('PASS: p=4 isotropic baseline c=',c,
      'weighted Hessian anisotropy radius eta=',eta)
print('PASS: nonconvex baseline Hessian determinant',M.det())
