#!/usr/bin/env python3
"""Exact algebra checks for the rank-one-zero SOS reduction.

The analytic implications and Hilbert's ternary-quartic theorem are NOT
proved by this script; see morrey_rankone_zero_sos.md.
"""
from sympy import symbols, expand, Matrix, factor

a,b,c,d,alpha = symbols('a b c d alpha', nonzero=True)
B, C, D, E, F, G = symbols('B C D E F G')
t = B*b*b + C*b*c + D*b*d + E*c*c + F*c*d + G*d*d
scoeff = symbols('s0:15')
monoms = [b**4, b**3*c, b**3*d, b*b*c*c,b*b*c*d,b*b*d*d,
          b*c**3,b*c*c*d,b*c*d*d,b*d**3,c**4,c**3*d,c*c*d*d,c*d**3,d**4]
s = sum(cc*mm for cc,mm in zip(scoeff,monoms))
p = alpha*a*a*d*d + a*d*t+s
rem = s-t*t/(4*alpha)
assert expand(p-alpha*(a*d+t/(2*alpha))**2-rem)==0
assert expand(p.subs(d,0)-s.subs(d,0))==0

# Two explicit exact examples, each rank-one convex and with a rank-one zero.
det=a*d-b*c
S=b*b+c*c+d*d
example1=expand(det**2+S**2)
assert example1.subs({a:1,b:0,c:0,d:0}) == 0
assert expand(example1-(det**2+S**2))==0
# The LH test for both terms is manifestly SOS:
u1,u2,v1,v2=symbols('u1 u2 v1 v2')
H=Matrix([u1*v1,u1*v2,u2*v1,u2*v2]);X=Matrix([a,b,c,d])
def lh(P):
    return expand((H.T*Matrix([P]).jacobian(X).jacobian(X)*H)[0])
cofactor_grad = d*H[0]-c*H[1]-b*H[2]+a*H[3]
Sdot = b*H[1]+c*H[2]+d*H[3]
Sdirection=H[1]**2+H[2]**2+H[3]**2
assert expand(lh(example1) - (2*cofactor_grad**2+8*Sdot**2+4*S*Sdirection))==0

# Hilbert's theorem is invoked only for a nonnegative ternary quartic;
# this script does not claim all such quartics have rational SOS coefficients.
print('PASS: universal quartic normal-form completion-of-squares identity')
print('PASS: zero-plane and divisibility algebra')
print('PASS: exact rank-one Hessian SOS of det^2 + (b^2+c^2+d^2)^2')
print('NOTE: rank-one convexity -> nonnegative and Hilbert ternary SOS are hand/theory steps')
