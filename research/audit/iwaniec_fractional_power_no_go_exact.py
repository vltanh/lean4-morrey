#!/usr/bin/env python3
"""Exact t=1/2 second derivative for fractional powers of Q.

At t=1/2, Q(diag(1,t))=5/16, Q'=-1, Q''=1.
For q=p/4 the sign of (Q**q)'' is sign(q-11/16),
hence negative for all 2<p<11/4.
"""
from fractions import Fraction as Q
def f(t): return (1+t*t)*(1-t)*(1-t)
def fp(t):return -2+4*t-6*t*t+4*t*t*t
def fpp(t):return 4-12*t+12*t*t
t=Q(1,2)
assert f(t)==Q(5,16)
assert fp(t)==-1
assert fpp(t)==1
for p in (Q(201,100),Q(5,2),Q(8,3)):
 q=p/4
 assert q-Q(11,16)<0
assert Q(11,4)/4==Q(11,16)
print("PASS: exact rank-one-line fractional-power Hessian obstruction for 2<p<11/4")
