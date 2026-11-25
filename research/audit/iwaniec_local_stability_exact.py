#!/usr/bin/env python3
"""Exact acoustic lower bound μ=1/6 at diag(1,0), for the p4 Chebyshev profile.

Standard-library-only Fraction verifier. The Fourier/Taylor bridge
is proved in the research note and is not part of this checker.
"""
from fractions import Fraction as F

a = [37676885,55559819,22507846,3634764,1122809,1068027,57237,
     275379,623336,96945,-261804,-126467,-6991]
D=2**24
def add(x,y):
 return tuple((x[i] if i<len(x) else 0)+(y[i] if i<len(y) else 0)
              for i in range(max(len(x),len(y))))
def sub(x,y):
 return add(x,tuple(-t for t in y))
def scale(x,s):
 return tuple(s*t for t in x)
t=[(1,),(0,1)]
for j in range(2,len(a)):
 old,prev=t[-1],t[-2]
 x0=(0,)+old
 t.append(sub(scale(x0,2),prev))
H=(0,)
for c,p in zip(a,t): H=add(H,scale(p,c))
assert len(H)==13
h0=F(H[0],D);h1=F(H[1],D);h2=F(2*H[2],D)
assert (h0,h1,h2)==(
 F(2139095,2097152),F(50331651,16777216),F(2264943,4194304))
B=4*h0;U=3*B;V=h2;T=2*h1
assert (B,U,V,T)==(
 F(2139095,524288),F(6417285,524288),
 F(2264943,4194304),F(50331651,8388608))
mu=F(1,6)
assert U>mu and B>mu and V>mu and T>B-mu
gap=(U-mu)*(V-mu)-(T-B+mu)**2
assert gap==F(32352523009765,211106232532992)>0
print("PASS: exact p4 Hessian rank-one margin >= 1/6 at diag(1,0)")
