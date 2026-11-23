#!/usr/bin/env python3
"""Exact symbolic identities for one-multiplier nonconformal poly-affine support.

Checks algebra only, not global convexity or the scalar sign condition.
Requires SymPy. No numerical optimizer, no Lean proof.
"""
import sympy as sp

p,t,H,m,c,a,s,Z=sp.symbols('p t H m c a s Z',real=True)
u=p*H-t*m-c*t
v=m-c
k=-(p-1)*H+c*t
P=Z-k-a*(u+v*s)-c*a*a*s
scalar=Z+(p-1)*H-a*(p*H+m*(s-t))+c*(a-1)*(t-a*s)
assert sp.expand(P-scalar)==0
assert sp.expand(k+u+t*v+c*t-H)==0
L=((1+t)*m-p*H)/(1-t)
U=(p*H+(1-t)*m)/(1+t)
assert sp.cancel(U-L-2*(p*H-2*t*m)/(1-t*t))==0
assert sp.expand(u-v-((1-t)*c+p*H-(1+t)*m))==0
assert sp.expand(u+v-(-(1+t)*c+p*H+(1-t)*m))==0
print('PASS: support identity, touching condition, and interval-width formula')
