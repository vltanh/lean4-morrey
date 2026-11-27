#!/usr/bin/env python3
"""Exact identity checks for the isotropic p-homogeneous acoustic tensor.

SymPy required. No numerical random sampling, no Lean build.
See docs/research/IWANIEC_MORREY_ACOUSTIC.md for the endpoint proof.
"""
import sympy as sp
p,r,h,h1,h2=sp.symbols("p r h h1 h2",real=True)
u1,u2,v1,v2=sp.symbols("u1 u2 v1 v2",real=True)
x,y,z,w=u1*v1,u1*v2,u2*v1,u2*v2
C=p*h-2*r*h1
B=C/(1-r**2)
U=(p-1)*C+r*r*h2
V=h2
T=r*B+(p-2)*h1-r*h2

raw=(C*((p-1)*x*x+(y*y+z*z+2*r*y*z)/(1-r*r))
     +2*(p-2)*h1*y*z+h2*(w-r*x)**2)
ac=((U*v1*v1+B*v2*v2)*u1*u1+2*T*v1*v2*u1*u2
    +(B*v1*v1+V*v2*v2)*u2*u2)
assert sp.cancel(raw-ac)==0
det=sp.expand((U*v1*v1+B*v2*v2)*(B*v1*v1+V*v2*v2)-(T*v1*v2)**2)
expected=U*B*v1**4+(U*V+B*B-T*T)*v1*v1*v2*v2+B*V*v2**4
assert sp.cancel(det-expected)==0

for sign in (1,-1):
    s={p:2,h:sign*r,h1:sign,h2:0}
    assert all(sp.simplify(e.subs(s))==0 for e in (C,B,U,V,T))

single={h:1,h1:0,h2:0}
assert sp.simplify(T.subs(single)-r*B.subs(single))==0
print("PASS: exact acoustic and determinant identities")
