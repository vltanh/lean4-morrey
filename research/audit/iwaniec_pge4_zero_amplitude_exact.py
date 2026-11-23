#!/usr/bin/env python3
"""Exact endpoint identities for p>2 zero-amplitude poly-affine support.

Uses SymPy for identities and Fraction for a concrete positive control.
No claim of the universal p>=4 support feasibility.
"""
import sympy as s
from fractions import Fraction as Q
p,t,H,m=s.symbols('p t H m',real=True)
C=p*H-2*t*m
L=((1+t)*m-p*H)/(1-t)
U=(p*H+(1-t)*m)/(1+t)
target=(p-2)*H/2
assert s.factor((p-1)*H-t*U-target-(1-t)*C/(2*(1+t)))==0
assert s.factor((p-1)*H-t*L-target-(1+t)*C/(2*(1-t)))==0
assert s.factor(U-L-2*C/(1-t*t))==0
# A positive admissible control; exact lower cutoff and gap.
pv=Q(9,2);tv=Q(1,3);Hv=Q(2);mv=Q(1)
lv=((1+tv)*mv-pv*Hv)/(1-tv)
uv=(pv*Hv+(1-tv)*mv)/(1+tv)
assert lv<=uv and pv*Hv-2*tv*mv>=0
c0=max(abs(lv),abs(uv))
M0=pv*Hv+2*abs(mv)+2*c0
rho=min(Q(1),(pv-2)*Hv/(4*M0))
assert rho>0
for c in (lv,(lv+uv)/2,uv):
 assert (pv-1)*Hv-c*tv >= (pv-2)*Hv/2
 assert (pv-2)*Hv/2-rho*M0 >= (pv-2)*Hv/4
print('PASS: universal endpoint identities and rational small-amplitude control',rho)
