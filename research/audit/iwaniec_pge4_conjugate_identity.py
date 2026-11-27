#!/usr/bin/env python3
"""Check the global p>=4 Fenchel support identity and universal tail formula.

SymPy for the symbolic identity, Fraction for a rational cutoff control.
The continuum feasibility/positivity conjecture remains UNPROVED.
"""
import sympy as s
from fractions import Fraction as Q
p,t,H,m,c,a,r,z=s.symbols('p t H m c a r z',real=True,positive=False)
P=a**p*z+(p-1)*H-a*(p*H+m*(r-t))+c*(a-1)*(t-a*r)
q=a**(1-p)*(m+c*(a-1))
R=(p-1)*H-a*p*H+a*m*t+c*(a-1)*t
# Power cancellation is legitimate when a>0, as in the theorem.
identity=P-(a**p*(z-q*r)+R)
assert s.simplify(s.powsimp(identity,force=True))==0
L=((1+t)*m-p*H)/(1-t)
U=(p*H+(1-t)*m)/(1+t)
assert s.cancel(U-L-2*(p*H-2*t*m)/(1-t*t))==0
# Exact rational p=9/2, t=1/2, H=3, m=1, h_min=1/2 control.
pv=Q(9,2);tv=Q(1,2);Hv=Q(3);mv=Q(1);hmin=Q(1,2)
lower=((1+tv)*mv-pv*Hv)/(1-tv)
upper=(pv*Hv+(1-tv)*mv)/(1+tv)
C0=max(abs(lower),abs(upper))
M=pv*Hv+2*abs(mv)+C0
radius=next(k for k in range(1,1000)
            if k*k>=4*C0/hmin and k*k*k>=4*M/hmin)
assert radius==14
assert Q(radius)**2>=4*C0/hmin
assert Q(radius)**3>=4*M/hmin
print("PASS: symbolic amplitude reduction and exact global tail cutoff R=14")
