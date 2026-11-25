#!/usr/bin/env python3
"""Exact algebra controls for envelope subtraction and rank-one-envelope amplification.
These are identities/budget checks, not numerical proofs of the incompatibility theorem.
"""
from fractions import Fraction as Q
import sympy as s
from itertools import product
I=s.eye(2)
X=s.Matrix(2,2,s.symbols('x:4'))
p=s.Matrix(2,2,s.symbols('p:4'))
f,D,t=s.symbols('f D t')
T=f*I-X.T*p
# At a contact state, g=f-t*q-t*D=(1-t)*f-t*D,
# with Dg=(1-t)*Df. The recentered shifted stress contracts.
Tg=((1-t)*f-t*D)*I-X.T*((1-t)*p)
assert (Tg+D*I-(1-t)*(T+D*I)).applyfunc(s.expand)==s.zeros(2)
# At a maximizing base, f=0, q=-D and the g shift is t*D.
q0=-D
g0=-t*q0
Qg0=(1-t)*q0
assert s.expand(g0-Qg0-D)==0
# PC/QC envelope gap scales by (1-t); use abstract q,p scalar levels.
q0,p0=s.symbols('q0 p0')
assert s.expand((1-t)*q0-(1-t)*p0-(1-t)*(q0-p0))==0

# On a true contact law, energy-momentum shift from increasing only
# the recentered base by (c-1)D.
c=s.symbols('c')
Tc=(f-(c-1)*D)*I-X.T*p
assert (Tc+c*D*I-(T+D*I)).applyfunc(s.expand)==s.zeros(2)
print('Exact stress contraction, base-defect and envelope-gap identities passed.')

# For obstacle U_c=q+c(f-q), strong RC envelope with margin kappa.
# Lower bound for each atom's penalty (m-kappa)|X-A|^2/2
# + (c-1)*max(0,D-M*|X-A|^2).
count=0
for m,M,D,k_frac,c0 in product([Q(1,10),Q(1),Q(2)], [Q(1),Q(3)], [Q(1,100),Q(2)], [Q(1,4),Q(1,2)], [Q(1),Q(3,2),Q(4)]):
    if m>M: continue
    kappa=k_frac*m
    cc=1+c0*(m-kappa)/(2*M)
    b=D*min(cc-1,(m-kappa)/(2*M))
    for v in [Q(0),D/(4*M),D/(2*M),D/M,2*D/M,10*D/M]:
        assert (m-kappa)*v/2+(cc-1)*max(Q(0),D-M*v)>=b
        count+=1
print(f'{count} exact atom-penalty and curvature-budget checks passed.')
print('No numerical Morrey counterexample or independent analytic certification.')
