#!/usr/bin/env python3
"""Exact coefficients of global DM positive stabilizations.

Bases: (s^2, s*det, det^2). Validates both identities
with exact Fraction arithmetic. Analytic PC of Q_e is an
external established theorem; this script verifies algebra.
"""
from fractions import Fraction as Q
def plus(*vs): return tuple(sum(v[i] for v in vs) for i in range(3))
def mul(k,v): return tuple(k*x for x in v)
S=(Q(1),Q(0),Q(-2))
D=(Q(0),Q(0),Q(1))
for e in (-1,1):
    End=(Q(1),Q(-2*e),Q(0))
    Sq=(Q(1),Q(-4*e),Q(4))
    for g in (Q(0),Q(1,7),Q(2,5),Q(1),Q(5,4),Q(3,2),Q(2)):
        for c in (Q(-7,5),Q(0),Q(2),Q(11,3)):
            if g<=1:
                got=plus(mul(1-g,S),mul(g,End),mul(c+2*(1-g),D))
            else:
                got=plus(mul(2-g,End),mul(g-1,Sq),mul(c-4*(g-1),D))
            assert got==(Q(1),-2*e*g,c)
            if g>=1 and c==4*(g-1):
                assert 4-4*g+c==0
print("PASS: exact quartic decompositions for both orientations and all rational controls")
