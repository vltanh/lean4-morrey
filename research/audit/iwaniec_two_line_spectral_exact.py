#!/usr/bin/env python3
"""Exact rational Fourier-line energy projection control for all-gradient Morrey.

The global two-ridge Jensen theorem is analytic prior art; this checker
only validates primitive directions, Parseval bookkeeping and top-two energies.
"""
from fractions import Fraction as Q
from math import gcd

coeffs={
(1,0):(Q(1),Q(2)),(-1,0):(Q(1),Q(2)),
(0,1):(Q(3),Q(4)),(0,-1):(Q(3),Q(4)),
(1,1):(Q(2),Q(1)),(-1,-1):(Q(2),Q(1)),
(2,-1):(Q(1),Q(1)),(-2,1):(Q(1),Q(1)),
(3,2):(Q(4),Q(1)),(-3,-2):(Q(4),Q(1)),
}
def primitive(k):
    g=gcd(*k)
    a,b=k[0]//g,k[1]//g
    return (a,b) if a>0 or (a==0 and b>0) else (-a,-b)
direction_energy={}
for k,v in coeffs.items():
    e=Q(k[0]**2+k[1]**2)*sum(a*a for a in v)
    direction_energy[primitive(k)]=direction_energy.get(primitive(k),Q(0))+e
values=sorted(direction_energy.values(),reverse=True)
assert values==[Q(442),Q(50),Q(20),Q(20),Q(10)]
assert sum(values)==Q(542)
assert sum(values[:2])==Q(492)
assert sum(values[2:])==Q(50)
print('PASS: Fourier total 542, retained-top-two 492, remainder-tail 50')
