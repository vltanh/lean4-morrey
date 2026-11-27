#!/usr/bin/env python3
"""Exact minors-compatible T3 law, known non-realizable as gradient Young measure.

This validates ONLY rational moments and lack of rank-one pairs.
The nonrealizability comes from Sverak three-gradient rigidity,
not from the checker itself.
"""
from fractions import Fraction as Q
w=[Q(1,3)]*3
x=[Q(0),Q(3,4),Q(9,4)]
y=[-Q(3,2),Q(9,4),-Q(3,4)]
assert sum(w)==1
assert sum(w[i]*x[i] for i in range(3))==1
assert sum(w[i]*y[i] for i in range(3))==0
assert sum(w[i]*x[i]*y[i] for i in range(3))==0
dets=[(x[i]-x[j])*(y[i]-y[j]) for i in range(3) for j in range(i+1,3)]
assert dets==[Q(45,16),Q(27,16),-Q(9,2)]
print("PASS: exact minors-compatible T3 control; pairwise rank-two differences")
print("NOTE: failure of gradient realization is an external 1993/1994 rigidity theorem")
