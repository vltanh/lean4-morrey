#!/usr/bin/env python3
"""Exact residual T4 signed-diagonal minors law with no rank-one pairs.

This verifies nonempty residual geometry, NOT an energy Jensen gap.
The two-atom merging theorem in the research note is mathematical.
"""
from fractions import Fraction as Q
w=[Q(1,4)]*4
x=[Q(-2),Q(0),Q(2),Q(4)]
y=[Q(-1),Q(3),Q(-3),Q(1)]
assert sum(w)==1
assert sum(w[i]*x[i] for i in range(4))==1
assert sum(w[i]*y[i] for i in range(4))==0
assert sum(w[i]*x[i]*y[i] for i in range(4))==0
assert all((x[i]-x[j])*(y[i]-y[j])!=0
           for i in range(4) for j in range(i+1,4))
print("PASS: exact four-atom minors law, every pair full-rank separated")
