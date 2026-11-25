#!/usr/bin/env python3
"""Exact residual three-diagonal-atom minor-law geometry.

The sample has barycenter diag(1,0), determinant mean zero,
and no rank-one-connected pair. It is NOT a gradient Young
measure or a Jensen violation. Proof that connected-pair
three-atom laws laminate is in the research note.
"""
from fractions import Fraction as Q
w=(Q(1,3),)*3
x=(Q(0),Q(3,4),Q(9,4))
y=(Q(-3,2),Q(9,4),Q(-3,4))
assert sum(w)==1
assert sum(w[i]*x[i] for i in range(3))==1
assert sum(w[i]*y[i] for i in range(3))==0
assert sum(w[i]*x[i]*y[i] for i in range(3))==0
assert all((x[i]-x[j])*(y[i]-y[j])!=0 for i in range(3) for j in range(i+1,3))
print("PASS: exact 3-atom minor law with no rank-one-connected pair")
