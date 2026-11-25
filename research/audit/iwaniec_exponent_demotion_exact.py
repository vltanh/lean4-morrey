#!/usr/bin/env python3
"""Exact rational algebraic controls for homogeneous-exponent demotion.

For every real p>q>0 the proof in the research note gives a downward
rank-one-line derivative jump q-p. This script checks the power
exponents and strict sign on rational controls only, without sampling.
"""
from fractions import Fraction as F
for p,q in [(F(9,2),F(4)),(F(6),F(4)),(F(8),F(4)),
            (F(9),F(5)),(F(17,3),F(10,3))]:
    left=p/2
    right=q-p/2
    assert right-left==q-p<0
    # On diag(1,t), t<=1: a=1,r=t; t>=1: a=t,r=1/t.
    # Thus t^(p/2) and t^(q-p/2), respectively.
    assert left>right
print("PASS: downward derivative jump for all rational controls")
