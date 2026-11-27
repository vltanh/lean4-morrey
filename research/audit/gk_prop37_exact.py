#!/usr/bin/env python3
"""Exact minors-barycenter audit for Guerra–Kristensen (2022), Proposition 3.7.

The printed 3-atom equal-weight witness has the WRONG determinant
barycenter (-15 != 1). A replacement rational 3-atom probability
law exactly matches the matrix AND determinant moments at I and
vanishes under F_p for every p>=2.

This is a POLYCONVEXITY obstruction. It is NOT an actual gradient
Young measure or a quasiconvexity counterexample.
"""
from fractions import Fraction as Q


def moments(items):
    assert sum(weight for weight, _, _ in items) == 1
    return (
        sum(weight * a for weight, a, d in items),
        sum(weight * d for weight, a, d in items),
        sum(weight * a * d for weight, a, d in items),
    )


def base_energy(a, d):
    # Diagonal 2x2 special case of F_2(A) = a_+ d_+ + (b²+c²)/2.
    return max(a, 0) * max(d, 0)


original = (
    (Q(1, 3), Q(-3), Q(-3)),
    (Q(1, 3), Q(9), Q(-3)),
    (Q(1, 3), Q(-3), Q(9)),
)
corrected = (
    (Q(1, 4), Q(-2), Q(-2)),
    (Q(3, 8), Q(4), Q(0)),
    (Q(3, 8), Q(0), Q(4)),
)
assert moments(original) == (1, 1, -15)
assert moments(corrected) == (1, 1, 1)
assert all(base_energy(a, d) == 0 for _, a, d in corrected)
assert base_energy(Q(1), Q(1)) == 1
print("PASS: original determinant mean=-15; corrected minors=(1,1,1); energy gap 1>0")
