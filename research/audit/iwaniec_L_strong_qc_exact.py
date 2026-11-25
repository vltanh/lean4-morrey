#!/usr/bin/env python3
"""Exact lifted Jensen witness for W_e = 1 + L + e ||A||_F^2.

At e=1/8 the four matrices ±D and ±4I have lifted barycenter
(A,det A)=(0,0), but their energy mean is W_e(0)-1/17.
This proves nonpolyconvexity, NOT nonquasiconvexity.
Requires Python's standard library only.
"""
from fractions import Fraction as F

e = F(1, 8)
D = ((F(1), F(0)), (F(0), F(-1)))
I4 = ((F(4), F(0)), (F(0), F(4)))

def neg(A):
    return tuple(tuple(-x for x in row) for row in A)

def det(A):
    return A[0][0] * A[1][1] - A[0][1] * A[1][0]

def normsq(A):
    return sum(x * x for row in A for x in row)

def l_special(A):
    # Only required on ±D and ±4I; formula follows from complex form.
    if A == D or A == neg(D):
        return F(-1)
    if A == I4 or A == neg(I4):
        return F(7)
    raise ValueError("not an admitted rational atom")

atoms = [
    (F(8, 17), D),
    (F(8, 17), neg(D)),
    (F(1, 34), I4),
    (F(1, 34), neg(I4)),
]
assert sum(weight for weight, _ in atoms) == 1
assert det(D) == -1 and det(I4) == 16
assert all(sum(weight * A[i][j] for weight, A in atoms) == 0
           for i in range(2) for j in range(2))
assert sum(weight * det(A) for weight, A in atoms) == 0
gap = sum(weight * (l_special(A) + e * normsq(A))
          for weight, A in atoms)
assert gap == F(-1, 17), gap
assert gap + F(2, 100) < 0  # pointwise smoothing error < 1/100
print("PASS: exact 4-atom minors barycenter (0,0), Jensen gap -1/17")
