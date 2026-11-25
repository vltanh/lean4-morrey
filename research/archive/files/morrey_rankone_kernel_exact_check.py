#!/usr/bin/env python3
"""Exact integer/rational checks supporting the grid-independent Hessian certificate theorem.
Uses only Python stdlib. Proves neither quartic Morrey nor unrestricted Morrey.
"""
from itertools import combinations, product
from math import comb
from fractions import Fraction as Q

def allowed_monomials_after_rankone_second_derivatives():
    # For a polynomial vanishing under D^2P(A)[H,H] for all rank-1 H,
    # coordinate H force exponents <=1, and same-row/column H force
    # monomials containing ab,ac,bd,cd to vanish.
    forbidden = {(0,1),(0,2),(1,3),(2,3)}
    allowed=[]
    for r in range(5):
        for support in combinations(range(4),r):
            if all(not set(pair).issubset(support) for pair in forbidden):
                allowed.append(support)
    return allowed

allowed = allowed_monomials_after_rankone_second_derivatives()
assert allowed == [(),(0,),(1,),(2,),(3,),(0,3),(1,2)],allowed
# H=(1,1;1,1) is rank-one and imposes coeff(ad)+coeff(bc)=0.
# Thus 6-dimensional kernel: affine functions + determinant.
for d in range(2,9):
    print('degree <=',d,'polynomial dimension',comb(d+4,4),
          'rank of all rank-one Hessian evaluations',comb(d+4,4)-6,
          'max nonnegative certificate terms',comb(d+4,4)-6)

# Rational counterexample to a moment-only Morrey approach. Verify rank-one
# convexity by exact SOS after SO(2)xSO(2) reduces rank-one H to E11:
# (1/4)D²f(A)[E11,E11] = 3(a-9d/16)^2 + 13d^2/256 +
# (b+9c/16)^2 + 175c^2/256.
gamma=Q(9,8)
def energy(A):
    a,b,c,d=A
    s=sum(x*x for x in A)
    det=a*d-b*c
    return s*s-2*gamma*s*det
I=(Q(1),Q(0),Q(0),Q(1))
J=(Q(1,5),Q(0),Q(0),Q(-1,5))
def det(A):return A[0]*A[3]-A[1]*A[2]
alpha=Q(1,26); beta=Q(25,26)
assert alpha+beta==1
assert alpha*det(I)+beta*det(J)==0
# symmetric masses +/-I and +/-J guarantee mean zero.
assert alpha*energy(I)+beta*energy(J)==-Q(2,325)
for a,b,c,d in product(range(-3,4),repeat=4):
    lhs=3*a*a+b*b+c*c+d*d-3*gamma*a*d+gamma*b*c
    rhs=3*(Q(a)-Q(9,16)*d)**2+Q(13,256)*d*d+(Q(b)+Q(9,16)*c)**2+Q(175,256)*c*c
    assert lhs==rhs
    assert rhs>=0
print('EXACT: rank-one Hessian SOS verified for gamma=9/8 at E11')
print('EXACT: non-gradient measure has E[A]=0, E[det A]=0, and f_gamma Jensen gap = -2/325')
print('ALL CHECKS PASSED')
