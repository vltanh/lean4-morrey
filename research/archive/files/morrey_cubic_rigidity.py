#!/usr/bin/env python3
"""Exact, bounded linear-algebra certificate for cubic rigidity in Morrey 2x2.

If a polynomial P of total degree <=3 is globally rank-one convex, then
for each rank-one H, the polynomial A -> D²P(A)[H,H] is affine and >=0
on the whole space, hence its degree-one part is zero. This forces
D²P_3(A)[H,H] == 0, where P_3 is homogeneous cubic.

This script verifies that the only homogeneous cubic satisfying these
linear identities is the zero polynomial. It also verifies the much
smaller hand-proof basis H=E11,E12,E21,E22,E11+E12,E21+E22 suffices.
"""
from itertools import product
from sympy import Matrix, Poly, hessian, symbols, zeros, expand

x=symbols('x11 x12 x21 x22')
p,q,r,s=symbols('p q r s')
monomials=[__import__('sympy').prod(x[j]**t[j] for j in range(4))
           for t in product(range(4),repeat=4) if sum(t)==3]
assert len(monomials)==20

# For each H, D²monomial(A)[H,H] is a linear form in A.
def coefficient_rows(H):
    return [[expand((Matrix([H]).reshape(1,4)*hessian(M,x)*Matrix(H))[0]).coeff(z)
             for M in monomials] for z in x]

basis=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),
       (1,1,0,0),(0,0,1,1)]
rows=[r for H in basis for r in coefficient_rows(H)]
M=Matrix(rows)
assert M.shape==(24,20)
assert M.rank()==20
assert M.nullspace()==[]

# Independently expand generic rank-one H=a tensor n and compare.
H=(p*r,p*s,q*r,q*s)
polys=[Poly(expand((Matrix([H]).reshape(1,4)*hessian(m,x)*Matrix(H))[0]),
            *(x+(p,q,r,s))) for m in monomials]
allterms=sorted(set(t for poly in polys for t,_ in poly.terms()))
C=Matrix([[poly.coeff_monomial(term) for poly in polys] for term in allterms])
assert C.shape==(36,20)
assert C.rank()==20

print('PASS: 20 homogeneous cubic coefficients')
print('PASS: six rank-one test directions produce a 24x20 matrix of rank 20')
print('PASS: generic rank-one polynomial identity has 36 independent rows, rank 20')
print('THEOREM: global rank-one-convex polynomial degree <= 3 is degree <= 2')
print('COMBINE with Fourier/Plancherel quadratic quasiconvexity: all such P are quasiconvex')
print('NOT A PROOF of the unrestricted Morrey conjecture')
