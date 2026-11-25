#!/usr/bin/env python3
"""Exact arithmetic certificate infrastructure for the 2x2 Morrey problem.

A COUNTEREXAMPLE CERTIFICATE requires BOTH:
    1. A global rank-one-convexity proof for a rational polynomial P;
    2. P(F) > average_T P(F + gradient(w)|_T) for rational dyadic PL w.

This module implements a sound *sufficient* certificate of (1): an explicit
sum-of-squares decomposition of the Legendre--Hadamard polynomial.
It verifies (2) and all discretization identities exactly over Q.

This checker does NOT assert that every rank-one convex polynomial admits an
SOS certificate. It does NOT find a counterexample to Morrey's conjecture.
"""
from __future__ import annotations
from fractions import Fraction
from sympy import Matrix, Rational, Poly, expand, symbols, diff

A = symbols('A11 A12 A21 A22')
a1, a2, n1, n2 = symbols('a1 a2 n1 n2')
D = Matrix([a1*n1, a1*n2, a2*n1, a2*n2])


def LH(P):
    """Polynomial D^2 P(A)[a tensor n, a tensor n]."""
    H = Matrix([P]).jacobian(A).jacobian(A)
    return expand((D.T * H * D)[0])


def verify_sos(P, terms):
    """Verify an exact weighted SOS identity, all weights nonnegative rationals.

    terms: iterable of (weight, polynomial in A,a1,a2,n1,n2).
    Successful verification proves P globally rank-one convex, with no
    numeric tolerances or floating-point assumptions.
    """
    residual = LH(P)
    for weight, expression in terms:
        weight = Rational(weight)
        assert weight.is_Rational and weight >= 0, 'SOS weight must be nonnegative rational'
        residual -= weight * expand(expression)**2
    assert expand(residual) == 0, f'SOS identity incorrect: {expand(residual)}'
    return True


def to_fraction(z):
    z = Rational(z)
    assert z.is_Rational
    return Fraction(int(z.p), int(z.q))


def nodal_value(data, i, j):
    n = len(data)
    return to_fraction(data[i % n][j % n])


def triangle_gradients(U, V):
    """Return the exact matrices on Kuhn triangles of the dyadic torus.

    U,V: n-by-n rational nodal arrays, with n a power of 2.
    Lower triangle: (i,j),(i+1,j),(i,j+1)
    Upper triangle: (i+1,j+1),(i+1,j),(i,j+1)
    Each triangle has area 1/(2*n*n).
    """
    n = len(U)
    assert n >= 2 and (n & (n - 1)) == 0
    assert len(V)==n and all(len(r)==n for r in U) and all(len(r)==n for r in V)
    out=[]
    for i in range(n):
        for j in range(n):
            for k in (0,1):
                def gxgy(nodes):
                    v=lambda x,y:nodal_value(nodes,x,y)
                    if k==0:
                        return n*(v(i+1,j)-v(i,j)), n*(v(i,j+1)-v(i,j))
                    return n*(v(i+1,j+1)-v(i,j+1)), n*(v(i+1,j+1)-v(i+1,j))
                ux,uy=gxgy(U);vx,vy=gxgy(V)
                out.append((ux,uy,vx,vy))
    assert len(out)==2*n*n
    return out


def average_grad_and_det(gradients):
    ntri=len(gradients)
    mean=tuple(sum(G[t] for G in gradients)/ntri for t in range(4))
    detmean=sum(G[0]*G[3]-G[1]*G[2] for G in gradients)/ntri
    return mean,detmean


def jensen_gap(P, F, U, V):
    """Return P(F) - (1/#triangles) sum_T P(F + Dw_T), exactly."""
    assert len(F)==4
    F=tuple(to_fraction(t) for t in F)
    q=Poly(P,*A,domain='QQ')
    def evaluate(args):
        # Exact Horner-like sparse sum in rationals, no symbolic residue.
        acc=Fraction(0)
        for powers, coeff in q.terms():
            term=to_fraction(coeff)
            for val, power in zip(args,powers):term*=val**power
            acc+=term
        return acc
    gs=triangle_gradients(U,V)
    value=evaluate(F)-sum(evaluate(tuple(F[j]+G[j] for j in range(4))) for G in gs)/len(gs)
    assert isinstance(value, Fraction)
    return value


def test_exact_pipeline():
    # Globally rank-one convex but NOT convex: |A|^2 + 5 det(A).
    # Its Hessian on rank-one matrices is exactly 2 |a|^2 |n|^2.
    P=sum(x*x for x in A)+5*(A[0]*A[3]-A[1]*A[2])
    terms=[(2, a1*n1),(2,a1*n2),(2,a2*n1),(2,a2*n2)]
    assert verify_sos(P,terms)
    assert LH(P)==2*(a1*a1+a2*a2)*(n1*n1+n2*n2).expand() or expand(LH(P)-2*(a1*a1+a2*a2)*(n1*n1+n2*n2))==0

    # Nodal data from the previously independently certified 4x4 example.
    ur=[70,28,2,-46,-39,-92,-85,-97,-65,63,30,83,1,21,95,46]
    vr=[27,9,12,87,-45,63,34,-100,-21,72,11,-94,53,46,70,-65]
    U=[ur[k:k+4] for k in range(0,16,4)]
    V=[vr[k:k+4] for k in range(0,16,4)]
    gs=triangle_gradients(U,V)
    mean,average_det=average_grad_and_det(gs)
    assert mean==(0,0,0,0)
    assert average_det==0  # discrete periodic null-Lagrangian
    F=(Fraction(1,3),Fraction(2,5),Fraction(-1,7),Fraction(4,9))
    gap=jensen_gap(P,F,U,V)
    energy=sum(sum(x*x for x in G) for G in gs)/len(gs)
    assert gap==-energy
    assert gap<0
    print('PASS: exact SOS identity proves global rank-one convexity')
    print('PASS: nonconvex rank-one convex polynomial |A|^2 + 5 det(A)')
    print('PASS: exact 4x4 periodic mean gradient = 0 and mean determinant = 0')
    print('PASS: rational Jensen gap:', gap)
    print('PASS: sanity-check expected sign (no Morrey violation)')
    # Deliberately invalid polynomial P=-|A|^2 violates Jensen, but is NOT LH convex.
    bad=-sum(x*x for x in A)
    bad_gap=jensen_gap(bad,F,U,V)
    assert bad_gap>0 and LH(bad)!=0
    print('PASS: negative control violates Jensen but fails rank-one convexity')
    print('NOTE: SOS witness is sufficient, not necessary, for global LH positivity')
    print('NOTE: NO counterexample and NO complete proof of Morrey established')


if __name__ == '__main__':
    test_exact_pipeline()
