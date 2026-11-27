#!/usr/bin/env python3
"""Exact quadratic, cofactor and transport-bound controls; not a Morrey proof."""
from fractions import Fraction as Q
from itertools import combinations
from math import factorial
import sympy as s

J = s.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
I = s.eye(4)
assert J.T == J and J*J == I
x = s.Matrix(s.symbols('a b c d'))
y = s.Matrix(s.symbols('y0:4'))

def detq(v):
    return (v.T*J*v)[0]/2

assert s.expand(detq(x) - (x[0]*x[3]-x[1]*x[2])) == 0
assert s.expand(detq(J*x)-detq(x)) == 0

def is_psd(A):
    assert A == A.T
    return all(A.extract(k,k).det() >= 0
               for n in range(1,A.rows+1)
               for k in combinations(range(A.rows),n))

def shear_hessian(H,t):
    return H*(I+t*J*H).inv()

def quadratic_transform(H,p,c,t,z):
    X=(I+t*J*H).inv()*(z-t*J*p)
    P=H*X+p
    G=(X.T*H*X)[0]/2+(p.T*X)[0]+c+t*detq(P)
    return s.expand(G),P

K0=s.Matrix([[1,2,0,1],[2,0,-1,0],[0,1,1,2],[1,-1,0,0]])
K=K0.T*K0/32
m=s.Rational(1,5)
c=s.Rational(-2,5)
H0=m*I+c*J
H=H0+K
p=s.Matrix([s.Rational(1,3),s.Rational(-1,4),2,0])
for t in [s.Rational(1,8),s.Rational(-1,7),s.Rational(1,3)]:
    # Verify exact algebra on a Hessian containing a positive part and a
    # possibly indefinite determinant part. The tested pencils are invertible.
    L=shear_hessian(H,t)
    L0=shear_hessian(H0,t)
    assert L==L.T and is_psd(L-L0)
    den=(1+t*c)**2-t*t*m*m
    assert L0==m/den*I+(c+t*(c*c-m*m))/den*J
    assert shear_hessian(L,-t)==H
    G,P=quadratic_transform(H,p,s.Rational(3,7),t,y)
    assert all(s.expand(s.diff(G,v)-w)==0 for v,w in zip(y,P))
    gy=s.Matrix([s.diff(G,v) for v in y])
    Gback,Pback=quadratic_transform(s.hessian(G,y),gy.subs(dict.fromkeys(y,0)),G.subs(dict.fromkeys(y,0)),-t,x)
    F=(x.T*H*x)[0]/2+(p.T*x)[0]+s.Rational(3,7)
    assert s.expand(Gback-F)==0
    # Monotonicity at fixed matrix argument is stronger than eigenvalue
    # comparison at the same original X. Exact order control for quadratics.
    F0,_=quadratic_transform(H0,p,s.Rational(3,7),t,y)
    D=s.expand(G-F0);DH=s.hessian(D,y)
    assert is_psd(DH)
    # Both transformed quadratics agree at the common image of x=0.
    y0=t*J*p
    assert D.subs(dict(zip(y,y0)))==0
    assert all(s.diff(D,v).subs(dict(zip(y,y0)))==0 for v in y)

# Verify the cofactor switches Fourier gradient and solenoidal directions.
R=s.Matrix([[0,-1],[1,0]])
for a in [s.Matrix([1,2]),s.Matrix([2,-3])]:
    for k in [s.Matrix([1,0]),s.Matrix([2,3]),s.Matrix([-3,1])]:
        X=a*k.T
        v=s.Matrix(list(X))
        assert J*v==s.Matrix(list((R*a)*(R*k).T))
        assert (R*k).dot(k)==0
        assert detq(v)==0

# Rank-one curvature lower bound for the baseline pencil and the simple
# exact inequality behind exp(7/12) < 9/5.
a=Q(7,12)
upper=sum(a**k/factorial(k) for k in range(4)) + a**4/factorial(4)/(1-a/5)
assert upper == Q(3938881,2198016) < Q(9,5)
assert Q(1,50)<Q(1,49)
assert Q(3,7)*Q(25,1058)==Q(75,7406)>Q(1,100)
assert -Q(1,2)+Q(1,200)==-Q(99,200)
assert Q(99,199)<Q(1,2)
print('Exact cofactor, transformed quadratic derivative, inverse, PSD/order and Fourier controls passed (3 shear parameters, 6 Fourier modes).')
print('Exact transport and universal-margin constants passed; no unrestricted positivity proof or numerical search.')
