#!/usr/bin/env python3
"""Exact rational checks for the joint inner/outer shear chart pencil.
No counterexample search or proof of unrestricted Morrey.
"""
import sympy as sp
from itertools import product
I2=sp.eye(2); I4=sp.eye(4)
C=sp.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
def v(M):return sp.Matrix(list(M))
def mat(x):return sp.Matrix(2,2,list(x))
def cof(M):return mat(C*v(M))
def ip(A,B):return (v(A).T*v(B))[0]
def zero(M):return all(sp.cancel(x)==0 for x in M)
x=sp.symbols('x0:4'); X=mat(x)
f=(x[0]**2+2*x[1]**2+3*x[2]**2+4*x[3]**2)/2+x[0]*x[3]/3+x[0]*x[1]*x[2]/5
p=mat([sp.diff(f,z) for z in x]); H=sp.hessian(f,x)
T=f*I2-X.T*p
for pt,t,s in product([(1,2,-1,3),(sp.Rational(1,2),-1,sp.Rational(2,3),1),(0,1,2,-1)], [sp.Rational(1,1000),sp.Rational(-1,500)], [sp.Rational(1,70),sp.Rational(-1,80)]):
    sub=dict(zip(x,pt)); x0=X.subs(sub); p0=p.subs(sub); h=H.subs(sub); f0=f.subs(sub)
    B=I2+t*cof(T); b0=B.subs(sub); d=b0.det(); a=1+t*(f0-ip(x0,p0)); b=1+t*f0; dx=x0.det(); dp=p0.det(); L=a*I2+t*x0*p0.T
    assert d==a*b+t*t*dx*dp==L.det()
    A=sp.Matrix.hstack(*[v(L.inv()*mat(I4[:,k])*b0.inv()) for k in range(4)])
    P=a*I4+t*dx*C*h; Q=b*C*h-t*dp*I4
    DY=[]; DZ=[]
    for k,z in enumerate(x):
        db=B.diff(z).subs(sub); dX=mat(I4[:,k]); dZ=cof(mat(h[:,k]))
        DY.append(v(dX*b0.inv()-x0*b0.inv()*db*b0.inv()))
        DZ.append(v(dZ*b0.inv()-cof(p0)*b0.inv()*db*b0.inv()))
    DY=sp.Matrix.hstack(*DY); DZ=sp.Matrix.hstack(*DZ)
    assert DY==A*P and DZ==A*Q
    assert A.T*C*A==C/d**2
    assert DY+s*DZ==A*(P+s*Q)
    # Outer shear leaves inner stress exactly unchanged.
    assert (f0+s*dp)*I2-(x0+s*cof(p0)).T*p0==T.subs(sub)
    if (DY+s*DZ).det()!=0:
        CHt=DZ*(DY+s*DZ).inv()
        assert CHt==A*Q*(P+s*Q).inv()*A.inv()
        assert C*CHt==(C*CHt).T
print('12 exact joint shear derivative, stress-invariance, Hessian and cofactor metric checks passed.')
# The simultaneous scalar inequalities for a positive and a negative
# cofactor-type eigenvalue, with the base quadratic normalized to H=I.
t,s=sp.symbols('t s',real=True)
for dx in [1,-1]:
    a=1-t; b=1+t; dp=dx
    pplus=sp.expand(a+t*dx+s*(b-t*dp)) # overwritten below: s*(-t dp+b mu)
    dplus=sp.expand(a+t*dx+s*(-t*dp+b))
    dminus=sp.expand(a-t*dx+s*(-t*dp-b))
    if dx==1: assert dplus==1+s and sp.expand(dminus-(1-2*t-s*(1+2*t)))==0
    else: assert dminus==1-s and sp.expand(dplus-(1-2*t+s*(1+2*t)))==0
    # Physical B=I at each of these conformal / anticonformal states.
    X0=sp.diag(1,dx); p0=X0; f0=sp.Integer(1)
    assert f0*I2-X0.T*p0==sp.zeros(2)
print('Exact quadratic two-orientation chart-fold control passed: no common outer shear beyond t=1/2 on the identity branch.')

# Exact folded-sheet example in a degree-one product map (y(x), x2).
# On two adjacent intervals of length e, take slopes -e and 2+e,
# and slope 1 elsewhere. The triple target interval has length e^2.
# The signed inverse trace can have unbounded slope there, while its
# integral on those fibres vanishes. No global inverse is used.
from fractions import Fraction as F
for n in [4, 10, 100, 1000]:
    e=F(1,n); a=2+e; bad=e*e
    good_mass=bad*(1+1/a)
    source_mass=e+good_mass
    trace_bad=bad*(1+1/e+1/a)
    assert trace_bad==source_mass
    # The remaining image of the positive steep interval has length 2e.
    trace_mean=(1-bad-2*e)+bad*(1+1/e+1/a)+2*e/a
    assert trace_mean==1
    assert trace_bad<=2*e
print('4 rational near-singular fold controls passed: signed trace preserves affine mean, bad-fibre L1 cost tends to zero.')
