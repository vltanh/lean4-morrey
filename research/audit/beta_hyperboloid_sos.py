#!/usr/bin/env python3
"""Discover and verify a parameter-uniform near-hyperboloid certificate.

The floating LP only discovers the coefficients.  The symbolic/rational
checks certify the continuum identities used in the accompanying proof.
The adaptive moment tests are necessary for actual gradients, not sufficient
for unrestricted gradient realizability.  No zero-beta proof is claimed.
"""
from fractions import Fraction as Q
from itertools import product
import hashlib
import pathlib
import sympy as sp
import numpy as np
from scipy.optimize import linprog

# A = 4/kappa >= 4. Seek mu(A), B(A) in the basis (A-4)^i, i=0,1,2.
t = sp.symbols('t', nonnegative=True)
A = 4+t
v = sp.symbols('u0:3')+sp.symbols('b0:3')
mu = sum(v[i]*t**i for i in range(3))
B = sum(v[3+i]*t**i for i in range(3))
# Nonnegative coefficients suffice on the entire half-line t>=0.
# These are the budgets in the local polynomial square decompositions.
budgets = [mu-A*A, B-A+2-mu, B-A-2, B-A+2-4*A, mu-4]
rows=[]; rhs=[]
for poly in budgets:
    p=sp.Poly(poly,t)
    for i in range(3):
        c=p.nth(i)
        row=[sp.diff(c,x) for x in v]
        constant=c.subs(dict.fromkeys(v,0))
        rows.append([-float(a) for a in row]);rhs.append(float(constant))
res=linprog(np.ones(len(v)),A_ub=rows,b_ub=rhs,bounds=[(0,None)]*len(v),method='highs')
assert res.success, res.message
rational=tuple(Q(float(x)).limit_denominator(100000) for x in res.x)
assert rational==(16,8,1,18,9,1)
sub={x:sp.Rational(y.numerator,y.denominator) for x,y in zip(v,rational)}
for p in budgets:
    assert all(c>=0 for c in sp.Poly(p.subs(sub),t).all_coeffs())
assert sp.expand(mu.subs(sub)-A*A)==0
assert sp.expand(B.subs(sub)-(A*A+A-2))==0
print('LP:',res.message,'; objective',res.fun)
print('Exact coefficient vector in basis (A-4)^i:',rational)
print('All 15 rational coefficient inequalities hold on A>=4.')

# Verify pointwise certificate. For symmetric part of Z=I-Y,
# r=trace(Z)-2, d=det(sym Z), k=|skew Y|^2, e=|d-1|.
# The lower bound h/M >= kappa*E/2-|det Y| and the triangle inequality
# |det Y| <= e+|r|+k/2 give the following residual.
a,r,d,k=sp.symbols('A r d k',real=True)
E=r*r+2*r+2*(1-d)+k
mu=a*a; B=mu+a-2; lam=a-2; C=a/2-1
# Use A*kappa=4 to substitute for A*h/M.
def residual(absr,e,G):
    return sp.expand(2*E-a*(e+absr+k/2)-E+B*e+C*k+lam*r-mu*G)
z,e=sp.symbols('z e',nonnegative=True)
# Positive semidefinite, r>=0: both determinant signs relative to 1.
assert sp.expand(residual(r,1-d,0).subs(d,1-e)-(r*r+mu*e))==0
assert sp.expand(residual(r,d-1,0).subs(d,1+e)-(r*r+(mu-4)*e))==0
# PSD with r<0: z=-r, d<=1, and 2e-z>=0.
assert sp.expand(residual(-r,1-d,0).subs({r:-z,d:1-e})-(z*z+2*a*(2*e-z)+(mu-4*a)*e))==0
# Non-PSD: G=-d. All r signs and both d<=1, d>=1.
assert sp.expand(residual(r,1-d,-d)-(r*r+mu))==0
assert sp.expand(residual(r,d-1,-d).subs(d,1+e)-(r*r+mu+(2*mu-4)*e))==0
assert sp.expand(residual(-r,1-d,-d).subs(r,-z)-(z-a)**2)==0
assert sp.expand(residual(-r,d-1,-d).subs({r:-z,d:1+e})-((z-a)**2+(2*mu-4)*e))==0
# Exact elementary PSD trace/determinant certificate: 2e-z=s-2d>=0
# if the eigenvalues p,q are nonnegative and s=p+q<=2.
p,q=sp.symbols('p q',real=True)
s=p+q
assert sp.expand(s-2*p*q-(s*(2-s)/2+(p-q)**2/2))==0
assert sp.expand(C+B/2-(a*a/2+a-2))==0
print('Seven exact local square identities, PSD trace identity and skew coefficient passed.')

# Rational controls for the old traps, including anisotropy, arbitrary
# amplitude and dilution.  The exact moment condition is evaluated at a
# single normalization; the theorem holds at EVERY invertible P,Q.
traps=[([(-Q(1),Q(1,2)),(Q(1,2),-Q(1)),(Q(2),Q(2))], [Q(4,9),Q(4,9),Q(1,9)]),
       ([(-Q(5),Q(5,6)),(Q(5,6),-Q(5)),(Q(2),Q(2))], [Q(12,49),Q(12,49),Q(25,49)])]

def moments(X,w):
    assert sum(w)==1
    assert sum(a*x for (x,y),a in zip(X,w))==sum(a*y for (x,y),a in zip(X,w))==0
    assert sum(a*x*y for (x,y),a in zip(X,w))==0
    return sum(a*(x*x+y*y) for (x,y),a in zip(X,w))

controls=0
for (pts,w0),scale,dil in product(traps,[Q(1),Q(3),Q(1000)],[Q(1,2),Q(1,10),Q(1,100)]):
    E0=moments(pts,w0)
    X=[(scale*x,scale*dil*y) for x,y in pts]
    E=moments(X,w0)
    wt=1/E
    w=[wt*v for v in w0]+[1-wt]
    X=X+[(Q(0),Q(0))]
    assert moments(X,w)==1
    Y=[(x/scale,y/(scale*dil)) for x,y in X]
    EY=moments(Y,w)
    assert EY==wt*E0>0
    # Weighted determinant residual D_Y = detY - trY; zero exactly.
    cov_error=sum(a*(x*y-x-y)**2/(1+u*u+v*v)
                  for (x,y),(u,v),a in zip(Y,X,w))
    assert cov_error==0
    # At stabilized equality j=0 and skew=0, moment certificate says EY<=0.
    controls+=1
print(controls,'exact transformed/diluted trap laws rejected, without an amplitude assumption.')

# Near-critical mixtures. Choose finite rational eps sufficiently small
# for an explicit conservative margin in each transformed control.
# We use the old common-energy bounds (or still looser ones for trap 2).
# H <= L |X|^2/2 at all X, with L<=5/4, and H=0 on the trap.
# Thus j<=5 eps/8. Pick eps from bounds, no floating comparisons.
near=0
for (pts,w0),scale,dil in product(traps,[Q(1),Q(3),Q(1000)],[Q(1,2),Q(1,10),Q(1,100)]):
    X0=[(scale*x,scale*dil*y) for x,y in pts]
    wt=1/moments(X0,w0)
    w=[wt*v for v in w0]+[1-wt]; X=X0+[(Q(0),Q(0))]
    Y=[(x/scale,y/(scale*dil)) for x,y in X]
    EY0=moments(Y,w)
    # Conservative original LH margin, valid for both common energies
    # after normalization by sufficiently large Hessian bound. These
    # numbers are abstract margin bounds; smaller m only weakens test.
    b=Q(1,10**30)*dil*dil
    # pullback to Y: original transform has least singular value scale*dil.
    m=2*b*scale*scale*dil*dil
    M=Q(5,4)*scale*scale
    kap=m/M; AA=4/kap; BB=AA*AA+AA-2
    # Mixture with symmetric rank-one atoms ±diag(1,0). E_X remains one.
    # D_Y = ±1/scale there; weighted residual = eps/(2 scale^2).
    eps=min(Q(1,4), m*EY0/80, (EY0*scale/(16*BB))**2)
    W=[(1-eps)*v for v in w]+[eps/2,eps/2]
    X2=X+[(Q(1),Q(0)),(-Q(1),Q(0))]
    Y2=Y+[(1/scale,Q(0)),(-1/scale,Q(0))]
    assert moments(X2,W)==1
    EY=moments(Y2,W)
    R=sum(a*(x*y-x-y)**2/(1+u*u+v*v) for (x,y),(u,v),a in zip(Y2,X2,W))
    assert R==eps/(2*scale*scale)
    assert EY>=Q(3,4)*EY0
    # Certificate RHS <= 4j/m+B sqrt(2R). Check the root by squaring.
    assert 4*(Q(5,8)*eps)/m<=EY0/16
    assert BB*BB*2*R<=(EY0/16)**2
    assert EY>EY0/8
    near+=1
print(near,'exact near-critical nonblocked perturbations rejected using the weighted fourth-moment constraint.')
print('Scope: all-transform moment inequality and PC bounded-support gate; no unrestricted beta=0 result.')

# The entire affine detector depends on only the lifted covariance.
# Verify its coefficient formula for generic 2x2 left/right maps.
x=sp.Matrix(2,2,sp.symbols('x0:4'))
P=sp.Matrix(2,2,sp.symbols('p0:4')); Qr=sp.Matrix(2,2,sp.symbols('q0:4'))
Y=P*x*Qr
Z=sp.Matrix(list(x)+[x.det()])
coef=sp.Matrix(list(-(Qr*P).T)+[P.det()*Qr.det()])
assert sp.expand(Y.det()-sp.trace(Y)-(coef.T*Z)[0])==0
O=sp.Matrix.hstack(*[sp.Matrix(list(P*sp.Matrix(2,2,list(sp.eye(4)[:,i]))*Qr)) for i in range(4)])
assert (O*sp.Matrix(list(x))-sp.Matrix(list(Y))).applyfunc(sp.expand)==sp.zeros(4,1)
# The covariance-only PC compactness proof uses this rank-one-line
# exclusion: det^2 cannot have a nonzero second moment when the
# covariance lives in a rank-one line. Check the algebraic trap center.
for pts,weights in traps:
    Sigma=sp.zeros(5)
    for (xx,yy),w in zip(pts,weights):
        zz=sp.Matrix([xx,0,0,yy,xx*yy]);Sigma+=sp.Rational(w.numerator,w.denominator)*zz*zz.T
    assert Sigma*sp.Matrix([-1,0,0,-1,1])==sp.zeros(5,1)
    assert Sigma[:4,:4].trace()>0
    assert Sigma[4,4]>0
print('Exact generic affine coefficient identities and covariance-only trap relations passed.')
