#!/usr/bin/env python3
"""Exact checks for product-metric Legendre dual normalization and beta comparison.

The LP is a finite control for the row-parameter elimination, NOT a
proof of Morrey or a search for an actual negative gradient witness.
"""
from fractions import Fraction as Q
from itertools import product
import sympy as sp
from scipy.optimize import linprog

C = sp.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
I = sp.eye(4)
k,l,c,b = sp.symbols('k l c b', positive=True)
D = k*l-1
K = sp.diag(k,k,l,l)
A = sp.diag(l,l,k,k)/D
B = sp.diag(1/(k+1),1/(k+1),1/(l+1),1/(l+1))
R = A-B
partner = sp.diag(l,l,k,k)
assert ((K+c*C)*(partner-c*C)-(k*l-c*c)*I).applyfunc(sp.simplify)==sp.zeros(4)
for sign in [-1,1]:
    assert ((K+sign*C)*(A-sign*C/D)-I).applyfunc(sp.simplify)==sp.zeros(4)
assert sp.simplify(R[0,0]*R[2,2]-1/D**2)==0
assert sp.simplify(R[0,0]-(l+1)/(D*(k+1)))==0
assert sp.simplify(R[2,2]-(k+1)/(D*(l+1)))==0
assert (A+2*b*R-B-(1+2*b)*R).applyfunc(sp.simplify)==sp.zeros(4)
for i,partner_i in [(0,2),(2,0)]:
    assert sp.simplify((1+2*b)*B[i,i]+B[i,i]**2/R[i,i] - (1+2*b*B[i,i]-B[partner_i,partner_i]))==0
print('Exact row-metric inverse, endpoint, Hessian normalization and Fenchel coefficient identities passed.')

# Arbitrary product metric: k1*k4=k2*k3=s>1, with all ki>0.
# Choose a parameterization giving exact positive products.
n=0
for k1,k2,s0 in product([Q(1,10),Q(1),Q(7)], [Q(1,7),Q(2),Q(5)], [Q(5,4),Q(3),Q(20)]):
    ks=[k1,k2,s0/k2,s0/k1]; dd=s0-1
    aa=[ks[3-i]/dd for i in range(4)]
    bb=[1/(x+1) for x in ks]
    rr=[x-y for x,y in zip(aa,bb)]
    assert min(rr)>0 and rr[0]*rr[3]==rr[1]*rr[2]==1/dd**2
    # R^{1/2} can be realized by constant invertible left/right maps.
    # R itself is a product of positive row and column metrics.
    row=[rr[0],rr[2]]; col=[Q(1),rr[1]/rr[0]]
    assert [x*y for x in row for y in col]==rr
    for beta in [Q(1,100),Q(1,8)]:
        a=1+2*beta
        coeff=[a*bb[i]+bb[i]**2/rr[i] for i in range(4)]
        assert all(coeff[i]==1+2*beta*bb[i]-bb[3-i] for i in range(4))
        # Isotropic formal covariance and q=0 pass EVEN the stronger
        # comparison with the quadratic optimized over arbitrary Y.
        assert sum(coeff)/4 == 1+(2*beta-1)*sum(bb)/4 < 1
        n+=1
print(n,'exact anisotropic product-metric controls passed (formal state, not a common-energy actual gradient witness).')

# Eliminate B1=1/(k+1), B2=1/(l+1): positive triangle B1+B2<1.
# For a linear objective, the closed triangle maximum is exactly the
# maximum of its three vertex values; LP runs are controls only.
cases=[(Q(1,8),Q(1,2),Q(0),Q(0)),
       (Q(1,8),Q(9,10),Q(0),Q(0)),
       (Q(1,20),Q(1,2),Q(1,10),Q(1,10)),
       (Q(1,20),Q(3,4),Q(1,2),Q(1,20)),
       (Q(1,100),Q(99,100),Q(0),Q(0))]
for beta,e1,v1,v2 in cases:
    a=1+2*beta; e2=1-e1
    c1=2*beta*e1-e2+v1/a
    c2=2*beta*e2-e1+v2/a
    exact=max(Q(0),c1,c2)
    res=linprog([-float(c1),-float(c2)], A_ub=[[1,1]], b_ub=[1], bounds=[(0,None),(0,None)], method='highs')
    assert res.success and abs(-res.fun-float(exact))<1e-9
    print('row control b=',beta,'E1=',e1,'V=',(v1,v2),'exact worst violation=',exact)
print('All five LP controls agree with exact triangle-vertex elimination.')
print('No universal beta self-contraction or genuine negative witness obtained.')
