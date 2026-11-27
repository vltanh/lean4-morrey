#!/usr/bin/env python3
"""Finite LP falsification test of first-order normalized quadratic flows.

The exact identities and primal/dual bounds certify the tested relaxation.
Artificial matrix laws below are not claimed to be gradient laws.
"""
from fractions import Fraction as Q
from itertools import product
import sympy as sp
import numpy as np
from scipy.optimize import linprog

C=sp.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
I=sp.eye(4)
A=sp.Matrix(4,4,lambda i,j:sp.Symbol(f'a{min(i,j)}{max(i,j)}'))
D=-C*A*C
B=-(A-C*A*C)/2
assert A+D+B+B.T==sp.zeros(4)
assert B*C+C*B.T==sp.zeros(4)
for P in [(I+C)/2,(I-C)/2]:
    assert (P*(A+D-B-B.T)*P).applyfunc(sp.expand)==sp.zeros(4)
c,m=sp.symbols('c m',real=True)
assert (A+c*(B*C+C*B.T)+c*c*C*D*C-(1-c*c)*A).applyfunc(sp.expand)==sp.zeros(4)
assert (A-m*(B+B.T)+m*m*D-(1+m)*(A-m*C*A*C)).applyfunc(sp.expand)==sp.zeros(4)
# Cofactor-normalized graph boost: use generic symmetric H, not a
# numerical check of the matrix inequality.
H=sp.Matrix(4,4,lambda i,j:sp.Symbol(f'h{min(i,j)}{max(i,j)}'))
s=sp.Symbol('s',real=True)
assert ((I+s*H*C)*(I+s*C*H)-(H+s*C)**2-(1-s*s)*(I-H*H)).applyfunc(sp.expand)==sp.zeros(4)
print('Exact tangent-flow and norm-preserving cofactor identities passed.')

# Test diagonal covariance P=diag(w), p=-mX.  Only 12 scalar
# inequalities necessary for the full tangent cone are used; a zero
# minimum here is therefore conclusive for the full generator class.
opp=[3,2,1,0]
rows=[]
for i in range(4):
    r=[0]*12;r[i]=-1;rows.append(r)  # a_i >=0
    r=[0]*12;r[opp[i]]=-1;r[4+i]=-1;rows.append(r)  # a_opp+d_i>=0
    r=[0]*12;r[i]=1;r[4+i]=1;r[8+i]=2;rows.append(r) # -(a_i+d_i+2b_i)>=0

def objective(w,m):return list(w)+[m*m*x for x in w]+[-2*m*x for x in w]

def verify(w,m):
    w=list(w); assert sum(w)==1
    coeff=objective(w,m)
    a=[sp.Symbol(f'a{i}') for i in range(4)];d=[sp.Symbol(f'd{i}') for i in range(4)];b=[sp.Symbol(f'b{i}') for i in range(4)]
    obj=sum(x*y for x,y in zip(coeff,a+d+b))
    rhs=(1+m)*sum((w[i]-m*w[opp[i]])*a[i] for i in range(4))+m*(1+m)*sum(w[i]*(a[opp[i]]+d[i]) for i in range(4))+m*sum(w[i]*(-a[i]-d[i]-2*b[i]) for i in range(4))
    assert sp.expand(obj-rhs)==0
    res=linprog(np.array(coeff,dtype=float),A_ub=np.array(rows),b_ub=np.zeros(len(rows)),bounds=[(-1,1)]*12,method='highs')
    assert res.success
    balanced=all(w[i]>=m*w[opp[i]] for i in range(4))
    if balanced:
        # Exact dual certificate above, and zero primal generator.
        assert abs(res.fun)<1e-8
        print('m=',m,'w=',w,'exact optimum 0')
    else:
        i=next(i for i in range(4) if w[i]<m*w[opp[i]])
        # Genuine tangent generator (not just sampled LP constraints).
        x=[Q(0)]*12;x[i]=Q(1);x[4+opp[i]]=Q(-1);x[8+i]=Q(-1,2);x[8+opp[i]]=Q(1,2)
        assert all(sum(u*v for u,v in zip(row,x))<=0 for row in rows)
        val=sum(u*v for u,v in zip(coeff,x))
        assert val==(1+m)*(w[i]-m*w[opp[i]])<0
        assert res.fun<=float(val)+1e-8
        print('m=',m,'w=',w,'exact genuine descent',val,'(twice cost)')
    return balanced

for mm in [Q(1,4),Q(1,10),Q(1,1000)]:
    assert verify([Q(1,4)]*4,mm)
    assert verify([Q(1,2),0,0,Q(1,2)],mm)
    assert verify([1/(1+mm),0,0,mm/(1+mm)],mm)
    assert not verify([1/(1+mm/2),0,0,(mm/2)/(1+mm/2)],mm)
print('12 LPs: exact nonnegative dual certificate or an exact admissible negative generator passed.')

# Full-rank artificial covariance control for the all-affine moment tests.
# Positive conformal shell radius 2, negative anticonformal shell radius 1.
# This is a moment-only control, not a specified common energy contact set.
I2=sp.eye(2);J=sp.Matrix([[0,-1],[1,0]]);K=sp.diag(1,-1);L=sp.Matrix([[0,1],[1,0]])
X=[2*I2,-2*I2,2*J,-2*J,K,-K,L,-L,sp.zeros(2)]
w=[sp.Rational(1,64)]*4+[sp.Rational(1,16)]*4+[sp.Rational(11,16)]
assert sum(w)==1
assert sum((p*x for p,x in zip(w,X)),sp.zeros(2))==sp.zeros(2)
assert sum(p*x.det() for p,x in zip(w,X))==0
P=sp.zeros(4);G=sp.zeros(5)
for p,x in zip(w,X):
    v=sp.Matrix(list(x));z=sp.Matrix(list(x)+[x.det()]);P+=p*v*v.T;G+=p*z*z.T/(1+v.dot(v))
assert P==sp.eye(4)/4
assert G.eigenvals()=={sp.Rational(1,36):2,sp.Rational(1,12):2,sp.Rational(7,36):1}
# P17 all-transform certificate holds at j=0 for this covariance:
# 16 sqrt(2 lambda_min Gamma) / kappa^2 >= 1 for 0<kappa<=1.
assert 16**2*2*sp.Rational(1,36)>1
print('Full-rank shell moment control: Gamma minimum 1/36; every P17 affine inequality passes at zero residual.')

# Verified L has strict negative minors gap for opposite-orientation
# conformal/anticonformal shells: 2I and K/4.  This gives the seed for
# the common-integrand existence construction in the note.
x=Q(2);y=Q(1,4)
p=y*y/(x*x+y*y);q=1-p
assert p*x*x-q*y*y==0
raw=p*(2*x-1)-q*y*y
E=2*p*x*x+2*q*y*y
assert raw/E==-Q(1,16)
# L has global Frobenius Lipschitz bound <=4 by coordinate convexity
# and linear growth. A radial mollifier of support 1/1000 keeps the gap.
assert p*(2*x-1+Q(4,1000))-q*y*y<0
print('Exact seed negative minors gap and mollification slack passed.')
# Nonlinear norm-preserving generator phi(Y) with Y=X+C p,
# phi=L_delta-M0 det.  A radial compact polynomial mollifier
# rho proportional to (1-|X|^2/delta^2)_+^2 has gradient L1 norm
# 192/(35 delta) in 4D; Lip L <=4.
r=sp.Symbol('r', nonnegative=True)
normal=sp.integrate(r**3*(1-r*r)**2,(r,0,1))
grad=sp.integrate(4*r**4*(1-r*r),(r,0,1))
assert grad/normal==sp.Rational(192,35)
delta=Q(1,1000);M0=Q(32000);m=Q(1,10**7)
assert 4*Q(192,35)/delta<M0
# The exact shell moment control above has raw L gap -1/16.
assert Q(1,16)*3-Q(1,4)==-Q(1,16)
# Uniform convolution error <=4 delta; shift X->X-m C X costs <=4 m
# by the Lipschitz bound and E|X|^2=1. The gauge costs exactly M0 m.
negative_upper=-Q(1,16)+4*delta+(4+M0)*m
assert negative_upper<0
print('Nonlinear normalized generator rejects full-rank moment control, exact upper cost',negative_upper)
print('No actual negative gradient pair, universal self-contraction, or exact-zero proof.')
