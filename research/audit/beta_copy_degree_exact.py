#!/usr/bin/env python3
"""Exact bounded-degree fake-law certificates, NOT compatible gradient witnesses.
Default: reconstruct rational weights from the saved LP bases, no optimizer.
Optional --discover: run finite LPs to rediscover bases (SciPy + NumPy).
"""
from fractions import Fraction as Q
from itertools import product
import sys
import sympy as s

# Centered diagonal coordinates, so the base is (0,0) (matrix I before translation).
nu = [(Q(1,4),-3,-3),(Q(3,8),3,-1),(Q(3,8),-1,3)]
a = Q(12,83)
def sig(k):
    uniform = (Q(1,2)**(k+1)-Q(-1,2)**(k+1))/(k+1)
    return a*uniform+(1-a)*(Q(28,29)*Q(-1,2)**k+Q(1,29)*14**k)
def mom(i,j):
    return sum(w*Q(x)**i*Q(y)**j for w,x,y in nu)
assert sig(0)==1 and sig(1)==0 and sig(2)==6
assert [mom(i,j) for i,j in [(0,0),(1,0),(0,1),(1,1),(2,0),(0,2)]]==[1,0,0,0,6,6]
assert a/Q(12)+(1-a)*7==6

BASES={
2:'0,10,1/2;1,23/2,15/4',
4:'0,-1,-5/4;0,1,5/4;0,7/2,-1/2;0,10,1/2;0,21/2,-5/4;1,-3,2;1,-2,6;1,0,13/4;1,3/4,-3;1,5/2,11;1,11/4,15/4',
6:'0,-1,-5/4;0,1,5/4;0,3/2,5/4;0,7/2,-1/2;0,4,-1/2;0,9/2,11;0,7,27/2;0,15/2,-11/4;0,8,3/4;0,10,1/2;0,21/2,-5/4;1,-11/4,3/2;1,-9/4,1/4;1,-7/4,23/2;1,-1,8;1,-3/4,21/2;1,-1/2,-5/4;1,-1/4,15/2;1,0,13/4;1,2,0;1,5/2,11;1,13,7;1,13,19/2;1,14,11/2',
8:'0,-3/2,-11/4;0,0,-3/4;0,3/2,5/4;0,7/4,-1;0,13/4,14;0,15/4,27/2;0,4,-1/2;0,9/2,5/2;0,13/2,-5/4;0,13/2,3/4;0,8,3/4;0,17/2,-5/4;0,9,14;0,21/2,-5/4;0,23/2,0;0,12,14;0,13,14;0,27/2,0;0,27/2,5/4;1,-3,-5/2;1,-9/4,1/4;1,-7/4,7/2;1,-5/4,5;1,-5/4,25/2;1,-3/4,3/4;1,-3/4,21/2;1,-1/4,-1/2;1,-1/4,15/2;1,0,5/4;1,0,13/4;1,1/4,25/2;1,1/2,12;1,5/4,6;1,2,0;1,9/4,3/4;1,21/2,14;1,25/2,14;1,13,19/2;1,14,13/4;1,14,11/2;1,14,10'
}

def monomials(d):
    return [(i,j) for i in range(d+1) for j in range(d+1-i) if i>=2 or j>=2]
def deriv(i,j,k,x,y):
    # evaluate derivatives in coordinates scaled by 14
    x,y=x/14,y/14
    if k==0:return i*(i-1)*x**(i-2)*y**j if i>=2 else Q(0)
    return j*(j-1)*x**i*y**(j-2) if j>=2 else Q(0)
def moment(i,j,t):
    return ((1-t)*sig(i)*sig(j)+t*mom(i,j))/14**(i+j)
def parse(st):
    return [(int(k),Q(x),Q(y)) for k,x,y in (v.split(',') for v in st.split(';'))]
def verify(d,t,cols):
    mons=monomials(d)
    A=s.Matrix([[deriv(i,j,*c) for c in cols] for i,j in mons]);rhs=s.Matrix([moment(i,j,t) for i,j in mons])
    weights,params=A.gauss_jordan_solve(rhs)
    assert len(params)==0 and A*weights==rhs and min(weights)>0
    for i in range(d+1):
        for j in range(d+1-i):
            left=moment(i,j,t)-(1 if i==j==0 else 0)
            assert left==sum(w*deriv(i,j,*c) for w,c in zip(weights,cols))
    return len(weights),min(float(w) for w in weights)

# Explicit rational estimate for arbitrary d, from the inverse monomial Gram matrix.
def analytic_t(d):
    assert d>=2
    n=d-2
    G=s.Matrix(n+1,n+1,lambda i,j:0 if (i+j)%2 else s.Rational(2,i+j+1))
    Ginv=G.inv()
    r=[sum(abs(Ginv[i,j]) for j in range(n+1)) for i in range(n+1)]
    Cx=Cy=s.Integer(0)
    for i,j in monomials(d):
        m=abs(mom(i,j)*4**(i+j))
        if i>=2:Cx+=m*r[i-2]*r[j]/(i*(i-1))
        else:Cy+=m*r[i]*r[j-2]/(j*(j-1))
    gamma=s.Rational(12,83)**2/64
    return gamma/(gamma+max(Cx,Cy))

def discover(d):
    import numpy as np
    from scipy.optimize import linprog
    nodes=sorted(set([Q(i,4) for i in range(-12,17)]+[Q(i,2) for i in range(9,29)]+[Q(-1,2),Q(14)]))
    cols=[(k,x,y) for k in range(2) for x,y in product(nodes,repeat=2)]
    mons=monomials(d)
    A=np.array([[float(deriv(i,j,*c)) for c in cols] for i,j in mons])
    rhs=np.array([float(moment(i,j,Q(1,16))) for i,j in mons])
    sc=np.maximum(np.abs(np.array([float(moment(i,j,Q(0))) for i,j in mons])),1e-7)
    obj=np.random.default_rng(24).random(len(cols))
    out=linprog(obj,A_eq=A/sc[:,None],b_eq=rhs/sc,bounds=(0,None),method='highs',options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
    assert out.success,out.message
    return [cols[k] for k in np.flatnonzero(out.x>1e-15)]

for d in (2,4,6,8):
    nodes=discover(d) if '--discover' in sys.argv else parse(BASES[d])
    count,small=verify(d,Q(1,16),nodes)
    print(f'degree {d}: exact positive weights={count}, min weight={small:.6g}, t=1/16; analytic sufficient t≈{float(analytic_t(d)):.4g}')

# Globally C11 RC discriminator with a quadratic exterior; all witness values exact.
def phi(x):
    x=Q(x); delta=Q(1,4)
    return Q(0) if x<=-delta else x if x>=delta else (x+delta)**2/(4*delta)
def fdiag(x,y):return phi(x)*phi(y)
assert sum(w*fdiag(1+x,1+y) for w,x,y in nu)-fdiag(1,1)==-Q(13,16)
assert phi(Q(1,2))==Q(1,2) and phi(15)==15
r0,R=32,64
B0,G0,H0=2*(R+1)**2,2*(R+1),2*(R+1)+1
k=Q(B0+3,R*R-r0*r0)
M=max(H0,2*k)+(G0+2*k*R)**2/2
assert 2*15**2<r0*r0 and k*(R*R-r0*r0)==B0+3
print('Global derivative-Lipschitz bound M=',M,'strict artificial normalized gap at t=1/16:',-Q(13,16)*Q(1,16)/(12*M))
# K_r(X-rI) = (s-r)_+ (r-det/s), a verified QC test (not polynomial).
def K(x,y,r):
    x,y=Q(x-r),Q(y-r);sz=max(abs(x),abs(y))
    return max(sz-r,0)*(r-(x*y/sz if sz else 0))
assert K(1,1,16)==0 and K(Q(1,2),15,16)==0
assert sum(w*K(1+x,1+y,16) for w,x,y in nu)==-1
print('Verified-L discriminator: exact Jensen gap -1/16 for the fake mixture, zero on the positive product component.')
print('No actual negative gradient witness or self-contraction certificate.')
