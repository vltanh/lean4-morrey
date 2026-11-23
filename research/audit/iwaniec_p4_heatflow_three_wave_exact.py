#!/usr/bin/env python3
"""Exact three-wave periodic heatflow obstruction for F(A)=det(A)^2.

All integrals via cosine Fourier multiplication and rational coefficients.
No floating point, external libraries, or numerical sampling.
"""
from fractions import Fraction as Q
from collections import defaultdict
K=((1,-1),(2,2),(1,3))
a=(-2,3,2)
b=(0,-1,-3)
A=((8,-2),(-18,-17))
lam=tuple(i*i+j*j for i,j in K)
zero=(0,0)
def can(k):
    return k if (k[0]>0 or (k[0]==0 and k[1]>=0)) else (-k[0],-k[1])
def series(terms):
    out=defaultdict(Q)
    for k,v in terms:
        out[can(k)]+=Q(v)
    return {k:v for k,v in out.items() if v}
def add(x,y,s=1):
    return series(list(x.items())+[(k,Q(s)*v) for k,v in y.items()])
def mul(x,y):
    terms=[]
    for (i,j),u in x.items():
        for (k,l),v in y.items():
            terms.append(((i+k,j+l),u*v/Q(2)))
            terms.append(((i-k,j-l),u*v/Q(2)))
    return series(terms)
def mode(row,col,time=False):
    terms=[(zero,A[row][col])] if not time else []
    for j,k in enumerate(K):
        v=(a if row==0 else b)[j]*k[col]
        if time:v*=-lam[j]
        terms.append((k,v))
    return series(terms)
g11,g12,g21,g22=(mode(0,0),mode(0,1),mode(1,0),mode(1,1))
t11,t12,t21,t22=(mode(0,0,True),mode(0,1,True),mode(1,0,True),mode(1,1,True))
J=add(mul(g11,g22),mul(g12,g21),-1)
Jt=add(add(mul(t11,g22),mul(g11,t22)),
       add(mul(t12,g21),mul(g12,t21)),-1)
assert J[zero]==Q(-172) and zero not in Jt
assert mul(J,J)[zero]==Q(31332)
assert 2*mul(J,Jt)[zero]==Q(920)
expected={can(k):Q(v) for k,v in [
    (zero,-172),((1,-1),56),((2,2),-2),
    ((3,1),4),((0,4),12),((3,5),-14)]}
assert J==expected,(J,expected)
assert Jt=={can(k):Q(v) for k,v in [
    ((1,-1),112),((2,2),-32),((3,1),-40),
    ((0,4),-144),((3,5),252)]}
print("PASS: exact compatible heatflow; energy=31332; derivative=+920")
