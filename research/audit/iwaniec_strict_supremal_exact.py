#!/usr/bin/env python3
"""Exact determinant-lift full-dimensionality and power-Jensen controls.

The strict maximum principle also relies on the published
Conti–De Lellis–Müller–Romeo polyconvex-sublevel theorem.
The script checks only its elementary 5D geometry and an
example of the powered Jensen threshold, not that theorem.
"""
from fractions import Fraction as Q
import itertools

def det(B):return B[0]*B[3]-B[1]*B[2]
def phi(B):return tuple(B)+(det(B),)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(c,a):return tuple(c*x for x in a)
def colmat(cols):return [[c[i] for c in cols] for i in range(len(cols[0]))]
def determinant(M):
    n=len(M)
    a=[list(x) for x in M];out=Q(1)
    for i in range(n):
        j=next(k for k in range(i,n) if a[k][i]!=0)
        if j!=i:a[i],a[j]=a[j],a[i];out=-out
        z=a[i][i];out*=z
        for k in range(i+1,n):
            q=a[k][i]/z
            for l in range(i,n):a[k][l]-=q*a[i][l]
    return out

for B in [(Q(0),)*4,(Q(2),-Q(3),Q(5),Q(7)),
          (Q(1,2),Q(3,4),-Q(4,3),Q(2))]:
    e=[tuple(Q(i==j) for i in range(4)) for j in range(4)]
    v=[tuple((phi(add(B,t)) [i]-phi(B)[i]) for i in range(5))
       for t in e]
    v.append((Q(0),Q(0),Q(0),Q(0),Q(1)))
    assert determinant(colmat(v))==1
    I=(Q(1),Q(0),Q(0),Q(1))
    D=(Q(1),Q(0),Q(0),-Q(1))
    for H,sign in ((I,1),(D,-1)):
        lhs=scale(Q(1,2),add(phi(add(B,H)),phi(add(B,scale(-1,H)))))
        assert lhs==add(phi(B),(Q(0),Q(0),Q(0),Q(0),Q(sign)))
# Illustrative two-point rank-one law: 1/2 at 0, 1/2 at 2E;
# energy F(A)=||A||_F^4 and base E=diag(1,0).
base=Q(1)
for q in [1,2,3,5]:
    assert Q(1,2)*Q(16)**q>=base**q
print("PASS: exact five-dimensional determinant-lift crosspolytope controls")
