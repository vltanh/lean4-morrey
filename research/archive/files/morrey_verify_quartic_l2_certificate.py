#!/usr/bin/env python3
"""Independent exact rational verifier for one level-two quartic Jensen identity.

The certificate states: sum_T P(G_T) = Σ_j λ_j D²P(B_j)[a_j⊗n_j,a_j⊗n_j]
for EVERY homogeneous quartic polynomial P in four matrix entries.
Here G_T is the periodic 4x4 nodal gradient DIVIDED BY 4. Each λ_j>=0.
All computations use Python integers and Fraction, no floats or SymPy.
This proves positivity for quartic rank-one-convex polynomials at F=0 for
ONE explicit gradient law, not the unrestricted Morrey conjecture.
"""
from fractions import Fraction
import json
from pathlib import Path

DATA=Path(__file__).with_name('morrey_quartic_l2_dual_certificate.json')
d=json.loads(DATA.read_text())
monomials=[tuple(x) for x in d['monomials']]
assert len(monomials)==35 and all(sum(t)==4 for t in monomials)

U=(70,28,2,-46,-39,-92,-85,-97,-65,63,30,83,1,21,95,46)
V=(27,9,12,87,-45,63,34,-100,-21,72,11,-94,53,46,70,-65)
N=4

def value(A,i,j):return A[(i%N)*N+j%N]
def grad(A,i,j,k):
 if k==0:return (value(A,i+1,j)-value(A,i,j),value(A,i,j+1)-value(A,i,j))
 return (value(A,i+1,j+1)-value(A,i,j+1),value(A,i+1,j+1)-value(A,i+1,j))

G=[]
for i in range(N):
 for j in range(N):
  for k in range(2):
   G.append((*grad(U,i,j,k),*grad(V,i,j,k)))
assert len(G)==32

def monomial(powers, X):
 out=1
 for v,a in zip(X,powers):out*=v**a
 return out

def LH_monomial(powers, X, H):
 ans=0
 for i in range(4):
  for j in range(4):
   c=powers[i]*(powers[j]-(i==j))
   if c==0:continue
   exps=list(powers);exps[i]-=1;exps[j]-=1
   ans+=c*monomial(exps,X)*H[i]*H[j]
 return ans

assert [sum(monomial(m,X) for X in G) for m in monomials]==[int(v) for v in d['rhs']]
assert all(sum(X[i] for X in G)==0 for i in range(4))
assert sum(X[0]*X[3]-X[1]*X[2] for X in G)==0

rhs=[Fraction(0) for _ in monomials]
for w,B,a,n in zip(d['weights'],d['B'],d['a'],d['n']):
 ww=Fraction(w)
 assert ww>=0
 H=(a[0]*n[0],a[0]*n[1],a[1]*n[0],a[1]*n[1])
 assert H[0]*H[3]==H[1]*H[2]
 for i,m in enumerate(monomials):
  rhs[i]+=ww*LH_monomial(m,B,H)
assert rhs==[Fraction(int(v)) for v in d['rhs']]
print(f'PASS: exact rational identity for all {len(monomials)} homogeneous quartic coefficients')
print(f'PASS: {len(d["weights"])} nonnegative rational Hessian evaluations at integer rank-one directions')
print('PASS: 32 level-two gradients have zero mean and zero mean determinant')
print('PROVED: for this concrete level-two ν, every homogeneous quartic rank-one convex P satisfies P(0) <= average P(Dw)')
print('LIMIT: one ν and homogeneous quartics at base F=0; NOT unrestricted Morrey')
