#!/usr/bin/env python3
"""Certify a rational open ball around the explicit level-two quartic example."""
import json
from fractions import Fraction
from pathlib import Path
from sympy import Matrix
from sympy.polys.matrices import DomainMatrix
src=Path('/mnt/data/morrey_quartic_l2_dual_certificate.json')
d=json.loads(src.read_text())
A=Matrix(d['matrix'])
assert A.shape==(35,35)
IA=DomainMatrix.from_Matrix(A).to_field().inv().to_Matrix()
lam=IA*Matrix(d['rhs'])
assert all(v>0 for v in lam)
assert A*lam==Matrix(d['rhs'])
minw=min(lam)
inf_norm=max(sum(abs(IA[i,j]) for j in range(35)) for i in range(35))
# Original grad without x4, bounded by K.
U=[70,28,2,-46,-39,-92,-85,-97,-65,63,30,83,1,21,95,46]
V=[27,9,12,87,-45,63,34,-100,-21,72,11,-94,53,46,70,-65]
def val(D,i,j):return D[4*(i%4)+(j%4)]
K=0
for i in range(4):
 for j in range(4):
  for k in (0,1):
   for D in (U,V):
    if k==0:g=[val(D,i+1,j)-val(D,i,j),val(D,i,j+1)-val(D,i,j)]
    else:g=[val(D,i+1,j+1)-val(D,i,j+1),val(D,i+1,j+1)-val(D,i+1,j)]
    K=max(K,*map(abs,g))
# Each nodal value variation at most δ implies each coordinate gradient
# difference ≤2δ. Monomial degree 4 has derivative 1-norm at most
# 4(K+2)^3, hence one term changes ≤8δ(K+2)^3.
# Sum over 32 triangles -> max change to each b coefficient ≤256δ(K+2)^3.
B=256*(K+2)**3
# For δ<=1 and δ B ||A^-1||_infty < min_j λ_j/2, positivity persists.
N=1
while Fraction(1,2**N)*B*inf_norm>=minw/2:
 N+=1
print('exact K=',K,'Lipschitz B=',B)
print('min dual weight approx',float(minw),'inverse infinity norm approx',float(inf_norm))
print('CERTIFIED OPEN BALL: max absolute perturbation in each of the 32 nodal scalar values < 2^(-%s)'%N)
assert Fraction(1,2**N)*B*inf_norm<minw/2
out={'node_bound':K,'moment_lipschitz_B':B,'denominator_exponent_N':N,
     'delta':'1/'+str(2**N),'min_weight':str(minw),'inverse_inf_norm':str(inf_norm),
     'explanation':'If all 32 scalar periodic nodal values for U,V change by < 2^-N, each quartic moment changes by at most B*delta; the unique weights solving A*lambda=b remain > 0 since ||A^-1||∞*B*delta < min(lambda)/2. Thus homogeneous quartic Jensen remains valid for the whole open ball.'}
Path('/mnt/data/morrey_quartic_open_neighborhood.json').write_text(json.dumps(out,indent=2))
# Also allow an arbitrary base matrix F with each entry bounded by δ.
# For each quartic monomial: 32 evaluations on (G + F) change by at most
# 32 * 4 * (K+3)^3 * 3δ = 384(K+3)^3 δ.
# The subtractive 32*P(F) contributes at most 32δ^4 <= 32δ.
Bshift=384*(K+3)**3 + 32
Nshift=1
while Fraction(1,2**Nshift)*Bshift*inf_norm>=minw/2:
 Nshift+=1
print('CERTIFIED JOINT OPEN BALL: all 32 nodal perturbations and all 4 base F coordinates < 2^(-%s)'%Nshift)
assert Fraction(1,2**Nshift)*Bshift*inf_norm<minw/2
out['Bshift']=Bshift;out['joint_denominator_exponent_N']=Nshift;out['joint_delta']='1/'+str(2**Nshift)
Path('/mnt/data/morrey_quartic_open_neighborhood.json').write_text(json.dumps(out,indent=2))
print('PASS: exact rational positivity margin including arbitrary small base F')
