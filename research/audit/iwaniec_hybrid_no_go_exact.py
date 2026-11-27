#!/usr/bin/env python3
"""Exact p=4 obstruction to hybrid Burkholder/polyconvex certificate completeness.

No floating point or external packages. Proves 7 integer polynomial sign
conditions by rational Bernstein subdivision, and an exact two-point gap.
See docs/research/IWANIEC_MORREY_HYBRID_NOGO.md for the analytic bridge.
"""
from fractions import Fraction as Q
from math import comb

DEN=1<<24
COEFFS=[37676885,55559819,22507846,3634764,1122809,1068027,57237,
        275379,623336,96945,-261804,-126467,-6991]

def trim(a):
 a=list(a)
 while len(a)>1 and a[-1]==0:a.pop()
 return tuple(a)
def add(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def scale(a,c):return trim([c*v for v in a])
def sub(a,b):return add(a,scale(b,-1))
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return trim(c)
def deriv(a):return trim([i*a[i] for i in range(1,len(a))] or [0])
def evaluate(a,x):
 v=Q(0)
 for c in reversed(a):v=v*x+c
 return v
one=(1,);r=(0,1);rr=(0,0,1)
cheb=[one,r]
for _ in range(2,len(COEFFS)):
 cheb.append(sub(scale(mul(r,cheb[-1]),2),cheb[-2]))
H=(0,)
for c,t in zip(COEFFS,cheb):H=add(H,scale(t,c))
M=deriv(H);N=deriv(M);C=sub(scale(H,4),scale(mul(r,M),2))
U=add(scale(C,3),mul(rr,N))
E=sub(scale(M,2),mul(r,N))
Pplus=add(C,mul(sub(one,r),E))
Pminus=sub(C,mul(add(one,r),E))
Qplus=sub(mul(mul(sub(one,r),sub(one,r)),mul(U,N)),mul(Pplus,Pplus))
Qminus=sub(mul(mul(add(one,r),add(one,r)),mul(U,N)),mul(Pminus,Pminus))
names=('H','C','N','Pplus','Pminus','Qplus','Qminus')
polys=(H,C,N,Pplus,Pminus,Qplus,Qminus)

def bernstein(a):
 """Exact Bernstein coefficients on [-1,1], via x=2t-1."""
 n=len(a)-1
 c=[sum(a[i]*comb(i,j)*2**j*(-1)**(i-j) for i in range(j,len(a))) for j in range(n+1)]
 return tuple(sum((Q(c[j]*comb(k,j),comb(n,j)) for j in range(k+1)),Q(0)) for k in range(n+1))
def halve(a):
 """de Casteljau halves preserve the exact represented polynomial."""
 v=list(a);left=[v[0]];right=[v[-1]]
 for _ in range(len(a)-1):
  v=[(v[i]+v[i+1])/2 for i in range(len(v)-1)]
  left.append(v[0]);right.append(v[-1])
 return tuple(left),tuple(reversed(right))
leaves=0;depth_max=0
def prove(v,depth):
 global leaves,depth_max
 good=[all(c>0 for c in z) for z in v]
 if good[0] and good[1] and good[2] and (good[3] or good[5]) and (good[4] or good[6]):
  leaves+=1;depth_max=max(depth_max,depth);return
 if depth>=22:
  raise AssertionError('Unproved sign interval: '+str([(n,min(z)) for n,z in zip(names,v)]))
 children=[halve(z) for z in v]
 prove(tuple(t[0] for t in children),depth+1)
 prove(tuple(t[1] for t in children),depth+1)
prove(tuple(bernstein(z) for z in polys),0)
assert leaves==12 and depth_max==6
print('PASS: global rank-one acoustic inequalities, 12 rational Bernstein intervals, depth 6')

# Positive two-point functional separates every hybrid cone generator.
rminus,rplus=Q(-1,3),Q(1,3)
gap=evaluate(H,Q(0))-Q(5,4)*evaluate(H,rminus)-Q(7,20)*evaluate(H,rplus)
assert gap/DEN==Q(356912972869,17832200896512) and gap>0
for sign in (-1,1):
 g=lambda t:Q(1,2)+sign*t
 assert Q(5,4)*g(rminus)+Q(7,20)*g(rplus)>=g(Q(0))
# For (c+mr)_+^2: divide by c^2, minimize the convex function
# (5/4)(1-z/3)_+^2+(7/20)(1+z/3)_+^2 over all real z.
z=Q(27,16)
assert -3<z<3
assert Q(5,4)*(1-z/3)**2+Q(7,20)*(1+z/3)**2==Q(35,32)>1
# Its derivative at z is zero, hence global minimum by convexity.
assert Q(5,4)*(-Q(1,3))*(1-z/3)+Q(7,20)*Q(1,3)*(1+z/3)==0
print('PASS: two-point separator for all hybrid generators; exact gap:',gap/DEN)
