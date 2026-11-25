#!/usr/bin/env python3
"""Exact algebra controls for the quadratic-tail truncation theorem.
The scalar projection lemma is a verified external input; this script is
not an implementation of that projection or a proof of Morrey.
"""
from fractions import Fraction as Q
from itertools import product
from math import factorial

# Two genuine scalar periodic piecewise-affine derivatives, lifted as
# first-row planar gradients with the other row zero. Both means vanish.
# The selected Y satisfies both projection properties. It need not be the
# potential-space L2 projection itself; this is an algebraic control.
x = list(map(Q, (1, -1, 9, -9)))
y = list(map(Q, (4, -4, 4, -4)))
lam, B, r, R = Q(2), Q(1), Q(1), Q(4)
avg = lambda xs: sum(xs, Q(0))/len(xs)
assert avg(x)==avg(y)==0
assert all(a==b or abs(b)==R for a,b in zip(x,y))
assert all(abs(b)<=R for b in y)
assert avg([b*(a-b) for a,b in zip(x,y)])==4
D = avg([(a-b)**2 for a,b in zip(x,y)])
assert D==17
# A smooth compactly supported V with |V|<=1 and V(+-1)=-1
# can be used after slightly enlarging r, e.g. to 3/2.
r=Q(3,2)
assert B/(R-r)**2<=lam/4
# Only sample values of V enter the control. Changes inside the core
# pay a positive penalty, whereas the total quadratic cost decreases.
HX=lam*avg([a*a for a in x])/2-Q(1,2)
HY=lam*avg([b*b for b in y])/2
assert HY-HX==-Q(49,2)
assert HY-HX<=-lam*D/4
assert avg([b*b for b in y]) <= avg([a*a for a in x])-D
print('Exact clipping control: changed-core penalty included; energy decrease 49/2, squared error 17.')

# Row Helmholtz symbol and row rotation on nonzero frequencies.
n=0
for a,b in product(range(-4,5),repeat=2):
    if a==b==0: continue
    d=a*a+b*b
    r=Q(a*a-b*b,d); s=Q(2*a*b,d)
    P=((Q(1+r,2),s/2),(s/2,Q(1-r,2)))
    want=((Q(a*a,d),Q(a*b,d)),(Q(a*b,d),Q(b*b,d)))
    assert P==want
    assert all(sum(P[i][k]*P[k][j] for k in range(2))==P[i][j] for i in range(2) for j in range(2))
    w=(-b,a)
    assert w[0]*a+w[1]*b==0
    assert (w[1],-w[0])==(a,b)
    n+=1
print(f'{n} exact Helmholtz symbol and row rotation controls passed.')

# Variance preservation and quantitative inner-stress bounds.
assert (1-Q(1,2))**2==Q(1,4)
assert Q(4,3)<2 and Q(4,3)**2<2 and 2*Q(4,3)**3<5
assert Q(5,4)**2<2
assert 2*(4+10)+2*3*4+2*2==56<64
assert 4*32<12**2
# L-infinity bounded stress: balance lambda*sqrt(delta) with 1/lambda.
assert Q(1,2)-Q(1,4)==Q(1,4)
# Fixed annulus: exclude collapse of all the relative variance to zero.
for m,M in [(Q(1,100),Q(1)),(Q(1),Q(2)),(Q(1),Q(1))]:
    assert (m/2-m/8-m/8)/M==m/(4*M)
# Optional bounded-forcing argument gives exponential relative moments.
for k in range(2,101):
    assert k**k<=3**k*factorial(k)
print('Relative variance, inner-variation, truncation rate, annulus and exponential budgets passed.')
print('No numerical critical sequence or exact-zero proof was constructed.')
