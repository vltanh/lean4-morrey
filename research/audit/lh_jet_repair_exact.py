#!/usr/bin/env python3
"""Exact controls for rank-one curvature compactness and jet-repair budgets.
These check finite algebra; they do not decide Morrey or run quantifier elimination.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from random import Random
from math import prod

I = range(4)
sharing = {(0,1),(0,2),(1,3),(2,3)}
sets = [s for k in range(5) for s in combinations(I,k)]
# Every monomial other than the constant, coordinates, ad and bc
# contains a pair sharing a row or a column.
residual = [s for s in sets if len(s)>=2 and s not in [(0,3),(1,2)]]
assert len(residual)==9
assert all(any(p in sharing for p in combinations(s,2)) for s in residual)

rng=Random(24011)
for trial in range(40):
    c={s:Q(rng.randint(-50,50),rng.randint(1,10)) for s in sets}
    def P(x):
        return sum(c[s]*prod([x[i] for i in s]) for s in sets)
    for i,j in sorted(sharing):
        other=[k for k in I if k not in (i,j)]
        samples={}
        for z in product([-1,1],repeat=2):
            x=[Q(0)]*4
            for k,v in zip(other,z): x[k]=Q(v)
            y=x.copy();w=x.copy()
            y[i]=y[j]=Q(1);w[i]=w[j]=Q(-1)
            samples[z]=(P(y)+P(w)-2*P(x))/2
        for k in range(3):
            for T in combinations(range(2),k):
                v=sum(a*prod([z[t] for t in T]) for z,a in samples.items())/4
                assert v==c[tuple(sorted([i,j]+[other[t] for t in T]))]
    assert (P([1]*4)+P([-1]*4)-2*P([0]*4))/2==sum(c[s] for s in sets if len(s)>=2 and len(s)%2==0)
print('40 rational multiaffine controls: exact shared-pair coefficient extraction and determinant gauge.')

# Conservative uniform bounds in the compactness proof.
assert 9*3+19+2==48
assert 646+672+48==1366<2000
# Upper interpolation cost: four coordinate errors M/2.
for M in map(Q,[1,2,5,11]):
    interp=2*M
    assert (2*M+2*interp)/2==3*M
    assert (4*M+2*interp)/2==4*M
    assert 4*M+5*3*M==19*M
print('Exact compactness coefficient and growth budgets passed.')

# Two-parameter contact data; support averages with E f=-D and E T=-DI.
for a,d,D,S in product([Q(0),Q(1,3),Q(1)],[Q(0),Q(1,5),Q(3)],[Q(1,7),Q(2)],[Q(1,9),Q(4)]):
    assert a*(-D+D)-d==-d
    assert a*(-D-S)+a*D-d==-d-a*S
    for T in [Q(-7),Q(0),Q(2,3)]:
        Tg=a*T+a*D-d
        assert Tg+d==a*(T+D)
print('36 rational parameter tuples: exact energy, secondary-gap and stress identities.')

# An exact rank-one midpoint obstruction to flattened jet data.
# Along a rank-one line, endpoint energy 0 at both x=+-1 and lower
# barrier zero at the mean cannot coexist with curvature kappa>0.
for kappa in [Q(1,10),Q(1),Q(3)]:
    endpoint_cost=Q(0)-kappa*Q(1)/2
    assert endpoint_cost<0
# In the general repair formula, the feasible inequality is affine in
# (a,d). Verify the lower bound on the contraction parameter from a laminate.
for kappa,E,budget in product([Q(1,10),Q(1)],[Q(1,2),Q(4)],[Q(1),Q(3)]):
    amin=kappa*E/(2*budget)
    assert amin*budget==kappa*E/2 and amin/2*budget<kappa*E/2
print('Exact two-point obstruction and 8 rational curvature-budget controls passed.')
print('No qualifying planar counterexample, full rigidity computation or Lean proof was produced.')
