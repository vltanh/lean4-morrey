#!/usr/bin/env python3
"""Exact finite controls for the four-wave parity-laminate hand theorem.

The universal lamination theorem uses Sebestyen--Szekelyhidi (2017),
while the universal Fourier/Cauchy--Schwarz inequality is a hand proof.
These tests verify odd-resonance classification, exact area rho=1/3,
parity weights and determinant null-lagrangian moments.
Standard-library Python; no floating point or random tests.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from functools import reduce
from math import gcd

def det(a,b): return a[0]*b[1]-a[1]*b[0]

def odd_resonant(sub):
    """Does some all-odd integer coefficient vector annihilate sub?"""
    if not sub: return False
    if any(k==(0,0) for k in sub): raise ValueError('zero wavevector')
    sm=(sum(k[0] for k in sub),sum(k[1] for k in sub))
    if sm[0]%2 or sm[1]%2: return False
    half=(sm[0]//2,sm[1]//2)
    d=reduce(gcd,(abs(det(a,b)) for a,b in combinations(sub,2)),0)
    if d: return all(det(half,k)%d==0 for k in sub)
    first=sub[0]; g=gcd(abs(first[0]),abs(first[1]))
    e=(first[0]//g,first[1]//g); j=0 if e[0] else 1
    ms=[k[j]//e[j] for k in sub]
    assert all(m*e[0]==k[0] and m*e[1]==k[1]
               for m,k in zip(ms,sub))
    gg=reduce(gcd,(abs(m) for m in ms),0)
    return sum(ms)%(2*gg)==0

def first_resonant_subset(ks):
    for r in range(1,len(ks)+1):
        for ids in combinations(range(len(ks)),r):
            if odd_resonant([ks[i] for i in ids]):return ids
    return None

def clip(poly,a,b,c):
    """Intersect rational polygon with a*x+b*y<=c."""
    out=[]
    if not poly:return out
    for x,y in zip(poly,poly[1:]+poly[:1]):
        vx=a*x[0]+b*x[1]-c;vy=a*y[0]+b*y[1]-c
        if vx<=0:out.append(x)
        if (vx<0<vy) or (vy<0<vx):
            out.append(tuple(x[i]+(-vx)*(y[i]-x[i])/(vy-vx)
                             for i in range(2)))
        elif vx>0 and vy==0:out.append(y)
    return out

def area(poly):
    if len(poly)<3:return Q(0)
    return abs(sum(x[0]*y[1]-x[1]*y[0]
                   for x,y in zip(poly,poly[1:]+poly[:1])))/2

def four_correlation_zero_phase():
    """After half-period symmetries, integrate exactly over [0,1]^2."""
    square=[(Q(0),Q(0)),(Q(1),Q(0)),(Q(1),Q(1)),(Q(0),Q(1))]
    total=Q(0);cell=[]
    for i,j in product(range(3),repeat=2):
        poly=square[:]
        for a,b,c in ((1,2,i+1),(-1,-2,-i),(2,1,j+1),(-2,-1,-j)):
            poly=clip(poly,Q(a),Q(b),Q(c))
        ar=area(poly);cell.append(ar)
        total+=ar*((-1)**(i+j))
    assert sum(cell)==1
    assert cell==[Q(1,6),Q(1,12),Q(0),Q(1,12),Q(1,3),Q(1,12),Q(0),Q(1,12),Q(1,6)]
    return total

def parity_moments(n,rho):
    signs=list(product((-1,1),repeat=n))
    masses={e:Q(1,2**n)*(1+rho*reduce(int.__mul__,e,1)) for e in signs}
    assert all(w>=0 for w in masses.values())
    assert sum(masses.values())==1
    for count in range(1,n):
        for sub in combinations(range(n),count):
            assert sum(w*reduce(int.__mul__,(e[j] for j in sub),1)
                       for e,w in masses.items())==0
    assert sum(w*reduce(int.__mul__,e,1) for e,w in masses.items())==rho
    return masses

def lifted_moment_control(masses):
    H=[(Q(1),Q(0),Q(0),Q(0)),(Q(0),Q(0),Q(0),Q(1)),
       (Q(2),Q(2),Q(0),Q(0)),(Q(0),Q(3),Q(0),Q(3))]
    def D(a):return a[0]*a[3]-a[1]*a[2]
    def mat(e):return [sum(e[i]*H[i][j] for i in range(4)) for j in range(4)]
    assert all(sum(w*mat(e)[j] for e,w in masses.items())==0 for j in range(4))
    assert sum(w*D(mat(e)) for e,w in masses.items())==0

def run():
    quartet=[(1,0),(0,1),(1,2),(2,1)]
    for r in range(1,4):
        assert all(not odd_resonant([quartet[i] for i in sub])
                   for sub in combinations(range(4),r))
    assert first_resonant_subset(quartet)==(0,1,2,3)
    assert all(-3*quartet[0][j]-3*quartet[1][j]+quartet[2][j]+quartet[3][j]==0
               for j in range(2))
    assert first_resonant_subset([(1,2**i) for i in range(10)]) is None
    assert first_resonant_subset([(1,0),(0,1),(1,1)])==(0,1,2)
    assert first_resonant_subset([(1,0),(2,0)]) is None
    assert first_resonant_subset([(1,0),(3,0)])==(0,1)
    assert Q(8)*Q(1,4)**2-Q(4)*Q(1,4)==-Q(1,2)
    rho=four_correlation_zero_phase()
    assert rho==Q(1,3)
    masses=parity_moments(4,rho)
    assert set(masses.values())=={Q(1,12),Q(1,24)}
    lifted_moment_control(masses)
    print('PASS: no lower-order odd resonance; exact 4-way relation; 10-wave nonresonance')
    print('PASS: 4-wave zero-phase correlation rho=1/3 from nine rational polygons')
    print('PASS: 16 exact parity probabilities 1/12 or 1/24; zero matrix/minor moments')
    print('NOTE: all-phase rho<=1/2 and lamination use analytic proofs + published 3-wave theorem')

if __name__=='__main__':run()
