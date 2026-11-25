#!/usr/bin/env python3
"""Exact checks for the uniform finite-accuracy localization constants.
No large mesh is constructed. The logarithmic bound is stored symbolically.
"""
from fractions import Fraction as Q
from math import ceil

def ceil_log2_fraction(x):
    assert x >= 1
    j=max(0,x.numerator.bit_length()-x.denominator.bit_length())
    while Q(2)**j < x:j+=1
    while j and Q(2)**(j-1)>=x:j-=1
    return j

def params(e):
    assert 0<e<=1
    d=e/128
    M=16/d
    T=256/d**2
    theta=e/(1024*(M+1)); zeta=theta
    s=1
    while True:
        lam=Q(1,2**s)
        if (lam<=theta/16 and 4*M*lam**2<=e/32 and
            1024*T*lam<=e/32 and M*(6*theta+256*lam**2/theta**2)<=e/32):break
        s+=1
    g=2*s+1
    K=ceil(1024*g/e**2)
    D=ceil_log2_fraction(1/theta)
    Z=ceil_log2_fraction(1/zeta)
    L=max(K+g+s+6,5+D,6+2*D)+2
    # n=2**logn, and 3H/sqrt(n) <= (3/4) 2**(-Z) <= zeta.
    logn=2*(L+Z+2)
    assert 4*Q(g,K+g)<=e**2/256
    assert M*(4+zeta)*zeta<=e/32
    assert (2+zeta)**2<=9
    assert Q(3,4)*Q(1,2**Z)<=zeta
    assert 8*d<=e/16
    return dict(eps=str(e),s=s,g=g,K=K,L=L,Z=Z,log2_mesh_side=logn)

def v(n,k):
    return max(Q(0),min(Q(1),Q(2)-Q(abs(k),n)))
def p(i,k):
    return v(2**i,k[0])*v(2**i,k[1])
def d(i,k):
    return p(i,k)-(p(i-1,k) if i else 0)

# Independent exact Fourier multiplier and discarded-gap energy controls.
for k1 in range(-16,17):
    for k2 in range(-16,17):
        if (k1,k2)==(0,0):continue
        k=(k1,k2); q=[d(i,k) for i in range(7)]
        assert all(x>=0 for x in q) and sum(q)==1
        for i,x in enumerate(q):
            if x:
                assert max(map(abs,k))<2**(i+1)
                if i:assert max(map(abs,k))>2**(i-1)
        for K,g in [(3,3),(7,5)]:
            P=K+g
            ds=[sum(x for i,x in enumerate(q) if (i-offset)%P<g) for offset in range(P)]
            assert sum(ds)==g and sum(x*x for x in ds)<=g
print('Exact multiplier positivity, support, partition, and gap-average checks passed.')
for e in [Q(1),Q(1,2),Q(1,4),Q(1,10),Q(1,100),Q(1,1000)]:
    print(params(e))
print('All explicit parameter and error-budget checks passed. No finite mesh was enumerated.')
