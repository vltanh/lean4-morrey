#!/usr/bin/env python3
"""Exact controls for the relative mesh-margin localization budget."""
from fractions import Fraction as Q
from math import ceil

def budget(M,T,e):
    rho=min(Q(1,16),e/(1024*(M+1)))
    theta=rho**2;zeta=rho
    s=1
    while True:
        lam=Q(1,2**s)
        if lam<=rho**3/16 and 1024*T*lam<=e/8 and 4*M*lam**2<=e/8:break
        s+=1
    g=2*s+1;K=ceil(64*g*(M+1)/e)
    alpha=Q(g,K+g)
    gamma=2*rho+16*lam/theta+zeta
    err=4*M*lam**2+1024*T*lam+M*(6*theta+256*lam**2/theta**2)+M*(4+zeta)*zeta
    total=Q(5,2)*M*alpha+err+M*(2*gamma+gamma**2)/2
    assert lam<=theta/16 and gamma<=4*rho and total<e
    return float(total/e)

cases=[(Q(M),Q(T),e) for M in [0,1,10,10**4] for T in [0,1,100,10**6] for e in [Q(1,1000),Q(1,10),Q(1),Q(10)]]
ratios=[budget(M,T,e) for M,T,e in cases]
print(f'{len(cases)} exact relative-margin budgets passed; largest tested error/tolerance = {max(ratios):.6f}.')
