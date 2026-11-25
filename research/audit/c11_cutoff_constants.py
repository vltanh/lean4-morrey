#!/usr/bin/env python3
"""Exact arithmetic controls for C^{1,1} localization and normalized data repair.
No large finite meshes or data sets are materialized.
"""
from fractions import Fraction as Q
from math import ceil


def ceil_log2(x):
    assert x >= 1
    k=max(0,x.numerator.bit_length()-x.denominator.bit_length())
    while Q(2)**k < x: k+=1
    while k and Q(2)**(k-1)>=x: k-=1
    return k


def localization(M,eta):
    rho=min(Q(1,16),eta/(1024*(M+1)))
    theta=rho*rho
    zeta=rho
    s=max(1,ceil_log2(16/rho**3))
    lam=Q(1,2**s)
    g=2*s+1
    K=max(1,ceil(64*g*(M+1)/eta))
    alpha=Q(g,K+g)
    gamma=2*rho+16*lam/theta+zeta
    loc=4*M*lam**2+64*M*lam+M*(6*theta+256*lam**2/theta**2)+M*(4+zeta)*zeta
    err=Q(5,2)*M*alpha+loc+M*(2*gamma+gamma**2)/2
    assert lam<=theta/16 and gamma<=4*rho and err<eta
    # H0=16*2^(K+g+2)/lambda+32/theta+64/theta^2 <= 2^L.
    # Verify symbolically by bounding each summand, avoiding gigantic powers.
    D=ceil_log2(1/theta)
    Z=ceil_log2(1/zeta)
    L=max(K+g+s+6,5+D,6+2*D)+2
    assert L>=K+g+s+8 and L>=7+D and L>=8+2*D
    logn=L+Z+3
    # 8 H0/n <= 2^-Z <= zeta.
    assert logn-L>=Z+3 and Q(1,2**Z)<=zeta
    return err/eta,logn


def repair(tol):
    mu=tol/128
    assert 0<mu<=1
    # L>=1 and delta=tol/(1024L), t<=mu delta^2/(256L),
    # h<=mu t^2/(256L) give the uniform midpoint/Hessian budget.
    # Bound 5h + 40Lh/t^2 + 43Lt/delta^2 <= (5+40+43)mu/256.
    assert Q(5+40+43,256)<1
    # S=log(R/r)>=128/mu; radial cutoff derivative bounds.
    assert Q(2,128)<=Q(1,64)
    assert Q(2,128)+Q(60,128**2)*mu <= Q(1,32)
    # Product rule errors at most (1+mu)*mu*(1/32+1/64)<mu.
    assert (1+mu)*(Q(1,32)+Q(1,64))<1
    # Data repair relative gap; E>=1/2.
    assert 16*tol/1024+3*mu<=tol/8
    # Nodal rounding delta_u<=tol/128, E' >=(1-delta_u)^2.
    du=tol/128
    assert (1-du)**2>=Q(1,2) and (1+du)**2<=2
    assert 10*du<=tol/8
    # Interval width from geometry, rounding, and data repair.
    assert Q(3,8)*tol+Q(1,8)*tol<tol


if __name__=='__main__':
    cases=[(Q(M),e) for M in [0,1,10,10**4] for e in [Q(1,1000),Q(1,10),Q(1),Q(10)]]
    results=[localization(M,e) for M,e in cases]
    for tol in [Q(1),Q(1,2),Q(1,10),Q(1,100),Q(1,1000)]:repair(tol)
    print(f'{len(cases)} exact localization budgets, 5 normalized-repair and rounding budgets passed.')
    print('Largest checked localization error/tolerance:',float(max(x[0] for x in results)))
    for eta in [Q(1),Q(1,10),Q(1,100)]:
        print(f'M=1, eta={eta}: log2(mesh side)={localization(Q(1),eta)[1]}')
    print('No large mesh, LP, or exact-zero positivity test was executed.')
