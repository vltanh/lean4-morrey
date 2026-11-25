#!/usr/bin/env python3
"""Rational verification of the continuum scalar bound for beta_* >= -58/125.

The analytic proof reduces it to the scalar inequality in the accompanying
note. This checks all nontrivial rational/transcendental constant bounds
there, and exact radial-kernel integrals. It does not sample a gradient or
certify the unresolved self-contraction to zero.
"""
from fractions import Fraction as Q
from math import factorial

c, lam = Q(58,125), Q(1,10)


def exp_bounds(x, n):
    """Positive rational Taylor bounds for exp(x), x>=0."""
    assert x >= 0 and x < n+2
    lower = sum((x**j/factorial(j) for j in range(n+1)), Q(0))
    upper = lower + x**(n+1)/factorial(n+1)/(1-x/Q(n+2))
    return lower, upper


# log(2) < 7/10.
assert exp_bounds(Q(7,10), 4)[0] > 2
# The uncapped maximizer for k=41/20 is sqrt(37/41).
assert Q(949,1000)**2 < Q(37,41) < Q(19,20)**2
assert exp_bounds(Q(18,5), 16)[1] < Q(1949,51)
Bmax = Q(41,20)*Q(19,20)-lam*Q(18,5)
assert Bmax == Q(127,80)
assert c*(c-3*lam/2) > Q(381,1000)**2
assert Bmax+lam*(Q(5,8)+Q(7,5)) == Q(179,100)
assert 2*c+lam+2*Q(381,1000) == Q(179,100)
# G(q) is increasing for q>=5/4.
assert c*(1-Q(4,5)**2)-lam*(Q(1,2)+Q(4,5)) > 0
# The uncapped gap decreases until cap activation, since y* > 2c.
assert (2*c)**2 < Q(9,10)
k = Q(41,20)
assert k*k-2*lam*k-4 < 0

# The capped gap G(p) is strictly convex for p>1. Its derivative
# is a rational expression. Bracket its unique minimum and use a
# tangent at p0 for a rigorous global lower bound.
def Gprime(p):
    return 2*c*(1-1/p**2)-lam*(1+1/p+4/(p**2-1))

lo, p0, hi = Q(147,100), Q(37,25), Q(149,100)
assert Gprime(lo)<0<Gprime(hi)
assert abs(Gprime(p0))<Q(1,1000)
arg = 4*p0*(p0-1)**2/(p0+1)**2
assert arg == Q(5328,24025)
assert exp_bounds(Q(3,2),16)[1] < 1/arg
G0 = 2*c*(p0+1/p0)-2-lam*p0+lam*Q(3,2)
assert G0==Q(1141,462500)
Gmin = G0-Q(1,100000)
assert Gmin>0
assert lam/2<c
assert c/(c+Q(1,2))==Q(116,241)
print('All rational scalar-inequality budgets passed.')
print('Global capped-gap lower certificate:', Gmin, '=',float(Gmin))

# Exact L1 distance between radial Taylor kernels of radii a,b.
# For a<=b, crossing at r=ab/(a+b). The positive triangle of
# the difference has twice-area (b-a)/(b+a).
controls=0
for a in [Q(1,16),Q(1,3),Q(1),Q(4)]:
    for b in [Q(1,16),Q(1,3),Q(1),Q(4),Q(29)]:
        a0,b0=sorted((a,b))
        r=a0*b0/(a0+b0)
        def integral(s,t):
            return t/s-t*t/(2*s*s)
        positive=integral(a0,r)-integral(b0,r)
        assert 2*positive==(b0-a0)/(b0+a0)
        controls+=1
print(controls,'exact radial-kernel controls passed.')
print('No exact-zero proof, full finite-mesh search, or numerical counterexample is claimed.')
