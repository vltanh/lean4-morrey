"""Exact rational checks for signed scale-integral generators.
The general exponent and quasiconvexity statements are proved analytically.
"""
from fractions import Fraction as Q
from math import isqrt


def sqrt(q):
    q = Q(q)
    a, b = isqrt(q.numerator), isqrt(q.denominator)
    assert a*a == q.numerator and b*b == q.denominator
    return Q(a,b)


def powhalf(q, j):
    if q == 0:
        assert j > 0
        return Q(0)
    return sqrt(q)**j


def subquad_integral(t,c):
    # p=3/2, sigma=1; normalized scale integral.
    p=Q(3,2); C=(p-1)*(2-p)
    if t>=-c:
        return C*((1+t)/(p-1)-1/p+t/(2-p))
    r0=(1+t)/(1-c); r1=sqrt(-t/c)
    # integrate L_r on [0,r0], clipped constant on [r0,r1], det on [r1,infty)
    first=(1+t)*powhalf(r0,1)/(p-1)-powhalf(r0,3)/p
    mid=-c*(powhalf(r1,3)-powhalf(r0,3))/p
    tail=t*powhalf(r1,-1)/(2-p)
    return C*(first+mid+tail)


def superquad_integral(p,b,t):
    # p integral, sigma=1; choose t so the active radius is rational.
    C=(p-1)*(p-2); x=(1+t)/2; y=(1-t)/2
    s=Q(1) if b*x<=y else b*x+sqrt(b*b*x*x+t)
    z=max(y,b*x)
    val=C*(t*s**(p-2)/(p-2)+2*z*s**(p-1)/(p-1)-s**p/p)
    return val,s


def main():
    p=Q(3,2); a=(2-p)/p; c=Q(1,16)
    for t in (-1,-c,0,1):
        t=Q(t); got=subquad_integral(t,c)
        if t>=-c: assert got==a+t
        else: assert got==-Q(1,3)
    H=subquad_integral(Q(-1),c); m=-(p/2)*H
    assert H==-Q(1,3) and m==Q(1,4)
    assert H+m*(1-a)==-Q(1,6)
    # p>2: explicit active radii parameterized by s.
    b=Q(5,12); threshold=(1-b)/(1+b)
    for p in (4,6,8):
        k=Q(p-2,p)
        for t in (Q(-1),Q(0),threshold):
            got,s=superquad_integral(p,b,t)
            assert s==1 and got==k+t
        for s0 in (Q(5,4),Q(3,2)):
            t=(s0*s0-b*s0)/(1+b*s0)
            assert threshold<t<=1
            got,s=superquad_integral(p,b,t)
            assert s==s0 and got==s**(p-2)*(t+k*s*s)
            assert got>k+t
            if p==4 and t==1: assert got==Q(153,32)
    print('Exact signed-scale checks passed: p=3/2 clipping and negative tangent gap -1/6; p=4,6,8 active radii and integral identities.')

if __name__=='__main__': main()
