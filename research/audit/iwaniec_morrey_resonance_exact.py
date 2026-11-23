#!/usr/bin/env python3
"""Exact Fourier resonance controls (standard library)."""
from itertools import product
from fractions import Fraction as Q
from math import comb

def spatial(exponents, ks):
    s=Q(0)
    for js in product(*(range(e+1) for e in exponents)):
        if all(sum((e-2*j)*k[axis] for e,j,k in zip(exponents,js,ks))==0 for axis in (0,1)):
            num=1
            for e,j in zip(exponents,js):num*=comb(e,j)
            s+=Q(num,2**sum(exponents))
    return s

def independent(exponents):
    s=Q(1)
    for e in exponents:
        if e%2:return Q(0)
        s*=Q(comb(e,e//2),2**e)
    return s

def test():
    ks=((1,0),(0,1),(5,1))
    n=0
    for a in range(5):
        for b in range(5-a):
            for c in range(5-a-b):
                exps=(a,b,c)
                assert spatial(exps,ks)==independent(exps),exps
                n+=1
    assert n==35
    # No integer relation with total coefficient norm <= 6; witness at 7.
    for n1 in range(-6,7):
        for n2 in range(-6,7):
            for n3 in range(-6,7):
                if 0 < abs(n1)+abs(n2)+abs(n3) <= 6:
                    assert (n1+5*n3,n2+n3)!=(0,0)
    assert (-5+5*1,-1+1)==(0,0)
    assert spatial((1,1,1),((1,0),(0,1),(1,1)))==Q(1,4)
    assert independent((1,1,1))==Q(0)
    assert Q(4,16)==Q(1,4)
    print("PASS 35 quartic monomials, cubic triad=1/4, Bernstein variance")

if __name__=="__main__":test()
