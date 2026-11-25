"""Exact controls for minimal odd resonances and parallel-block peeling."""
from itertools import combinations
from math import gcd
from functools import reduce
from random import Random


def det(a,b): return a[0]*b[1]-a[1]*b[0]
def rank2(K): return any(det(a,b) for a,b in combinations(K,2))
def gcd_all(xs): return reduce(gcd,xs,0)


def in_lattice(v,K):
    if not K: return v==(0,0)
    d=gcd_all(det(a,b) for a,b in combinations(K,2))
    if d: return all(det(a,v)%d==0 for a in K)
    x,y=K[0]; g=gcd(x,y); p=(x//g,y//g)
    if det(p,v): return False
    j=0 if p[0] else 1
    assert v[j]%p[j]==0
    return (v[j]//p[j])%gcd_all(a[j]//p[j] for a in K)==0


def half_in_lattice(v,K):
    return not any(x%2 for x in v) and in_lattice(tuple(x//2 for x in v),K)


def odd(K):
    return bool(K) and half_in_lattice(tuple(map(sum,zip(*K))),K)


def minimal_resonances(K):
    out=[]
    for n in range(2,len(K)+1):
        for s in combinations(range(len(K)),n):
            if not any(t.issubset(s) for t in out) and odd([K[i] for i in s]):
                out.append(frozenset(s))
    return out


def classes(K):
    nonzero=[]
    for k in K:
        if half_in_lattice(k,K): continue
        for C in nonzero:
            if half_in_lattice((k[0]-C[0][0],k[1]-C[0][1]),K):
                C.append(k); break
        else: nonzero.append([k])
    return nonzero


def peel(K):
    K=list(K)
    while K:
        if not rank2(K): return []
        C=classes(K)
        assert len(C) in (2,3)
        if len(C)==3: return K
        B=next((c for c in C if not rank2(c)),None)
        if B is None: return K
        for k in B: K.remove(k)
    return K


def main():
    sharp=[(1,0),(0,1),(1,2),(2,1)]
    assert minimal_resonances(sharp)==[frozenset(range(4))]
    # Two nonzero classes, one parallel: can peel even with mixed correlations.
    K=[(1,0),(3,0),(0,1),(2,1),(4,0)]
    assert peel(K)==[]
    rng=Random(20261123)
    grid=[(a,b) for a in range(-3,4) for b in range(-3,4) if a or b]
    for _ in range(150):
        K=[rng.choice(grid) for _ in range(rng.randint(2,7))]
        C=minimal_resonances(K)
        assert all(len(s)<=4 for s in C),(K,C)
        mixed=any(rank2([K[i] for i in s]) for s in C)
        assert bool(peel(K))==mixed,(K,C,peel(K))
    large=[(1,0),(0,1),(1,1)]+[(1,2*j) for j in range(1,61)]
    assert len(peel(large))==len(large)
    assert all(odd([k,(0,1),(1,1)]) for k in large[3:])
    print('Sharp 4-circuit, parallel peeling, 150 small exact classifications, 63-wave irreducible family: passed')


if __name__=='__main__': main()
