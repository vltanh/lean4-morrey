#!/usr/bin/env python3
"""Exact rational boundary and interval-energy verifier for oriented 2-chains.

A negative *certified* filling of a verified RC chart energy is a genuine
Morrey counterexample by the BV trace theorem. No MILP solver is trusted.
"""
from fractions import Fraction as Q
from itertools import combinations
from collections import defaultdict
from math import isqrt
import argparse
import json
from pathlib import Path


def rat(x):
    if type(x) not in (int, str):
        raise ValueError('use exact integer or rational-string inputs')
    return Q(x)


def sqrt_bounds(x, bits=80):
    if x < 0:
        raise ValueError('negative square root')
    k = 1 << bits
    n = isqrt((x.numerator*k*k)//x.denominator)
    lo = Q(n,k)
    return lo, lo if lo*lo == x else Q(n+1,k)


def sqnorm(X):
    return sum(x*x for x in X)


def plus(I,J):
    return I[0]+J[0], I[1]+J[1]


def scale(c,I):
    return (c*I[0],c*I[1]) if c>=0 else (c*I[1],c*I[0])


def shift(I,c):
    return I[0]+c,I[1]+c


def wedge_half(p,q,r):
    u=[b-a for a,b in zip(p,q)]
    v=[b-a for a,b in zip(p,r)]
    return tuple((u[i]*v[j]-u[j]*v[i])/2 for i,j in combinations(range(4),2))


def mixed(xi):
    return (-xi[3],xi[1],-xi[4],xi[2])


def det(X):
    return X[0]*X[3]-X[1]*X[2]


def graph(A,y):
    return (*y,A[0]*y[0]+A[1]*y[1],A[2]*y[0]+A[3]*y[1])


def edge_add(edges,i,j,n):
    if i==j:
        raise ValueError('degenerate edge')
    if i>j:
        i,j,n=j,i,-n
    edges[i,j]+=n


def make_energy(spec,bits):
    kind=spec['kind']
    if kind=='truncated_L':
        M=Q(1)
        def C(X):
            a,b,c,d=X
            return sqrt_bounds((a+d)**2+(c-b)**2,bits)
        def W(X):
            a,b,c,d=X
            p=1-a*a-c*c; q=1-b*b-d*d
            if p>=0 and q>=0 and p*q>=(a*b+c*d)**2:
                return (det(X),)*2
            return shift(C(X),-1)
    elif kind=='norm_minus_one':
        M=Q(1)
        def C(X): return sqrt_bounds(sqnorm(X),bits)
        def W(X): return shift(C(X),-1)
    elif kind=='certified_polynomial_tail':
        from sphere_certificate import verify,parse,evaluate
        cert=spec['lh_certificate']
        verify(cert)  # exact global LH identity, not a sampled test
        P=parse(cert['integrand'],4)
        R=rat(spec['outer_radius']); r=rat(spec['tail_radius']); c=rat(spec['slope'])
        if not (0<r<R and c>0):
            raise ValueError('invalid tail parameters')
        bound=sum(abs(v)*R**sum(e) for e,v in P.items())
        if c*(R-r)<=bound:
            raise ValueError('strict gluing dominance not certified')
        M=c*r+bound
        def C(X): return scale(c,sqrt_bounds(sqnorm(X),bits))
        def W(X):
            barrier=shift(C(X),-c*r)
            if sqnorm(X)<=R*R:
                v=evaluate(P,X)
                barrier=(max(v,barrier[0]),max(v,barrier[1]))
            return shift(barrier,-bound)
    else:
        raise ValueError('unsupported energy; no RC certification')
    def Phi(xi):
        a=xi[0]; L=mixed(xi)
        if a>0:
            return scale(a,W(tuple(v/a for v in L)))
        return shift(C(L),-2*M*a)
    return Phi,M


def verify_filling(data,bits=80):
    A=tuple(map(rat,data['base']))
    if len(A)!=4:
        raise ValueError('base must have four matrix entries')
    V=[tuple(map(rat,p)) for p in data['vertices']]
    if any(len(p)!=4 for p in V) or len(set(V))!=len(V):
        raise ValueError('vertices must be distinct exact 4-vectors')
    corners=[graph(A,y) for y in ((Q(0),Q(0)),(Q(1),Q(0)),(Q(1),Q(1)),(Q(0),Q(1)))]
    try: ids=[V.index(p) for p in corners]
    except ValueError: raise ValueError('missing flat boundary vertex')
    bd=defaultdict(int)
    for i,j in zip(ids,ids[1:]+ids[:1]): edge_add(bd,i,j,1)
    Phi,M=make_energy(data['energy'],bits)
    eta=rat(data.get('area_penalty',0))
    if eta<0: raise ValueError('area penalty must be nonnegative')
    actual=defaultdict(int); total=(Q(0),)*6; energy=(Q(0),)*2; mass=(Q(0),)*2
    orientation_counts=defaultdict(int)
    for f in data['faces']:
        i,j,k=f['vertices']; n=f['multiplicity']
        if type(n) is not int or not n:
            raise ValueError('multiplicity must be a nonzero integer')
        if any(type(v) is not int or not 0<=v<len(V) for v in (i,j,k)) or len({i,j,k})!=3:
            raise ValueError('invalid face vertices')
        edge_add(actual,j,k,n); edge_add(actual,i,k,-n); edge_add(actual,i,j,n)
        xi=wedge_half(V[i],V[j],V[k])
        if not any(xi): raise ValueError('degenerate triangle')
        if n<0: xi=tuple(-v for v in xi)
        m=abs(n)
        assert xi[0]*xi[5]==det(mixed(xi))
        total=tuple(a+m*b for a,b in zip(total,xi))
        energy=plus(energy,scale(m,Phi(xi)))
        mass=plus(mass,scale(m,sqrt_bounds(sqnorm(xi),bits)))
        orientation_counts['positive' if xi[0]>0 else 'negative' if xi[0]<0 else 'vertical']+=m
    if {k:v for k,v in actual.items() if v}!={k:v for k,v in bd.items() if v}:
        raise ValueError('exact oriented boundary mismatch')
    ref=tuple(map(Q,(1,A[1],A[3],-A[0],-A[2],det(A))))
    if total!=ref: raise ValueError('bivector moment mismatch')
    base=Phi(ref)
    gap=plus(energy,scale(-1,base))
    penalized=plus(gap,scale(eta,plus(mass,scale(-1,sqrt_bounds(sqnorm(ref),bits)))))
    return {'gap_interval':list(map(str,gap)),'penalized_gap_interval':list(map(str,penalized)),
            'mass_interval':list(map(str,mass)), 'orientation_counts':dict(orientation_counts),
            'strict_negative':gap[1]<0,'strict_negative_penalized':penalized[1]<0,
            'boundary':'exact integer chain; integrated bivector checked',
            'scope':'energy interval plus verified RC construction; BV trace needed for graph witness'}


def control():
    # Flat square plus oriented boundary of a tetrahedron.  Its projection
    # has two vertical faces and one additional positive/negative pair.
    V=[[0,0,0,0],[1,0,0,0],[1,1,0,0],[0,1,0,0],
       ['1/4','1/4',0,0],['3/4','1/4',0,0],['1/4','3/4',0,0],['1/4','1/4','1/4',0]]
    faces=[([0,1,2],1),([0,2,3],1),([5,6,7],1),([4,6,7],-1),([4,5,7],1),([4,5,6],-1)]
    data={'base':[0,0,0,0],'vertices':V,'faces':[{'vertices':x,'multiplicity':n} for x,n in faces],
          'energy':{'kind':'truncated_L'},'area_penalty':'1/100'}
    out=verify_filling(data)
    assert out['orientation_counts']=={'positive':3,'vertical':2,'negative':1}
    assert Q(out['gap_interval'][0])>0
    import copy
    bad=copy.deepcopy(data); bad['faces'][2]['multiplicity']=-1
    try: verify_filling(bad)
    except ValueError: pass
    else: raise AssertionError('bad orientation accepted')
    bad=copy.deepcopy(data); bad['faces'][2]['multiplicity']='1/2'
    try: verify_filling(bad)
    except ValueError: pass
    else: raise AssertionError('fractional coefficient accepted')
    print(json.dumps(out,indent=2))
    print('Exact integer boundary and mixed minors, folded/vertical control, orientation and fractional multiplicity rejection: passed.')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate',nargs='?',type=Path)
    p.add_argument('--bits',type=int,default=80)
    args=p.parse_args()
    if args.bits<1: p.error('--bits must be positive')
    if args.certificate is None: control()
    else: print(json.dumps(verify_filling(json.loads(args.certificate.read_text()),args.bits),indent=2))
