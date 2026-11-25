from fractions import Fraction as Q
from itertools import product, combinations, combinations_with_replacement
from collections import defaultdict
from math import floor, ceil


def clip(poly,a,b,c):
    """Intersect with ax+by<=c using exact rational arithmetic."""
    out=[]
    if not poly: return out
    for p,q in zip(poly,poly[1:]+poly[:1]):
        f=a*p[0]+b*p[1]-c; g=a*q[0]+b*q[1]-c
        if f<=0: out.append(p)
        if (f<0<g) or (g<0<f):
            t=f/(f-g); out.append(tuple(x+t*(y-x) for x,y in zip(p,q)))
    return out


def area(poly):
    return abs(sum((p[0]*q[1]-p[1]*q[0] for p,q in zip(poly,poly[1:]+poly[:1])),Q(0)))/2 if poly else Q(0)


def exact_law(K,phases):
    cells=[((),[(Q(0),Q(0)),(Q(1),Q(0)),(Q(1),Q(1)),(Q(0),Q(1))])]
    for (a,b),c in zip(K,phases):
        new=[]
        lo=floor(2*(min(a,0)+min(b,0)+c)); hi=ceil(2*(max(a,0)+max(b,0)+c))
        for e,P in cells:
            for j in range(lo,hi):
                R=clip(P,a,b,Q(j+1,2)-c)
                R=clip(R,-a,-b,c-Q(j,2))
                if area(R)>0: new.append((e+((1 if j%2==0 else -1),),R))
        cells=new
    out=defaultdict(Q)
    for e,P in cells: out[e]+=area(P)
    assert sum(out.values())==1
    return dict(out)


def walsh(law,S):
    return sum((w*prod(e[i] for i in S) for e,w in law.items()),Q(0))


def prod(xs):
    p=1
    for x in xs: p*=x
    return p


def nonzero_moments(K,c):
    law=exact_law(K,c)
    return {tuple(i+1 for i in S):v for j in range(1,5) for S in combinations(range(4),j) if (v:=walsh(law,S))}


def check_patterns():
    classes=((0,0),(1,0),(0,1),(1,1)); counts=defaultdict(int)
    for pattern in combinations_with_replacement(classes,4):
        if len(set(pattern)-{(0,0)})<2: continue
        triples=[S for S in combinations(range(4),3) if all(sum(pattern[i][j] for i in S)%2==0 for j in range(2))]
        quad=all(sum(k[j] for k in pattern)%2==0 for j in range(2))
        assert len(triples)<=2 and not (len(triples)==2 and quad)
        counts[len(triples),quad]+=1
    print('normalized rank-two mod-2 multisets:',sum(counts.values()),sorted(counts.items()))


def check_corners():
    # All six generating points of the parallel-pair outer polytope.
    for u,v in ((0,0),(1,0),(0,1)):
        for c in (u-1,1-v):
            a,b=Q(u+v,2),Q(u-v,2)
            weights={e:Q(1,16)*(1+c*e[0]*e[1]+a*e[0]*e[2]*e[3]+b*e[1]*e[2]*e[3]) for e in product((-1,1),repeat=4)}
            assert min(weights.values())>=0 and sum(weights.values())==1
            if abs(c)==1:
                merged=defaultdict(Q)
                for e,w in weights.items():
                    if w:
                        assert e[1]==c*e[0]
                        merged[e[0],e[2],e[3]]+=w
                rho=walsh(merged,(0,1,2))
                assert abs(rho)<=Q(1,2)
            else:
                assert c==0 and abs(a)==abs(b)==Q(1,2)
    print('six parallel-pair generating points: exact masses and merged parity passed')


def main():
    check_patterns();check_corners()
    K=((1,0),(0,1),(1,1),(1,-1)); c=(Q(0),Q(0),Q(1,4),Q(1,4))
    D=nonzero_moments(K,c); print('unit double triad:',D)
    assert set(D)=={(1,2,3),(1,2,4)} and all(abs(v)==Q(1,2) for v in D.values())
    K=((1,0),(0,1),(1,1),(2,-2)); T=nonzero_moments(K,c); print('triple + quadruple:',T)
    assert T=={(1,2,3):Q(-1,2),(1,2,3,4):Q(1,4)}
    print('two exact actual-gradient controls passed; both exceed old total-parity budget')


if __name__=='__main__': main()
