"""Exact rational controls of phase-filtration obstruction and minor traps.
These are algebraic regression tests, not a proof of the all-gradient gate.
"""
from fractions import Fraction as Q
from itertools import product, combinations
from random import Random


def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(t,a): return tuple(t*x for x in a)
def cmul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def conj(a): return (a[0],-a[1])
def norm2(a): return sum(x*x for x in a)
def det(a): return a[0]*a[3]-a[1]*a[2]
def mean(xs): return tuple(sum(t)/len(xs) for t in zip(*xs))


def check_filtrations():
    # Uniform phase values on the fourth roots of unity. Four auxiliary
    # copies of each pair permit randomized observations of the phase pair.
    roots=((Q(1),Q(0)),(Q(0),Q(1)),(Q(-1),Q(0)),(Q(0),Q(-1)))
    rows=[(u,v,cmul(u,v)) for u,v,_ in product(roots,roots,range(4))]
    n=len(rows); K=((1,0),(0,1),(1,1)); rng=Random(20261123)
    def field(r,i,j,a,b): return tuple(r[i][a]*k for k in K[i])+tuple(r[j][b]*k for k in K[j])
    fields=[(i,j,a,b) for i,j in combinations(range(3),2) for a,b in product(range(2),repeat=2)]
    for _ in range(64):
        perm=list(range(n)); rng.shuffle(perm)
        # Arbitrary binary tree of successive random balanced partitions,
        # stopped at a random depth, with one final full reveal.
        depth=rng.randrange(7); levels=[[mean([r[k] for r in rows]) for k in range(3)] for _ in rows]
        prev=levels; z=(Q(0),Q(0)); product_sum=z; cross_cost=Q(0); costs=[Q(0)]*len(fields)
        for j in range(1,depth+2):
            if j==depth+1: cur=rows
            else:
                cur=[None]*n; size=n//(2**j)
                for off in range(0,n,size):
                    idx=perm[off:off+size]; v=tuple(mean([rows[i][k] for i in idx]) for k in range(3))
                    for i in idx: cur[i]=v
            for P,N in zip(prev,cur):
                u,v,w=P; U,V,W=N; du,dv,dw=(sub(x,y) for x,y in zip(N,P))
                term=add(cmul(conj(dw),add(cmul(u,dv),cmul(v,du))),cmul(conj(W),cmul(du,dv)))
                product_sum=add(product_sum,scale(Q(1,n),term))
                for h,(i,k,a,b) in enumerate(fields):
                    H=sub(field(N,i,k,a,b),field(P,i,k,a,b)); d=abs(det(H))
                    cross_cost+=d/n
                    costs[h]+=(norm2(H)/2 if j==depth+1 else d)/n
            prev=cur
        assert product_sum==(Q(1),Q(0)),product_sum
        assert cross_cost>=1 and sum(costs)>=1 and max(costs)>=Q(1,12)
    print('64 randomized rational phase filtrations: exact product identity and total defect >= 1 passed')


def check_traps():
    # q(Y)=tr(Y), E Y=0, E q=0: two separated sheets of det(Y-I)=1.
    for points,weights in [
        ([(-1,0,0,Q(1,2)),(Q(1,2),0,0,-1),(2,0,0,2)], [Q(4,9),Q(4,9),Q(1,9)]),
        ([(-1,0,0,Q(1,2)),(Q(1,2),0,0,-1),
          (Q(-1,25),Q(-18,25),Q(-18,25),Q(-23,50)),
          (Q(-23,50),Q(18,25),Q(18,25),Q(-1,25)),(2,0,0,2)],
         [Q(2,9)]*4+[Q(1,9)])]:
        assert sum(weights)==1
        assert tuple(sum(w*p[i] for p,w in zip(points,weights)) for i in range(4))==(0,0,0,0)
        assert all(det(p)==p[0]+p[3] and det(sub(p,(1,0,0,1)))==1 for p in points)
        assert sum(w*det(p) for p,w in zip(points,weights))==0
        assert any(p[0]+p[3]>2 for p in points) and any(p[0]+p[3]<2 for p in points)
    # Positive-likelihood exact minor-preserving rank-one split of a full product law.
    X=[(Q(a),Q(0),Q(0),Q(b)) for a,b in product((-1,1),repeat=2)]
    for s in (-1,1):
        p=[(1+s*x[0]/2)/4 for x in X]; M=tuple(sum(w*x[i] for w,x in zip(p,X)) for i in range(4))
        assert sum(p)==1 and min(p)>0 and M==(Q(s,2),0,0,0)
        assert sum(w*det(x) for w,x in zip(p,X))==det(M)==0
    print('two exact 2D/3D minor-trap controls and positive-likelihood rank-one split passed')


if __name__=='__main__': check_filtrations(); check_traps()
