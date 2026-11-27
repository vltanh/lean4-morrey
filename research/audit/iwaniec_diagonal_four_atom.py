#!/usr/bin/env python3
"""Exact 4-moment diagonal minor-law sparsifier using rational arithmetic.

Fixes atoms (x_i,y_i), weights and values. Reduces to <=4 positive weights
preserving mass, x, y and xy, with NO increase in average cost.
This is not a proof of universal p>2 polyconvexity.
"""
from fractions import Fraction as Q

def moments(atoms, w):
    return (sum(w),
            sum(t*x for t,(x,y) in zip(w,atoms)),
            sum(t*y for t,(x,y) in zip(w,atoms)),
            sum(t*x*y for t,(x,y) in zip(w,atoms)))

def relation(atoms):
    n=len(atoms)
    assert n>4
    rows=[[Q(1)]*n,[x for x,y in atoms],
          [y for x,y in atoms],[x*y for x,y in atoms]]
    pivots=[]
    rank=0
    for col in range(n):
        pivot=next((k for k in range(rank,4) if rows[k][col]),None)
        if pivot is None: continue
        rows[rank],rows[pivot]=rows[pivot],rows[rank]
        factor=rows[rank][col]
        rows[rank]=[z/factor for z in rows[rank]]
        for k in range(4):
            if k!=rank and rows[k][col]:
                factor=rows[k][col]
                rows[k]=[rows[k][j]-factor*rows[rank][j]
                         for j in range(n)]
        pivots.append(col)
        rank+=1
        if rank==4: break
    free=next(j for j in range(n) if j not in pivots)
    z=[Q(0)]*n
    z[free]=Q(1)
    for k,col in enumerate(pivots):
        z[col]=-rows[k][free]
    assert sum(z)==0 and min(z)<0<max(z)
    return z

def reduce_law(atoms,weights,costs):
    atoms=[(Q(x),Q(y)) for x,y in atoms]
    weights=list(map(Q,weights))
    costs=list(map(Q,costs))
    assert len(atoms)==len(weights)==len(costs)
    assert min(weights)>=0 and sum(weights)==1
    original=moments(atoms,weights)
    initial=sum(w*c for w,c in zip(weights,costs))
    while True:
        kept=[i for i,w in enumerate(weights) if w>0]
        atoms=[atoms[i] for i in kept]
        weights=[weights[i] for i in kept]
        costs=[costs[i] for i in kept]
        if len(atoms)<=4:break
        z=relation(atoms)
        if sum(z[i]*costs[i] for i in range(len(z)))>0:
            z=[-v for v in z]
        step=min(-weights[i]/z[i] for i in range(len(z)) if z[i]<0)
        weights=[weights[i]+step*z[i] for i in range(len(z))]
        assert all(w>=0 for w in weights)
        assert moments(atoms,weights)==original
    assert len(atoms)<=4 and moments(atoms,weights)==original
    assert sum(w*c for w,c in zip(weights,costs))<=initial
    return atoms,weights,costs

def test():
    # A known 3-atom nonpolyconvexity witness (NOT a gradient law).
    atoms=[(-2,-2),(4,0),(0,4)]
    weights=[Q(1,4),Q(3,8),Q(3,8)]
    costs=[Q(0),Q(0),Q(0)]
    assert moments(atoms,weights)==(1,1,1,1)
    assert sum(w*c for w,c in zip(weights,costs))==0
    # 32 additional exact high-cardinality controls
    for seed in range(32):
        n=5+seed%6
        atoms=[(Q((7*j+seed)%13-6,2),
                Q((11*j+3*seed)%17-8,3)) for j in range(n)]
        weights=[Q(1,n)]*n
        costs=[Q((13*j+7*seed)%19,5) for j in range(n)]
        target=moments(atoms,weights)
        initial=sum(w*c for w,c in zip(weights,costs))
        reduced=reduce_law(atoms,weights,costs)
        assert len(reduced[0])<=4
        assert moments(reduced[0],reduced[1])==target
        assert sum(w*c for w,c in zip(reduced[1],reduced[2]))<=initial
    print("PASS: 32 exact 4-moment reductions; <=4 atoms; no cost increase")

if __name__=="__main__":
    test()
