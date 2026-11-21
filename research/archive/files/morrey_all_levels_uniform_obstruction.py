#!/usr/bin/env python3
"""Finite exact certificate for the *all-levels* generic uniform-weight obstruction.

For every dyadic n=2^l, l>=2, consider the periodic n x n triangulation
with lower-left and upper-right triangles in each cell (diagonal x+y=const).
Each physical interface e has an average-gradient operator L_e from scalar
nodal values to R^2. This script certifies that L_e-L_f has rank TWO for
every distinct pair of physical interfaces e,f, for ALL dyadic n>=4.

Checks:
  * For n=4, a direct exhaustive 1128-pair exact check.
  * For n>=8, each interface's local 4-vertex coefficient stencil.
    Disjoint stencils give rank 2 immediately. Overlapping stencils reduce
    to 84 relative-shift/type cases on Z^2, checked exactly below.

Because rank(L_e-L_f)=2, the polynomial
  det((L_e-L_f)u, (L_e-L_f)v)
is nonzero. The product over all e != f is a nonzero polynomial, so its
nonvanishing defines a Zariski-open dense set of pairs (u,v). For such a pair,
no two distinct first-level interface barycenters of the UNIFORM leaf weights
are rank-one-connected; hence for every tri-dyadic mold S,
  t_unif NOT IN T_{l,S,u,v}(t_unif).

This does NOT rule out nonuniform fixed points, nor prove/refute Morrey 2x2.
Pure Python, integer arithmetic, no dependencies.
"""
from itertools import product, combinations
from collections import defaultdict

# Coefficients of (grad of first triangle + grad of second triangle)/n,
# indexed by nodal offsets relative to the base cell. For each interface
# type the 4 nonzero entries are 2-vectors (coefficient of x,y derivative).
stencils = {
    'D': {(0,0):(-1,-1), (1,0):(1,-1), (0,1):(-1,1), (1,1):(1,1)},
    'V': {(0,0):(-1,-2), (1,0):(1,0), (0,1):(1,2), (-1,1):(-1,0)},
    'H': {(0,0):(-2,-1), (1,0):(2,1), (0,1):(0,1), (1,-1):(0,-1)},
}

def rank_of_coefficients(co):
    nonzero=[c for c in co.values() if c!=(0,0)]
    if not nonzero:return 0
    x,y=nonzero[0]
    return 1 if all(x*b-y*a==0 for a,b in nonzero) else 2

def subtract_translated(e,f,dx,dy):
    co=defaultdict(lambda:(0,0))
    for p,(a,b) in stencils[e].items():
        x,y=co[p];co[p]=(x+a,y+b)
    for (px,py),(a,b) in stencils[f].items():
        p=(px+dx,py+dy)
        x,y=co[p];co[p]=(x-a,y-b)
    return co

# Every individual interface stencil has image R^2.
assert all(rank_of_coefficients(co)==2 for co in stencils.values())

# For n>=8, modulo-n collisions of the two supports can occur only when
# the two origins differ by dx,dy with both in [-2,2] modulo n.
# On that range the union of stencil supports has span at most 4 in each
# coordinate (<n), so the Z^2 calculation is identical to the torus.
overlap_cases=0
for e,f in product(stencils,repeat=2):
    for dx,dy in product(range(-2,3),repeat=2):
        if e==f and dx==dy==0:continue  # identical interface
        supp_e=set(stencils[e])
        supp_f={(i+dx,j+dy) for (i,j) in stencils[f]}
        if not supp_e.isdisjoint(supp_f):
            overlap_cases+=1
            rank=rank_of_coefficients(subtract_translated(e,f,dx,dy))
            assert rank==2,(e,f,dx,dy,rank)
assert overlap_cases==84

# Exchange of the two interfaces sends (e,f,dx,dy) to
# (f,e,-dx,-dy), preserving the rank of their difference. Thus the 84
# overlapping oriented cases have only 42 inequivalent orbits.
local_orbits=set()
for e,f in product(stencils,repeat=2):
    for dx,dy in product(range(-2,3),repeat=2):
        if e==f and dx==dy==0:continue
        supp_e=set(stencils[e])
        supp_f={(i+dx,j+dy) for i,j in stencils[f]}
        if not supp_e.isdisjoint(supp_f):
            local_orbits.add(min((e,f,dx,dy),(f,e,-dx,-dy)))
assert len(local_orbits)==42
assert all(rank_of_coefficients(subtract_translated(e,f,dx,dy))==2
           for e,f,dx,dy in local_orbits)

# Exceptional dyadic n=4: some nodes coincide modulo n, so use a direct check.
n=4
interfaces=[(typ,a,b) for typ in stencils for a in range(n) for b in range(n)]
assert len(interfaces)==48

def periodic_stencil(typ,a,b):
    out=defaultdict(lambda:(0,0))
    for (i,j),(x,y) in stencils[typ].items():
        p=((a+i)%n,(b+j)%n)
        v,w=out[p];out[p]=(v+x,w+y)
    return out

# Translation invariance allows us to place the first interface at (0,0).
# Swapping interfaces sends (e,f,dx,dy) to (f,e,-dx,-dy) modulo 4.
# This reduces the 1128 unordered pairs to just 75 different cases.
periodic_orbits={min((e,f,dx,dy),(f,e,(-dx)%n,(-dy)%n))
                 for e,f in product(stencils,repeat=2)
                 for dx,dy in product(range(n),repeat=2)
                 if not (e==f and dx==dy==0)}
assert len(periodic_orbits)==75
for e,f,dx,dy in periodic_orbits:
    co=defaultdict(lambda:(0,0))
    for p,(a,b) in periodic_stencil(e,0,0).items():
        x,y=co[p];co[p]=(x+a,y+b)
    for p,(a,b) in periodic_stencil(f,dx,dy).items():
        x,y=co[p];co[p]=(x-a,y-b)
    assert rank_of_coefficients(co)==2, (e,f,dx,dy)

periodic=[periodic_stencil(*e) for e in interfaces]
for i,j in combinations(range(len(interfaces)),2):
    co=defaultdict(lambda:(0,0))
    for p,(a,b) in periodic[i].items():
        x,y=co[p];co[p]=(x+a,y+b)
    for p,(a,b) in periodic[j].items():
        x,y=co[p];co[p]=(x-a,y-b)
    assert rank_of_coefficients(co)==2,(i,j,interfaces[i],interfaces[j])

print('PASS: each interface stencil independently has rank 2')
print('PASS: all',overlap_cases,'overlapping local cases; only',len(local_orbits),'swap-orbits')
print('PASS: all',len(interfaces)*(len(interfaces)-1)//2,'n=4 pairs; only',len(periodic_orbits),'translation/swap-orbits')
print('FINITE REDUCTION:',len(local_orbits)+len(periodic_orbits),'inequivalent rank checks cover all dyadic levels >=2')
print('THEOREM: for EVERY dyadic n=2^l >=4, every L_e-L_f (e!=f) has rank 2')
print('COROLLARY: generic (u,v) defeat UNIFORM-WEIGHT fixed points of every mold')
print('OPEN: existence of nonuniform fixed points and unrestricted Morrey 2x2')

# A further generic obstruction: a finite-order tree using each triangle
# exactly once with its prescribed equal weight cannot exist for l>=2.
# Triangle gradient stencils (in gradient/n coordinates):
tri_stencils={
    'L':{(0,0):(-1,-1), (1,0):(1,0), (0,1):(0,1)},
    'R':{(1,1):(1,1), (0,1):(-1,0), (1,0):(0,-1)},
}
endpoints={
    'D':{('L',0,0),('R',0,0)},
    'V':{('L',0,0),('R',-1,0)},
    'H':{('L',0,0),('R',0,-1)},
}

def subtract_stencils(first,second,dx,dy,factor=1):
    out=defaultdict(lambda:(0,0))
    for p,(a,b) in first.items():
        x,y=out[p];out[p]=(x+a,y+b)
    for (px,py),(a,b) in second.items():
        p=(px+dx,py+dy)
        x,y=out[p];out[p]=(x-factor*a,y-factor*b)
    return out

def periodic_difference(first,second,dx,dy,factor=1):
    out=defaultdict(lambda:(0,0))
    for (px,py),(a,b) in first.items():
        p=(px%n,py%n);x,y=out[p];out[p]=(x+a,y+b)
    for (px,py),(a,b) in second.items():
        p=((px+dx)%n,(py+dy)%n)
        x,y=out[p];out[p]=(x-factor*a,y-factor*b)
    return out

# All nonadjacent pairs of triangle gradients are independent linear maps.
# At n>=8 the overlap can only occur for offsets in [-2,2]^2.
adjacent_relative={('L','R',-1,0),('L','R',0,-1),('L','R',0,0),
                   ('R','L',0,0),('R','L',0,1),('R','L',1,0)}
tri_overlap=0
for s,t in product(tri_stencils,repeat=2):
    for dx,dy in product(range(-2,3),repeat=2):
        if s==t and dx==dy==0:continue
        a=set(tri_stencils[s]); b={(i+dx,j+dy) for i,j in tri_stencils[t]}
        if not a.isdisjoint(b):
            tri_overlap+=1
            rank=rank_of_coefficients(subtract_stencils(tri_stencils[s],tri_stencils[t],dx,dy))
            assert (rank==1)==((s,t,dx,dy) in adjacent_relative)
assert tri_overlap==24

# No interface-pair barycenter is generically rank-one-connected to any
# third triangle gradient: 42 local overlaps, all full rank.
pair_single_overlap=0
for e,t in product(stencils,tri_stencils):
    for dx,dy in product(range(-2,3),repeat=2):
        if (t,dx,dy) in endpoints[e]:continue
        a=set(stencils[e]); b={(i+dx,j+dy) for i,j in tri_stencils[t]}
        if not a.isdisjoint(b):
            pair_single_overlap+=1
            rank=rank_of_coefficients(subtract_stencils(stencils[e],tri_stencils[t],dx,dy,factor=2))
            assert rank==2,(e,t,dx,dy)
assert pair_single_overlap==42

# n=4 exceptional periodic collision cases: translation reduces all pairs
# to 2*2*16 = 64 relative triangle cases; 6 adjacent cases give rank 1.
n=4
adj_4=0
for s,t in product(tri_stencils,repeat=2):
    for dx,dy in product(range(n),repeat=2):
        if s==t and dx==dy==0:continue
        r=rank_of_coefficients(periodic_difference(tri_stencils[s],tri_stencils[t],dx,dy))
        if r==1:adj_4+=1
        else:assert r==2
assert adj_4==6

# n=4: 90 relative interface+third-triangle cases, all full rank.
case_4=0
for e,t in product(stencils,tri_stencils):
    endpoints_mod={(kind,dx%n,dy%n) for kind,dx,dy in endpoints[e]}
    for dx,dy in product(range(n),repeat=2):
        if (t,dx,dy) in endpoints_mod:continue
        r=rank_of_coefficients(periodic_difference(stencils[e],tri_stencils[t],dx,dy,factor=2))
        assert r==2,(e,t,dx,dy)
        case_4+=1
assert case_4==90
print('PASS: generic singleton pair constraint: 24 local overlap cases + 6 n=4 adjacency classes')
print('PASS: generic 3-leaf obstruction: 42 local cases + 90 exceptional n=4 relative cases')
print('THEOREM: for each l>=2, GENERIC dyadic gradient measures have no')
print('         equal-mass single-use binary lamination tree (duplicated leaves remain possible)')

# Contrast: the exceptional l=1 torus n=2 has accidental modulo-2
# identities of the interface midpoint stencils (the eight-sign cube).
n=2
small=[periodic_stencil(typ,a,b)
       for typ in stencils for a in range(n) for b in range(n)]
rankone_pairs=0
for i,j in combinations(range(len(small)),2):
    co=defaultdict(lambda:(0,0))
    for p,(a,b) in small[i].items():
        x,y=co[p];co[p]=(x+a,y+b)
    for p,(a,b) in small[j].items():
        x,y=co[p];co[p]=(x-a,y-b)
    if rank_of_coefficients(co)<=1:rankone_pairs+=1
assert rankone_pairs==12
print('EXCEPTION: at l=1, exactly 12 distinct interface pairs have rank <=1 difference')
