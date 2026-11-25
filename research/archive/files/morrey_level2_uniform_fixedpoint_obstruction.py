#!/usr/bin/env python3
"""Exact certificate: at l=2 one pair (u,v) has no uniform-weight
fixed point for ANY tri-dyadic mold of Pedregal's type.

Each scalar function is the periodic piecewise-affine interpolation of its
4x4 nodal array. We use gradients divided by 4, an irrelevant common factor.
The first-level barycenter for an interface is the midpoint of the two
adjacent triangle gradients. For the uniform weight vector to be a fixed
point, every higher merger has to connect rank-one-compatible first-level
barycenters. We check that no two different interface barycenters are
rank-one-compatible for this particular pair (u,v).

Uses only integer arithmetic and standard Python. Not a Lean formalization.
"""
from itertools import combinations

N = 4
# Values at (a,b), index a*N+b, for a,b in range(4).
U = (70, 28, 2, -46, -39, -92, -85, -97,
     -65, 63, 30, 83, 1, 21, 95, 46)
V = (27, 9, 12, 87, -45, 63, 34, -100,
     -21, 72, 11, -94, 53, 46, 70, -65)

def value(nodes, a, b):
    return nodes[(a % N) * N + (b % N)]

def gradient(nodes, a, b, k):
    # Lower-left triangle k=0, upper-right triangle k=1,
    # both of the square with lower-left corner (a/4,b/4).
    if k == 0:
        return (value(nodes,a+1,b)-value(nodes,a,b),
                value(nodes,a,b+1)-value(nodes,a,b))
    return (value(nodes,a+1,b+1)-value(nodes,a,b+1),
            value(nodes,a+1,b+1)-value(nodes,a+1,b))

def mat_for_triangle(a, b, k):
    return (gradient(U,a,b,k),gradient(V,a,b,k))

def add2(x,y):
    return (x[0]+y[0],x[1]+y[1])

def sub2(x,y):
    return (x[0]-y[0],x[1]-y[1])

def det2(x,y):
    return x[0]*y[1]-x[1]*y[0]

# An interface is two neighboring triangles.  There are exactly
# 16 diagonal, 16 vertical, and 16 horizontal periodic interfaces.
interfaces=[]
for a in range(N):
  for b in range(N):
    diag=((a,b,0),(a,b,1))
    vertical=((a,b,0),((a-1)%N,b,1))
    horizontal=((a,b,0),(a,(b-1)%N,1))
    interfaces += [('diagonal',a,b,diag),
                   ('vertical',a,b,vertical),
                   ('horizontal',a,b,horizontal)]
assert len(interfaces)==48
assert len(set(tuple(sorted(t)) for _,_,_,t in interfaces))==48

# First-level MIDPOINT = (A+B)/2.  Avoid fractions by using A+B.
# An above-first merger between interfaces e and f has difference
# (s_e - s_f)/2, so its determinant is det(s_e - s_f)/4.
interface_sums=[]
for _, a, b, tris in interfaces:
    p=mat_for_triangle(*tris[0]); q=mat_for_triangle(*tris[1])
    interface_sums.append((add2(p[0],q[0]),add2(p[1],q[1])))

determinants=[]
for i,j in combinations(range(48),2):
    du=sub2(interface_sums[i][0],interface_sums[j][0])
    dv=sub2(interface_sums[i][1],interface_sums[j][1])
    d=det2(du,dv)
    determinants.append(d)
    assert d!=0, ('failure', i, j, interfaces[i], interfaces[j])

assert len(determinants)==1128
assert min(map(abs,determinants))==7

# Independent check: the underlying triangle neighbor graph is exactly
# the set of universal rank-one pairs in the coefficient representation.
def linear_gradient(a,b,k):
    gx=[0]*(N*N);gy=[0]*(N*N)
    def inc(g,i,j,sgn): g[(i%N)*N+(j%N)] += sgn
    if k==0:
        inc(gx,a+1,b,1); inc(gx,a,b,-1)
        inc(gy,a,b+1,1); inc(gy,a,b,-1)
    else:
        inc(gx,a+1,b+1,1); inc(gx,a,b+1,-1)
        inc(gy,a+1,b+1,1); inc(gy,a+1,b,-1)
    return gx,gy

def linear_rank_le_one(c):
    x,y=c
    piv=next((i for i,v in enumerate(x) if v!=0),None)
    return piv is None or all(x[piv]*y[i]==y[piv]*x[i] for i in range(N*N))

tris=[(a,b,k) for a in range(N) for b in range(N) for k in (0,1)]
coeffs={t:linear_gradient(*t) for t in tris}
rank_one_edges=set()
for t,s in combinations(tris,2):
    diff=([coeffs[t][0][h]-coeffs[s][0][h] for h in range(16)],
          [coeffs[t][1][h]-coeffs[s][1][h] for h in range(16)])
    if linear_rank_le_one(diff):rank_one_edges.add(frozenset((t,s)))
assert rank_one_edges=={frozenset(e[3]) for e in interfaces}

print('PASS: 48 physical periodic interfaces verified exactly')
print('PASS: 1128/1128 distinct-interface midpoint differences have nonzero determinant')
print('Minimum absolute integer determinant:',min(map(abs,determinants)))
print('PASS: all 48 universal rank-one pairs of triangles are precisely interfaces')
print('Consequence: uniform t not in T_{2,S,u,v}(t) for ANY tri-dyadic mold S.')

# Additional finite-order obstruction if every atom occurs exactly once.
# We show there is NO rank-one binary splitting tree whose 32 leaves are
# the 32 distinct triangle gradients with mass 1/32 each.
tri_mats={t:mat_for_triangle(*t) for t in tris}
physical_edges={frozenset(pair) for _,_,_,pair in interfaces}
non_edges=[(a,b) for a,b in combinations(tris,2)
           if frozenset((a,b)) not in physical_edges]
def mat_sum(items):
    out=((0,0),(0,0))
    for t in items:
        M=tri_mats[t]
        out=(add2(out[0],M[0]),add2(out[1],M[1]))
    return out
def det_sumdiff(L,R,coefR=1,coefL=1):
    l,r=mat_sum(L),mat_sum(R)
    return det2(sub2((coefL*l[0][0],coefL*l[0][1]),
                     (coefR*r[0][0],coefR*r[0][1])),
                sub2((coefL*l[1][0],coefL*l[1][1]),
                     (coefR*r[1][0],coefR*r[1][1])))

# Non-adjacent singleton pairings are impossible for this particular u,v.
assert len(non_edges)==448
assert all(det_sumdiff((a,),(b,))!=0 for a,b in non_edges)
# Check that even adjacent atoms are distinct, despite rank-one jumps.
assert all(tri_mats[a]!=tri_mats[b] for a,b in (e[3] for e in interfaces))

# The first subtree with >2 leaves contains either 3 leaves (pair+single)
# or 4 leaves (pair+pair). Both are impossible with uniform singleton masses.
three=0
for a,b in (e[3] for e in interfaces):
    for t in tris:
        if t==a or t==b: continue
        # Compare (grad(a)+grad(b))/2 with grad(t).
        assert det_sumdiff((a,b),(t,),coefR=2)!=0
        three+=1
assert three==1440
four=0
for e,f in combinations((e[3] for e in interfaces),2):
    if len(set(e+f))<4:continue
    assert det_sumdiff(e,f)!=0
    four+=1
assert four==1032
print('PASS: 448 nonadjacent triangle-pair determinants nonzero')
print('PASS: 1440 pair+singleton and 1032 disjoint pair+pair determinants nonzero')
print('Consequence: this 32-atom measure has NO single-use 32-leaf laminate tree.')
print('CAUTION: this does NOT exclude trees with duplicated atoms or nonuniform leaf weights.')

# Strengthening: exclude an explicit neighborhood of uniform first-level
# relative weights, simultaneously for all molds.
# Let alpha_e be the fraction on the first triangle at physical interface e.
# M_e(alpha) = (g_A+g_B)/2 + (alpha-1/2)*(g_A-g_B).
# Since each jump g_A-g_B has determinant zero, the determinant of
# M_e(alpha_e)-M_f(alpha_f) is separately AFFINE in alpha_e,alpha_f.
# Consequently, if all 4 corners of a rectangle have the same nonzero sign,
# the determinant is nonzero everywhere in that rectangle.
Q=8192
edge_sums_diffs=[]
for _,_,_,(a,b) in interfaces:
    A=mat_for_triangle(*a);B=mat_for_triangle(*b)
    D=(sub2(A[0],B[0]),sub2(A[1],B[1]))
    assert det2(D[0],D[1])==0
    S=(add2(A[0],B[0]),add2(A[1],B[1]))
    edge_sums_diffs.append((S,D))
corner_count=0
for (S,D),(T,E) in combinations(edge_sums_diffs,2):
    P=(sub2(S[0],T[0]),sub2(S[1],T[1]))
    base=det2(P[0],P[1])
    assert base!=0
    for sigma,tau in ((-1,-1),(-1,1),(1,-1),(1,1)):
        # 2Q*(M_e-M_f) = Q*(S-T)+2sigma*D-2tau*E
        X=(Q*P[0][0]+2*sigma*D[0][0]-2*tau*E[0][0],
           Q*P[0][1]+2*sigma*D[0][1]-2*tau*E[0][1])
        Y=(Q*P[1][0]+2*sigma*D[1][0]-2*tau*E[1][0],
           Q*P[1][1]+2*sigma*D[1][1]-2*tau*E[1][1])
        assert det2(X,Y)*base>0
        corner_count+=1
assert corner_count==4512
print('PASS: 4512/4512 exact corner signs, allowing relative weights 1/2 +/- 1/8192')
print('Consequence: an open neighborhood of uniform weights contains NO fixed')
print('points of any level-two tri-dyadic mold for this explicit pair (u,v).')
