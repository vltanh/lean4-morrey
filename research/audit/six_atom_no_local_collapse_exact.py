#!/usr/bin/env python3
"""Rational certificate: a planar laminate with no compatible <=4-atom collapse.
No numerical optimizer is invoked. The analytic inputs are Mueller's diagonal
Jensen theorem and Faraco--Szekelyhidi's rank-one-free/T4 rigidity theorem.
"""
from fractions import Fraction as Q
from itertools import permutations, product

P = [(5, 2), (0, 2), (0, -10), (8, -10), (8, -6), (5, -6)]
X = [(-15, 2), (0, -22), (32, -10), (8, -2), (2, -6), (5, 26)]
xs = [-15, 0, 2, 5, 8, 32]
ys = [-22, -10, -6, -2, 2, 26]
# Entries of 48960*f at the grid (x rows, y columns).
raw = [
    [48960,-6243,-18944,-31645,-44346,48960],
    [-48960,-47328,-46784,-46240,-45696,-26048],
    [-42840,-47430,-48960,-48186,-45876,-32016],
    [-33660,-47583,-47872,-47009,-46146,-40968],
    [-24480,-47736,-46784,-45832,-44880,-39168],
    [48960,-48960,-38080,-27200,-16320,48960],
]
f = {(x,y): Q(raw[i][j],48960) for i,x in enumerate(xs) for j,y in enumerate(ys)}


def fraction(a,b,z):
    """Return w such that b=(1-w)*a+w*z, along a nonzero rank-one segment."""
    k = 0 if a[0]!=z[0] else 1
    assert a[k]!=z[k] and a[1-k]==b[1-k]==z[1-k]
    w=Q(b[k]-a[k],z[k]-a[k])
    assert 0<w<1
    assert all((1-w)*v+w*u==m for v,u,m in zip(a,z,b))
    return w


def gap(a,b,z):
    w=fraction(a,b,z)
    return (1-w)*f[a]+w*f[z]-f[b]


def cycle_weights(P,X):
    """Reverse splitting cycle at P[0], repeated to infinite depth."""
    remain=Q(1); mass=[Q(0)]*len(X)
    for i in reversed(range(len(X))):
        w=fraction(P[i],P[(i+1)%len(P)],X[i])
        mass[i]=remain*w;remain*=1-w
    assert 0<remain<1
    return [w/(1-remain) for w in mass]


def moment_rows(X):
    return [[1]*len(X), [x for x,y in X], [y for x,y in X], [x*y for x,y in X]]


def mv(A,v):
    return [sum(x*y for x,y in zip(row,v)) for row in A]


def det(A):
    if len(A)==1:return A[0][0]
    return sum((-1)**j*a*det([row[:j]+row[j+1:] for row in A[1:]]) for j,a in enumerate(A[0]))


assert len(set(x for x,y in X))==len(set(y for x,y in X))==6
assert all(-1<=v<=1 for v in f.values())
# Adjacent secant inequalities are exactly separate convexity of the
# piecewise bilinear interpolant; boundary slopes have magnitude <=1.
for x in xs:
    for a,b,c in zip(ys,ys[1:],ys[2:]): assert gap((x,a),(x,b),(x,c))>=0
    for a,b in zip(ys,ys[1:]): assert abs(f[x,b]-f[x,a])<=b-a
for y in ys:
    for a,b,c in zip(xs,xs[1:],xs[2:]): assert gap((a,y),(b,y),(c,y))>=0
    for a,b in zip(xs,xs[1:]): assert abs(f[b,y]-f[a,y])<=b-a
for a,b,z in zip(P,P[1:]+P[:1],X):assert gap(a,b,z)==0
w=cycle_weights(P,X)
assert w==[Q(n,485) for n in [9,36,24,96,192,128]]
assert mv(moment_rows(X),w)==[1,*P[0],P[0][0]*P[0][1]]
assert sum(a*f[x] for a,x in zip(w,X))==f[P[0]]
print('Exact 6-cycle laminate; separator has equality; rank-one-free support.')

# Exhaust all T4 cycles starting with a horizontal step. Every T4 with
# rank-one-free diagonal endpoints has alternating horizontal/vertical
# steps and is represented up to cyclic rotation by two positions.
cycles={}
for a,b,c,d in permutations(X,4):
    if (a,b,c,d)>(c,d,a,b):continue
    pp=[(d[0],a[1]),(b[0],a[1]),(b[0],c[1]),(d[0],c[1])]
    try:
        ww=[fraction(x,y,z) for x,y,z in zip(pp,pp[1:]+pp[:1],(a,b,c,d))]
        if pp[0][1]!=pp[1][1] or pp[1][0]!=pp[2][0] or pp[2][1]!=pp[3][1] or pp[3][0]!=pp[0][0]:continue
    except (AssertionError,ZeroDivisionError):continue
    cycles[(a,b,c,d)]=(pp,ww)
expected = {
    (X[0],X[1],X[2],X[5]):Q(4,255),
    (X[0],X[1],X[3],X[5]):Q(16,765),
    (X[0],X[4],X[3],X[5]):Q(4,255),
}
assert set(cycles)==set(expected)
for zz,(pp,ww) in cycles.items():
    assert det(moment_rows(zz))!=0
    assert sum(gap(a,b,z) for a,b,z in zip(pp,pp[1:]+pp[:1],zz))==expected[zz]
    # Check every corner law (strict energy gap). Any nontrivial
    # compatible law on this T4 has one of these representations by
    # determinant/matrix moments and the explicit rectangle+arms hull.
    margins=[]
    for i in range(4):
        z=list(zz[i:]+zz[:i]);p=pp[i:]+pp[:i]
        c=cycle_weights(p,z)
        assert mv(moment_rows(z),c)==[1,*p[0],p[0][0]*p[0][1]]
        margins.append(sum(v*f[x] for x,v in zip(z,c))-f[p[0]])
    assert min(margins)>0
    print('T4',tuple(X.index(x)+1 for x in zz),'sum of split gaps',expected[zz], 'min corner gap',min(margins),'moment det',det(moment_rows(zz)))
print('All exact certificates passed. No non-Dirac compatible sublaw on <=4 atoms can be collapsed while preserving compatibility.')
print('The entire six-atom law IS a laminate and can be collapsed. No counterexample to Morrey is claimed.')
