#!/usr/bin/env python3
"""Exact rational counterexamples to support-only pair and arbitrary T4 collapse.
All laws are diagonal. Compatibility uses the explicit laminate tree/cycle
proof and Mueller's diagonal theorem, not just determinant moments.
"""
from fractions import Fraction as Q
from itertools import combinations
from collections import defaultdict


def point(x, y):
    return Q(x), Q(y)


def rank_one(x, y):
    return x != y and (x[0] == y[0] or x[1] == y[1])


def mix(x, y, a):
    return tuple(a * z + (1 - a) * w for z, w in zip(x, y))


def energy(x):
    return max(x[0], 0) * max(x[1], 0)


def moments(law):
    return tuple(sum(w * f(x) for x, w in law.items()) for f in
                 (lambda x: 1, lambda x: x[0], lambda x: x[1],
                  lambda x: x[0] * x[1], energy))


def cycle(P, X):
    """At P[0], repeatedly split backwards around the rank-one cycle."""
    remain = Q(1)
    mass = defaultdict(Q)
    for i in reversed(range(4)):
        a, b, x = P[i], P[(i + 1) % 4], X[i]
        assert rank_one(a, x)
        axis = 0 if a[0] != x[0] else 1
        w = (b[axis] - a[axis]) / (x[axis] - a[axis])
        assert 0 < w < 1 and mix(x, a, w) == b
        mass[x] += remain * w
        remain *= 1 - w
    ans = {x: w / (1 - remain) for x, w in mass.items()}
    assert moments(ans)[:4] == (1, *P[0], P[0][0] * P[0][1])
    return ans


def rectangle(u, v, a, b):
    P = [point(u, v), point(u+a, v), point(u+a, v+b), point(u, v+b)]
    X = [point(u+2*a, v), point(u+a, v+2*b), point(u-a, v+b), point(u, v-b)]
    return P, X


def replace(law, x, child):
    assert sum(child.values()) == 1
    assert moments(child)[:4] == (1, *x, x[0] * x[1])
    w = law.pop(x)
    for y, v in child.items():
        law[y] = law.get(y, Q(0)) + w * v


def split(law, x, y, z, w):
    assert rank_one(y, z) and mix(y, z, w) == x
    replace(law, x, {y: w, z: 1-w})


A = point(1, 1)
nu = {A: Q(1)}
split(nu, A, point(0, 1), point(2, 1), Q(1, 2))
split(nu, point(2, 1), point(2, 0), point(2, 2), Q(1, 2))
split(nu, point(2, 0), point(-1, 0), point(5, 0), Q(1, 2))
P, X = rectangle(Q(2), Q(2), Q(1,10), Q(1,10))
positive = cycle(P, X)
assert [positive[x] for x in X] == [Q(1,15), Q(2,15), Q(4,15), Q(8,15)]
replace(nu, point(2, 2), positive)
P, X = rectangle(Q(-9,8), Q(-2,3), Q(1,4), Q(4,3))
negative = defaultdict(Q)
for i in range(4):
    for x, w in cycle(P[i:]+P[:i], X[i:]+X[:i]).items():
        negative[x] += w / 4
assert all(w == Q(1,4) for w in negative.values())
# The four corners form a two-step laminate centered at (-1,0).
assert mix(mix(P[0], P[1], Q(1,2)), mix(P[3], P[2], Q(1,2)), Q(1,2)) == point(-1,0)
replace(nu, point(-1,0), negative)
assert len(nu) == 10
assert moments(nu) == (1, 1, 1, 1, 1)
pairs = [frozenset((x,y)) for x,y in combinations(nu,2) if rank_one(x,y)]
left, right = point(Q(-7,8),2), point(Q(11,5),2)
assert pairs == [frozenset((left,right))]
assert nu[left] == Q(1,32) and nu[right] == Q(1,60)


def merge(law, x, y, a, b):
    assert 0 < a <= law[x] and 0 < b <= law[y]
    out = law.copy()
    out[x] -= a
    out[y] -= b
    z = mix(x,y,a/(a+b))
    out[z] = out.get(z,Q(0)) + a+b
    return {p: w for p,w in out.items() if w}

for i in range(1,11):
    for j in range(1,11):
        a, b = nu[left]*Q(i,10), nu[right]*Q(j,10)
        out = merge(nu,left,right,a,b)
        assert moments(out)[:4] == moments(nu)[:4]
        assert moments(out)[4] == 1 - 2*min(Q(7,8)*a,Q(11,5)*b) < 1
full = merge(nu,left,right,nu[left],nu[right])
assert moments(full)[4] == 1-Q(7,128)
print('10-atom exact laminate; unique rank-one pair; whole merge violates diagonal Jensen by 7/128.')
print('100 rational partial merges preserve minors and violate the same Jensen inequality.')

# A different T4 selected across branches also cannot be removed, even
# in an arbitrarily small proportion. Its endpoint law is a laminate.
P = [point(Q(-5,8), Q(19,10)), point(Q(19,10), Q(19,10)),
     point(Q(19,10), 2), point(Q(-5,8), 2)]
X = [point(2,Q(19,10)), point(Q(19,10),Q(21,10)),
     left, point(Q(-5,8),Q(-2,3))]
mu = cycle(P,X)
assert all(x in nu for x in mu)
assert energy(P[0]) == 0 and moments(mu)[4] > 0
max_amount = min(nu[x]/w for x,w in mu.items())
for i in range(1,11):
    a = max_amount*Q(i,10)
    out = nu.copy()
    for x,w in mu.items(): out[x] -= a*w
    out[P[0]] = out.get(P[0],Q(0))+a
    assert all(w>=0 for w in out.values())
    assert moments(out)[:4] == moments(nu)[:4]
    assert moments(out)[4] == 1-a*moments(mu)[4] < 1
print('Mixed T4 collapse: every positive feasible amount violates diagonal Jensen; ten rational controls passed.')
print('Mixed T4 energy:', moments(mu)[4], 'maximal removable mass:', max_amount)
# Valid moves still exist: collapse either of the two nested original
# T4 laminates, returning to the outer explicit finite splitting tree.
assert moments(positive)[4] == 4 and moments(negative)[4] == 0
print('Scope: refutes existential pair-only merging and arbitrary T4 removal; does not refute existential pair-or-T4 collapse or Morrey.')
