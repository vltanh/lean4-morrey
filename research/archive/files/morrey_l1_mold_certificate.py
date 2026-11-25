"""Exact l=1 counterexample to proposed Morrey fixed-point generic-absence B/B1.

Under the standard collinearity convention (determinant zero, including zero
vectors), constructs a Definition 4.1 tri-dyadic mold with a fixed point
at t=(1/48,...,1/48) for *every* periodic P_1 pair (u,v).

Uses exact Fraction arithmetic and separately verifies physical adjacency
on the periodic 2-by-2 triangulation, all weight constraints and all 23
nonautomatic rank-one constraints. No numerical optimizer is involved.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product

HALF = F(1, 2)
ZERO = F(0)
SIGN = (-1, 1)


def tri_grid():
    """Triangle label -> (three signs, three geometric vertices)."""
    out = {}
    for i, j in product(range(2), repeat=2):
        x, y = F(i, 2), F(j, 2)
        vertices = {
            'L': ((x, y), (x + HALF, y), (x, y + HALF)),
            'U': ((x + HALF, y + HALF), (x + HALF, y), (x, y + HALF)),
        }
        for side, vs in vertices.items():
            s = (1 if i == 0 else -1, 1 if j == 0 else -1,
                 (-1) ** (i + j) * (1 if side == 'L' else -1))
            out[i, j, side] = (s, vs)
    return out


def edge_key(p, q):
    # On the torus, same endpoints do not necessarily identify the same
    # physical interface: distinguish the two wraps by their midpoints.
    pts = tuple(sorted((tuple(z % 1 for z in p), tuple(z % 1 for z in q))))
    mid = tuple(((x + y) / 2) % 1 for x, y in zip(p, q))
    return pts, mid


def physical_edges(triangles):
    occurrence = {}
    for (label, (sign, vertices)) in triangles.items():
        for p, q in combinations(vertices, 2):
            occurrence.setdefault(edge_key(p, q), []).append(sign)
    assert len(occurrence) == 12
    assert all(len(v) == 2 for v in occurrence.values())
    edges = set()
    for (a, b) in occurrence.values():
        assert sum(a[k] != b[k] for k in range(3)) == 1
        edges.add(frozenset((a, b)))
    assert len(edges) == 12
    return edges


def mean(a, b):
    return tuple((x + y) / 2 for x, y in zip(a, b))


def subtract(a, b):
    return tuple(x - y for x, y in zip(a, b))


def matrix(coeff, components):
    """Flattened 2x2 matrix = sum_i coeff[i] * (a_i tensor n_i)."""
    return tuple(sum(coeff[k] * components[k][a][b] for k in range(3))
                 for a in range(2) for b in range(2))


def det(m):
    return m[0] * m[3] - m[1] * m[2]


def cross(v, w):
    return v[0] * w[1] - v[1] * w[0]


def make_certificate():
    grid = tri_grid()
    assert set(sign for sign, _ in grid.values()) == set(product(SIGN, repeat=3))
    physical = physical_edges(grid)
    a = ((F(1), F(0)), (F(0), F(1)), (F(1), F(1)))
    n = ((F(1), F(0)), (F(0), F(1)), (F(1), F(1)))
    q = (cross(a[0], a[1]), cross(a[0], a[2]), cross(a[2], a[1]))
    assert q == (1, 1, 1)
    C = tuple(tuple(tuple(a[k][i]*n[k][j] for j in range(2)) for i in range(2))
              for k in range(3))
    assert all(det((r[0][0], r[0][1], r[1][0], r[1][1])) == 0 for r in C)

    triangle_occurrences = Counter()
    edge_occurrences = Counter()
    equations_checked = 0
    submold_info = []
    roots=[]
    for d, e in combinations(range(3), 2):
        h = next(i for i in range(3) if i not in (d, e))
        first_layer_edges = []
        # In the order: h=+ then -, and inside each h sign: direction d,
        # direction e; within each direction, vary the other chosen sign.
        for sign_h in (1, -1):
            for axis in (d, e):
                remaining = next(i for i in range(3) if i not in (axis, h))
                for sign_remaining in (1, -1):
                    left = [None] * 3
                    right = [None] * 3
                    left[h] = right[h] = sign_h
                    left[remaining] = right[remaining] = sign_remaining
                    left[axis], right[axis] = -1, 1
                    left, right = tuple(left), tuple(right)
                    assert frozenset((left, right)) in physical
                    edge_occurrences[frozenset((left, right))] += 1
                    triangle_occurrences[left] += 1
                    triangle_occurrences[right] += 1
                    first_layer_edges.append((left, right))

        assert len(first_layer_edges) == 8
        coeffs = [tuple(F(x) for x in s)
                  for pair in first_layer_edges for s in pair]
        level_summaries=[]
        for level in range(1, 5):
            directions = [subtract(x, y) for x, y in zip(coeffs[::2], coeffs[1::2])]
            matrices = [matrix(diff, C) for diff in directions]
            assert all(sum(x != 0 for x in diff) <= 1 for diff in directions), (d,e,level,directions)
            assert all(det(m) == 0 for m in matrices)
            if level > 1:
                equations_checked += len(directions)
            level_summaries.append((len(directions),
                                    sum(all(x == 0 for x in diff) for diff in directions)))
            coeffs = [mean(x, y) for x, y in zip(coeffs[::2], coeffs[1::2])]
        assert coeffs == [(ZERO, ZERO, ZERO)]
        roots.append(coeffs[0])
        submold_info.append(((d+1, e+1), first_layer_edges, level_summaries))

    assert len(edge_occurrences) == 12
    assert all(v == 2 for v in edge_occurrences.values())
    assert len(triangle_occurrences) == 8
    assert all(v == 6 for v in triangle_occurrences.values())
    assert all(v == (ZERO, ZERO, ZERO) for v in roots)
    # Two final mergers have difference zero.
    equations_checked += 2
    assert equations_checked == 23
    # At l=1 there are 48 leaves of weight 1/48: six copies per triangle,
    # and every first-level interface has two leaves with mass 1/24.
    t = F(1, 48)
    assert 6*t == F(1, 8)
    assert 2*t == F(1, 24)
    print('q =', q)
    print('All 12 physical interfaces checked; 2 copies per interface over 3 submolds.')
    print('Every triangle has 6 occurrences; uniform t = 1/48 lies in Theta_1.')
    for axes, edges, levels in submold_info:
        print('Submold with normals', axes)
        print('  First-stage interface pairs:', edges)
        print('  (number of directions, number zero) by level:', levels)
    print('All 23 nonautomatic equations hold exactly, for every possible C_i.')
    print('Therefore t belongs to T_{1,S*,u,v}(t), including for q=(1,1,1).')


if __name__ == '__main__':
    make_certificate()
