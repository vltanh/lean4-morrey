"""Numerical model of Pedregal arXiv:1905.06571v5, Sections 4-7.

tau_l: unit square, n=2^l cells per side, each cell (a,b) split by the anti-diagonal
(normal (1,1)) into L(a,b) (vertices (a,b),(a+1,b),(a,b+1)) and U(a,b).
Interfaces (periodic):  V(a,b) normal (1,0): U(a,b) | L(a+1,b)
                        H(a,b) normal (0,1): U(a,b) | L(a,b+1)
                        D(a,b) normal (1,1): L(a,b) | U(a,b)
Tree j=1 uses V,H; j=2 uses V,D; j=3 uses H,D   (eq. (4.2)).
A mold = for each j an ordering of its 2n^2 interfaces (+ which side is leaf 2i-1),
then dyadic [2p-1,2p] above; final mixing [[W1,W2],W3].
"""
import numpy as np
from fractions import Fraction as Fr
import itertools, random

def tri_index(n, kind, a, b):  # kind 0 = L, 1 = U
    return 2 * ((a % n) * n + (b % n)) + kind

def gradients(n, w):
    """w: n x n nodal values; returns array (2n^2, 2) of gradients on triangles."""
    h = 1.0 / n
    G = [None] * (2 * n * n)
    for a in range(n):
        for b in range(n):
            w00 = w[a % n][b % n]; w10 = w[(a+1) % n][b % n]
            w01 = w[a % n][(b+1) % n]; w11 = w[(a+1) % n][(b+1) % n]
            G[tri_index(n, 0, a, b)] = ((w10 - w00) / h, (w01 - w00) / h)
            G[tri_index(n, 1, a, b)] = ((w11 - w01) / h, (w11 - w10) / h)
    return G

def interfaces(n):
    V = [(tri_index(n,1,a,b), tri_index(n,0,a+1,b)) for a in range(n) for b in range(n)]
    H = [(tri_index(n,1,a,b), tri_index(n,0,a,b+1)) for a in range(n) for b in range(n)]
    D = [(tri_index(n,0,a,b), tri_index(n,1,a,b)) for a in range(n) for b in range(n)]
    return {1: V + H, 2: V + D, 3: H + D}

def make_mold(n, rng=None):
    """returns leaf_tri[j][k] for k=0..4n^2-1 (leaf 2i,2i+1 are interface i, 0-based)."""
    ifs = interfaces(n)
    mold = {}
    for j in (1, 2, 3):
        lst = list(ifs[j])
        if rng is not None:
            rng.shuffle(lst)
            lst = [(p, q) if rng.random() < .5 else (q, p) for (p, q) in lst]
        leaves = []
        for (p, q) in lst:
            leaves += [p, q]
        mold[j] = leaves
    return mold

def check_mold(n, mold):
    # each triangle appears exactly twice in each tree (6 times total): partition C_s
    for j in (1, 2, 3):
        cnt = [0] * (2 * n * n)
        for s in mold[j]:
            cnt[s] += 1
        assert all(c == 2 for c in cnt), cnt

def tree_nodes(N):
    """internal nodes above the interface level of a dyadic tree with N interface nodes
    (N power of 2): list of (left_set, right_set) of interface indices."""
    nodes = []
    groups = [[i] for i in range(N)]
    while len(groups) > 1:
        new = []
        for p in range(0, len(groups), 2):
            nodes.append((groups[p], groups[p+1]))
            new.append(groups[p] + groups[p+1])
        groups = new
    return nodes

def direction_rows(n, mold, G):
    """For gradients G (per triangle) return, for every constrained node, the linear map
    r -> direction (2 x 48-ish matrix).  Global leaf index g = (j-1)*4n^2 + k."""
    NL = 4 * n * n          # leaves per tree
    NI = 2 * n * n          # interfaces per tree
    c = 1.0 / (3 * NI)      # pair sum
    tot = 3 * NL
    # interface point x_i(r) = (r_{2i} G_{2i} + r_{2i+1} G_{2i+1}) / c  (0-based)
    def x_map(j, i):
        M = np.zeros((2, tot))
        for k in (2*i, 2*i+1):
            g = (j-1)*NL + k
            M[:, g] = np.array(G[mold[j][k]]) / c
        return M
    rows = []
    roots = {}
    for j in (1, 2, 3):
        X = [x_map(j, i) for i in range(NI)]
        for (Lset, Rset) in tree_nodes(NI):
            ML = sum(X[i] for i in Lset) / len(Lset)
            MR = sum(X[i] for i in Rset) / len(Rset)
            rows.append(ML - MR)
        roots[j] = sum(X) / NI
    rows.append(roots[1] - roots[2])
    rows.append((roots[1] + roots[2]) / 2 - roots[3])
    return rows

def theta_constraints(n, mold):
    NL = 4*n*n; NI = 2*n*n; tot = 3*NL
    A = []; b = []
    for j in (1, 2, 3):
        for i in range(NI):
            row = np.zeros(tot); row[(j-1)*NL + 2*i] = 1; row[(j-1)*NL + 2*i+1] = 1
            A.append(row); b.append(1.0/(3*NI))
    for s in range(2*n*n):
        row = np.zeros(tot)
        for j in (1, 2, 3):
            for k in range(NL):
                if mold[j][k] == s:
                    row[(j-1)*NL + k] = 1
        A.append(row); b.append(1.0/(2*n*n))
    return np.array(A), np.array(b)

def T_constraints(n, mold, Gu, Gv, t):
    """rows of det(U_node(t), V_node(r)) = 0, linear in r."""
    Ru = direction_rows(n, mold, Gu)
    Rv = direction_rows(n, mold, Gv)
    A = []
    for Mu, Mv in zip(Ru, Rv):
        U = Mu @ t
        A.append(U[0] * Mv[1] - U[1] * Mv[0])
    return np.array(A)
