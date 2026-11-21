"""l = 1: for a generic instance (integer nodal values u, v from the seed, a random interior t in
Theta_1), is T(t) empty for EVERY tri-dyadic mold? Child order and leaf orientation do not affect
feasibility, so a mold is a triple of sub-mold shapes (perfect binary trees on the 8 interfaces of
each sub-mold, children unordered: 315 shapes) and the order of the last mixtures; leaving out the
two conditions of the last mixtures only weakens the system, so it suffices to check the shape
triples. Usage: python3 -I every_mold.py [seed]   (seed 11 in REPORT.md; a few minutes)."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import *
import itertools
import numpy.linalg as la
from scipy.optimize import linprog

n = 2; NL = 16; c = 1 / 24
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 11)
u = rng.integers(-3, 4, (2, 2)).astype(float); u[0, 0] = 0
v = rng.integers(-3, 4, (2, 2)).astype(float); v[0, 0] = 0
print("u", u.tolist(), "v", v.tolist(), flush=True)
Gu = np.array(gradients(n, u)); Gv = np.array(gradients(n, v))
IF = interfaces(n)


def shapes(items):
    items = list(items)
    if len(items) == 1:
        yield items[0]; return
    first = items[0]; rest = items[1:]; h = len(items) // 2
    for comb in itertools.combinations(rest, h - 1):
        L = [first] + list(comb); R = [x for x in rest if x not in comb]
        for a in shapes(L):
            for b in shapes(R):
                yield (a, b)


def leaves(s):
    return [s] if not isinstance(s, tuple) else leaves(s[0]) + leaves(s[1])


def nodes_of(sh):
    if not isinstance(sh, tuple): return []
    return [(leaves(sh[0]), leaves(sh[1]))] + nodes_of(sh[0]) + nodes_of(sh[1])


# generic t in Theta: lam[j][i] = relative weight of side B of interface i in sub-mold j,
# with the 8 triangle sums fixed: solve for a random point of the affine set near 1/2
def theta_point():
    import numpy.linalg as la
    rows = []; idx = [(j, i) for j in (1, 2, 3) for i in range(8)]
    A = np.zeros((8, 24)); b = np.zeros(8)
    for col, (j, i) in enumerate(idx):
        Aa, Bb = IF[j][i]
        A[Aa, col] -= 1; b[Aa] -= 1      # side A gets 1 - lam
        A[Bb, col] += 1                  # side B gets lam
    b = b + 3                            # each triangle: sum = 3 (units of c)
    lam0 = np.full(24, 0.5); N = la.svd(A)[2][la.matrix_rank(A):]
    lam = lam0 + N.T @ rng.uniform(-0.2, 0.2, N.shape[0])
    assert np.allclose(A @ lam, b) and lam.min() > 0 and lam.max() < 1
    return {(j, i): lam[k] for k, (j, i) in enumerate(idx)}
LAM = theta_point()
def tree_data(j):
    ifs = IF[j]
    Xu = [(1 - LAM[(j, i)]) * Gu[A] + LAM[(j, i)] * Gu[B] for i, (A, B) in enumerate(ifs)]
    Mv = [np.zeros((2, NL)) for _ in ifs]
    inc = np.zeros((8, NL))
    for i, (A, B) in enumerate(ifs):
        Mv[i][:, 2 * i] = Gv[A] / c; Mv[i][:, 2 * i + 1] = Gv[B] / c
        inc[A, 2 * i] = 1; inc[B, 2 * i + 1] = 1
    return Xu, Mv, inc


B = {}
for j in (1, 2, 3):
    Xu, Mv, inc = tree_data(j)
    lst = []
    for sh in shapes(range(8)):
        rows = []; rhs = []
        for i in range(8):
            row = np.zeros(NL); row[2 * i] = row[2 * i + 1] = 1; rows.append(row); rhs.append(c)
        for (L, R) in nodes_of(sh):
            U = np.mean([Xu[i] for i in L], 0) - np.mean([Xu[i] for i in R], 0)
            V = np.mean([Mv[i] for i in L], 0) - np.mean([Mv[i] for i in R], 0)
            rows.append(U[0] * V[1] - U[1] * V[0]); rhs.append(0)
        A = np.array(rows); b = np.array(rhs)
        p, _, rk, _ = la.lstsq(A, b, rcond=None)
        if la.norm(A @ p - b) > 1e-9:
            lst.append(None); continue
        N = la.svd(A)[2][rk:].T
        lst.append((sh, A, b, p, N, inc))
    B[j] = lst
    print("tree", j, "shapes", len(lst), "inconsistent alone:", sum(x is None for x in lst), flush=True)

tri_b = np.full(8, 1 / 8)
# final mixing: u-barycenters are generically nonzero; test all 3 final orders below
cnt_eq = 0; cnt_feas = 0; total = 0
L1 = [x for x in B[1] if x]; L2 = [x for x in B[2] if x]; L3 = [x for x in B[3] if x]
P3 = [x[5] @ x[3] for x in L3]; N3 = [x[5] @ x[4] for x in L3]
for ia, a in enumerate(L1):
    for b_ in L2:
        W = np.column_stack([a[5] @ a[4], b_[5] @ b_[4]])
        resid = tri_b - a[5] @ a[3] - b_[5] @ b_[3]
        for k, cd in enumerate(L3):
            M = np.column_stack([W, N3[k]]); rhs = resid - P3[k]
            sol = la.lstsq(M, rhs, rcond=None)[0]
            total += 1
            if la.norm(M @ sol - rhs) < 1e-9:
                cnt_eq += 1
                Aeq = np.zeros((0, 48)); beq = []
                for jj, d in zip((0, 1, 2), (a, b_, cd)):
                    blk = np.zeros((d[1].shape[0], 48)); blk[:, 16 * jj:16 * jj + 16] = d[1]
                    Aeq = np.vstack([Aeq, blk]); beq += list(d[2])
                tri = np.hstack([a[5], b_[5], cd[5]]); Aeq = np.vstack([Aeq, tri]); beq += list(tri_b)
                r = linprog(np.zeros(48), A_eq=Aeq, b_eq=np.array(beq), bounds=[(0, None)] * 48, method='highs')
                if r.status == 0:
                    cnt_feas += 1
    print("progress", ia + 1, "/", len(L1), "total", total, "eq-consistent", cnt_eq, "feasible", cnt_feas, flush=True)
print("DONE total", total, "eq-consistent", cnt_eq, "feasible", cnt_feas)
