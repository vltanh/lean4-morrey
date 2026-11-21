"""Which step of the proof of Proposition 7.1 fails? Per sub-mold j (Step 2 summary):
exists r_j >= 0 with pair sums c, v-directions parallel to u-directions at all internal nodes
above the first level, and (a) no root condition, (b) root = U_j (eq. (7.6)), the paper's
top-to-bottom start. Then (c): all three together with the triangle masses (Step 3 target)."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import *
from scipy.optimize import linprog
rng = random.Random(3); nrng = np.random.default_rng(3)
for l in (1, 2):
    n = 2**l; NL = 4*n*n; NI = 2*n*n; c = 1/(3*NI); tot = 3*NL
    res = {'a': 0, 'b': 0, 'c': 0}; trials = 30
    for trial in range(trials):
        mold = make_mold(n, rng)
        u = nrng.standard_normal((n, n)); v = nrng.standard_normal((n, n))
        Gu, Gv = gradients(n, u), gradients(n, v)
        A, b = theta_constraints(n, mold)
        t = np.full(tot, 1/tot)
        Ns = np.linalg.svd(A)[2][np.linalg.matrix_rank(A):]
        t = t + (Ns.T @ nrng.standard_normal(Ns.shape[0])) * 0.002
        Ru = direction_rows(n, mold, Gu); Rv = direction_rows(n, mold, Gv)
        nodes_per_tree = NI - 1
        okb_all = True
        for j in (1, 2, 3):
            sl = slice((j-1)*NL, j*NL)
            rows = []; rhs = []
            for i in range(NI):
                row = np.zeros(tot); row[(j-1)*NL+2*i] = row[(j-1)*NL+2*i+1] = 1; rows.append(row); rhs.append(c)
            for q in range((j-1)*nodes_per_tree, j*nodes_per_tree):
                U = Ru[q] @ t; rows.append(U[0]*Rv[q][1] - U[1]*Rv[q][0]); rhs.append(0)
            # restrict to tree j variables
            Aj = np.array(rows)[:, sl]; bj = np.array(rhs)
            ra = linprog(np.zeros(NL), A_eq=Aj, b_eq=bj, bounds=[(0, None)]*NL, method='highs')
            res['a'] += (ra.status == 0)
            # root condition: v-root(r) = u-root(t): root map = average of interface points
            Mroot_v = np.zeros((2, tot)); Mroot_u = np.zeros((2, tot))
            for i in range(NI):
                for k in (2*i, 2*i+1):
                    g = (j-1)*NL + k
                    Mroot_v[:, g] = np.array(Gv[mold[j][k]])/c/NI; Mroot_u[:, g] = np.array(Gu[mold[j][k]])/c/NI
            Uroot = Mroot_u @ t
            Ab = np.vstack([Aj, Mroot_v[:, sl]]); bb = np.concatenate([bj, Uroot])
            rb = linprog(np.zeros(NL), A_eq=Ab, b_eq=bb, bounds=[(0, None)]*NL, method='highs')
            res['b'] += (rb.status == 0)
        C = T_constraints(n, mold, Gu, Gv, t)
        rc = linprog(np.zeros(tot), A_eq=np.vstack([A, C]), b_eq=np.concatenate([b, np.zeros(len(C))]), bounds=[(0, None)]*tot, method='highs')
        res['c'] += (rc.status == 0)
    print(f"l={l}: per sub-mold feasible (a) no root cond: {res['a']}/{3*trials}; (b) root = U_j: {res['b']}/{3*trials}; (c) T(t) nonempty: {res['c']}/{trials}")
