import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import *
from scipy.optimize import linprog
rng = random.Random(1)
nrng = np.random.default_rng(1)
for l in (1, 2):
    n = 2**l
    stats = {'feasible': 0, 'infeasible': 0, 'eq_inconsistent': 0}
    for trial in range(40):
        mold = make_mold(n, rng); check_mold(n, mold)
        u = nrng.standard_normal((n, n)); v = nrng.standard_normal((n, n))
        Gu, Gv = gradients(n, u), gradients(n, v)
        A, b = theta_constraints(n, mold)
        tot = A.shape[1]
        # sanity: t uniform in Theta; also check T(t) contains t when v = u
        t = np.full(tot, 1.0/tot)
        assert np.allclose(A @ t, b)
        assert np.allclose(T_constraints(n, mold, Gu, Gu, t) @ t, 0)
        # random interior t in Theta: perturb along nullspace
        Ns = np.linalg.svd(A)[2][np.linalg.matrix_rank(A):]
        t = t + (Ns.T @ nrng.standard_normal(Ns.shape[0])) * 0.002
        assert (t > 0).all() and np.allclose(A @ t, b)
        C = T_constraints(n, mold, Gu, Gv, t)
        Aeq = np.vstack([A, C]); beq = np.concatenate([b, np.zeros(C.shape[0])])
        # consistency of equalities alone
        rk = np.linalg.matrix_rank(Aeq, tol=1e-9); rkb = np.linalg.matrix_rank(np.column_stack([Aeq, beq]), tol=1e-9)
        if rkb > rk: stats['eq_inconsistent'] += 1
        res = linprog(np.zeros(tot), A_eq=Aeq, b_eq=beq, bounds=[(0, None)]*tot, method='highs')
        stats['feasible' if res.status == 0 else 'infeasible'] += 1
        if trial == 0:
            print(f"l={l}: vars={tot}, rank Theta eqs={np.linalg.matrix_rank(A)}, dim Theta={tot-np.linalg.matrix_rank(A)}, parallel constraints={C.shape[0]}, rank all eqs={rk}")
    print(l, stats)
