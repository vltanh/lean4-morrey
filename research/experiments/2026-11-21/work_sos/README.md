# Global polynomial search

No 2-by-2 counterexample was found. These are numerical searches over a
sufficient algebraic class of globally rank-one-convex polynomials, not an
exhaustive search over rank-one-convex functions and not a proof of quasiconvexity.

## Certificate formulation

For a polynomial f of degree at most 2k, impose the coefficient identity

    D²f(A)[u tensor v, u tensor v] = z(A,u,v)^T Q z(A,u,v),
    z = (all monomials in A of degree <= k-1) tensor u tensor v.

Q positive semidefinite and an exact identity imply global rank-one convexity.
The numerical SDP uses trace(Q)=1, Q >= 1e-7 I. Affine coefficients are omitted;
the determinant coefficient ambiguity is fixed by an orthogonality condition.
Degree4 uses 65 polynomial coefficients and a 20-by-20 Gram matrix. Degree6
uses 205 coefficients and a 60-by-60 Gram matrix. One coefficient direction is
removed in each case by the determinant normalization.

Nonhomogeneous polynomials are allowed. Thus translating a homogeneous
integrand to a nonzero base is represented by the cubic/quadratic (and, in
degree 6, quintic etc.) coefficients, modulo affine terms. The fixed normalized
Gram margin is an additional search restriction; completeness is not claimed.

For a fixed periodic gradient field, optimize f by SDP; for fixed f, optimize
the nodal field by L-BFGS. The field is a genuine continuous periodic piecewise
affine map on a descending-diagonal square triangulation. Integration is the
finite average over equal-area triangles. Mean gradient, mean determinant,
gradient variance and analytic derivatives are checked.

## Preventing uninformative collapse

The initial quartic run converged near zero gaps through degenerate fields.
A barrier on the covariance of the four matrix entries prevents collapse
into a proper linear subspace but still allows det(Du)=0 pointwise. The later
`feature_search.py` uses centered covariance of every monomial of degree 1–2
(quartic case) or1–3 (degree 6 case). This discourages concentration in low-degree
algebraic zero sets. The actual reported gap excludes the barrier.

Neither barrier turns local optimization into a global lower bound. No claims
about fields excluded or discouraged by the barrier follow from a run.

## Runs

The retained result directories contain all alternating steps and optimizer
diagnostics, plus the best stored polynomial, Gram matrix and field.

| Directory | Degree | Grid | Restarts × alternating steps | Field regularizer |
|---|---:|---:|---:|---|
| search4 |4|4×4|12×6|None|
| search8_diverse |4|8×8|12×6|Entry covariance|
| search6 |6|4×4|6×5|Entry covariance|
| features4 |4|8×8|6×4|Degree1–2 feature covariance|
| features6 |6|8×8|6×4|Degree1–3 feature covariance|

These are 42 restarts and 222 alternating steps, not 222 independent searches.
No recorded gap was negative. `search_summary.json` contains the exact attained
values and residual ranges. Many solver returns are `optimal_inaccurate`;
their numerical Gram matrices are not exact certificates. The best quartic
feature run has coefficient residual about3.8e-8, which must be corrected before
claiming exact feasibility. No positive gap is a certified lower bound.

## Exact known higher-dimensional control

The same algorithm on 3-by-2 matrices, with

    w(x,y)=(sin x, sin y, sin(x+y)),

finds the established Šverák type failure mechanism. Its numerical polynomial
and Gram matrix were rounded to rational numbers and the coefficient identity
repaired exactly. `certify_control.py` verifies with integer/Fraction arithmetic:

- the complete polynomial identity;
- positive definiteness of a 42-by-42 Gram matrix via exact LDL decomposition;
- the exact periodic integral gap

    -103817049981 / 8000000000000 < 0.

The verifier requires only the Python standard library; rebuilding the
certificate additionally requires NumPy. This control validates the pipeline
on a known 3-by-2 mechanism. It is NOT a 2-by-2 counterexample or a new resolution
of a higher-dimensional problem. The companion independent audit in `work_lit`
checks exact Hessian values by a different finite-difference identity.

## Reproduce from the archive root

```
python work_sos/certify_control.py
OPENBLAS_NUM_THREADS=1 python work_sos/sos_search.py --control --out work_sos/control_rebuilt
OPENBLAS_NUM_THREADS=1 python work_sos/sos_search.py --degree 4 --k 4 --starts 12 --rounds 6 --out work_sos/search4_rebuilt
OPENBLAS_NUM_THREADS=1 python work_sos/sos_search.py --degree 4 --k 8 --starts 12 --rounds 6 --barrier .0001 --out work_sos/search8_rebuilt
OPENBLAS_NUM_THREADS=1 python work_sos/sos_search.py --degree 6 --k 4 --starts 6 --rounds 5 --barrier .0001 --out work_sos/search6_rebuilt
OPENBLAS_NUM_THREADS=1 python work_sos/feature_search.py --degree 4 --out work_sos/features4_rebuilt
OPENBLAS_NUM_THREADS=1 python work_sos/feature_search.py --degree 6 --out work_sos/features6_rebuilt
python work_sos/validate_outputs.py
```

NumPy, SciPy, SymPy, CVXPY and Clarabel are required for the searches. Solvers
and local optimization can produce different floating results on another
version. Stored NPZ files include the monomial ordering needed to interpret Q;
the first quartic run used a different ordering, which is explicitly retained.
