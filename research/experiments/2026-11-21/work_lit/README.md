# Anisotropic degree-one counterexample search

## Outcome

No negative Jensen gap was found in 472 local optimization runs for two globally
rank-one-convex Dacorogna--Haeberly energies. This is a numerical search result,
not a proof of quasiconvexity or a global lower bound.

## Literature and parameter verification

Primary reference: B. Dacorogna and J.-P. Haeberly, *On convexity properties of
homogeneous functions of degree one*, Proc. Royal Soc. Edinburgh 126A (1996),
947--956, DOI 10.1017/S0308210500023180.

Accessible primary PDF:
https://doc.rero.ch/record/290415/files/S0308210500023180.pdf

Their Theorem 1.4 and Corollary 1.5 supply rank-one convexity criteria for
f(A)=vec(A)^T N vec(A)/|A|, with f(0)=0. The paper's Remark 1.11 leaves
quasiconvexity open; its 1998 numerical sequel already studies this family.
Searches here therefore do not establish priority for the method or candidate.
The bibliographic search did not locate a later theorem resolving this exact
anisotropic family, but it was not an exhaustive citation database search.

Both matrices below commute with the determinant involution E. Their smallest
and largest eigenspaces have positive determinant. For ordered eigenvalues
lambda1<=lambda2<=lambda3<=lambda4, the relevant RC inequalities are
4 lambda1 >= lambda3+lambda4 and lambda1+lambda2 >= lambda4.

The stronger boundary candidate uses

N = (1/10) [[8,0,0,2],[0,5,1,0],[0,1,5,0],[2,0,0,8]],

with eigenvalues (0.4,0.6,0.6,1). Both RC inequalities are equalities.
The original published example at gamma=1, scaled by 1/10, uses

N = (1/10) [[10,0,0,1],[0,7,2,0],[0,2,7,0],[1,0,0,10]],

with eigenvalues (0.5,0.9,0.9,1.1). Nonconvexity of each follows from
2 lambda1-lambda4<0. These are continuous, finite-valued, anisotropic integrands;
the 2026 isotropic quartic theorem does not apply to them.

## Computation

Maps are continuous piecewise affine periodic maps on an n by n square grid,
each square split along its descending diagonal. Their gradients are constant
on 2n^2 equal-area triangles. Thus the integral is a finite average of energy
values, with no spatial quadrature approximation. Energy evaluation and
optimization use floating point.

Every search enforces mean |Du|^2=1 by normalizing the actual gradient, not just
the coefficient vector. The mean gradient and determinant identity are checked.
Analytic derivatives of the normalized objective agree with centered finite
differences to 6.96e-12 in the initial check.

1. `dh_fem_search.py`: 48 runs; grids 4,8,16, 8 starts, two energies, base entries
   optimized within [-4,4]. Near-zero minima collapse to rank-one-base affine
   configurations. They are not evidence of a useful near-counterexample.
2. `dh_fixedbase_search.py`: 360 runs; grids 4,8,16, five base scales
   (0.25,0.5,1,2,4), three full-rank base shapes, four starts, two energies.
   Minimum gaps: 0.0005373773418817507 (strong) and 0.004650699647464229 (original).
3. `dh_conditioned_search.py`: 64 runs; grids 8,16, both determinant signs,
   eight starts, two energies. Base norm is bounded by 6 and its singular value
   ratio is at least (1-0.85)/(1+0.85). Minimum gaps:
   0.00009789845752639081 (strong), 0.0001251099920747123 (original).
   Many runs reach the iteration limit; these are attained values, not minima
   proven globally or even certified local minima.

## Negative control

At base F=3I and the piecewise-affine one-wave gradient taking +/-E12, the strong
admissible energy has exact gap (37/2)/sqrt(19)-sqrt(18)>0 (approximately
0.0015503894861064). Increasing its largest eigenvalue outside the RC range
produces exact gap (97/5)/sqrt(19)-(189/10)/sqrt(18)<0 (approximately
-0.0041074843863518). The code detects the latter. This control demonstrates
the pipeline can detect a genuine nonquasiconvexity witness, but the modified
control energy is not rank-one convex and is not a Morrey counterexample.

## Sum-of-squares clarification

`verify_sos_and_dh_parameters.py` verifies an exact SOS identity for the Hessian
of P_beta(A)=(ad-2bc)^2+beta(b^2+c^2+d^2)^2 modulo det(H), beta>=5/2.
Consequently its LH polynomial after H=u tensor v is a sum of squares, despite
this family being nonpolyconvex. A search imposing SOS-LH is therefore not
automatically restricted to polyconvex integrands. This does not imply that it
will contain a counterexample to quasiconvexity.

## Reproduce

Python 3 with NumPy, SciPy, SymPy is sufficient. From this folder, run:

```
OPENBLAS_NUM_THREADS=1 python dh_fem_search.py
OPENBLAS_NUM_THREADS=1 python dh_fixedbase_search.py
OPENBLAS_NUM_THREADS=1 python dh_conditioned_search.py
python verify_sos_and_dh_parameters.py
```

Full parameters, convergence status, logs and best fields are retained beside
these scripts. `search_summary.json` aggregates the runs.
