# P_beta search at the exact rank-one convexity threshold

## Outcome

No Morrey counterexample was found. The exact algebraic result used in the search is

\[
P_\beta\begin{pmatrix}a&b\\c&d\end{pmatrix}
=(ad-2bc)^2+\beta(b^2+c^2+d^2)^2
\quad\text{is rank-one convex if and only if }\beta\ge2.
\]

The earlier sufficient value 5/2 was not sharp. This gives a stronger search target; it does not prove quasiconvexity or nonquasiconvexity.

## Global rank-one convexity certificate

Write the rank-one direction as H=(A,B;C,D), with AD=BC, and put y=(b,c,d). For D nonzero, completing a square gives

\[
\tfrac12D^2P_2(M)[H,H]
=(aD-2(cB+bC))^2+D^{-2}y^T K(B,C,D)y,
\]

where

\[
K=\begin{pmatrix}
4D^2(3B^2+C^2+D^2)&10BCD^2&-2BC^2D+8BD^3\\
10BCD^2&4D^2(B^2+3C^2+D^2)&-2B^2CD+8CD^3\\
-2BC^2D+8BD^3&-2B^2CD+8CD^3&B^2C^2+4D^2(B^2+C^2+3D^2)
\end{pmatrix}.
\]

All three leading principal minors are strictly positive for D nonzero; the exact verifier expands each as a sum of positive multiples of even monomials, including a positive D-only monomial. Sylvester's criterion gives positive definiteness. Rank-one directions with D nonzero are dense in the rank-one cone, so continuity covers D=0. Increasing beta adds a convex function.

For necessity, take

\[
M_t=\begin{pmatrix}2(t^2-1)&-1/t\\1&2/t\end{pmatrix},\qquad
H_t=\begin{pmatrix}t^3&t^2\\t&1\end{pmatrix}.
\]

Then det H_t=0, and exactly

\[
\tfrac12D^2P_\beta(M_t)[H_t,H_t]
=(2\beta-4)t^4+(12\beta+4)t^2+12\beta+26\beta/t^2.
\]

This is negative for sufficiently large t whenever beta<2. The symbolic checker verifies these identities; the global argument is ordinary real algebra, not a Lean proof.

## Search objective and base elimination

For a periodic gradient X with mean zero define

\[
g(X)=ad-2bc,\quad r(X)=b^2+c^2+d^2,\quad
v(X)=(d,-2c,-2b,a)^T,\quad y(X)=(0,b,c,d)^T.
\]

Let G be the symmetric matrix with G_ad=1/2, G_bc=-1 and their transposed entries, and E=diag(0,1,1,1). The Jensen gap at any constant base F is exactly

\[
J(F)=F^T K_0 F+2h^T F+c_0,
\]

with

\[
K_0=\langle vv^T\rangle+2\langle g\rangle G
+\beta(2\langle r\rangle E+4\langle yy^T\rangle),
\]

\[
h=\langle vg\rangle+2\beta\langle yr\rangle,
\qquad c_0=\langle g^2+\beta r^2\rangle.
\]

Thus the base is optimized analytically, F=-K_0^{-1}h in the nonsingular case, instead of fixed at zero. A pseudoinverse is used only near degeneracy. At beta>=2 the quadratic form K_0 is nonnegative for every actual gradient by the Fourier characterization of quadratic quasiconvexity.

The field is normalized by <b^2+c^2+d^2>=1. Normalizing the full gradient instead allowed trivial collapse onto the flat E11 axis, producing uninformative near-zero gaps. The new normalization prevents that particular collapse. It does not turn local optimization into a global test.

## Completed numerical searches

All use beta=2 and optimize both components and phases/nodal values.

| Test class | Starts | Lowest floating gap |
|---|---:|---:|
| Six Fourier directions | 30 | 2.0000000000000027 |
| All 24 directions with max coordinate frequency 3 | 60 | 2.000000000000127 |
| Periodic 8 by 8 nodal grid, 128 triangles | 40 | 2.0000000000000377 |
| Targeted 24-direction starts, u1(x) amplitudes amplified 3–300 times | 60 | 2.0000000000232054 |

The Fourier grids have size 4K+1 per coordinate. Every quartic trigonometric integral is therefore resolved without aliasing in exact arithmetic. The FEM gradients are constant on 128 equal-area triangles, so averaging triangle energies is exact apart from floating arithmetic.

Analytic derivative checks against directional finite differences had maximum errors below 1.3e-10. Base elimination was independently checked against direct energy subtraction. Ten cases (the lowest gap in each class and every severely ill-conditioned base system) were recomputed with 60-digit arithmetic, a newly minimized base, and direct integral evaluation. None became negative; agreement between the high-precision quadratic formula and direct integration was better than 3e-53.

No lower bound over all fields or all starts is certified. In particular, the numerical floor near 2 is not a theorem. A positive result from these local searches does not rule out this integrand or solve Morrey's problem.

## Files and reproduction

Requirements: Python, NumPy, SciPy, SymPy, mpmath. Single BLAS threads make the small linear algebra faster.

```bash
python beta2_certificate.py
OPENBLAS_NUM_THREADS=1 python pbeta_fourier_search.py --modes six --starts 30 --maxiter 1000 --normalization transverse --output six_transverse_results.json
OPENBLAS_NUM_THREADS=1 python pbeta_fourier_search.py --modes 3 --starts 60 --maxiter 1000 --normalization transverse --output k3_transverse_results.json
OPENBLAS_NUM_THREADS=1 python pbeta_fem_search.py --n 8 --starts 40 --maxiter 1000 --output fem8_results.json
OPENBLAS_NUM_THREADS=1 python pbeta_targeted_search.py
OPENBLAS_NUM_THREADS=1 python validate_results.py
```

The targeted script and validator use their containing directory for data. JSON files retain every field, optimized base, gap, condition information, and optimizer status. Failed convergence is recorded rather than silently counted as certification. The earlier `six_results.json` is a diagnostic run using full-gradient normalization and should not be presented as substantive evidence.

## Prior-work check and novelty status

Bandeira and Pedregal, *Finding new families of rank-one convex polynomials*, Ann. IHP AN 26 (2009), 1621–1634, DOI [10.1016/j.anihpc.2008.08.002](https://www.numdam.org/item/10.1016/j.anihpc.2008.08.002.pdf), was checked directly. It does not give this family or threshold. Its homogeneous 2-by-2 examples are positive on every nonzero rank-one matrix, excluding equivalence to P_beta under invertible left/right changes, transposition and positive scaling. Broader novelty remains unknown. Their Section 3 already uses the homogeneous-quartic Hessian reduction to a generalized eigenvalue problem; that methodology should not be claimed as new here.
