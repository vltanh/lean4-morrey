# Counterexample-pipeline audit: exact extensions

These files are new audit work, separate from the immutable historical search package.
They do not provide a planar Morrey counterexample or a certified lower bound on the searches.
They are standalone certificate/diagnostic infrastructure; the archived discovery optimizers have
not been patched, and a weighted-SOS candidate-generation solver is not included.

From the repository root, run all six exact checks without modifying these saved outputs:

```sh
python3 research/verify_audit.py --out /tmp/morrey-audit-check
```

This requires SymPy for the two symbolic identities; the other checks use the standard library.
Individual commands below assume the working directory is `research/audit` (or a copy).
The [pipeline audit](../../docs/research/PIPELINE_AUDIT.md) identifies the affected archived
routines; the [global certificate proof](../../docs/research/GLOBAL_CERTIFICATES.md) states the
soundness and completeness claims precisely.

## 1. Direct SOS at the sharp P₂ boundary

Run `python3 pbeta_exact_sos.py` (SymPy). The exact identity is

`D²P₂(A)[H,H] = ten positively weighted squares + 8 det(A) det(H)`.

The ten squares and coefficients are in `pbeta_exact_sos.json`. Thus the remainder vanishes
on rank-one H. This improves the earlier displayed sufficient direct-SOS range β≥5/2 to β≥2,
by adding the convex term `(β−2)(b²+c²+d²)²`. The already recorded necessity for β≥2 is separate.
No novelty claim or quasiconvexity result is made.

An exploratory floating 16×16 SDP suggested the identity. It returned `optimal_inaccurate` and
a negative Gram eigenvalue, so its output is not used as proof and is not part of this handoff.
The ten-square verifier is independent of the solver and the archived SOS coefficient assembly.

## 2. Exact quadratic-base classification

Run `python3 exact_base.py` (standard library). `minimize_psd(K,h,c)` analyzes
`J(F)=FᵀKF+2hᵀF+c` using exact principal minors and rational row reduction.

- If K is PSD and h is in Range(K), return an exact minimizer and its value.
- If K is PSD but h has a nonzero pairing with its kernel, return a rational base with a strict
  negative value and identify the direction in which the objective tends to −∞.
- Reject an indefinite K; do not silently turn it into a PSD problem.

`exact_base_controls.json` contains the singular, tiny-positive-curvature and safe-singular
regressions. These are quadratic-objective controls, not gradient counterexamples.

## 3. A richer global LH certificate

Run:

```sh
python3 sphere_control.py
python3 sphere_certificate.py sphere_control_certificate.json
python3 sphere_certificate.py norm_control_certificate.json
```

These use only the standard library. They check all polynomial coefficients over the rationals,
nonnegative square weights, a strict positive margin and optional actual periodic PL gradients.
The control `f(A)=(1+|A|²)²+5 det A` is nonconvex but rank-one convex; both certificate formats
pass, including norm-multiplier order k=1; its sample gradient gap is +80. Three kinds of
malformed certificate (altered curvature, negative square weight, zero margin) are rejected in
each format, for six rejection controls in total.

Let `x=(t,A)∈R⁵`, `u,v∈R²`, and `D=2m` be an even degree bound. The program homogenizes
`D²f(A)[u⊗v,u⊗v]` to degree `2m−2` in x, writing it as h(x,u,v).
Set `Nx=|x|²`, `Nu=|u|²`, `Nv=|v|²`.

It accepts either exact identity:

1. `h−ε = Σ λᵢsᵢ² + τx(1−Nx)+τu(1−Nu)+τv(1−Nv)`.
2. `(Nx Nu Nv)^k [h−ε Nx^(m−1) Nu Nv] = Σ λᵢsᵢ²`.

Here `ε>0`, every `λᵢ≥0`, k is a nonnegative integer, and all coefficients are rational.
On the product of the three unit spheres the left side is `h−ε`; consequently h≥ε.
Rescaling x,u,v proves, for all physical matrices/directions,

`D²f(A)[u⊗v,u⊗v] ≥ ε(1+|A|²)^(m−1)|u|²|v|²`.

The optional witness consists of a rational base and a rational periodic nodal grid with the
same two triangles per cell as the existing FE code. The evaluator constructs the gradients,
checks the mean and determinant identities, and computes the Jensen gap exactly.

The companion audit-reduction argument establishes that such certificates, with unbounded
degree and hierarchy order, can certify a counterexample if one exists after strict radial
stabilization. This file checks a supplied certificate; it does not construct all certificates,
provide a finite order bound or guarantee solver convergence.

For a weighted Gram solver, `norm_gram_basis(D,k)` supplies the full multihomogeneous monomial
basis with degrees `(m−1+k,1+k,1+k)` in `(x,u,v)`. Its size is
`binomial(m+k+3,4)(k+2)²`: quartic k=1 is 135, sextic k=1 is 315. These basis sizes describe individual SDP blocks; their practical conditioning and solve time
have not been benchmarked here. The full hierarchy is infinite.

## 4. All-field endpoint identity

`python3 pbeta_schur_reduction_check.py` verifies the exact polynomial expansion behind
`J = αM² + 2hM + C₂`. Its remainder integrates to zero by the mean-gradient and determinant
identities. The [structural audit](../../docs/research/STRUCTURAL_AUDIT.md) states the remaining
universal inequality and proves the zero-variance boundary. The checker verifies the algebra,
not that unresolved inequality.

## Dependencies and provenance

The sphere and exact-base checkers use only Python's standard library. The P₂ identity verifier
uses SymPy. Temporary solver dependencies, discovery-probe output and caches are excluded from
this handoff. None of the regression controls is claimed to occur in a saved search run.
The research notes cite rational Putinar representations as the completeness input, e.g.
V. Powers, [Rational certificates of positivity on compact semialgebraic sets](https://www.math.emory.edu/~vicki/pub/rationalreps.pdf).
