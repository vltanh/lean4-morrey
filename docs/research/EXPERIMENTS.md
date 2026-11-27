# Counterexample searches: experiments and verdicts

**Completion-audit update:** the archived runs remain unchanged. The
[pipeline audit](PIPELINE_AUDIT.md) identifies cutoff-based base minimization and fixed Gram
margins as search restrictions; it does not establish a missed saved counterexample.
New exact checks and a complete certificate hierarchy are indexed in
[COMPLETION_AUDIT.md](COMPLETION_AUDIT.md).


Snapshot: 21 November 2026. **No validated counterexample in `2 × 2` was found.**
This page consolidates the latest search round; the [research ledger](README.md#result-ledger)
records the earlier routes and their corrections. All scripts, fields, solver
diagnostics and logs are retained in
[`research/experiments/2026-11-21/`](../../research/experiments/2026-11-21/).
The [reproduction guide](REPRODUCING.md) distinguishes checking saved evidence
from launching new optimization.

Throughout this page the Jensen gap is

\[
J_f(F,\varphi)=\fint_Q f(F+D\varphi)\,dx-f(F).
\]

A counterexample requires **strictly negative** `J`, a genuine admissible
gradient, and global rank-one convexity of the same integrand. An attained
positive value is not a lower bound. Normalizations differ between families,
so their gap magnitudes should not be ranked against one another. Counts of
alternating SDP/field steps are not counts of independent restarts.

## 1. Exact algebra that supports the search

These checks were rerun in exact Python/SymPy arithmetic for this consolidation.
They are not Lean proofs. The interpretation of a symbolic identity still uses
the mathematical arguments recorded in the linked notes.

| Result | Exact evidence | Scope and limitation |
| --- | --- | --- |
| `Pβ(A) = (ad − 2bc)² + β(b²+c²+d²)²` is globally rank-one convex exactly when `β ≥ 2` | [Certificate](../../research/experiments/2026-11-21/work_pb/beta2_certificate.py), [argument](../../research/experiments/2026-11-21/work_pb/README.md) | Sharpens the earlier sufficient bound `5/2`; gives neither quasiconvexity nor its failure. Broader novelty is unestablished. |
| `Pβ` has an SOS Legendre–Hadamard identity for `β ≥ 5/2` | [SOS and parameter checker](../../research/experiments/2026-11-21/work_lit/verify_sos_and_dh_parameters.py) | Shows the SOS search class need not be confined to polyconvex energies. Does not show that this class contains a Morrey counterexample. |
| A Cassese planar penalty family contains the zero integrand and a determinant square | [Exact identities](../../research/experiments/2026-11-21/work_cassese/exact_degeneracy.py) | Explains spurious small search objectives; does not refute the source's higher-dimensional construction. |
| A rational `3 × 2` polynomial with an exact positive-definite Gram certificate has a negative periodic gap | [Certificate JSON](../../research/experiments/2026-11-21/work_sos/control_run/exact_control_certificate.json), [independent verifier](../../research/experiments/2026-11-21/work_sos/certify_control.py) | A control for the known Šverák mechanism, **not a `2 × 2` result**. |

For the last row the test map is `(sin x, sin y, sin(x+y))`, and the exact gap is

\[
-\frac{103817049981}{8000000000000}<0.
\]

The verifier checks every coefficient of the Hessian/Gram identity and positive
definiteness of its `42 × 42` Gram matrix by rational LDL decomposition. Its
integral calculation is exact. It requires only Python's standard library.

## 2. The sharp `Pβ` family: 190 starts

All runs use `β = 2`. For a fixed mean-zero gradient field the quartic gap is quadratic in
all four entries of the base matrix `F`. The implementation eliminates them with a cutoff
pseudoinverse; [A01](README.md#completion-audit) explains why discarded directions can matter.
The selected high-precision checks below validate those saved fields, not every discarded direction. The field normalization
is `mean(b²+c²+d²) = 1`, which prevents collapse onto the flat `E11` direction.

| Search | Starts | Lowest recorded gap |
| --- | ---: | ---: |
| Six Fourier directions, both phases | 30 | `2.0000000000000027` |
| 24 Fourier directions, maximum coordinate frequency 3 | 60 | `2.000000000000127` |
| Periodic `8 × 8` nodal grid, 128 triangles | 40 | `2.0000000000000377` |
| Targeted Fourier starts with flat-direction amplitudes amplified by factors 3–300 | 60 | `2.0000000000232054` |

The Fourier quadrature resolves the quartic trigonometric polynomial without
aliasing in exact arithmetic. For the finite-element fields, integration is a
finite average over constant triangle gradients. Floating arithmetic remains.
Ten selected cases, including severely ill-conditioned base systems, were
recomputed at 60 digits with newly minimized bases and direct energy
evaluation. Formula and direct integral agreed within `3 × 10⁻⁵³`.

**Verdict:** no negative gap, and no theorem asserting the observed floor near
2. The family remains a possible research target. Raw data and prior-work
qualifications: [branch report](../../research/experiments/2026-11-21/work_pb/README.md),
[high-precision audit](../../research/experiments/2026-11-21/work_pb/high_precision_audit.json).

## 3. Dacorogna–Haeberly anisotropic degree-one energies: 472 runs

These are the continuous finite-valued energies
`f(A) = vec(A)ᵀ N vec(A) / |A|`, with `f(0) = 0`. Rank-one convexity follows from
the published eigenvalue criterion, with parameters checked exactly. The
original scaled matrix has eigenvalues `(0.5, 0.9, 0.9, 1.1)`; the stronger
boundary matrix has `(0.4, 0.6, 0.6, 1)`.

| Search | Runs | Strong candidate: lowest attained `J` | Original candidate: lowest attained `J` |
| --- | ---: | ---: | ---: |
| Joint field/base search, grids 4, 8, 16 | 48 | `7.11 × 10⁻¹⁵` | `1.24 × 10⁻¹⁴` |
| Fixed full-rank bases, five scales, three shapes, grids 4, 8, 16 | 360 | `5.37377 × 10⁻⁴` | `4.65070 × 10⁻³` |
| Optimized conditioned bases, both determinant signs, grids 8, 16 | 64 | `9.78985 × 10⁻⁵` | `1.25110 × 10⁻⁴` |

The first row converges toward rank-one-base affine degeneracies and is not a
useful near-counterexample. The last row restricts `|F| ≤ 6` and the singular
value ratio to at least `(1−0.85)/(1+0.85)`. Many runs reach their iteration
limits. None of these values is a certified local or global minimum.

A deliberately non-rank-one-convex perturbation gives the expected negative
one-wave control gap, about `−0.00410748`. It validates detection of energy
decrease but is not admissible for Morrey's question.

**Verdict:** no negative admissible gap. This is an established candidate
family, not a novelty claim. Primary references, exact matrices and parameters:
[branch report](../../research/experiments/2026-11-21/work_lit/README.md).
Counts and convergence status:
[search summary](../../research/experiments/2026-11-21/work_lit/search_summary.json).

## 4. Cassese pullbacks and revised planar penalties

### 4.1 Inherited rank-one-convex family: 84 runs

For the quartic `h` of Cassese's `2 × 3` construction, the planar family is
`f(A) = h(M+AB)` with `B ∈ ℝ^{2×3}`. Rank-one convexity is inherited from `h`.
The preprint and its public Lean definitions were inspected; the external Lean
project was not rebuilt for these experiments.

The search uses eight Fourier directions and optimizes all six entries of the
ambient base `M` analytically. It tested `δ = 1, .1, .01, .001`, variable and
fixed planes, and nearly tangent planes with angles down to `.001`. There were
12 variable-plane, 36 fixed-plane and 36 tangent-plane runs. All gaps were
positive, with the smallest normalized `J/δ` approximately `0.999999996`.
Seventy-five of 84 optimizations reported success. Independent evaluation in
the original coordinates on a finer grid agreed within `1.3 × 10⁻¹¹`.

**Verdict:** no candidate in the recorded runs. Positive values do not prove
quasiconvexity of arbitrary pullbacks.

### 4.2 Replacing the inherited penalty: 176 alternating steps

The planar candidate is

\[
f(A)=\pm q(AB)+\alpha L(AB)^2+\beta L(AB)P(AB)+\gamma P(AB)^2.
\]

Once these coefficients change, rank-one convexity must be established anew.
The search uses a complete floating SOS coefficient identity for the
Legendre–Hadamard form, alternating with periodic finite-element optimization.

| Variant | Recorded steps | Numerical screening and outcome |
| --- | ---: | --- |
| Nonnegative penalty coefficients | 80 | 60 pass residual/eigenvalue screening; lowest screened `J = 1.0475752 × 10⁻⁵`. The raw smallest gap has Gram eigenvalue `−8.34 × 10⁻⁵` and is invalid as a PSD certificate. |
| Free mixed coefficient, both signs of `q`, entry-covariance barrier | 96 | 24 steps excluded as zero-integrand degeneracies. Remaining 72 have smallest `J = 0.002893133`; 55 pass numerical screening. |

Screening means coefficient residual at most `10⁻⁸` and minimum Gram eigenvalue
at least `−10⁻⁸`; this is **not exact feasibility**. A proposed fifth nearly
singular plane failed in Clarabel and is excluded.

For `B = [[1,0,0],[0,1,0]]`, exact identities explain the degeneracies:

\[
q+\tfrac14L^2-LP+\tfrac34P^2\equiv0,
\qquad -q-\tfrac12LP+\tfrac32P^2=4(\det A)^2.
\]

Thus fixing the `q` coefficient does not normalize the integrand, and entry
covariance alone does not rule out determinant-square wells.

**Quarantined records:** `penalty_sos_best.npz` has an unacceptable Gram matrix;
`penalty_barrier_best.npz` represents a zero-integrand degeneration. They are
retained for audit and must not be treated as candidates. See the
[branch report](../../research/experiments/2026-11-21/work_cassese/README.md) and
[screening summary](../../research/experiments/2026-11-21/work_cassese/penalty_summary.json).

## 5. General polynomial SOS search: 42 restarts, 222 alternating steps

For degree at most `2k`, impose

\[
D^2f(A)[u\otimes v,u\otimes v]=z(A,u,v)^TQz(A,u,v),\qquad Q\succeq0,
\]

where `z` contains the monomials in `A` of degree at most `k−1`, multiplied by
`u_i v_j`. An **exact** identity and PSD certificate imply global rank-one
convexity. The floating search uses `trace(Q)=1` and `Q ⪰ 10⁻⁷I`, which restrict
the search further. Degree four uses 65 nonaffine coefficients and a `20 × 20`
Gram matrix; degree six uses 205 and `60 × 60`. The determinant ambiguity is
fixed. Translation of the integrand accommodates nonzero bases in this
nonhomogeneous polynomial class, modulo affine terms.

| Record directory | Degree / grid | Restarts × steps | Field penalty | Lowest attained `J` |
| --- | --- | ---: | --- | ---: |
| `search4` | 4 / `4 × 4` | `12 × 6` | None | `5.83670 × 10⁻⁸` |
| `search8_diverse` | 4 / `8 × 8` | `12 × 6` | Entry covariance | `4.58500 × 10⁻⁵` |
| `search6` | 6 / `4 × 4` | `6 × 5` | Entry covariance | `1.86010 × 10⁻⁵` |
| `features4` | 4 / `8 × 8` | `6 × 4` | Covariance of degree 1–2 monomials | `1.07907 × 10⁻⁴` |
| `features6` | 6 / `8 × 8` | `6 × 4` | Covariance of degree 1–3 monomials | `7.47634 × 10⁻⁵` |

The initial very small gaps come with field degeneracy. The feature penalties
discourage concentration on algebraic zero sets that entry covariance misses.
Reported gaps exclude the penalties; nevertheless the penalties change the
optimization landscape and cannot support an exhaustive conclusion.

Many SDPs return `optimal_inaccurate`. The best quartic feature record has
coefficient residual approximately `3.8 × 10⁻⁸`. None of the `2 × 2` floating
Gram outputs has been promoted here to an exact rank-one-convex certificate.
The saved NPZ files retain their own monomial ordering; the first quartic run
used a different ordering. Do not infer this ordering from a later script.

**Verdict:** no negative recorded gap and no certified lower bound. Supporting
data: [summary](../../research/experiments/2026-11-21/work_sos/search_summary.json),
[best-output audit](../../research/experiments/2026-11-21/work_sos/floating_output_audit.json),
[independent review](../../research/experiments/2026-11-21/work_lit/SOS_AUDIT.md).

## 6. What the checks establish

The consolidation reran eight saved-artifact verifiers successfully; see
[`research/verification/2026-11-21/results.json`](../../research/verification/2026-11-21/results.json).
They cover exact symbolic identities and the higher-dimensional control,
floating Gram reconstruction and gradient constraints, finer-grid evaluation,
60-digit base minimization, and independent derivative checks. They do not
repeat the optimization campaigns, certify positive lower bounds, compile
Lean, establish novelty, or settle the `2 × 2` question.
