# Counterexample pipeline audit

## Outcome

The current negative-search evidence is correctly described as inconclusive. The AI-assisted source audit found a real
algorithmic blind spot in analytic base minimization, a concrete restriction imposed by the
fixed Gram margin, and a practical certificate extension that closes the direct-SOS completeness
gap in principle when combined with the [global-certificate argument](GLOBAL_CERTIFICATES.md). No planar counterexample
was found, and no new random optimization campaign was run.

New code and exact outputs are in [research/audit](../../research/audit/README.md). The principal useful outputs are the
ten-square P₂ identity, exact base-minimization diagnostic, and the product-sphere / norm-multiplier
certificate verifier with exact periodic-gradient evaluation. The untrusted threshold-probe
output is explicitly not a certificate.

## 1. Sound components of the existing pipeline

- The SOS coefficient assembly uses physical `H=u⊗v`, and it matches all monomial coefficients,
  rather than merely sampling curvature. Its mathematical implication is valid **if** the identity
  and Gram PSD condition are exact. The saved floating results do not meet that standard by default.
- The FE map constructs actual periodic continuous piecewise affine maps, with both triangles in
  each cell. This is stronger than imposing just mean and determinant moments on an arbitrary law.
- Fourier fields are gradients of periodic maps. The Pβ quadrature grid exceeds four times the
  maximum coordinate frequency, which resolves quartic Fourier moments in exact arithmetic.
- Omitting an explicit base in the general nonhomogeneous polynomial search causes no loss at
  the level of the unrestricted same-degree polynomial class: replace f(A) by f(F+A) modulo
  affine terms. The **normalized positive-Gram-margin slice**, however, is not invariant under
  that translation without rechecking its margin.
- Unit full-gradient variance is also harmless at the level of all coefficients and all
  nonzero fields, by scaling the integrand's argument. It is not harmless if coefficients or
  relative Gram conditioning are held fixed.
- For Pβ, transverse normalization omits only fields whose gradient is on the flat E11 line.
  Those fields obey one-dimensional rank-one Jensen. Nearly flat fields remain noncompact after
  normalization and can require extremely large bases; the finite starts do not cover that limit.

## 2. Real blind spot: cutoff pseudoinverses are not complete base minimizers

For a fixed mean-zero gradient field and a quartic integrand, the base-dependent Jensen gap is

`J(F)=c+2hᵀF+FᵀKF`.

The quadratic dependence follows because the F⁴ term cancels and the F³ term is proportional to
the mean gradient. If the integrand is globally RC, its homogeneous quartic part f₄ is RC.
Symmetry of its fourth derivative gives `FᵀKF = (1/2) mean D²f₄(F)[G,G]`. For each fixed F,
this is the integral of a rank-one nonnegative quadratic form of a genuine gradient, hence is
nonnegative by quadratic quasiconvexity. Thus K is PSD. This does not, by itself, prove h
belongs to Range(K).

The affected archived functions, under `research/experiments/2026-11-21/`, are:

| Source and function | Cutoff / behavior |
| --- | --- |
| `work_pb/pbeta_fourier_search.py`, `base_min`, line 29 | Absolute cutoff `1e−13`; discarded linear components are ignored. |
| `work_cassese/search.py`, `Search.value`, lines 69–76 | Relative cutoff `1e−11*max(1,λmax)`; reports a kernel residual without acting on it. |
| `work_cassese/penalty_sos.py`, `Penalty.base`, line 72 | Relative cutoff `1e−10*max(1,λmax)`; discarded linear components are ignored. |

The correct dichotomy for PSD K is:

- If h is orthogonal to ker K, the minimum is `c−hᵀK†h`.
- Otherwise the infimum is −∞. A rational null vector with nonzero pairing provides an explicit
  finite base at which the gap is strictly negative.

Even a *positive* eigenvalue below the cutoff is important: dropping it removes the decrease
`(uᵀh)²/λ`. In the exact control `K=diag(1,10⁻¹⁴)`, `h=(0,10⁻⁶)`, `c=1`, the true minimum is
**−99 at F=(0,−10⁸)**; the cutoff routine returns 1. For `K=diag(1,0)`, `h=(0,1)`, `c=1`, it also
returns 1 although the infimum is −∞ and F=(0,−1) gives −1.

These are diagnostic quadratic controls, not evidence that either case occurs for the saved
planar energies. The selected high-precision saved-field checks remain valid; they do not certify
every field visited or every direction discarded during optimization.

**Action:** use the exact rational diagnostic at promotion time; during exploration, monitor the
discarded h components and the omitted correction, increase precision near small eigenvalues,
and refuse to describe a thresholded value as the global base minimum. Probe the corresponding
large-base ray explicitly rather than silently dropping it. Original archived scripts remain unchanged.

## 3. Fixed Gram margins exclude a concrete interesting face

`research/experiments/2026-11-21/work_sos/sos_search.py`, `SOS.__init__`, line 69,
enforces `Q≽εI` together with `trace Q=1`, which is stronger than SOS rank-one convexity. It forces a positive
curvature lower bound proportional to the squared monomial-feature norm. The fixed ε=10⁻⁷ is
therefore not a neutral scale normalization; it excludes forms whose normalized Gram margin is
smaller, and every integrand with the relevant exact flat directions.

A new exact identity shows the sharp P₂ family is in the **direct SOS class** already:

`D²P₂(A)[H,H] = Σᵢ λᵢSᵢ(A,H)² + 8 det(A)det(H)`, all λᵢ>0.

The ten squares are in [pbeta_exact_sos.json](../../research/audit/pbeta_exact_sos.json), independently checked by SymPy.
This improves the earlier displayed sufficient direct-SOS parameter β≥5/2 to β≥2; the positive
convex term for β>2 preserves SOS. It does not prove quasiconvexity or novelty.

At A=E11 and H=E11 the P₂ curvature is zero while the Gram feature vector is nonzero. Thus no
strictly positive Gram matrix can represent it. This directly demonstrates the margin restriction.
The separate Pβ analytic-family search did include β=2, so this observation does not retroactively
exclude those runs. It matters for interpreting the *general* polynomial-SOS search.

**Action:** allow singular exact certificates, or use an explicit margin schedule ε↓0. If adding
a strictifying radial polynomial, account for its actual Jensen cost and retain the negative margin.
Do not infer that P₂ is outside the direct SOS cone from failure under a fixed Gram lower bound.

## 4. Remaining search restrictions

The feature-covariance penalty in
`research/experiments/2026-11-21/work_sos/feature_search.py`, lines 36–41, fixes
`ε=10⁻⁷` and `μ=0.0005`. A fixed penalty can move the optimizer away from a negative
unregularized objective. There is no implication from a barrier
local minimum to a minimum of J. Anneal the penalty and reoptimize J alone before stopping a run.
The exact null-Lagrangian constraints do not prevent all algebraic wells; current exclusions of
the zero integrand and determinant-square wells are appropriate but not an exhaustive taxonomy.

The DH conditioned routine
`research/experiments/2026-11-21/work_lit/dh_conditioned_search.py`, line 42, restricts
base norm to `[0.2,6]` and its eccentricity parameter to `[0,0.85]`, hence the singular-value
ratio to at least `(1−0.85)/(1+0.85)=3/37≈0.08108`. Its attained positive values have no
implication outside those ranges. The Cassese searches retain low-dimensional penalty
families and finite Fourier directions; no certificate-completeness statement follows from them.
Alternating convex SDP / nonconvex field optimization is local in the joint problem even when the
SDP subproblem is solved accurately. None of these are errors if the output is described as attained
values, as the ledger presently does.

## 5. Global improvement: a complete negative-certificate hierarchy

The new verifier supports strict rational LH positivity after compactification on `S⁴×S¹×S¹`,
either via SOS plus the sphere ideal, or via a product-of-norms multiplier. The companion [global-certificate audit](GLOBAL_CERTIFICATES.md) explains why any strict planar counterexample can be approximated/strictified to admit a
certificate at some finite polynomial degree and hierarchy order. This replaces the unsupported
hope that one unweighted SOS class is complete.

For D=2m, the weighted certificate is

`(Nx Nu Nv)^k [h−δ Nx^(m−1)NuNv] = Σ λᵢsᵢ²`,

with x=(t,A), `Nx=|x|²`, `Nu=|u|²`, `Nv=|v|²`. The precise verifier, rational controls and Gram
basis generator are in `sphere_certificate.py` / `sphere_control.py`. Its k=1 Gram dimensions are
135 for quartics and 315 for sextics. On the unit product spheres, the multiplier is one; homogeneous
rescaling then proves the global physical LH inequality. Exact periodic PL evaluation is included.

The nonconvex RC control `f=(1+|A|²)²+5det A` passes both formats, including the norm
multiplier at k=1, with actual PL gap +80. Changed-curvature, negative-square-weight and
zero-margin controls are rejected separately in both formats (six rejection cases). These are
proof format checks, not new counterexamples, saved-run failures or tests of search efficiency.
The reduction agent independently checked the verifier and mixed-degree homogenization.

**What is still missing:** a solver/discovery stage producing a strict negative actual-gradient
gap. Increasing degree/order or mesh in this hierarchy has no known uniform bound, so it is a
complete *semidecision route for a negative answer*, not a finite positive classification. A useful
next implementation is one weighted-Gram block and exact extraction using the existing gradient
parameterization; a useful next mathematical target is the all-gradient moment inequality from
the reduction audit. Neither should be confused with merely running more random starts.


## 6. Executable handoff and unfinished implementation

This audit adds standalone exact diagnostics and certificate validation, not a production search
fix. No archived optimizer was changed. The norm-basis builder supplies a search interface, but
there is no weighted-Gram SDP assembly, solver, automatic rational extraction or global field
optimizer in the new package. A supplied strict negative rational witness could be verified; no
such witness is supplied. The ten-square identity and quadratic regression controls are exact,
but no part of this new Python infrastructure is Lean-formalized.

The executable interface, controls and reproduction commands are in
[research/audit/README.md](../../research/audit/README.md). The exploratory numerical probe was
used only to guess an identity that the independent exact script verifies. Its untrusted output,
temporary solver dependencies and caches are excluded. The polynomial expansion for the
all-field endpoint reduction is also replayable there.
