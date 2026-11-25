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

## 5. All-exponent rational homogeneous certificate interface (23 Nov 2026)

The [global p≥4 smooth-class negative semidecision](../../docs/research/IWANIEC_MORREY_PGE4_EXACT_HIERARCHY.md)
uses the standalone standard-library verifier:

~~~sh
python3 research/audit/iwaniec_all_p_rational_cert.py
python3 research/audit/iwaniec_all_p_rational_cert.py research/audit/iwaniec_pge4_positive_control.json
~~~

Both commands certify global nonnegativity and strict rank-one convexity,
not just curvature samples. The control p=9/2 with h(r)=2+2r²+r⁴
has two Bernstein leaves of depth 1. Both can be run without SymPy,
an SDP solver, or any access to the network.

A JSON input contains rational p≥4, a list of rational monomial
coefficients h in increasing degree, and optionally up to four
diagonal triples (weight,x,y). If atoms are included the verifier:
(1) checks the **exact** matrix and determinant moments for a
base diag(1,t), |t|<1; (2) encloses rational powers by exact dyadic
root isolation; (3) accepts a strict negative Jensen gap only when
the certified rational **upper** bound is below zero. A nonnegative
or inconclusive gap is **not** accepted as a counterexample.

The acoustic Bernstein test is **sufficient** rather than
a complete rank-one-convexity decision procedure. The
separate mathematical completeness statement is conditional on
existence of a counterexample with **C² signed-singular profile**,
and allows unbounded degree/subdivision depth and rational
denominators. A failure to find such a certificate cannot prove
the positive p≥4 polyconvexity conjecture. A certificate of
nonpolyconvexity is **not** a planar gradient witness to non-QC.


## 6. Unrestricted four-wave parity and odd-resonance controls

The [all-N parity and correlated four-wave hand theorem](../../docs/research/IWANIEC_MORREY_FOUR_WAVE_PARITY_THEOREM.md)
covers arbitrary **finite rank-one-convex**
integrands without symmetry, homogeneity
or sign assumptions, but only one
genuinely resonant four-wave family
(and wider structural no-resonance
and pure-parity classes).
It relies on the **published
Sebestyén–Székelyhidi 2017**
three-wave laminate theorem.

Run from repository root:

~~~sh
python3 research/audit/iwaniec_four_wave_parity_exact.py
~~~

Standard library only; checks integer
odd-resonance classification for
specified tuples, 10 nonparallel
lacunary waves, the exact rho=1/3
four-wave correlation via **nine
rational polygons**, all 16 rational
parity weights and a sample
matrix/determinant moment control.
The global all-phase Fourier bound
and universal laminate induction
are hand arguments, **not**
established by the finite checker.
No negative gradient Jensen
witness or full Morrey proof is claimed.

## Post-reset compactification and flat-region controls

Run `python3 research/audit/parametric_compactification_exact.py` (SymPy). The executed checks cover graph-bivector and Hodge-coordinate identities, six polynomial angular curvature Taylor identities, the spherical kernel normalization and second-moment calculation, and the shifted-kernel and flat-region algebra. See [unrestricted parametric reduction](../../docs/research/IWANIEC_MORREY_PARAMETRIC_COMPACTIFICATION.md) and [flat contact resolution](../../docs/research/IWANIEC_MORREY_FLAT_CONTACT_RESOLUTION.md). These are exact algebra controls, not an enumeration of the finite-accuracy families or a proof of the unresolved spatial stress condition.

## Folded graph and signed trace controls

Run `python3 research/audit/signed_trace_exact.py` (SymPy). Executed controls verify the mixed-minor relation, Piola cancellation, a rational degree-one three-sheet folded map with exact signed trace gradient and energy lower bound, and flat-sector identities. See [signed trace and folding theorem](../../docs/research/IWANIEC_MORREY_SIGNED_TRACE_FOLD_TRANSFER.md). The analytic theorem also uses Sard, the area formula and W¹,¹ approximation. The finite algebra controls do not establish general Morrey.

## Degree-one integer filling discovery and exact verification

Run `python3 research/audit/integer_filling_exact.py` for the folded/vertical rational tetrahedron control (gap exactly 3/8) and rejection of invalid boundary and fractional multiplicities. To run the finite discovery control (requires NumPy/SciPy):

```sh
python3 research/audit/integer_filling_search.py research/audit/integer_filling_search_control.json --seconds 10 --candidate /tmp/filling-candidate.json
python3 research/audit/integer_filling_exact.py /tmp/filling-candidate.json
```

Executed report: [integer_filling_search_control_result.json](integer_filling_search_control_result.json). This is an attained floating MILP result and independently verified exact candidate, not a new positive lower bound. The [BV trace theorem](../../docs/research/IWANIEC_MORREY_INTEGER_FILLINGS.md) supplies the mathematical bridge to actual gradients for any strict negative certified integer filling. Polynomial-tail energies replay the existing global LH certificate; that path has not been separately exercised in this control. Real/multigraph relaxation is not accepted as degree-one compatibility.

## Uniform multiscale geometry cutoff

Run `python3 research/audit/multiscale_constants.py` and `python3 research/audit/relative_margin_constants.py`. The first verifies exact Fourier multiplier support/partition and discarded-gap averaging on integer frequencies in [-16,16]^2, and explicit budgets for six rational tolerances. The second verifies 64 relative-margin parameter triples. See the [analytic proof](../../docs/research/IWANIEC_MORREY_UNIFORM_GEOMETRY_CUTOFF.md). Both scripts were actually executed; they check arithmetic, not the universal localization theorem. The enormous finite optimizations have not been enumerated or solved.

## Global C¹,¹ relative localization and normalized data repair

Run `python3 research/audit/c11_cutoff_constants.py`. Actual local execution checked 16 exact localization budgets and five normalized-repair and rounding budgets. The [analytic proof](../../docs/research/IWANIEC_MORREY_C11_OPTIMAL_MARGIN.md) establishes the all-amplitude relative theorem, explicit rational intervals for the universal margin, and the known-condition-number exact alternative. No large finite LP was evaluated and no exact-zero result or Lean theorem is claimed.

## Cofactor shear duality and universal margin bound

Run `python3 research/audit/cofactor_duality_exact.py` (SymPy). The actually executed exact controls verify the transformed quadratic gradient and inverse formulas, PSD/order comparisons for three shear parameters, six Fourier cofactor-gradient controls, and rational transport/margin constants. See the [hand proof](../../docs/research/IWANIEC_MORREY_COFACTOR_DUALITY.md). This is not independent certification of the analytic duality or a proof of exact zero.

## Joint Hamiltonian flow controls and sufficient transfer certificate

Run `python3 research/audit/joint_hamiltonian_exact.py` (SymPy) and `python3 research/audit/joint_hamiltonian_gap.py` (standard library). The former checks exact canonical/Riccati identities and 27 rational null-direction/4x2 rank-one curvature controls. The latter verifies exact direct LH-SOS identities, rational periodic PL geometry and the sufficient flow-gap upper bound from the [hand proof](../../docs/research/IWANIEC_MORREY_JOINT_HAMILTONIAN_FLOW.md). Both were actually executed. The negative-derivative null scaling control has planar gap 2 and joint Bregman gap -4, but does not pass the strict negative flow test; a corrupted LH-SOS identity is rejected. These are regression tests, not a completed higher-dimensional counterexample campaign or Lean certification.

## Full stationary lift exact algebra

Run `python3 research/audit/full_stationary_lift_exact.py` (SymPy). Actual local execution checked the full lift first/second derivatives, null rank-one tangent identities, three-wave exterior exactness coefficients, canonical Cassese direct-block exactness and quartic densities, and one split-signature row remix. See [the hand proof](../../docs/research/IWANIEC_MORREY_FULL_STATIONARY_LIFT.md). No new solver campaign or qualifying negative planar certificate is claimed.

## Quadratic-tail critical states

Run `python3 research/audit/quadratic_tail_exact.py` (standard library). Actual execution verified the exact changed-core clipping comparison (energy decrease 49/2 and squared error 17), 80 rational Fourier projection/row-rotation controls, and relative variance, inner variation, truncation-rate, annulus and exponential budgets. The [analytic proof](../../docs/research/IWANIEC_MORREY_QUADRATIC_TAIL_CRITICAL.md) uses the pinned verified scalar projection theorem for its exact bounded-amplitude reduction and bounded compatible full lift. The toy clipping control is not a numerical implementation of that projection. No new Lean theorem or exact rigidity result is claimed.

## Inner-stress shear and maximum-defect law

Run `python3 research/audit/inner_stress_shear_exact.py` (SymPy). Actual local execution passed four rational polynomial-jet controls, the symbolic null rank-one contact-Hessian identity, and exact defect/stress-mean and regular-chart budget checks. See the [hand proof](../../docs/research/IWANIEC_MORREY_INNER_STRESS_SHEAR.md). No qualifying planar negative energy was constructed; the local amplifier is conditional on an existing nonzero defect, not a uniform normalized separation or Lean theorem.

## Combined shear and projective transfer

Run `python3 research/audit/combined_shear_exact.py` (SymPy). The executed script (SHA-256 43021001adfbfff7387a4a97105552b4439ae42bf23f79a3baba9690f9cad125) passed 12 exact rational joint-shear algebra checks, an exact quadratic two-orientation chart control, and four rational near-singular folded-sheet controls. See [the analytic proof](../../docs/research/IWANIEC_MORREY_COMBINED_SHEAR_CONTINUATION.md). No exact-zero calculation, qualifying negative planar witness, or new Lean validation is claimed.

## Planar envelope pinching and chart-free contraction

Run `python3 research/audit/envelope_contact_exact.py` (SymPy). Actual execution passed the exact stress/defect and envelope-level algebra and 360 rational atom-penalty checks. The [analytic proof](../../docs/research/IWANIEC_MORREY_ENVELOPE_PINCHING.md) relies explicitly on published planar incompatibility and transition-layer theorems for its new relative coercivity result. Those analytic arguments are not independently verified by the script; no new Lean proof, uniform normalized amplifier or counterexample is claimed.

## Rank-one curvature compactness and optimal contact repair

Run `python3 research/audit/lh_jet_repair_exact.py` (standard library). Actual local execution passed 40 rational multiaffine controls, exact coefficient/growth budgets, 36 contact-parameter controls and the two-point/eight curvature-budget checks. See [the proof](../../docs/research/IWANIEC_MORREY_LH_COMPACTNESS_JET_REPAIR.md). The effective uniform-rigidity algorithm is a theoretical construction depending on R16 and the published generalized gradient YM characterization; no full quantifier-elimination stage was executed. No independent analytic certification, new Lean theorem or unrestricted result.

## Exact local-collapse falsification

Run `python3 research/audit/six_atom_no_local_collapse_exact.py` and `python3 research/audit/reverse_merge_exact.py`. Actual local executions verified the rational six-cycle, separate-convex grid certificate, all three T4 configurations and strict corner gaps/moment determinants, 100 partial pair merges, and ten mixed T4 collapses. See [the analytic proof](../../docs/research/IWANIEC_MORREY_NO_LOCAL_COLLAPSE.md) for why the six-atom test rules out ALL compatible non-Dirac sublaws on at most four atoms, not just selected cycle weights. This is a refutation of a specific universal local-move lemma, not a Morrey counterexample. No new Lean result.

## Direct radial matching universal margin

Run `python3 research/audit/beta_radial_exact.py` (standard library). The actual execution checked rational Taylor-series bounds, scalar-inequality derivative and tangent budgets, and 20 exact radial-kernel controls. The [hand proof](../../docs/research/IWANIEC_MORREY_BETA_RADIAL_MATCHING.md) uses the verified truncated determinant to prove beta_*≥−58/125 for the full normalized C11 class. It does not establish a self-contraction to zero or a new Lean theorem.

## Direct acoustic heat estimate

Run `python3 research/audit/beta_acoustic_exact.py` (SymPy). Actual local execution passed the symbolic heat contraction, trace split, perpendicular acoustic and square-completion identities, and the exact artificial two-state relaxation control. See [the analytic proof](../../docs/research/IWANIEC_MORREY_BETA_ACOUSTIC_HEAT.md). It proves the improved bound −1/8 and curvature contrast ≤5 without an Iwaniec dependency. No actual negative gradient witness, self-contraction, or Lean theorem.

## Heat-jet saturation and exact stronger-relaxation control

Run `python3 research/audit/beta_heat_jet_exact.py` (SymPy). Actual execution verified the spectrum, rank-one curvature, heat cost, all 64 quadratic covariance identities and 16 constant-target weighted identities on 128 symmetrized artificial states, and rational strictness budgets. See [the hand proof](../../docs/research/IWANIEC_MORREY_BETA_HEAT_JET_RIGIDITY.md). These are algebraic checks, not a gradient or constitutive realization, Lean proof, or proof of Morrey.

## Bounded-degree independent-copy contraction test

Run `python3 research/audit/beta_copy_degree_exact.py` (SymPy), or append `--discover` for the actual SciPy/NumPy LP discovery. Both modes passed locally: exact positive rational quadrature weights at degrees 2,4,6,8 for the same artificial law at t=1/16; exact normalization and verified-L discriminator checks. The [hand proof](../../docs/research/IWANIEC_MORREY_BETA_COPY_DEGREE_TEST.md) extends the obstruction to every fixed degree and closure under the listed abstract law operations. No compatible negative gradient law, new universal beta bound, self-contraction or Lean theorem.

## Finite beta certificate and adaptive-detector controls

Run `python3 research/audit/beta_adaptive_detector_exact.py` (standard library). Executed exact rational checks passed the common-energy contact/curvature budgets, 12 anisotropy/dilution checks, the second trap scale-detector failure, and four near-critical nonblocked perturbations with regression-adaptive detection. See [the hand proof](../../docs/research/IWANIEC_MORREY_BETA_ADAPTIVE_CERTIFICATE.md). The finite baseline is refuted by artificial common-energy laws. No actual gradient counterexample, full QE/SDP infeasibility certificate or Lean validation.

## All-affine hyperboloid LP certificate

Run `python3 research/audit/beta_hyperboloid_sos.py` (SciPy, NumPy, SymPy). Actual local execution: six-variable LP with 15 inequalities, HiGHS objective 53, exact coefficient vectors (16,8,1), (18,9,1); all coefficient budgets, seven square decompositions, PSD trace/skew and generic affine identities, 18 transformed trap and 18 near-critical controls passed. SHA-256 4324a7e6c4fa42f2ba5b825c0f5512811f2c7ddcc48e42b323d31215625c1e02. See [the analytic proof](../../docs/research/IWANIEC_MORREY_BETA_HYPERBOLOID_CERTIFICATE.md). No full covariance QE, general QC reweighting theorem, Lean verification or Morrey proof.

## Direct product-metric Legendre beta comparison

Run `python3 research/audit/beta_legendre_exact.py` (SymPy, SciPy). Actual execution checked the exact inverse/normalization identities, 54 rational product-metric controls, and five LP controls against exact triangle-vertex elimination. See [the proof and comparison limitation](../../docs/research/IWANIEC_MORREY_BETA_LEGENDRE_TEST.md). The artificial surviving state is not a common-energy gradient witness. No self-contraction, improved universal bound, or Lean result.
