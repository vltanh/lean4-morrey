# Roadmap to completion

## PRIMARY RESEARCH DIRECTION — remove homogeneity while retaining isotropy

The user is handling the audit/formalization of the signed homogeneous
candidate. Do not reopen the already verified nonnegative theorem.
The new [nonhomogeneous affine-shell theorem](IWANIEC_MORREY_NONHOMOG_SHELL_AFFINE.md)
proves RC=>QC for every finite-valued integrand
F(X)=U(s)+V(s)delta, s=operator norm, delta=signed smaller singular value,
without homogeneity, sign, smoothness or growth assumptions.
It uses only the already formalized L theorem, NOT the signed
homogeneous candidate under separate audit.

Rank-one convexity gives the distributional inequality
U''>=s|V''| and the conformal boundary condition
U'>=|V-sV'|. Hence the two nonnegative measures
mu_±=(U''/s ± V'')/2 represent the entire function, by
positive integrals of the QC kernels K_r^±=(s-r)_+(r±delta)
plus a polyconvex initial support. Truncation at epsilon>0
handles possibly infinite measure near zero and converges
locally uniformly. This closes the full arbitrary radial
affine-shell class, not a fixed-exponent family.

The exact spectral tests for this whole class consist of
the two conformal norm inequalities, the determinant identity,
and the two kernel tests at all positive radii. Compress any
spectral law to its conditional mean delta at each radius:
all these tests are unchanged, while Jensen in delta lowers
EVERY isotropic RC integrand. This does not preserve actual
gradient compatibility. The compact obstacle duality gives
an exact criterion for universal touching affine-shell lower
supports on bounded sets.

**Remaining global target:** arbitrary two-variable isotropic
profiles. The contact-path calculation gives a scalar
differential inclusion for c=M' with
z'=(c-f_sdelta)/f_deltadelta, D*=f_ss-(c-f_sdelta)^2/f_deltadelta,
and -D*/(s-z)<=c'<=D*/(s+z), plus the explicit angular bounds.
Pointwise feasibility follows from planar quadratic
polyconvexity; global viability does NOT follow. Need a
global obstacle minorant, allowing noncontact intervals.
Do not infer full isotropic Morrey or pursue a new exponent,
wave, or polynomial-degree ladder.

Exact rational mixed atomic/diffuse representation and
spectral compression controls passed in the working container.
Hand proofs, not new Lean results. The signed homogeneous
audit and formalization remain separate.

## SIGNED HOMOGENEOUS ISOTROPIC — candidate complete hand proof, every p>0

**Formal baseline corrected:** the separate
[homogeneous-isotropic branch at f70d7e9](https://github.com/vltanh/lean4-morrey/tree/f70d7e9253ecf59ea6c862893d1fdd3fb60cffa9)
has Lean proofs of the nonnegative theorem for every p>0,
signed p=2, p=1 and 0<p<1, and its
[CI including axiom audit passed](https://github.com/vltanh/lean4-morrey/actions/runs/45323677832).
The pinned lean4-iwaniec dependency at 972c0127 contains
Agazzi.quasiconvex_integrandL and Agazzi.quasiconvex_burkholderB.
Older descriptions of this baseline as unformalized/conditional
are superseded.

The [new signed characteristic-integration proof](IWANIEC_MORREY_SIGNED_CHARACTERISTICS.md)
removes the nonnegativity assumption at hand-proof level for
EVERY p>0 and EVERY base, retaining isotropy and homogeneity.
It uses the formalized truncated determinant L rather than
postulating a new analytic theorem.

At a hard base the restricted signed support q in the previous
spectral note touches F, is valid on the unit operator-norm ball,
and supplies monotone supporting planes in (|z|,det) for p<2
or (|w|,det) for p>2. Choose e=-1 or +1 respectively.
Strongly convexify the scalar profile by adding a vanishing
convex Frobenius p-power; parameterize by the inverse supporting
slope T(m) and k(m)=h(T(m))-mT(m). The scalar ODE
dm/dlog(s)=p(k(m)-a m)/(T(m)+e) stays in the hard region
and is well-defined through nonsmooth profile kinks.
The scaled determinant coefficient c_s satisfies e c_s'>=0
by monotonicity of the restricted supporting planes; the t'
terms cancel exactly. Thus w(s)=e c_s' is a nonnegative weight.

Integrate the scaled truncated-determinant QC kernels
K_r^e=(sigma-r)(r+e delta) for sigma>r, zero otherwise,
from radius 1 to infinity with weight w. The resulting global
QC function q+integral w K touches F at the base and, for
every sigma>=1, equals sigma^p times the supporting line
of h at the evolved slope. Hence it lies below F on ALL
matrices, including the earlier exceptional cones. Endpoint,
nonsmooth and non-strict cases follow by the argument in the
note. There is no fixed-wave or fixed-exponent hierarchy.

**Status:** proposed complete signed homogeneous-isotropic
QC theorem by hand; independent proof audit and new Lean
formalization remain. The symbolic checker was executed:
14 exact identities and two exact kink controls passed.
Do NOT claim unrestricted Morrey or general nonhomogeneous
isotropic Morrey. Next priority is independent logical audit
and formalization of the signed extension, then removing
homogeneity while retaining isotropy.

## Signed problem: unconditional spectral half-space supports for EVERY nonzero base

The [new signed spectral-support theorem](IWANIEC_MORREY_SIGNED_SPECTRAL_SUPPORT.md)
gives explicit polyaffine supports for every signed isotropic
p-homogeneous RC integrand, oriented to have its negative values at
negative determinants. Normalize the base operator norm to 1.
For 1<p<2 the support is valid on **all matrices with signed smaller
singular value delta<=1**; for p>2 it is valid on **all matrices with
delta>=-1**. Both cover arbitrary gradient amplitudes and all base
ratios. For the superquadratic hard case the support is also valid
on all nonnegative-energy matrices. Jensen follows on these regions
for every compact law with the correct matrix/determinant moments.
This result is unconditional and does not use the 2026 QC preprint.

The subquadratic hard case uses the new negative scale-maximum proof:
the scale polynomial tends to minus infinity at BOTH ends when det<0,
so its stationary maximum (even negative) is controlled by one
rank-one tangent. Direct rank-one slope inequalities extend the
support to positive determinants with delta<=1. The complementary
superquadratic argument uses the stationary polynomial and two
endpoint estimates to cover every negative-energy matrix with
delta>=-1. The easy bases use elementary signed Burkholder
polyaffine supports on the same spectral regions, with no external
QC theorem.

The theorem gives an explicit global deficit bound by the integral
of a scale-rescaled support discrepancy over the exceptional cones.
**Remaining signed gate:** compensate this discrepancy for all
actual compatible gradients, not just those avoiding expansive
opposite-orientation matrices. No proof of this compensation or of
the full signed conjecture is claimed. The [exact checker](../../research/audit/iwaniec_signed_spectral_exact.py)
was run locally: 160 polynomial and 27 interval feasibility controls
passed. Hand proofs only, no Lean or external review claim.

## PRIMARY RESEARCH DIRECTION — signed isotropic homogeneous quasiconvexity

The fixed-wave and abstract martingale/compatibility-penalty research
is retained below as historical work, but suspended as the main direction.
Return to the provisional all-p>=2 nonnegative isotropic homogeneous
polyconvexity theorem and the conditional 1<p<2 quasiconvexity theorem.
Remove nonnegativity first, targeting QC rather than PC, simultaneously
for all exponents and all base matrices.

The [signed scale-maximal generator theorem](IWANIEC_MORREY_SIGNED_SCALE_MAX.md)
uses **Theorem 1** of Agazzi et al. (2026), arXiv:2609.28311v2,
rather than only its Burkholder corollary. It proves an infinite-dimensional
family of signed, isotropic, p-homogeneous QC integrands for every p>1
by taking the pointwise maximum of the scaled truncated determinant L_r
with a scaled convex competitor BEFORE integrating over radii. Explicit
convergence and scaling arguments make the Jensen proof global.

For every p>2 the new explicit family agrees with Burkholder exactly
on a prescribed cone t<=c in (0,1) and is strictly above it outside,
addressing the earlier signed-cone support limitation constructively.
For every 1<p<2 another exact signed family has a negative conformal
base where no affine Burkholder-profile support is possible, yet is
globally QC. Both follow directly from the 2026 L theorem; no numerical
rank-one-convexity assumption or fixed-wave hypothesis is used.

**All-integrand base coverage:** for 1<p<2, the signed theorem holds
at every nonnegative-energy base, including zero, by the endpoint
tangent argument. For p>2, all nonpositive-energy bases are covered,
and the remaining positive-energy bases with admissible affine tangent
are also covered. The signed p=2 case is polyconvex; p=1 is classical
convexity under isotropy; 0<p<1 gives identically zero.

**Next main gate:** prove quasiconvexity at the genuinely missing
signed bases for every profile. Try constructing touching global
minorants using the new scale-maximal generators; the convex competitor
is not fixed to a single parametric family. No completeness theorem
for this support method is established. Do not substitute an infinite
sequence of special exponents, model gradient fields or new equivalent
martingale formulations for the global signed-profile problem.

The [checker](../../research/audit/iwaniec_signed_scale_exact.py) passed
in the working container. Hand proofs conditional on the cited preprint;
no Lean or human review claim. The signed problem and unrestricted
Morrey remain open.

## MAIN GATE correction — the proposed universal Delta-preserving split is REFUTED

The [new exact no-go theorem](IWANIEC_MORREY_DELTA_NOGO.md)
proves that **all minor-compatible laws with full covariance condition
number <=3/2 automatically have Delta=0**, uniformly over EVERY affine
transform in the penalty. The proof combines the semiconvex bound
g<=s/2 for the determinant-index Jensen gap with the negative-sheet
bound g<=(1/2+kappa)v, where s,v are the transformed centered symmetric
and skew variances and kappa is the covariance condition number.

The explicit law with atoms +/-5I,+/-5J each of mass 1/104 and
+/-diag(1,-1),+/-[[0,1],[1,0]] each of mass 25/104 has mean and
mean determinant zero, covariance (25/26)I4, and Delta=0. Yet the
globally rank-one convex signed Dacorogna--Marcellini quartic
F=|X|^4-(9/4)|X|²det X has **exact Jensen gap -50/13**.
Rank-one convexity has a direct rational SOS proof. This is an
abstract nonlaminate, NOT an actual compatible-gradient witness.
The no-go does not depend on the recent quasiconvexity preprint.

Consequently r_comp(nu)>r(nu)>0 for this abstract law: an optimal
unconstrained decomposition cannot simultaneously have zero average
Delta, by the exact trap classification. The stronger proposed
uniform splitting principle on ALL minor-compatible Delta-zero
laws is false and must NOT be pursued further. The counterexample
persists for smooth compact densities with connected support.
A further proof gives both laminate and nonlaminate realizations
of any prescribed positive definite determinant-neutral covariance.

The original equality r_comp=r for ACTUAL gradient laws remains
open and equivalent to Morrey; it is not refuted by this example.
The quantitative trap exclusion and exact neutral martingale tools
are unaffected. Any continuation must use spatial information
beyond these determinant-index tests and second moments, not
another finite-wave hierarchy.

The [exact checker](../../research/audit/iwaniec_delta_nogo_exact.py)
was actually executed locally: exact moments, quartic gap, SOS
coefficients and 256 rational affine controls passed. The all-transform
inequality is a hand proof, not a sampling inference. No Lean or
external review claim.

## MAIN GATE refinement — quantitative compatibility penalty detecting EVERY terminal trap

The [new trap compatibility note](IWANIEC_MORREY_TRAP_COMPATIBILITY.md)
uses spatial compatibility beyond mean/determinant moments. Every
blocked geometry from the adaptive theorem has an invertible affine
normalization to a symmetric law of mean I and determinant one,
with opposite-sheet mass w>0. The classical Šverák determinant-index
integrand, together with a periodic Helmholtz decomposition, gives
an explicit all-gradient inequality for arbitrary full 2x2 laws:
h(sym A)<=E h(sym X)+||sym X||_2 ||skew(X-A)||_2.
Thus a normalized blocked law is at W2 distance at least
w/(3||X||_2+2) from every compact homogeneous gradient law.
The known qualitative hyperboloid rigidity is acknowledged as
prior art; this is a quantitative form and all-trap application.

A full-matrix extension theorem approximates any continuous
quadratic-growth symmetric Hessian-quasiconvex function on compact
symmetric sets by smooth globally strongly QC functions with
bounded Hessian (Helmholtz projection plus quadratic skew penalty).
It gives explicit full-matrix QC separators for every trap.

**Single compatibility penalty Delta(eta):** maximize the positive
violation of the displayed sheet inequality over affine transforms
P X Q+B with the three Frobenius norms <=1. This is a compact
12-real-parameter maximum, continuous on laws with common compact
support, zero for every gradient law, and strictly positive for
EVERY nontrivial blocked law. It does not depend on wave count,
atom count or integrand degree.

Let r be the earlier minimum unresolved variance over feasible
adaptive decompositions, and r_comp the same minimum constrained
to average Delta=0. For gradient laws r_comp is feasible at least
at the trivial decomposition. **The sole new main target** is
r_comp=r for all actual gradient laws. Equivalently it suffices
to construct feasible decompositions with residual approaching
r and average Delta approaching zero. Compactness and the exact
trap classification would then force r=0 and settle Morrey.
A stronger sufficient uniform construction is a nonzero rank-one
split preserving Delta=0 at every non-Dirac minor-compatible
law with Delta=0; its existence is NOT established. **SUPERSEDED: this stronger uniform principle is refuted by the Delta no-go above.**

**Mandatory caution:** an explicit smooth separable product
gradient (already a laminate) admits a legal nonzero rank-one
minor-preserving observation with a nonlaminate trapped posterior
of probability 1/9. Thus arbitrary greedy neutral conditioning
does NOT preserve compatibility. The optimization over choices
is essential. This is not a negative Morrey witness.

The [exact checker](../../research/audit/iwaniec_trap_compatibility_exact.py)
was actually executed: 2D/3D trap moments, four nonsymmetric
normalization controls and the smooth plateau probability bounds
passed (explicit W2 lower bound 1/72 for the diagonal trap).
Hand proofs only, no Lean/external review/novelty claim.
No fixed-wave or atom-count investigation is resumed.

## MAIN GATE refinement — exact input-adaptive representation and complete terminal-trap geometry

The [new adaptive martingale note](IWANIEC_MORREY_ADAPTIVE_MARTINGALE.md)
contains three global structural results, not more fixed-wave cases.

**Mandatory change to Beurling strategy:** a single COMMON
filtration for all inputs is impossible, even approximately.
The product identity of three Fourier phase martingales proves
that twelve fixed smooth individually laminate two-ridge gradients
have total common-filtration determinant cost >=1, independently
of depth and auxiliary randomness. Continuous covariations give
the same obstruction. For projected Beurling representations in
a common continuous filtration, some input has expected absolute
trace-bracket mismatch >1/300. Thus a successful determinant
martingale construction must be input-specific, not a universal
linear/common-filtration representation.

**Exact continuous characterization:** every compact laminate
(and only such a law) is the terminal law of a bounded continuous
matrix martingale whose determinant is a martingale. This follows
from unit-speed stopped Brownian rank-one splits, tightness on
compact time intervals and a uniform terminal time tail bound.
It removes any concern that exact continuous representation might
be strictly stronger than D=0.

**Global adaptive reduction:** at a conditional law satisfying the
minor identity, use its centered lifted covariance in R^5.
An exact minor-preserving rank-one binary observation exists
iff the projection at zero determinant-coordinate contains a
nonzero rank-one matrix. All nontrivial blocked laws are supported
on BOTH sheets of a two-sheeted hyperboloid, in affine dimension
2 or 3, and none is a laminate. A compact maximal-variance
decomposition over minor-compatible conditional laws with
laminate barycenter distribution leaves only Diracs and these
classified traps; its minimum residual r satisfies D<=r/2 and
r=0 iff D=0.

Every nonconstant smooth periodic gradient has connected support
and satisfies the minor identity, so admits an exact
minor-preserving nonzero rank-one split. Positive likelihoods
retain the original support and permit further finite steps,
but this does NOT establish vanishing residual at infinite depth.
Conditional laws may lose actual gradient compatibility.

**Sole open global gate:** use actual gradient compatibility to
avoid the nontrivial two-sheeted traps in an OPTIMAL adaptive
decomposition (r=0), or construct the equivalent exact input-specific
neutral martingale. An arbitrary nonoptimal trapped decomposition
does not refute Morrey. No proof of global avoidance or actual
negative witness is provided; no wave/degree ladder is resumed.

The [exact checker](../../research/audit/iwaniec_adaptive_martingale_exact.py)
passed locally: 64 rational phase-filtration controls and
two 2D/3D trap controls plus the explicit positive-likelihood split.
Hand proofs only, no external review, novelty or Lean claim.

## MAIN ROUTE — unrestricted scalar determinant defect; fixed-wave investigations suspended

The [new global martingale-defect theorem](IWANIEC_MORREY_MARTINGALE_DEFECT.md)
defines a nonnegative scalar D(nu) for ANY compact planar matrix law:
inf over finite binary conditional-expectation filtrations of
E sum |det Delta M| plus half the unresolved terminal variance.
**No fixed wave count, integrand degree, isotropy or homogeneity.**

- Quantitative repair: nearest rank-one truncation of each binary
  increment, with a controlled stopping rule, yields a finite-order
  laminate supported in B_{4R}(A) at W2-squared distance <=2D(nu)
  in the infimum. A two-sided coupling continuity bound and the
  classical bounded prelaminate approximation theorem show
  **D=0 iff laminate**. For every smooth RC F of local Hessian
  bound K, the Jensen deficit is <=K D(nu).
- Exact global dual: D is the supremal Jensen deficit over smooth
  functions with Hessian lower bound -2|det H| in each direction.
  A determinant-penalized binary Bellman envelope proves exact
  duality, not a heuristic or finite termination guarantee.
- Continuous covariance repair: a PSD determinant-neutral
  covariance is a sum of rank-one outer products. Itô yields
  the Jensen deficit <=K times expected absolute determinant
  bracket variation.
- **Beurling projection bridge:** for any projected martingale
  representation U_T=g(P), E[V_T|P]=Bg(P), define delta as
  expected total variation of the difference of the two complex
  trace brackets. Unitarity gives projection variance <=delta;
  Taylor plus the covariance estimate gives the actual gradient
  Jensen deficit <=2K delta, without a false conditional Jensen
  step. A smooth bounded-Hessian extension matching the test
  ball removes all growth restrictions.

The exact checker actually passed 160 rational martingale controls,
59 with early stopping, plus a projection algebra control.
These are hand proofs and exact regression checks, not Lean or
human certification. No proof of the zero-defect assertion or
counterexample is claimed.

**Sole main mathematical gate:** prove D(law(A+Dphi))=0 for
every periodic Lipschitz phi, e.g. construct projected Beurling
martingale representations of arbitrary smooth periodic gradients
with absolute bracket mismatch delta -> 0. Alternatively find
a genuine compatible gradient with certified D>0.
Standard projected representations and norm bounds do not give
this pathwise/total-variation property. A signed cancellation is
not enough. No wave-count or degree ladder will establish it.

The earlier four-wave D/TQ corner list is retained below as
historical subordinate work but **suspended**: closure of one or
both corners would not advance the missing global implication
without a universal coupling/induction argument.

## N=0,...,4 ledger: entire four-wave problem reduced to TWO fixed corner inequalities

The [new exhaustive four-wave reduction](IWANIEC_MORREY_FOUR_WAVE_CASES.md)
clarifies the crucial quantifier: the bound of four applies to
minimal odd-resonance supports, NOT to total wave count.
N=0,1,2 are elementary and N=3 is the published
Sebestyén–Székelyhidi theorem. The general N=4 gate is now
reduced by hand proofs to **two fixed 16-atom weight laws**,
each tested on arbitrary rank-one H_1,...,H_4 and arbitrary F:
D has density (1+e123/2+e124/2)/16 and TQ has density
(1+e123/2+e1234/2)/16. Both corner inequalities remain OPEN.

New proof components: (i) exhaustive six-row normalized mod-2
classification of four pairwise nonparallel frequencies;
(ii) **universal absolute fourth-Walsh-correlation bound 1/2**
for all distinct directions, including the nonminimal
triple+quadruple case, by lattice-projection index bounds,
Cauchy–Schwarz, and a separate explicit unit-triad integral;
(iii) complete three-direction case (one parallel pair) using
conditional triangular correlation, 2-adic support and a
six-vertex outer polytope, reduced to the SAME two corners.
One/two spatial directions are elementary. No additional
integer-frequency cases remain in this sufficient N=4 reduction.

The [exact checker](../../research/audit/iwaniec_four_wave_cases_exact.py)
was run locally: 22 mod-2 multisets, six parallel-pair
generating points and two rational polygon sign-law controls
passed. One actual unit double triad attains D exactly;
one triple+quadruple field has correlations 1/2 and 1/4,
so the earlier total-parity budget genuinely fails.

**Next bounded task:** prove D and TQ, e.g. via fixed-weight
rank-one cube certificates parametrized by split-signature
determinant forms. These are sufficient outer corner laws;
failure for arbitrary H_i without actual spatial compatibility
would not itself be a four-wave counterexample. No bound on
certificate-tree size is asserted. Neither Lean nor external
human review yet. Even closing both corners would not prove
the all-N induction needed for unrestricted Morrey.

## All-N composition theorem for overlapping circuits, and nonunit three-ridge waveforms

The [new random-cube composition theorem](IWANIEC_MORREY_CUBE_COUPLING.md)
handles arbitrary N bounded rank-one-subspace-valued profiles with
pairwise independent reference variables and a joint density p
relative to the product marginals. It proves universal Jensen whenever
||p-1||∞ ≤ 1/[2(3^N-2N²-1)], or under the sharper local
mixed-difference parity budget. Randomly sampled pairs in each
coordinate yield translated rank-one cubes with overlapping parity
interactions. The proof uses the published planar three-wave theorem,
finite subset Möbius inversion for **exact** probability reconstruction,
and independent midpoint convex Jensen. The same theorem gives
conditional block removal with an arbitrary retained tail.

An explicit **arbitrary-N actual-gradient** application has all
frequency lengths within a factor of five, no dyadic or parallel-block
peeling, and m nonparallel minimal triple circuits sharing two core
waves, with simultaneously nonzero triple correlations. The two core
ridge derivatives are arbitrary bounded vector-valued profiles.
A uniform grid-discrepancy argument proves near-product density for
every phase choice. This is not an assertion of arbitrary comparable-
scale Jensen; the family is weakly dependent.

A separate nonperturbative antithetic-pair argument handles two
arbitrary bounded ridge derivatives plus a sawtooth in a third
nonparallel direction whenever that direction's coefficient in
the primitive frequency relation has magnitude ≥2. Arbitrary third
step profiles are covered if the coefficient times their minimum
interval length is ≥16. The unrestricted three-ridge waveform claim
remains open; there is no fixed-winding fine-partition limit.

The [checker](../../research/audit/iwaniec_cube_coupling_exact.py)
actually passed: exact nonbinary overlapping-cube reconstruction,
exact rational grid discrepancy controls, and arithmetic construction
checks through 102 variables. Hand proofs only; no Lean or human
certification or novelty claim.

**Remaining P2 gate:** remove the small-dependence assumption or
prove a gap-preserving universal conditional decomposition for
strongly correlated clusters. Do not enumerate larger isolated
cases or infer universal Jensen from pairwise independence.

## Bounded minimal resonance circuits and complete parallel-block peeling criterion

The [new arithmetic/circuit theorem](IWANIEC_MORREY_MINIMAL_RESONANCE.md)
proves for **arbitrary N and arbitrary integer frequencies** that
every odd-resonant subset contains an inclusion-minimal odd-resonant
subset of size at most four. This bound is sharp. Normalize the
subgroup generated by a subset, reduce modulo twice that subgroup,
and use an odd-index argument. The only minimal patterns are a
parallel pair, three distinct nonzero mod-2 classes, or a pairwise
nonparallel quadruple in two mod-2 classes with multiplicities 2+2.

**All isolated minimal blocks are laminates:** the full four-circuit
case is now closed by the Fourier Cauchy–Schwarz argument with
odd determinant denominator, including non-unimodular coordinate
pairs. No special frequency-family hypothesis remains for minimal
four-circuits. The deep input is the published planar three-wave
theorem. The all-N pure-parity mixture also handles arbitrary overlaps
when the total absolute nonconstant Walsh correlation is at most 1/2
and all pair moments vanish; this covers the doubly resonant
nonunit-triad 2+1+1 four-wave class uniformly in phases.

**Complete all-N theorem for parallel-block peeling:** a tuple
can be fully eliminated by parallel rank-one blocks satisfying
the even/infinite-order tail-lattice criterion **if and only if**
it contains no rank-two minimal odd-resonant circuit. A greedy
algorithm works in every such case; it removes an entire parallel
nonzero mod-2 class and recomputes the lattice. Any rank-two circuit
is invariant under all permitted peeling steps. This is a
necessary/sufficient condition for this METHOD, not for Jensen.

The [exact checker](../../research/audit/iwaniec_minimal_resonance_exact.py)
passed locally (150 small exact classifications and a 63-wave
irreducible control). Hand proofs; no Lean/human certification.

**Remaining P2 gate:** interactions between bounded circuits are
still unbounded. Explicit tuples of arbitrary size have every
wave in a rank-two triple circuit and admit no parallel-block
peeling. Do not infer a bounded wave-count reduction or universal
Jensen from the bounded minimal-circuit classification; a genuine
coupling/conditional laminate theorem is required.

## Unrestricted wave count: conditional dyadic lamination and arithmetic peeling

The [new conditional-lamination theorem](IWANIEC_MORREY_DYADIC_LAMINATION.md)
establishes a block removal inequality for arbitrary finite-valued planar
rank-one convex integrands, at every base and for arbitrary phases and
amplitudes. An arbitrary block of at most three integer-frequency waves
can be removed in the presence of ANY tail whose frequencies are
multiples of a suitable explicit power of two. In the distinct nonzero
mod-2 classes, a factor of 4 suffices. The key is a finite-grid triple
parity bound **conditional on the entire tail**, including the sharp
unit-triad case; the published N=3 theorem is the deep input.

Iteration proves Jensen for arbitrarily many interacting dyadic-scale
blocks, with no wave-count bound (explicit cross-scale correlation 1/4).
The general lattice peeling rule also removes any wave of even or infinite
order modulo the lattice of the others, or a whole such block in a
common rank-one subspace. A hypothetical negative gap survives deletion.
The [exact finite-grid checker](../../research/audit/iwaniec_dyadic_grid_exact.py)
passed locally. These are hand proofs, not Lean-certified or independently
refereed, and no novelty claim is made.

**Remaining unrestricted gate:** control irreducible comparable-scale
resonance clusters, which still have unbounded size. Do not enumerate
ever larger separated chains or infer a bounded wave-count cutoff.
No general four-wave or unrestricted Morrey proof is claimed.

## New unrestricted four-wave gate — one genuine correlated family CLOSED

The [correlated four-wave theorem](IWANIEC_MORREY_FOUR_WAVE_PARITY_THEOREM.md)
is a **global every-integrand, all-amplitude,
all-phase** rank-one Jensen theorem for the
**four-parameter integer frequency family**
\(u,v,a u+b v,c u+d v\),
where a,d are arbitrary odd and
b,c arbitrary nonzero even integers,
with u,v independent integer vectors.
It does not assume isotropy, homogeneity,
p-growth, positivity, polynomiality
or strict ellipticity.
The gradient sign law has a nonzero
four-way parity correlation (rho=1/3
at zero phase), yet the all-phase
Fourier/Cauchy–Schwarz estimate
\(|\rho|\le1/2\) places it in a planar
laminate family. The critical
input is Sebestyén–Székelyhidi's
**already published N=3 theorem**.
The [exact checker](../../research/audit/iwaniec_four_wave_parity_exact.py)
passed rational polygon/probability
and integer odd-resonance controls.

Two **unbounded-N** structural results:
(a) absent any subset odd-frequency
resonance, all signs are independent
for EVERY choice of phases, so the
resulting gradient law is a finite
laminate of arbitrary order;
(b) every N≥3 pure-parity law
\(2^{-N}(1+\rho\prod_i\epsilon_i)\)
on rank-one cube directions is a
laminate whenever \(|\rho|\le1/2\),
by the published N=3 case followed
by repeated rank-one conditional splits.

**Remaining open positive gate:** for
an arbitrary 4-wave tuple, the
sign law may have **several nonzero
triple and fourth-order Walsh
coefficients**. A universal rank-one
Jensen argument for those genuinely
coupled measures is not supplied.
Even a complete N=4 theorem would
not alone imply the ALL-N
characterization required for
Morrey. Avoid rediscovering
N≤3 prior art or treating
minor-compatible laws as
gradient laws; this work operates
on **actual** periodic gradients.



## Unrestricted sign/regularity gate — closed by reduction

[Positive smooth coercive strongly RC reduction](IWANIEC_MORREY_POSITIVITY_REDUCTION.md): any strict Morrey counterexample can be mollified, exponentiated and quadratically strictified while preserving a negative compatible-gradient Jensen gap. The unrestricted theorem is equivalent to its restriction to this positive smooth coercive class. The reduction also preserves isotropy but not homogeneity. The universal QC step remains open.


## Unrestricted exact finite-symmetry reduction

[New elementary reduction](IWANIEC_MORREY_FINITE_SYMMETRY_REDUCTION.md): any unrestricted strict counterexample can be translated, localized by a finite maximum of affine-biased orbit copies, and clipped to become nonnegative and invariant under any prescribed finite rank-one-preserving orthogonal group. Thus proving QC for all such nonnegative finite-symmetry RC energies at all bases is equivalent to unrestricted Morrey. No homogeneous or continuous-isotropy reduction follows. Hand proof, no novelty or Lean claim.


## G1 achieved conditionally: global anisotropic and nonhomogeneous QC neighborhoods of EVERY strict isotropic core

**Assume** the p≥2 nonnegative isotropic
p-homogeneous RC⇒PC hand theorem has
been independently verified, as
requested by the user. The new
[quantitative all-p stability theorem](IWANIEC_MORREY_ANISOTROPIC_QUANT_STABILITY.md)
then proves a **direct all-gradient bridge**
for each smooth isotropic p-homogeneous
core F0 obeying
\(F_0(A)\ge\alpha|A|^p\) and
\(D²F_0(A)[H,H]\ge\mu|A|^{p-2}|H|²\)
on every rank-one H, with α,μ>0.

An explicit p-power subtraction
\(B=F_0-c|A|^p\),
\(c=\tfrac12\min(\alpha,\mu/[p(p-1)])\),
remains nonnegative isotropic p-hom
and globally RC, hence **PC by the
assumed theorem**. The p-power's
explicit uniform convexity constant
\(c_p=p/[(p-1)4^{p-1}3^{p-2}]\)
gives a **quantitative QC margin**.
Any arbitrary, including anisotropic
and nonhomogeneous, C² perturbation G
satisfying
\[
\|D²G(A)\|_{\rm op}
 \le c\,c_p\,|A|^{p-2}
\]
then yields F0+G globally **RC and QC**,
with positive weighted Jensen margin
\(c\,c_p/2\) for EVERY periodic
gradient with arbitrary amplitude
and wavelength.

A nonconvex explicit isotropic
quartic core
\(F_0=s(s-2\det A)+s²/100\)
admits the exact perturbation
Hessian radius \(1/259200\);
[exact coefficient checker](../../research/audit/iwaniec_anisotropic_stability_exact.py)
passed.

**CLOSED G1 only in this quantitative
strict ellipticity regime**:
this is an infinite-dimensional
neighborhood around EVERY such
core, not just a finite sample.
**G2–G4 remain OPEN**:
the proof does not control arbitrary
large anisotropic/nonhomogeneous
departures, degenerate rank-one
ellipticity, or all compatible
gradient Young measures.
An unrestricted result must
control these without a small
weighted C² assumption.
The assumed isotropic theorem and
this new deduction remain
hand-level, not Lean-certified.


## Global two-line frequency-tail theorem (all gradient fields, 23 Nov 2026)

The **unconditional** [two-direction Fourier-tail bound](IWANIEC_MORREY_TWO_LINE_SPECTRAL.md)
applies to every globally RC finite-valued
2×2 F, including signed, anisotropic,
nonhomogeneous and nonsmooth energies,
at EVERY base and for EVERY periodic
W¹∞ planar gradient. Fourier projection
onto any two primitive frequency lines
is a genuine compatible two-ridge field,
and the standard two-ridge rank-one Jensen
inequality applies. Hence
\[
 F(A)-\fint F(A+D\varphi)
 \le L_R
 \sqrt{\|D\varphi\|_2^2-
        e_{(1)}-e_{(2)}},
\]
where \(e_{(1)},e_{(2)}\) are the
two largest Fourier gradient energies
grouped by primitive line. A true
Morrey counterexample with gap δ>0
would need at least \(\delta^2/L_R^2\)
of energy outside its two strongest
Fourier directions. The [exact
spectral regression](../../research/audit/iwaniec_two_line_spectral_exact.py)
passed.

**Scope:** No finite reduction for
general gradients is obtained. The
published two-wave Jensen result is
the essential input. A proposed
three-direction replacement was
invalidated by an inequality-direction
error (see [retraction](IWANIEC_MORREY_THREE_RIDGE_GLOBAL_QC.md)).
The unrestricted positive Morrey
gate remains control of arbitrary
three-and-higher correlated gradients
with no strict LH margin.


## UNRESTRICTED progress and explicit failed extension (23 November 2026)

**New valid exact all-N positivity theorem.** The
[strict-curvature high-resonance theorem](IWANIEC_MORREY_STRICT_RESONANCE.md)
shows that for **every** \(C^2\) isotropic OR anisotropic,
positive OR signed, homogeneous OR nonhomogeneous
integrand having a uniform rank-one Hessian
margin \(\mu>0\) and full Hessian bound M on
the relevant matrix cube, arbitrary finite N
compatible sinusoidal waves satisfy **exact Jensen**
whenever a suitable n obeys
\(4n<\ell\) and \(4MR^2/n\le\mu\sum_j\|H_j\|_F^2/4\).
This follows from an exact independent-phase
strong Jensen margin plus the established
Bernstein/Fourier resonance approximation bound;
the proof has **no fixed wave-count restriction**.
[Exact signed/anisotropic/nonhomogeneous rational regression](../../research/audit/iwaniec_strict_resonance_exact.py)
passed locally, with minimal resonance length
1026 and a positive margin above the
Bernstein correlation-error bound.

**MANDATORY correction:** An attempted derivation of
Jensen for *all arbitrary three-ridge waveforms*
from the 2017 Sebestyén–Székelyhidi
three-**sawtooth** theorem was **INVALID**:
randomizing vector-valued ridge derivatives
into sawtooths and invoking rank-one convexity
gives \(F(\mathbb EZ)\le \mathbb EF(Z)\),
while the published Jensen lower bound
controls only the randomized average.
Those two inequalities give **no lower
bound for the original ridge field**.
See the [explicit retraction/audit](IWANIEC_MORREY_THREE_RIDGE_GLOBAL_QC.md).
The proposed all-gradient spectral
distance-to-three-lines estimate is
therefore **NOT PROVED** and must
NOT be used in any further gate.

**Next global gate:** Control the
short-resonance correlations without
requiring a positive uniform rank-one
Hessian margin. No existing argument
handles all gradient fields; unrestricted
Morrey remains OPEN. Do not claim a
positive all-three-ridge result until
a fundamentally different lower-bound
argument is supplied.


## Global Morrey route: arbitrary-F rank-one Fourier resonance sieve (23 November 2026)

**New exact result:** the [all-N resonance theorem](IWANIEC_MORREY_RESONANCE_SIEVE.md)
works for EVERY finite-valued globally rank-one-convex \(F:\mathbb R^{2\times2}\to\mathbb R\),
including signed, anisotropic, nonhomogeneous functions.

For an actual periodic gradient consisting of ANY FINITE number of rank-one
sinusoidal waves with integer wavevectors \(k_j\), define \(\ell\) as the
smallest nonzero integer-relation order \(\sum|n_j|\) with
\(\sum n_j k_j=0\). For ANY rank-one-convex polynomial \(F\) of total
degree \(d\), \(\ell>d\) **guarantees exact Jensen** at every base,
arbitrary amplitude and any phases. For arbitrary (nonpolynomial) RC
\(F\), a four-coordinate tensor Bernstein proof gives a **quantitative**
bound on its possible Jensen deficit of \(4L_RR/\sqrt{n}\) whenever
\(4n<\ell\) (or \(4M_RR^2/n\) for C² \(F\)). Therefore any prescribed
strict negative gap forces a **bounded-order integer resonance**.
The [pure rational checker](../../research/audit/iwaniec_morrey_resonance_exact.py)
tests all 35 quartic cosine moments for a triple with minimum
resonance length 7, and a nonzero cubic-triad correlation.

**PRIOR ART:** Two-wave quasiconvexity from RC is known, and the
three-sawtooth-wave planar theorem is **Sebestyén–Székelyhidi (2017)**,
restated by Guerra–Teixeira da Costa (2021), Theorem 3.3(d).
Do not duplicate these achievements or claim novelty. The
new sieve is a global frequency-geometry reduction, **NOT**
a proof of all-wave Jensen, and no uniform bound on the
number or size of waves is obtained.

**Decisive open gate:** Prove a phase-correlated *resonant*
energy inequality uniformly over arbitrary wave count and
all rank-one-convex \(F\), or exhibit an exactly certified
compatible-gradient counterexample. Do not grind a
growing list of fixed wave counts; the bound is intended
to isolate the universal resonance mechanism.


## 23 November: global anisotropic and nonhomogeneous QC open neighborhood

The [new open-family theorem](IWANIEC_MORREY_ANISOTROPIC_OPEN_QC_NONPC.md)
produces **an infinite-dimensional open ball** of
positive, coercive, uniformly strongly RC,
globally QC but nonpolyconvex 2×2 integrands.
They are permitted to be **both anisotropic and
nonhomogeneous simultaneously**.
The exact four-atom nonpolyconvexity
gap survives **every** bounded C²
perturbation with
\(\|G\|_\infty<10^{-4}\),
\(\|D^2G\|_\infty<10^{-3}\).
Global QC is conditional on the
Bruno–Pasqualotto (2026)
quasiconvexity theorem for the
Dacorogna–Marcellini quartic;
all other inequalities have exact
hand proofs and a rational checker.
This goes beyond the isotropic
homogeneous subclass for **all
gradient amplitudes and oscillations**,
but the proof uses *one known QC
core plus a convex perturbation*.
It is not a proof of universal
RC⇒QC. Do not confuse the
minor-law PC counterexample
with a compatible-gradient QC
counterexample.

The [fresh independent logic audit](IWANIEC_MORREY_PGE2_BRIDGE_LOGIC_AUDIT.md)
checks seven central Case I identities
and the no-homogeneity obstruction
exactly; no fatal gap in the new
isotropic p≥2 hand proof was
identified. The isotropic theorem
is NOT Lean-certified or externally
human-reviewed.

**Unrestricted next target:** a
phase-sensitive and scale-sensitive
gradient Jensen bound for arbitrary
RC integrands, or a genuine
globally certified compatible-gradient
counterexample. Existing
[negative certificate hierarchy](GLOBAL_CERTIFICATES.md)
is complete with *unbounded*
degree/mesh/SOS order, but
supplies no universal finite cutoff.
No theorem currently bridges
this missing step.


## Research update — provisional isotropic completion, unrestricted remains open (23 Nov 2026)

The new [all-p≥2 isotropic p-homogeneous theorem](IWANIEC_MORREY_PGE2_POLYCONVEXITY.md)
claims a **global poly-affine minorant at every matrix** for
every nonnegative isotropic p-homogeneous RC integrand, p≥2.
An [independent logical audit](IWANIEC_MORREY_PGE2_INDEPENDENT_AUDIT.md)
verified the major algebra and the formerly missing Case I
rank-one-line/scaling step and found no fatal gap. This is a
**provisional AI hand proof**, not a Lean theorem, external
referee report, or settled priority claim. All previous
I12 "still open" text below is historical and is
**superseded provisionally** by this audit; the
generalized result must be independently verified
before being treated as accepted.

**Unrestricted Morrey remains OPEN.** Do NOT attempt to
remove homogeneity or isotropy while demanding
polyconvexity: both are provably impossible.

- Remove isotropy: nonnegative anisotropic positively
  p-homogeneous RC energies are nonpolyconvex for
  **every p≥2**. The [corrected exact
  three-atom witness](IWANIEC_MORREY_P2_SIGNED.md)
  repairs a determinant arithmetic error in
  Guerra–Kristensen (2022), Proposition 3.7.
- Remove homogeneity: the [fully explicit
  strictly positive isotropic example](IWANIEC_MORREY_NONHOMOG_PC_NOGO.md)
  W(A)=exp(||A||_F^4−(9/4)||A||_F² det A)
  is RC but nonpolyconvex, certified by
  a rank-one Hessian SOS and four exact atoms.

Neither witness shows **nonquasiconvexity**.
The new unrestricted gate is an actual-gradient
Jensen theorem for arbitrary anisotropic and
nonhomogeneous RC functions (or a fully verified
counterexample). The proposed isotropic proof's
critical equality F(A_tau)=F(A/lambda), when two
matrices share signed singular magnitudes,
breaks **without isotropy**. Its stationary
rescaling breaks **without homogeneity**.
These are exact barriers to this proof route.

### Smooth/coercive/strongly rank-one convex does not repair the PC bridge

The [positive isotropic no-go](IWANIEC_MORREY_NONHOMOG_PC_NOGO.md#2a-the-counterexample-can-be-smooth-coercive-and-uniformly-strictly-rank-one-convex)
extends to
\(W_\varepsilon(A)=
 e^{\|A\|_F^4-(9/4)\|A\|_F^2\det A}
 +\|A\|_F^2/1000\).
It is **real analytic, coercive, strictly positive and
globally rank-one convex with an exact uniform
ellipticity margin 1/500**, yet fails
four-atom polyconvex Jensen at zero with an
explicit rational gap. Therefore none of
smoothness, coercivity or a strong
Legendre–Hadamard margin allows simply
discarding the homogeneity hypothesis of
the p≥2 isotropic polyconvexity theorem.
An unrestricted proof **must** use
actual gradient compatibility to
establish **QC**, not PC.


### An all-anisotropic averaged positive consequence (conditional on the new theorem)

For any **nonnegative positively p-homogeneous,
p≥2, rank-one-convex** F, even if anisotropic,
the bi-SO(2) average
\(\bar F(A)=\int_{SO(2)^2}F(RAS)\,dR\,dS\)
is nonnegative, p-homogeneous, isotropic and RC,
so the new theorem, if independently validated,
implies \(\bar F\) is polyconvex.
Thus for **every** minor-compatible law ν with barycenter A,
\[
\int\!\!\int F(RBS)\,dR\,dS\,d\nu(B)
\ge\int F(RAS)\,dR\,dS .
\]
This is a globally quantified
**rotation-averaged Jensen inequality**, not a
pointwise inequality for F. The anisotropic
three-atom non-PC example shows deaveraging
cannot hold for arbitrary minors laws.
The full QC/Morrey implication remains
the main unresolved obstacle.




**Status: open.** The positive and negative routes below are alternatives. Neither is completed
by the present ledger. The main task is a statement about every planar gradient and every
rank-one-convex integrand, or one globally certified planar counterexample.

### Signed p=2 extension and an anisotropic no-go (22 November 2026)

A [new hand proof](IWANIEC_MORREY_P2_SIGNED.md) removes
nonnegativity entirely for **isotropic 2-homogeneous**
rank-one-convex energies: each is *globally polyconvex*
because its convex signed-singular profile has affine
supports with nonnegative intercepts. This is independent
of Iwaniec 2026 and remains unformalized in Lean.
The same note fixes a determinant-arithmetic error
in Guerra–Kristensen (2022), Proposition 3.7 by
an exact 3-point minors-preserving counterexample
to polyconvexity for a **nonisotropic** rank-one
convex 2-homogeneous energy.

**Stop rule:** No claim that GL-transformed signed
p=2 isotropic polyconvex generators and their
positive/supremum closures can span *all* anisotropic
rank-one-convex p=2 integrands. The verified
nonpolyconvex example rules out that approach.
This does not refute quasiconvexity.

### Smooth coercive nonpolyconvex QC generators (22 November 2026)

The new [Iwaniec stabilization note](IWANIEC_MORREY_SMOOTH_QC.md)
gives a **four-atom exact rational minors-preserving
Jensen witness** of strict nonpolyconvexity,
gap -1/17, for the coercive, strongly rank-one-convex
\(W_{1/8}=1+L+\|A\|_F^2/8\). This survives
smooth convolution and invertible affine transformations;
quasiconvexity remains conditional on the 2026
global L theorem. This closes the **regularity/
coercivity robustness issue for this generator**,
but the four atoms are not a planar gradient law.

**Stop rule:** Smoothness, coercivity,
strict rank-one convexity, anisotropy and
nonhomogeneity of particular QC generators
do not imply a universal representation of
every rank-one-convex integrand. The
[L-cone no-go](IWANIEC_MORREY_CONE_NOGO.md)
still rules out the simple positive-cone approach.


The same construction has a **sharp scalar threshold**:
\(W_\varepsilon=1+L+\varepsilon\|A\|_F^2\)
violates lifted-minor Jensen at zero whenever
\(\varepsilon<1/4\), but for every
\(\varepsilon\ge1/4\) it satisfies
\(W_\varepsilon(A)\ge
W_\varepsilon(0)+\det A/2\) globally.
This closes its *at-zero poly-affine support*
question only; global polyconvexity is not
claimed for large ε.

### Global L-cone no-go (22 November 2026)

The [exact no-go theorem](IWANIEC_MORREY_CONE_NOGO.md)
shows that the positive cone of **all** matrix-translated
and invertible GL-transformed Iwaniec calibrators L,
augmented by **all** polyconvex functions, has a
strict, exact support-envelope gap of **1**
at a simple rank-one-convex anisotropic
2-homogeneous integrand T. The proof uses its
whole rank-one-flat line and the corrected
Guerra–Kristensen minors witness; it does not
claim T is not quasiconvex.

**Stop rule:** Do not claim that closure of
positive polyconvex plus L-generator cones
can settle unrestricted Morrey, regardless of
the number of terms, transformations or
pointwise supremum operations. The
no-go is global in this class. Any
renewed calibration program must introduce
a qualitatively new generator or abandon
global pointwise minorants; otherwise
prioritize an all-gradient Jensen proof
or an actual negative planar witness.

### A global p>2 support at ALL rank-one bases of the exact candidate

The exact p=4 candidate in
[the hybrid no-go](IWANIEC_MORREY_HYBRID_NOGO.md)
is **polyconvex at every rank-one base**, not merely
locally quasiconvex. The [global support theorem](IWANIEC_MORREY_RANKONE_SUPPORT.md)
provides an explicit determinant-affine minorant touching
at \(\operatorname{diag}(1,0)\), with a
**178+6-cell exact Bernstein/Hessian proof**
covering every real 2×2 matrix, and extends
through SO(2)×SO(2) isotropy and homogeneity.
The homogeneous-cone no-go remains valid,
but it no longer suggests this candidate
could violate QC at rank-one bases.
Do not spend further search effort on
**any amplitude** periodic gradient witnesses
at these bases.

The [separator nonrealizability theorem](IWANIEC_MORREY_SEPARATOR_NONREALIZABLE.md)
independently proves the old two-ratio
profile separator cannot meet the matrix
barycenter and determinant moments, even
before requiring gradient compatibility.
Its two exact SOS identities yield
\(\mathbb E\|A\|_{\rm op}\le59/60<1\).

### A sharper all-p nonconformal completion gate

For any differentiable isotropic positively
p-homogeneous integrand, the [one-multiplier
support criterion](IWANIEC_MORREY_GENERAL_SUPPORT_CRITERION.md)
gives a **necessary and sufficient** condition
for a global poly-affine minorant touching
at \(E_t=\operatorname{diag}(1,t)\), \(|t|<1\):
find \(c\) in the explicit orientation interval
satisfying one scalar inequality for
**every** amplitude a≥0 and signed
ratio s∈[-1,1]. For globally RC F the interval
has nonnegative width
\(2(ph(t)-2th'(t))/(1-t^2)\).
If there is no feasible c, **at most two
scalar amplitude/ratio tests** witness
failure (1D interval Helly theorem).
This is a finite *negative witness type*,
not a finite positive decision procedure.

**Main p>2 gate:** Prove a feasible c exists
for **every** nonnegative isotropic
rank-one-convex p-homogeneous integrand,
every exponent p>2, and every base t,
or construct an exact counterexample
to this *polyconvexity* claim.
The overall Morrey QC problem is still
weaker and remains open regardless
of a failed poly-affine support.

The exact p=4 support persists for an
**open C² neighborhood of profiles and
exponents near 4**, and for an
**open interval of nonconformal full-rank
base matrices**, by the strict exact
certificate and Hessian compactness.
This goes beyond the rank-one base
without inventing a finite cutoff.

**Prior-art qualification:** Wiedemann–Peter
(2026), [Theorem 1.4 and Corollary 1.5](https://doi.org/10.1007/s00526-025-03222-z),
already reduce global isotropic polyconvexity
to diagonal signed-singular variables.
The one-multiplier criterion specializes
that context; do not claim the general
diagonal reduction is new.

### Uniform local-gradient stability excludes every small perturbation

The exact p=4 candidate of the
[hybrid no-go](IWANIEC_MORREY_HYBRID_NOGO.md)
has an explicit 1/6 strict rank-one Hessian
margin at \(A_0=\operatorname{diag}(1,0)\).
A [global-frequency, local-amplitude proof](IWANIEC_MORREY_LOCAL_STABILITY.md)
gives \(J_F(A_0,\varphi)\ge
\frac1{24}\fint\|D\varphi\|_F^2\)
for **all** periodic fields whose gradients
are sufficiently small in L∞,
independent of wavelength or grid.
The same argument works uniformly on any
compact set of nonconformal nonzero bases,
using the strict acoustic positivity
from the exact rational certificate.

**Search gate:** No further small-amplitude
local test near such bases can give a
Morrey counterexample. A negative
gradient witness, if any, must be
large-amplitude/nonlinear. This is only
a stability result and does **not**
establish quasiconvexity for arbitrary
test gradients or settle Morrey.


### CLOSED: The proposed p>2 hybrid envelope is not complete

[Exact p=4 no-go theorem](IWANIEC_MORREY_HYBRID_NOGO.md)
gives an **entire globally rank-one-convex**, nonnegative isotropic
4-homogeneous F with a rational Bernstein
proof and strict rational two-point separator.
The hybrid envelope is strictly below F
at a rank-one base, with exact gap
\(356912972869/17832200896512>0\).
A standard-library rational [checker](../../research/audit/iwaniec_hybrid_no_go_exact.py)
verifies the scalar acoustic sign conditions and
the separating constants without floating point.

**Status:** the old G_p "completeness for all p>2"
gate is **refuted** already at p=4; it must not
remain an open positive target. This is NOT
a negative planar-gradient Jensen witness,
and therefore NOT a counterexample to
quasiconvexity or Morrey. The obstruction
applies to the stated generator class only,
not arbitrary quasiconvex functions.

**Reorientation:** either enlarge the
generator class in a provably useful way
or test the new exact F with actual periodic
gradient laws. Do not spend additional
effort on the false positive G_p statement.


### Exact univariate acoustic reduction of the whole smooth isotropic class

The [acoustic criterion](IWANIEC_MORREY_ACOUSTIC.md)
gives necessary-and-sufficient **rank-one convexity**
tests for every real-valued C² signed-singular profile
and every p>1, using **one scalar r∈(-1,1)**
and two endpoint conditions. Its exact algebra
is [symbolically checkable](../../research/audit/iwaniec_acoustic_exact.py).
No claim of priority over classical
Knowles–Sternberg-type conditions is made;
the global endpoint argument is still
hand-level, not Lean-checked.

**Main positive gate:** At p>2, prove that
every such admissible profile has a globally
touching minorant from the hybrid
Burkholder–polyconvex generator cone,
or produce an exact separating profile
showing the cone is incomplete. A separating
profile is only a method no-go, not a
Morrey counterexample. This is a universal
one-dimensional functional gate, **not**
a finite-mesh/fixed-degree search.


### Critical novelty and exponent correction

See [the exponent audit](IWANIEC_MORREY_EXPONENT_AUDIT.md).
The 0<p<1 case is trivial **in all matrix dimensions**:
every finite-valued globally RC p-homogeneous function vanishes.
At p=1, isotropic RC⇒convex on 2×2 is **Dacorogna (1989)**,
not a new result. Reserve novelty claims for an
independently validated all-base result at 1<p<2
or the signed p=2 conclusion. Main unclosed extensions:
signed 1<p<2, p>2 (the old hybrid-completeness
gate was refuted), or removing isotropy/homogeneity.

### Published warning: polyconvex level sets need not give polyconvex energies

Voss–Ghiba–Martin–Neff (2022)
[exhibit an isotropic RC but nonpolyconvex
integrand on GL⁺(2)](https://arxiv.org/abs/2009.09690)
with compact connected sublevel sets.
This refutes a naive function-level
inference from connected/convex
sublevels in that restricted domain.
It does **not** refute the globally
finite, nonnegative, p>2 homogeneous
Guerra–Kristensen question.
[Scope audit](IWANIEC_MORREY_LEVELSETS.md#3a-important-published-no-go-for-the-naive-cross-level-inference).
Use the **quantitative** four-atom
moment-energy inequalities, not
separate level-set inclusions, for
the remaining global proof.


### Global endpoint of finite-atom reduction: only T3/T4 remain

The [pair-merging theorem](IWANIEC_MORREY_FOUR_ATOM.md#5b-remove-all-rank-one-edges-from-a-minimal-negative-witness)
proves that **every** hypothetical
diagonal polyconvexity violation
has a minor-preserving witness
with **three or four atoms and
no rank-one-connected pair**.
Merging any rank-one-connected
pair preserves all four moments
and cannot increase the energy.
An exact four-atom unconnected
moment configuration confirms
the T4 geometry is nonempty.

This is a *completed global
structural reduction* with
uniform atom count independent
of p, profile, degree and mesh.
The remaining Jensen inequality
for the two continuous T3/T4
families is **unproved**.
Avoid branching to increasingly
large finite subclasses;
the universal functional
inequality is the next gate.


### Three-atom geometry: connected-pair class closed

In the [four-atom global theorem](IWANIEC_MORREY_FOUR_ATOM.md#5a-all-three-atom-laws-with-a-rank-one-pair-are-laminates),
**every** minors-preserving diagonal
three-atom law containing a rank-one
connected pair is a two-step laminate,
and hence obeys Jensen for every RC
integrand. This closes an infinite
geometric subclass, with no exponent
or profile restriction.
An [exact rational three-atom
example](../../research/audit/iwaniec_three_atom_geometry_exact.py)
shows the **remaining pairwise
unconnected** moment class is nonempty.
No energy inequality is solved there.
The genuinely unresolved
global diagonal-PC gates are
pairwise-unconnected three-atom
and arbitrary four-atom moment laws.


### Strict all-exponent supremal principle and power-witness limitation

The [strict global maximum principle](IWANIEC_MORREY_STRICT_SUPREMAL.md)
strengthens the published isotropic
polyconvex-sublevel conclusion:
for **every** nonnegative isotropic
positively p-homogeneous RC integrand,
any compactly supported probability
law preserving the matrix and determinant
moments whose support energies never
exceed \(F(A)>0\) must have
**all support energies equal to F(A)**.
The proof uses a full-dimensional
crosspolytope in the **five-dimensional
minors lift** at every strictly
lower-energy atom.

Consequently a strict Jensen violation
requires positive mass with energy both
**below and above** F(A). For every
**fixed** violating law, taking high
enough positive powers \(F^q\)
eventually **restores Jensen** for
that law, with an explicit q threshold
dependent on the law. There is no
uniform q across all laws: this
does **not** solve the global p≥4
PC or Morrey inequality. It rules out
a naive *single-law* extrapolation
from a putative p4 failure to all p>4.
The theorem is a hand deduction from
Conti–De Lellis–Müller–Romeo (2003),
not claimed publication-priority
or Lean-certified.


### Essential separation: three-atom PC tests versus actual gradient laws

[Three-atom rigidity audit](IWANIEC_MORREY_THREE_ATOM_RIGIDITY.md):
every homogeneous W¹∞ planar gradient
Young measure on ≤3 atoms is a
laminate. If one pair has rank-one
difference, determinant moment
compatibility gives a two-step
finite laminate; otherwise Šverák's
published three-gradient rigidity
forces the measure to be Dirac.
An exact rational example shows
three pairwise unconnected diagonal
atoms can satisfy *all minors moments*
yet fail gradient realizability.

**For the p≥4 polyconvexity target:**
Dacorogna–Koshigoe's universal test
STILL includes 3-atom laws; they may
refute PC without refuting QC.
**For Morrey:** any genuine nontrivial
finitely supported gradient law
needs ≥4 atoms. Four-atom T4
microstructures may be compatible
yet still laminates in the Jensen
sense—do not infer non-QC from
rank-two pairwise separation alone.
This prior-art theorem is a
research-route correction, not a
new proof of the universal
p≥4 or Morrey conjecture.


### Global exponent-descent obstruction: p=4 cannot simply represent p>4

The [exact all-exponent no-go](IWANIEC_MORREY_EXPONENT_DEMOTION_NOGO.md)
starts from the **globally polyconvex** isotropic
\(F_p(A)=(\det A)_+^{p/2}\) for arbitrary real p>4.
Replacing its p-homogeneity by any lower
degree q<p **without changing the signed-singular
profile** produces a function that fails rank-one
convexity along diag(1,t): the derivative
has an exact downward jump of q-p at t=1.
In particular the entire p>4 class cannot
be reduced to p=4 by multiplying by
\(\|A\|_{\rm op}^{4-p}\).

This is a *method obstruction*, NOT a
counterexample to the p>=4 polyconvexity
conjecture. A valid exponent-transfer
principle must change more than the
homogeneity prefactor, or use a
global argument independent of p.


### Exact five-variable support-obstruction query (all rational p≥4)

The [two-test interval/Helly encoding](IWANIEC_MORREY_PGE4_TWO_TEST_QE.md)
compresses failure of the Dacorogna–Koshigoe
poly-affine support at any nonconformal
base to a quantifier-free existential
real polynomial formula with just
**five real variables when p is integer,
seven when p is nonintegral rational**.
It works for polynomial profiles of
arbitrary finite degree. A local exact
nonlinear-real solver reported
UNSAT/SAT/SAT on three elementary
p=4 controls; the p=9/2 positive
control timed out. Both outcomes are
explicitly documented; no global
positive result is inferred.

**Critical premises:** To interpret an
UNSAT result as global polyconvexity
for p≥4, first verify that the input
is nonnegative and globally RC.
Conformal bases then use the published
Guerra–Kristensen theorem. For all
inputs without these premises, use
the direct four-atom QF_NRA query.
A PC failure is not an ordinary
Morrey quasiconvexity violation.


### Exact decision for EACH rational-polynomial input (not for the whole class)

[The complete input-wise QE reduction](IWANIEC_MORREY_PGE4_INSTANCE_QE.md)
encodes the full global p-homogeneous isotropic integrand
for **any specified rational p≥4 and rational
polynomial profile h of unrestricted degree**.
Three exact existential QF_NRA formulas
are SAT precisely when F fails
nonnegativity, rank-one convexity or
polyconvexity, respectively. The global
RC query uses the **defining rank-one
segment inequality**, not the smoother
acoustic shortcut; PC uses the published
1993 four-diagonal-atom equivalence.
Tarski–Seidenberg gives **complete
instance-wise decidability** with a
sound full QE/CAD engine.

**Stop rule:** No such engine was
run or is bundled. A generated
formula is NOT a certificate of
satisfiability or unsatisfiability.
This has no uniform degree or
rational-denominator cutoff and
does not decide irrational p,
arbitrary continuous h, or
nonpolyconvex quasiconvexity.
The global mathematical
\(\forall p\ge4,\forall F\) question
is still OPEN. Use this as a
candidate *validation interface*,
not as an alleged full proof.


### Uniform zero-amplitude support gap for ALL p>2

The [exact zero-amplitude theorem](IWANIEC_MORREY_PGE4_CONJUGATE.md#2a-new-zero-amplitude-is-automatically-safe-with-a-uniform-gap)
proves for **every** nonnegative
isotropic globally RC p-homogeneous
integrand with p>2, at each
nonconformal base E_t and every
orientation-admissible determinant
multiplier c,
\[
(p-1)h(t)-ct\ge (p-2)h(t)/2.
\]
Hence the a=0 support condition is
**automatic**. If h(t)>0,
every c is safe for all amplitudes
\(a\le\rho_t\) with an explicit
positive cutoff. Combined with
the previous large-amplitude cutoff
for strictly positive h, the
global scalar support problem
reduces to a compact **annulus**
\(\rho_t\le a\le R_t\),
uniformly over c in the
orientation interval.

This is a structural global
reduction (all p>2, all profiles),
not a proof that a common
support multiplier exists on
the remaining compact continuum.
No uniform all-integrand cutoff
or finite exhaustive
classification follows.


### All-p≥4 positive-proof reduction: one amplitude and explicit tail

The [Fenchel-conjugate support criterion](IWANIEC_MORREY_PGE4_CONJUGATE.md)
eliminates the second scalar variable
from the Dacorogna–Koshigoe
poly-affine support gate.
For each signed base ratio t,
a candidate determinant multiplier c
must satisfy **one scalar conjugate
inequality at every amplitude a>0**,
plus an explicit a=0 condition.
For any strictly positive profile
\(h_*=\min h>0\), **all amplitudes
a≥R are automatically safe** for
every c in the orientation interval,
with an explicit integer R determined
by h*,p,h(t),h'(t).

It also proves (without C² assumptions)
that **global PC for all strictly
positive nonnegative isotropic
p-homogeneous RC profiles, at each
fixed p≥4, implies the full
nonnegative-class theorem**:
add δ||A||_F^p and send δ→0 in the
minor-Jensen inequalities.

**Remaining gate:** Prove that the
resulting **compact continuum** of
conjugate inequalities has a common
c for every admissible profile.
This is NOT a finite list, no
uniform radius R exists across
all h by this argument, and the
proof of feasibility is OPEN.
A failed interval has a
two-amplitude dual obstruction
to **polyconvexity**, not directly
to quasiconvexity/Morrey.


### A rigorous all-p≥4 negative-certificate hierarchy (C² profiles)

The [global p≥4 semidecision theorem](IWANIEC_MORREY_PGE4_EXACT_HIERARCHY.md)
shows: **if** a nonnegative isotropic p≥4-homogeneous
rank-one-convex integrand with a C² signed-singular
profile fails global polyconvexity, **then**
a rational p≥4, a rational polynomial profile h,
and a minors-preserving rational diagonal law
on ≤4 atoms give a strict failure.
The rank-one-convexity certificate is a
**global** univariate rational Bernstein proof
over all signed ratios and all rank-one
directions. The [exact checker](../../research/audit/iwaniec_all_p_rational_cert.py)
handles rational exponents and rational-algebraic
Jensen powers. It passed strict positive
controls at p=4,9/2,5,6,10.

This hierarchy is **complete as a negative
semidecision only for the stated C² class**,
with unbounded degree, denominators, and
atom coordinates. It does NOT give a finite
positive decision procedure or a uniform
degree cutoff, and does NOT cover every
continuous/nonsmooth homogeneous RC
integrand. A negative *polyconvex* Jensen
law is not a gradient-law Morrey witness.
The old four-atom and isotropic diagonal
equivalences are Dacorogna–Koshigoe (1993)
prior art; the contribution here is a
strict regularization/rationalization
pipeline and exact checker for all p≥4.


### Global method stop rules: fractional powers and universal heatflow

The [exact fractional-power witness](IWANIEC_MORREY_FRACTIONAL_POWER_NOGO.md)
shows that raising the classical nonnegative
polyconvex quartic \(Q=s(s-2\det)\) to
\(p/4<1\) **destroys rank-one convexity**
for **every real 2<p<11/4**.
Thus downward power interpolation
from the p≥4 polyconvex quartic theorem
is NOT a general proof of all p>2.

The [exact three-wave Fourier theorem](IWANIEC_MORREY_P4_HEATFLOW_NOGO.md)
exhibits an **actual compatible smooth
periodic gradient**, with affine base, for
which the **globally polyconvex**
\(F=(\det A)^2\) has positive componentwise
heat-flow energy derivative **+920**.
The sign persists for \(F_p=|\det A|^{p/2}\)
on an open p-interval containing 4.
This supplies a short exact homogeneous
instance of the earlier H24 obstruction:
**universal heat-flow monotonicity is false
even inside the target positive isotropic
p>2 class**. It does NOT exclude specialized
flows, and is not a QC/Morrey counterexample.

**Decision:** The global G–K Question 1.7
still requires a new simultaneous
cross-level Jensen inequality or a
certified nonpolyconvex counterexample.
Do not repeat generic concave-power
interpolation or universal componentwise
heatflow as claimed positive completion
routes without a changed hypothesis.


### All-p quantitative global control, not yet an all-p proof

The [quadratic deficit theorem](IWANIEC_MORREY_GLOBAL_QUADRATIC_DEFICIT.md)
applies to EVERY finite nonnegative isotropic
rank-one-convex, positively p-homogeneous
\(F\) for **every real p≥2**, provided it
is C² near both nonzero conformal orientations.
Guerra–Kristensen's published determinant-power
polyconvex lower minorant, plus exact equality
of first derivatives at conformals, yields
\[
0\le F(A)-QF(A)\le
K_F\sigma_1(A)^{p-2}
(\sigma_1(A)-\sigma_2(A))^2
\quad\text{for all matrices }A.
\]
This is uniform over **all gradient laws,
oscillation frequencies and amplitudes**,
not a fixed-mesh bound. The rate improves
the earlier linear estimate but
**does not show zero deficit**;
the universal Jensen / full p>2 PC
question remains OPEN. It is a
straightforward quantitative consequence
of published conformal support,
not a new solution.

### Necessary quartic coefficient bounds and an entire closed sector

The [shear-bound theorem](IWANIEC_MORREY_QUARTIC_SHEAR_BOUND.md)
uses rank-one shear lines at I,D to prove
\(a\ge0,\ |b|\le4a\) for ALL invariant
quartic polynomials
\(F=a\,s^2+b\,s\,d+c\,d^2\),
and the diagonal Hessian gives the
universal necessary parabolic cutoff
\(c\ge3b^2/(8a)-2a\) for a>0.
Combining the sharp shear bound with
the previously proved positive-cone
decomposition closes **ALL** nonnegative
rank-one-convex quartics with
\(2a\le |b|\le4a\):
every one is globally PC.
Positive powers extend each to all
real p≥4.

The remaining low-coupling quartic
coefficients and all nonpolynomial
p>2 profiles are NOT classified by
these arguments; do not mistake
a coefficient-sector closure for
the unrestricted Guerra–Kristensen
question. The global QC/PC theorem
and, separately, Morrey itself
remain OPEN.


### CLASS-WIDE stop rule: positive Dacorogna–Marcellini stabilizations

An [exact quartic cone theorem](IWANIEC_MORREY_QUARTIC_STABILIZATION.md)
proves global **polyconvexity** for
\(P_{\gamma,c}(A)=s^2-2\gamma sd+c d^2\)
whenever 1≤|γ|≤2 and \(P_{\gamma,c}\ge0\)
everywhere. The nonnegativity threshold
is precisely \(c\ge4(|\gamma|-1)\),
and an explicit positive decomposition
into classical PC/convex generators
proves the conclusion. A wider
sufficient PC cone covers |γ|<1;
positive powers yield **all p≥4**.
[Exact coefficient checker](../../research/audit/iwaniec_dm_positive_stabilization_exact.py).

**Stop rule:** Never search for a
nonnegative isotropic RC/non-QC
counterexample in this **entire**
determinant-square-stabilized DM
quartic family, or its positive
powers at p≥4: every such member
is already PC. The universal
p>2 theorem, unrestricted
profiles and nonlinear forms
remain open. This is an analytic
infinite-parameter exclusion,
not a closure of the 1993
four-atom Jensen inequalities.


### PRIOR-ART CORRECTION: four atoms and supporting planes were known in 1993

[Dacorogna–Koshigoe (1993), Theorem 2.1](https://www.numdam.org/item/AFST_1993_6_2_2_163_0/), Theorem 2.1, already proves
both the **four-atom signed-diagonal Jensen equivalence** and the
**global poly-affine support equivalence** for SO(2)×SO(2)-isotropic
energies. Our rational sparsifier, one-multiplier formulas and
rank-one-pair merging are helpful explicit reformulations, but they
do NOT establish a new finite reduction. See the
[priority audit](IWANIEC_MORREY_PRIOR_ART_1993.md).

**No remaining finite-enumeration gate:** all unconnected three-/four-
atom configurations still range over continuous parameters, and the
universal Jensen inequalities remain open. Do not treat the 1993
criterion as progress towards proving the inequalities unless new
analytic control over all admissible integrands is obtained.

### GLOBAL bounded-atom reduction (all exponents, all profiles)

The new [four-atom theorem](IWANIEC_MORREY_FOUR_ATOM.md)
combines Wiedemann–Peter's published
isotropic diagonal characterization
with a four-moment extreme-point argument.
For **EVERY** finite nonnegative isotropic
RC p-homogeneous F and EVERY p>2,
F is globally polyconvex **iff** the
diagonal Jensen inequality holds for all
minor-preserving probability laws with
at most **four** atoms, at normalized
base \(E_t=\operatorname{diag}(1,t)\),
\(-1<t<1\). One- and two-atom laws
are automatically handled by RC.
Thus a negative counterexample to
the stronger polyconvexity question
is always witnessed by **three or
four** signed-diagonal atoms; a
nontrivial 3-atom law admits a
one-parameter covariance-free form.

**Crucial distinction:** This is
bounded in **atom count**, NOT a
finite degree/grid/coefficient
search. Real positions, weights,
exponents and profiles remain
arbitrary. The universal
3-/4-atom inequalities are **OPEN**.
An exact rational [cost-nonincreasing
reducer](../../research/audit/iwaniec_diagonal_four_atom.py)
checks all four moments.
A failure of the polyconvexity
inequality is **not** by itself an
actual planar-gradient Jensen gap
or a Morrey counterexample.


### Global all-exponent level-set result — closed, but weaker than Jensen

A [newly recorded all-\(p\) deduction](IWANIEC_MORREY_LEVELSETS.md)
from Conti–De Lellis–Müller–Romeo (2003) proves:
for every finite, nonnegative, SO(2)×SO(2)-isotropic,
positively homogeneous rank-one-convex integrand,
**every sublevel set is polyconvex**, without
a coercivity restriction. It yields the global
\(L^\infty\) supremal quasiconvexity inequality
at every matrix and for every bounded periodic
gradient, with arbitrary amplitude and scale.

**Critical scope warning:** The theorem concerns
the supremum of energy over a gradient field,
not the integral average. It does NOT establish
rank-one convexity⇒ordinary quasiconvexity for p>2,
and this is a direct corollary of published
set-hull theory, not a new solution.
The missing theorem is **cross-level compatibility**
of polyconvex supports or the global
one-multiplier feasibility in the signed-singular
profile representation. Do not treat
polyconvexity of all sets as polyconvexity
of the energy.


## 0. Iwaniec-dependent route (22 November 2026)

The [universal isotropic note](IWANIEC_MORREY_UNIVERSAL.md) proposes
an all-matrix RC→QC proof for every nonnegative isotropic p-homogeneous
2×2 integrand with 1<p<2 (conditional on the global 2026 Burkholder
quasiconvexity result), and an unconditional hand argument for p=2.
The new [hybrid hierarchy](IWANIEC_MORREY_GENERAL.md) gives an explicit
all-matrix quasiconvex minorant and a one-dimensional cone-completeness
gate for **every p>2**, plus GL-transformed anisotropic and
nonhomogeneous positive closures. Neither route settles arbitrary
2×2 integrands.

**Gate I8 CLOSED (negative):** The universal identity `E_p h=h` is **false**, by the [exact p=4 no-go](IWANIEC_MORREY_HYBRID_NOGO.md), and its failure persists on an [open family of profiles/exponents](IWANIEC_MORREY_HYBRID_OPEN.md). Do not try to establish this invalid positive completeness target. The unrestricted Morrey gate requires a genuinely stronger certificate family, an all-gradient inequality, or an actual planar negative witness.

The new research contains no Lean translation or independent
validation of Iwaniec's full proof. This Iwaniec-dependent route
must remain separate from the unrestricted negative-witness
search described below.

## 1. What counts as completion

| Route | Required mathematical output | Final formal output |
| --- | --- | --- |
| Positive | For every finite-valued rank-one-convex `f : ℝ²ˣ² → ℝ`, every base `F`, and every admissible planar test map `u`, prove `average f(F + Du) ≥ f(F)`. | A proof of `Pedregal.Theorem1_1_part2` or `Pedregal.Theorem1_2`, with an explicit bridge from any alternative definitions. |
| Negative | Exhibit a continuous finite-valued `f : ℝ²ˣ² → ℝ`, prove rank-one convexity globally, and give an actual planar gradient witness with a certified strict negative gap. | A planar theorem asserting continuity, rank-one convexity and failure of quasiconvexity in one of the project's definitions, with the needed bridges. |

The all-level **finite-order** laminate statement is sufficient for the positive route and is
stronger than the Jensen property actually needed. Abandoning that stronger statement is allowed.
Showing that a prescribed finite tree fails is not evidence that its gradient law violates Jensen.

## 2. Immediate priorities after the audit

The [22 November formalization audit](MAIN_FORMALIZATION_AUDIT.md) adds universal finite-laminate
Jensen, exact planar definition bridges, the dimension-general C² LH equivalence and an actual
periodic-gap acceptance theorem. Their Lean validation is recorded in that audit. These close
interfaces; they do not supply the open universal Jensen theorem or a negative candidate.
The remaining formal tasks are the exact polynomial-certificate evaluator and the periodic PL
gradient-sum-to-integral identity; the positive route additionally needs controlled dyadic
approximation. Do not treat numerical certificate checking as if it already instantiated the
Lean acceptance theorem.

Start with [COMPLETION_AUDIT.md](COMPLETION_AUDIT.md), the new exact interfaces in
[research/audit](../../research/audit/README.md), and the current [formal baseline](FORMAL_STATUS.md).
The source inventory and exact controls have been checked; repeat them after relevant changes,
not as a substitute for advancing the unresolved construction.

| Priority | Deliverable | Acceptance / stop rule |
| --- | --- | --- |
| 1 | Integrate range-sensitive base recovery and boundary Gram handling into a new discovery driver. | Use the exact quadratic diagnostic on reconstructed rational candidates. Monitor discarded linear components during floating exploration; do not silently discard tiny positive curvature. Permit singular certificates or a justified vanishing-margin schedule. |
| 2 | Add weighted-Gram discovery and rational certificate extraction, using the existing norm-basis builder and verifier. | Produce a coefficient identity with exact nonnegative square weights/PSD proof. Test the same actual-gradient inputs at orders zero and one with a recorded finite budget; do not interpret a null result as class exclusion. |
| 3 | If weighted discovery is impractical, try strict local-ball LH discovery with the explicit global radial tail. | Certify the ball, a buffer around every witness gradient, the tail bound and a surviving negative gap. Merely local RC is insufficient. |
| 4 | Independently evaluate and formalize any strict negative candidate immediately. | Same rational integrand, exact global LH certificate, actual planar test map and a strict negative integral. Reuse the existing periodic Lipschitz/domain equivalences. |
| 5 | On the positive route, prove universal exact Hessian-certificate feasibility or an equivalent all-gradient inequality. | All degrees and all admissible fields are covered. The radial-moment lemma supplies the subsequent compactness; isolated certificates are insufficient. |

The current package implements **verification**, basis enumeration and exact base diagnostics.
It does not implement a weighted-Gram solver, automatic rational extraction or an exhaustive
search. Those are concrete next engineering tasks, not completed capabilities.

There is no justified completion date or finite degree/grid/order cutoff. A bounded search can
end; the unrestricted mathematical question remains open if it finds nothing. The P₂ all-field
inequality in [STRUCTURAL_AUDIT.md](STRUCTURAL_AUDIT.md) is a useful subordinate benchmark with
a meaningful analytic endpoint. It must not displace the unrestricted goal.

## 3. Negative route: candidate to theorem

### N1 — Search in a class with a global certificate route

The polynomial/dyadic reduction H07 and the new [norm-multiplier proof](GLOBAL_CERTIFICATES.md)
give a complete negative-witness certificate hierarchy after a strict radial perturbation.
Enumerating polynomial degree, mesh, rational heights and multiplier order can detect a
counterexample if one exists. No finite bound or positive termination is supplied. A fixed
unweighted SOS class or a fixed positive Gram floor is still restrictive.

For degree at most `2m`, the exact format is
`(Nx Na Nb)^k [F_P − δ Nx^(m−1)NaNb] = Σ q_j²`, with rational `δ>0` and the homogenized LH
form `F_P`. The [verifier](../../research/audit/sphere_certificate.py) already checks this
identity and actual rational periodic PL witnesses. A strict local-on-ball certificate plus
the explicit radial extension is another valid discovery route.

Each finite campaign must state which certificate freedom changes, its actual-gradient
parameterization, artificial margins/penalties and budget. Remove permanent covariance
exclusions and let artificial margins decrease in any completeness claim. Alternating
optimization remains local even when every SDP subproblem is solved correctly.

**Exit:** save explicit integrand coefficients, base matrix, domain, actual nodal/Fourier map,
normalization and a strict negative candidate gap. A raw measure with the correct mean and
determinant moment does not meet this gate. Neither does the `3 × 2` positive control.

### N2 — Certify rank-one convexity everywhere

For a polynomial `P`, verify
`D²P(A)[a ⊗ n, a ⊗ n] ≥ 0` for every real `A, a, n`, then supply the elementary bridge from the
Hessian inequality to convexity along rank-one lines. Options include an exact rational Gram
identity with exact PSD factorization, a rigorous analytic inequality or real-algebraic
certification. If a floating SDP is rationalized, recheck every coefficient and positivity
condition after rationalization.

**Exit:** a standalone replayable certificate and its mathematical interpretation. Finite
curvature sampling, small identity residuals, approximate positive eigenvalues or solver
`optimal` status do not suffice. Failure of one SOS relaxation does not prove failure of RC.

### N3 — Certify the actual integral and admissibility

For periodic piecewise affine maps, use the exact triangle gradients and area weights; for
Fourier maps, use exact moments or interval quadrature with an explicit error bound. Independently
check gradient compatibility, mean gradient zero and the determinant identity. These identities
are necessary checks, not a substitute for constructing the map.

**Exit:** `J ≤ −ε` for an explicit positive rational `ε`, or an interval upper endpoint below
zero, after every approximation and rounding error is included. Save a second evaluator that
does not reuse the discovery code's derivative assembly.

The source now contains the general **periodic Lipschitz** equivalence
[External.Rindler.quasiconvexAtOn_iff_periodic](../../Morrey/Common/External/Rindler/Lemmas.lean),
and the bounded-open-domain equivalence in the same file. For a polynomial FE candidate,
instantiate lower semicontinuity/local boundedness, the actual periodic Lipschitz map and its
integral; a new general smoothing/cutoff proof is unnecessary. The older smooth witness lemma
[Sverak.lemma1_witness](../../Morrey/Sverak/Lemma1.lean) remains an alternative when an explicit
smooth compactly supported witness is wanted.

### N4 — Formalize and independently review the final statement

Translate the candidate, exact certificate and witness into Lean, including integrability and
the chosen definition of quasiconvexity. Use the existing Cassese–Šverák bridges where their
hypotheses fit; add the missing Pedregal bridge if that is the final interface.

**Exit:** the final planar theorem is proved, its definition matches the intended question,
`lake build` and the axiom audit pass, applicable route/Comparator checks pass, and an independent
review checks both the mathematical argument and the statement. A build that leaves the main
claim as `def ... : Prop` is not completion.

## 4. Positive route: the missing all-scale argument

### P1 — Select a sufficient global target

Choose an all-gradient Jensen inequality, a suitably controlled limiting laminate construction,
or the stronger all-level finite-order statement. Another sufficient target is: for every
compact actual planar gradient law and every degree `d`, construct an exact positive
rank-one-Hessian representation of its Jensen functional on polynomials of degree at most `d`.
State the quantifiers over bases, integrands, maps and degrees explicitly.

The [radial-moment theorem](GLOBAL_CERTIFICATES.md#4-correct-compactness-theorem-for-positive-certificates)
shows that these finite-degree positive measures need **no additional inter-degree consistency
or common support assumption**. Fixed mass and radial moments supply tightness, tail control
and a limit supported in the convex hull of the law. For arbitrary approximate certificates,
quantitative error and moment control would still be needed.

**Exit:** a precise universal feasibility theorem and its implication to the planar Morrey
statement. The conic-duality reductions H10–H11 and compactness theorem A04 do not construct
the positive measures; existence remains P2.

### P2 — Prove the central global existence or inequality

This is the unresolved mathematical core. Pedregal's map has empty values; another fixed-point
theorem cannot supply a missing hypothesis. A replacement map needs its own existence,
positivity, compatibility and compactness proof. Freeing weights changes the algebra and may
remove convexity, so it cannot be treated as a routine repair.

**Exit:** a proof applying to all admissible planar inputs. An all-quartic result, if obtained,
would be a major intermediate theorem, but would still require an all-degree/general-integrand
bridge. One fixed mesh, one open set of gradient laws or finitely many positive moment
certificates does not close this gate.

### P3 — Complete the analytic reduction in the appropriate definitions

For a laminate approach, prove Jensen for the project's `IsLaminate`, translation by a base
matrix, controlled dyadic interpolation of periodic maps and energy convergence. Reuse the
already available finite-valued RC local Lipschitz theorem and periodic Lipschitz/domain
bridges (F13–F14). A weak-limit/Hessian-measure approach instead assembles its limiting Jensen
theorem and the regularization/definition bridges it needs. The remaining work is integration
with the chosen universal hypothesis, not a new proof of every general analytic lemma.

**Exit:** a formal implication from the selected universal hypothesis to
`Pedregal.Theorem1_1_part2`. This work can proceed independently; it must continue to display
P2 as an assumption until P2 is actually proved.

### P4 — Independent review and formal closure

Check the universal quantifiers, zero-weight/boundary cases, and all compactness/positivity
arguments. Then implement the core proof and run the project's formal validation. No assertion
in an auxiliary file or imported axiom may stand in for the central theorem.

## 5. Useful side deliverables, with separate completion criteria

| Deliverable | What would complete it | Why it does not complete Morrey |
| --- | --- | --- |
| Pedregal-method note | Expose the existing formal counterexample and clearly identify the exact false premise; independently review the paper correspondence. | Refutes this argument, not its conclusion. No all-mold theorem is needed. |
| Universal level-one mold | Port the exact 48 leaf tags to `Pedregal.TriMold 1` and check all constraints in Lean. | Corrects the false B/B₁ conjectures; remains level one. |
| Uniform-weight obstruction at higher levels | Formalize the finite determinant/translation reduction and the refinement step. | Excludes uniform weights for certain data; does not exclude nonuniform fixed points. |
| Structural quartic lemmas | Independently audit and formalize the flat-line, rank-one-null, orbit and cone arguments, preserving hypotheses. | Gives subclasses or obstructions, without classifying all RC integrands. |
| Reuse Cassese infrastructure | Instantiate the current main-branch regularity, periodic/domain, polynomial and minor tools in the final planar construction. Preserve the named hypotheses of conditional nonplanar results. | Cassese's quartic is now formalized in `2 × 3`; it does not restrict automatically to a planar counterexample. |

## 6. Routes that require a new hypothesis before reopening

| Prior route | Present disposition | What would justify reopening |
| --- | --- | --- |
| Universal nonemptiness of Pedregal's original map | Refuted in Lean. | A changed construction with all needed hypotheses proved. |
| No fixed point for any level-one mold (B/B₁) | Refuted by the universal mold S*. | A genuinely different quantifier/level claim, stated explicitly. |
| Universal componentwise heat-flow energy decrease | Explicit failure even for a strongly RC polyconvex integrand. | A restricted class or different flow with a new sign argument. |
| Automatic spatial-averaging-to-laminate inference | Explicit split of rank two. | An adaptive construction with proved rank-one increments. |
| Linear span of known quartics implies positive-cone generation | Invalid inference; later cone obstruction is stronger. | A new positive decomposition theorem with valid coefficients. |
| Nonpolyconvexity plus compatible minors produces a gradient witness | False; explicit moment witnesses show the gap. | A realization theorem or an actual compatible map. |
| Quadratic bivector-norm affine planar pullbacks | Hand argument makes this class polyconvex. | A construction outside the stated form, or a flaw found in that argument. |
| Pure curvature sampling as a certificate | Earlier negative candidates failed exact LH tests. | A global exact/interval certificate. |
| Fixed positive Gram margin as an exhaustive SOS search | P₂ has exact LH-SOS but zero curvature at a nonzero feature vector. | Boundary-capable certificates or a justified margin schedule; no fixed-margin completeness claim. |
| More unstructured starts in the same quartic wells | Latest trials found flat/determinant-square/zero-integrand degeneracies. | Changed variables, geometry, objective or certificate class, with an explicit budget. |

The authoritative result and evidence for each disposition are in [LEDGER.md](LEDGER.md).
Keep this table updated when a hypothesis changes; preserve the previous rejection record.
