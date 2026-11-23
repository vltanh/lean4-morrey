# Roadmap to completion

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
