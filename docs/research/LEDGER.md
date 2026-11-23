# Research ledger

**Research snapshot: 21–22 November 2026. No proof or counterexample to the unrestricted planar Morrey problem has been obtained.**

This is the current interpretation of all recovered research, including failed routes and later
corrections. Entries F01–F15 describe the existing formal source, H01–H29 the earlier investigations,
E01–E08 the saved search, A01–A06 the completion audit, and R01 a calculation reconstructed from the prior discussion. See the
[roadmap](ROADMAP.md) for completion gates and [evidence definitions](README.md#reading-the-evidence).
A hand proof plus a symbolic checker is not a Lean theorem. Prior-art status is recorded in
[SOURCES.md](SOURCES.md); no new-priority claim is made by this consolidation.

The sign convention is `J_f(F,u) = average f(F + Du) − f(F)`. A valid counterexample must have
`J < 0` for an actual admissible **two-component, two-variable** gradient and the same globally
rank-one-convex integrand. The original notes are retained byte-for-byte and may use other
signs, old paths, tentative claims or stronger headings.

## Formal baseline

The full formal-status table, precise current paths and symbols are in
[FORMAL_STATUS.md](FORMAL_STATUS.md). The inspected upstream commit is
`cde348ba320b65d902c9f0f782f392e932ba507c`. Source inspection is distinct from a fresh build;
this PR does not claim to have recompiled Lean or rerun the axiom audit/Comparator.

| IDs | What is available | Current verdict and scope |
| --- | --- | --- |
| F01–F03 | Pedregal Proposition 7.1, Corollary 7.2 and both Step 2 summaries are refuted. | Lean proof bodies in [Counterexample.lean](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean). E13 uses directions `(2,0)` and `(*,4)`, whose determinant is 8. |
| F04, F06–F08 | Fixed point implies laminate; Kakutani conditional reduction; compactness, convexity, closed graph and upper semicontinuity; splitting-tree library. | Valid infrastructure. The nonemptiness premise needed by [Reduction.lean](../../Morrey/Pedregal/Reduction.lean) is false in general. |
| F05 | Every level-one gradient law is a finite-order laminate by the eight-vertex construction. | [LevelOne.lean](../../Morrey/Pedregal/LevelOne.lean); this does not establish higher levels. |
| F09 | All-level finite-order lamination and the two main planar RC/QC statements. | **Open:** [Introduction.lean](../../Morrey/Pedregal/Introduction.lean) defines propositions; it does not prove them. |
| F10–F11 | Šverák's `3 × 2` theorem and a general smooth periodic-to-compact-support witness lemma. | Already in Lean source; the boundary lemma is reusable for a future planar witness. |
| F12 | Cassese's `2 × 3` quartic, nearby exponents, all-`p>1` higher-dimensional theorem and the nonplanar landscape. | Now in main. The exact unconditional/conditional distinctions are recorded in [FORMAL_STATUS.md](FORMAL_STATUS.md). |
| F13–F15 | RC local Lipschitz regularity, periodic Lipschitz/domain equivalences and the degree-at-most-three quasiconvexity theorem. | Reusable Lean infrastructure added by the Cassese merge; these are no longer missing completion gates. |

The detailed paper audit, including E1–E18, proof-route differences and prior literature, remains
in [docs/Pedregal/REPORT.md](../Pedregal/REPORT.md). Its fixed-`u,v` closed-graph theorem is not
already a formal proof of joint closedness in `(u,v,t,r)` or an algebraic genericity theorem.

## Fixed-point and lamination investigations

| ID | Exact statement / finding | Evidence and scope | Current disposition |
| --- | --- | --- | --- |
| H01 | A level-one tri-dyadic mold `S*` admits the uniform weights as a fixed point for **every** pair in `P₁²`. | Hand construction and exact rational/combinatorial checker; not connected to the repository's Lean mold definitions. [Note](../../research/archive/files/morrey_l1_mold_counterexample.md), [checker](../../research/archive/files/morrey_l1_mold_certificate.py). | **Refutes research conjectures B and B₁ as originally quantified over every mold.** Does not repair Pedregal's universal nonemptiness claim. |
| H02 | At level two the displayed integer nodal pair has nonzero determinant between the midpoint matrices of every two distinct physical interfaces. | Exact integer check of all `1128` pairs; minimum absolute scaled determinant `7`. [Note](../../research/archive/files/morrey_level2_repair_status.md), [checker](../../research/archive/files/morrey_level2_uniform_fixedpoint_obstruction.py). | Rules out the **uniform candidate fixed point**, for every mold, for this pair. Does not rule out nonuniform fixed points. |
| H03 | For the same pair, no mold has a fixed point whose first-level relative weights all satisfy `\|α−1/2\| ≤ 1/8192`. | Exact `4512` corner-sign checks plus separate affinity of each two-interface determinant. Same note/checker as H02. | A concrete forbidden neighborhood of weights. It is not a global no-fixed-point result. |
| H04 | For every dyadic `l ≥ 2`, a nonempty Zariski-open set of nodal pairs defeats the uniform fixed-point candidate for every mold. | Finite-stencil reduction: `84` overlapping local cases, `1128` exceptional `n=4` pairs; symmetry reduces these to `42+75=117` checks. All-level argument is in the hand proof. [Checker](../../research/archive/files/morrey_all_levels_uniform_obstruction.py). | A global-in-level obstruction to **uniform weights**, not to adaptive weights. |
| H05 | For generic pairs at every `l ≥ 2`, no equal-mass binary lamination tree can use each distinct triangle-gradient atom exactly once. | Hand lowest-subtree argument and exact stencil checks. For the explicit level-two pair, `448` non-interface singleton pairs, `1440` pair-plus-singleton cases, and `1032` disjoint pair-pair cases fail compatibility. Same sources as H02/H04. | Rules out **single-use** trees. Repeated atoms with split masses remain permitted; finite-order lamination and weak-* laminate approximation are unresolved. |
| H06 | Original conjecture A: the `(u,v,t)` with nonempty `T(t)` lie in a proper algebraic subset, for each mold. | Only the user's historical numerical investigations and proposed maximal-minor strategy; no recovered proof. Dimension counts alone do not establish independent equations or the projection claim. | **Open in this work.** H01 does not refute A because its uniform `t` can belong to an exceptional algebraic slice. |

H01 is an important reversal of the initial roadmap. On the cube of level-one gradients `±C₁±C₂±C₃`, each sub-mold first averages interfaces in two coordinate directions, then equal means, then opposite means. Every merge direction is zero or a multiple of one `Cᵢ`. Each physical interface occurs twice and each triangle six times, so uniform leaf weight `1/48` obeys the required constraints. Taking `a₁=(1,0), a₂=(0,1), a₃=(1,1)` gives `q=(1,1,1)`, disproving B₁'s proposed necessary condition. The exact checker tests the abstract coefficient construction for arbitrary `Cᵢ`; a Lean bridge to `TriMold 1` is still needed. The archived note's suggested type name `TriDyadicMold 1` is historical, not the current repository identifier.

The genericity in H04/H05 is **for each level separately**. It does not assert a uniform quantitative neighborhood across all levels or a single fixed pair simultaneously satisfying every level's nodal conditions.

## Global reductions

| ID | Statement / finding | Evidence | Remaining gate |
| --- | --- | --- | --- |
| H07 | Failure of Morrey can be witnessed by a globally rank-one-convex rational polynomial, rational base, and rational nodal data on some dyadic periodic mesh. | Hand density/reduction proof: mollify, add a strict quadratic margin, approximate in `C²` on a ball, stabilize outside using a high-degree positive radial polynomial, and approximate the test map by dyadic interpolation. [Note](../../research/archive/files/morrey_polynomial_reduction.md). | Audit/formalize the analytic lemmas and periodic/zero-boundary passage. **No uniform degree or mesh bound**; not a finite positive decision procedure. |
| H08 | A globally rank-one-convex planar polynomial of degree at most three has zero cubic part; the quadratic remainder is quasiconvex. | Historical hand proof and [exact cubic checker](../../research/archive/files/morrey_cubic_rigidity.py); the degree-at-most-three quasiconvexity result is now also in Lean source (F15). | Known/folklore, not a new solution or novelty claim. |
| H09 | Rational SOS identities for the Legendre–Hadamard polynomial supply sound sufficient global rank-one-convexity certificates; rational PL Jensen gaps can be evaluated exactly. | [Checker](../../research/archive/files/morrey_polynomial_certificate.py). Checks zero mean gradient and determinant. | SOS is **not asserted complete**. A search must still produce a globally certified integrand and strict negative actual-gradient gap. |
| H10 | Jensen positivity on continuous rank-one-convex functions on a compact ball is equivalent to membership in the weak-* closed cone generated by rank-one splitting defects. | Hahn–Banach/bipolar hand argument; local-to-global extension uses H07's stabilization. [Note](../../research/archive/files/morrey_global_reorientation.md). | The universal inclusion for all gradient laws is exactly the missing problem. Cone reformulation is not a construction or a proof of feasibility. |
| H11 | At degree `d≥2` and a closed ball `K` with nonempty interior, Jensen positivity for **all polynomials with LH ≥ 0 on K** is equivalent to a positive rank-one Hessian quadrature with at most `binomial(d+4,4)−6` atoms. | Finite-dimensional conic separation and Carathéodory. Kernel is affine functions plus determinant, dimension six. [Note](../../research/archive/files/morrey_global_certificate_research.md), [kernel checker](../../research/archive/files/morrey_rankone_kernel_exact_check.py). | **Not** the same fixed-degree cone as globally rank-one-convex polynomials. Extending a local polynomial can increase its degree. All-degree feasibility for every gradient law remains missing. |
| H12 | Exact positive Hessian representations for every degree imply one compactly supported all-test-function representation, even when finite-degree measures are chosen independently. | **Strengthened by A04:** quadratic tests fix mass; higher radial moments give tightness, support localization and convergence. [Complete hand argument](GLOBAL_CERTIFICATES.md#4-correct-compactness-theorem-for-positive-certificates). | The earlier separate compatibility/support requirement was unnecessary. Universal exact feasibility remains unproved; arbitrary floating residuals do not suffice. |

H07 is a completeness statement **for negative witnesses in principle**. Real quantifier elimination can decide the polynomial's global LH formula, while finite rational gradient sums give the sign exactly. Neither the analytic reduction nor decidability supplies an efficient enumeration, a degree bound, or a terminating proof of a positive answer. The notation `P_l(Q)` in the historical note means rational vertex data, not a continuous nonconstant map with values in the disconnected space `Q²`.

H09's old quadratic sanity test prints `−405772` for `|A|²+5 det A` because it computes `f(F)−average f(F+Dw)`. Under the ledger convention this is **`J=+405772`**, correctly satisfying quasiconvexity. Its deliberately non-rank-one-convex negative quadratic is a rejected control, not a candidate.

## Positive certificates and their limitations

| ID | Statement / finding | Evidence | Scope |
| --- | --- | --- | --- |
| H13 | One explicit level-two, 32-atom gradient law satisfies Jensen for **every globally rank-one-convex homogeneous quartic**, at base zero. | Exact 35-term positive rational Hessian identity, checked coefficient-by-coefficient. [Data](../../research/archive/files/morrey_quartic_l2_dual_certificate.json), [independent verifier](../../research/archive/files/morrey_verify_quartic_l2_certificate.py), [short note](../../research/archive/files/morrey_quartic_l2_readme.md). | One law/full 35-coefficient homogeneous quartic class. Does not cover all laws, nonhomogeneous quartics, or higher degrees. Gradients in the certificate are physical gradients divided by four. |
| H14 | H13 persists for a specified joint neighborhood of nodal data and base matrix, radius `2⁻²¹` in the stated scaled convention. | Exact inverse matrix and conservative quartic moment bounds. [Script](../../research/archive/files/morrey_quartic_open_neighborhood.py), [bounds](../../research/archive/files/morrey_quartic_open_neighborhood.json). | Open family around the one certificate, not every level-two datum. Physical base entries `<2⁻²¹` give a conservative sufficient condition. |
| H15 | Sixteen sampled gradient laws on grids `4,8,16` admitted numerical positive Hessian representations for all degree-≤4 coefficient coordinates. | LPs sampling `9000` Hessian evaluations; `64` active atoms; reported residuals `<7e−14`. [Script](../../research/archive/files/morrey_quartic_global_probe.py), historical log in archive. | Floating-point evidence only; no universal theorem or exact certificates for these 16 laws. |
| H16 | `W_t=s²+4t s q+(6t²−2)q²`, `\|t\|≤1`, and its invertible left/right transforms generate a quasiconvex subcone; 35 explicit unimodular transforms at `t=1/2` are a linear basis of all homogeneous quartics. | External Bruno–Pasqualotto theorem plus exact basis certificate (`det C ≡41797 mod104729`). [Note](../../research/archive/files/morrey_global_quartic_orbit_note.md), [basis data](../../research/archive/files/morrey_quartic_gl_basis_unimodular.json), [verifier](../../research/archive/files/morrey_verify_quartic_orbit_basis.py). | **Linear span is not a positive cone.** The later hand argument H23 rules out the proposed cone equality; its analytic steps were rechecked in A06 and still require independent human review before a publication claim. |
| H17 | Split-Laplacian decomposition of homogeneous quartics into dimensions `25+9+1`; full orbit span has dimension `26` at `t=0`, `34` at `t=±1/3`, and `35` otherwise. | Hand equivariant decomposition plus exact polynomial identities and H16's basis certificate. [Verifier](../../research/archive/files/morrey_quartic_harmonic_verifier.py). | Linear representation theory, not Jensen positivity for arbitrary coefficients. |
| H18 | An explicit degree-≤4 coefficient neighborhood around `Q=\|A\|⁴−(9/4)\|A\|²det A+\|A\|²/256` is globally quasiconvex and nonpolyconvex. | Hand quantitative stability proof using the **external** Bruno–Pasqualotto endpoint theorem. Perturbation coefficient ℓ¹ norm ≤`1/4096`, coercive gap coefficient `1/512`; four-atom nonpolyconvexity witness. [Note](../../research/archive/files/morrey_global_quartic_open_ball.md), [rational check](../../research/archive/files/morrey_global_quartic_open_ball_verify.py). | A neighborhood of a known energy, not the whole quartic cone. The displayed bounded coefficient set is not itself a cone despite the archived title. |

The initial differentiation bug noted in the H13 discovery workflow was corrected before the archived exact certificate. The certificate's independent rational checker, not the discovery LP, carries its finite algebraic evidence.

## Structural subclasses and obstructions

| ID | Statement / finding | Evidence and analytic dependencies | Limitation / next use |
| --- | --- | --- | --- |
| H19 | If a global `C²` rank-one-convex function is affine on an **entire** rank-one line through `F`, it has a global determinant-affine support at `F`: `f(F+X)≥f(F)+Df(F):X+c det X`. | Hand separate-convexity/Hessian-normality proof. [Note](../../research/archive/files/morrey_flat_rankone_support.md), [algebra checker](../../research/archive/files/morrey_rankone_zero_global_check.py). | Quasiconvexity at points on that flat line only; no conclusion for functions with no such line. Not Lean-certified or novelty-cleared. |
| H20 | A homogeneous globally RC polynomial vanishing on the whole determinant-zero cone is zero, `c det` with real `c`, or `c det^(2k)` with `c>0` and integer `k≥1`. The ray `(det A)²` is exposed in the full homogeneous RC quartic cone. | Hand divisibility/convex-line limiting proof valid in all degrees, plus finite algebra checks. [Note](../../research/archive/files/morrey_rankone_null_rigidity.md), [checker](../../research/archive/files/morrey_rankone_null_rigidity.py). | Classifies a restrictive boundary class. Inhomogeneous extension in the note constrains only the **top homogeneous term**, not the entire polynomial. |
| H21 | A global `C²` RC function zero on every singular matrix has a single global support `f(A)≥c det A` and is quasiconvex at every singular base. | Hand normal-derivative argument using connectedness of the nonzero rank-one locus. [Note](../../research/archive/files/morrey_singular_base_support.md), [check](../../research/archive/files/morrey_singular_base_support_check.py). | Does not prove quasiconvexity at full-rank bases. |
| H22 | A globally RC homogeneous quartic with one nonzero rank-one zero is nonnegative and a sum of at most four squares of homogeneous quadratics. | Hand normal form `α(ad)²+(ad)T₂+S₄`, square completion, **Hilbert's ternary-quartic theorem**. [Note](../../research/archive/files/morrey_rankone_zero_sos.md), [algebra](../../research/archive/files/morrey_rankone_zero_sos.py). | Jensen at zero follows; nonnegativity/SOS does not establish quasiconvexity at every base or polyconvexity. |
| H23 | For every `β≥2`, `P_β=(ad−2bc)²+β(b²+c²+d²)²` is nonpolyconvex and lies outside the coefficientwise closed cone generated by polyconvex quartics and all `W_t(LAR)`, `\|t\|≤1`. | [Historical hand proof](../../research/archive/files/morrey_quartic_cone_no_go.md) stated `β≥5/2`; A06 checks that E01/A02 extend it to `β≥2`. [Exact historical identities](../../research/archive/files/morrey_rankone_zero_nonpolyconvex_verify.py). | Closes this proposed generator-cone route. It does not prove non-quasiconvexity and is not Lean-certified. |
| H24 | Universal componentwise heat-flow energy monotonicity fails even for strongly RC polyconvex `f_η=(det A)²+η\|A\|²`. | Explicit periodic map gives energy derivative `20s⁴−336ηs²>0` when `s²>84η/5`; hand calculation and symbolic verification. [Note](../../research/archive/files/morrey_global_reorientation.md), [checker](../../research/archive/files/morrey_heatflow_no_go.py). | Rules out that **specific universal monotonicity claim**, not all evolution/correction arguments, and not quasiconvexity. |
| H25 | Every affine planar pullback of a quadratic-bivector norm `G(X)=sqrt(Q(row₁X∧row₂X))`, with `Q≥0` on decomposable bivectors, is polyconvex. | Hand proof: row span ≤4; Finsler–Thorpe / equality S-lemma supplies PSD extension modulo the Plücker form; wedge depends affinely on `(A,det A)`. [Note](../../research/archive/files/morrey_counterexample_reorientation.md). | Blocks all embeddings/bases of this Grabovsky-type pullback family. Does **not** apply to Cassese's quartic or arbitrary higher-dimensional integrands. A06 verifies the primary Finsler–Thorpe input and its Bianchi-component bridge. Fifteen numerical Gram tests alone do not prove it. |
| H26 | Mean and determinant moments do not characterize gradient Young measures or guarantee Jensen for RC functions. | Exact four-atom measure with mean zero and mean determinant zero gives `J=−2/325` for `\|A\|⁴−(9/4)\|A\|²det A`; H18's known quasiconvexity rules out gradient realizability. H23 has a different three-atom witness with `J=−156317/59319`. | These are **nonpolyconvexity / nongradient-law witnesses**, not Morrey counterexamples. Actual gradient compatibility is indispensable. |

### Failed numerical candidates and superseded workflows

| ID | Attempt | Correct verdict |
| --- | --- | --- |
| H27 | Negative quartic Jensen values after imposing RC only at sampled points/directions. | Historically rejected using the reported rational LH value `−1205820883/1250000000` at `A=(3/5,0;0,4/5)`, `H=(-1,-2;3,6)`. The [checker](../../research/archive/files/morrey_false_quartic_exact_witness.py) requires `morrey_four_wave_exchange_last.npz`, which was not recovered; this value was not replayed here. Four-wave exchange/curvature searches are exploratory, not global certificates. |
| H28 | Earlier direct Cassese planar-pullback and Grabovsky-family searches. | No valid negative witness. Latest search bundle supersedes numerical coverage and validation; H25 excludes the specified Grabovsky route analytically. Older logs are historical evidence, not current acceptance tests. |
| H29 | Original numerical survey suggested no nondegenerate level-one fixed points for all molds. | Superseded by H01's explicit universal mold. Local minima, random molds and equation counts cannot establish universal absence. Preserve the initial conjecture as **refuted**, not as an open roadmap item. |

## Latest exact results and counterexample searches

The complete methods, normalizations, attained values and exclusions are in
[EXPERIMENTS.md](EXPERIMENTS.md). Counts of alternating steps must not be read as independent
restarts. Different families use different normalizations, so their gap magnitudes are not
directly comparable. All four search families produced **no validated planar counterexample**.

| ID | Result / campaign | Evidence and current verdict |
| --- | --- | --- |
| E01 | Sharp boundary for `Pβ=(ad−2bc)²+β(b²+c²+d²)²`: global RC exactly for `β≥2`. | Exact algebra plus a square-completion/Sylvester/continuity hand argument; [checker](../../research/experiments/2026-11-21/work_pb/beta2_certificate.py). Strengthens H23's earlier sufficient bound `5/2`. Novelty is unestablished; quasiconvexity is unresolved here. |
| E02 | `P₂`: 190 Fourier/finite-element/targeted starts, with all base entries eliminated by a cutoff pseudoinverse (see A01). | Lowest recorded values near `J=2` under the transverse normalization. Ten difficult cases checked at 60 digits. No negative gap; the apparent floor is **not** a theorem. [Report](../../research/experiments/2026-11-21/work_pb/README.md). |
| E03 | Dacorogna–Haeberly anisotropic degree-one energies: 472 FE runs, including 424 avoiding rank-one-base degeneracy. | All attained admissible gaps nonnegative; some iteration limits. Published RC criteria and parameter checks, not a claim of global numerical minimization. [Report](../../research/experiments/2026-11-21/work_lit/README.md). |
| E04 | Cassese inherited planar pullbacks: 84 runs; altered planar penalties: 80+96 alternating steps. | No valid negative gap. Inherited family independently reevaluated; altered penalties require their own RC certificates. Some Grams fail PSD screening; zero-integrand cases excluded. [Report](../../research/experiments/2026-11-21/work_cassese/README.md). |
| E05 | Exact degeneracies in a planar Cassese penalty family: `q+L²/4−LP+3P²/4=0` and `−q−LP/2+3P²/2=4(det A)²`. | [Symbolic checker](../../research/experiments/2026-11-21/work_cassese/exact_degeneracy.py). Fixing the `q` coefficient can leave the zero integrand; entry covariance does not exclude determinant-square wells. |
| E06 | General nonhomogeneous polynomial SOS search, degree 4/6: 42 restarts and 222 alternating steps. | Global coefficient-identity ansatz, but only floating Grams. All recorded gaps positive; feature barriers reduce degeneracy. No exact planar RC certificate or certified lower bound promoted from the runs. [Report](../../research/experiments/2026-11-21/work_sos/README.md). |
| E07 | Exact rational polynomial/Gram control in `3 × 2`, with periodic map `(sin x,sin y,sin(x+y))`. | Full coefficient identity, exact positive-definite LDL and exact integral `J=−103817049981/8000000000000`. [Certificate](../../research/experiments/2026-11-21/work_sos/control_run/exact_control_certificate.json), [checker](../../research/experiments/2026-11-21/work_sos/certify_control.py). Validates the known higher-dimensional mechanism; **not planar**. |
| E08 | Independent pipeline audits and SOS scope check. | The `Pβ` LH form has an exact SOS for `β≥5/2` although the integrand is nonpolyconvex. Derivatives, saved basis orderings, actual gradients and the `3 × 2` control were cross-checked. [Audit](../../research/experiments/2026-11-21/work_lit/SOS_AUDIT.md); [eight-check record](../../research/verification/2026-11-21/results.json). |

No amount of precision in E02–E06 turns an attained positive value into a lower bound. E07
shows the pipeline can certify a known negative mechanism in its correct dimension; it does
not guarantee that the chosen planar ansatz contains a negative example.

## Completion audit

See [COMPLETION_AUDIT.md](COMPLETION_AUDIT.md) for priorities and the distinction between a
new checker, a changed mathematical search class, and a solved universal theorem.

| ID | Result / finding | Evidence and current scope |
| --- | --- | --- |
| A01 | Cutoff-based base minimization can suppress a kernel linear term or a large decrease from tiny positive curvature. | Source audit plus [exact rational solver and controls](../../research/audit/exact_base.py). Demonstrated on quadratic regression inputs; no claim a saved planar candidate was missed. Archived search code is unchanged. |
| A02 | The sharp `P₂` endpoint has a ten-square LH identity modulo `8 det(A)det(H)`. Direct LH-SOS includes it, but a fixed positive Gram floor excludes its nonzero flat feature vector. | [Exact symbolic identity](../../research/audit/pbeta_exact_sos.py) and [output](../../research/audit/pbeta_exact_sos.json). Global RC only, no QC conclusion or novelty claim. |
| A03 | Norm-multiplier certificates for the compactified LH form are complete for negative planar witnesses after gap-preserving radial strictification. A local-ball certificate plus an explicit radial tail is another sufficient route. | [Hand proof with rational Putinar input](GLOBAL_CERTIFICATES.md). No uniform degree/grid/order bound, no positive termination, no assertion that a fixed SDP search is exhaustive. |
| A04 | Exact positive Hessian quadratures at every degree automatically admit a common compactly supported limit. | [Radial-moment compactness theorem](GLOBAL_CERTIFICATES.md#4-correct-compactness-theorem-for-positive-certificates). Corrects H12. Universal certificate feasibility is still the missing positive theorem. |
| A05 | Exact rational verifier for sphere-ideal and norm-multiplier LH certificates, with actual periodic PL witness construction and exact gap evaluation. | [Implementation and controls](../../research/audit/README.md). Both formats pass a nonconvex RC control; malformed identities are rejected. Control gap is positive; no candidate discovery or Lean proof is claimed. |
| A06 | H19–H25 survive the hand audit within their hypotheses. The entire `Pβ`, `β≥2`, family reduces to the all-field inequality `αC₂≥h²`, with the `α=0` boundary proved safe. | [Structural audit and formulas](STRUCTURAL_AUDIT.md), [exact expansion check](../../research/audit/pbeta_schur_reduction_check.py). The remaining inequality is open and would settle this family, not arbitrary integrands. |

## Exponent-range qualification (22 November 2026)

[Complete novelty and exponent audit](IWANIEC_MORREY_EXPONENT_AUDIT.md):
**0<p<1 gives only the zero integrand** for any finite-valued
globally RC p-homogeneous F in every finite matrix dimension
(elementary proof using sublinear growth of convex rank-one lines);
**p=1 isotropic RC⇒convex is already Dacorogna (1989)**.
Potential new mathematical content is confined to
**1<p<2**, where the proposed *all-matrix* nonnegative
isotropic RC⇒QC generator representation uses the
2026 global Burkholder theorem, and to the
independently derived but unreviewed signed p=2 polyconvex result.
Do not label the full range (0,2] a new breakthrough.

## Iwaniec–Morrey program, 22 November 2026 (I01–I09)

The global planar RC⇒QC problem is still open. The
[2026 Iwaniec/Burkholder preprint](https://arxiv.org/abs/2609.28311v2)
is used as an **external, not independently formalized**
quasiconvexity theorem, not as a proof of Morrey.
This section distinguishes proved algebra,
conditional analytic inputs, and refuted
certificate-completeness conjectures.

| ID | Statement/evidence | Current verdict and scope |
| --- | --- | --- |
| **I01** | [Source audit and exact moving calibration](IWANIEC_MORREY.md): The 2026 preprint claims QC of L and every Burkholder Bₚ; L admits the pointwise selecting-gradient decomposition from its projection lemma. | **Conditional source result**, not independently Lean-checked. Does not imply all 2×2 RC integrands are QC. |
| **I02** | [Universal p∈(1,2) isotropic theorem](IWANIEC_MORREY_UNIVERSAL.md): every nonnegative, isotropic, positively p-homogeneous RC F has global touching minorants given by nonnegative sums of the two Burkholder orientations at **every** matrix. Full 1-D supporting-line hand proof recorded. | **Conditional hand proof** on Burkholder QC; far stronger than conformal-only prior statement but unreviewed and not Lean-certified. No anisotropic/nonhomogeneous conclusion. |
| **I03** | [Signed isotropic p=2](IWANIEC_MORREY_P2_SIGNED.md): global polyconvexity for all real-valued isotropic 2-homogeneous RC F; an elementary rank-one midpoint proof gives nonnegative intercepts of all signed-singular profile supports. | **Hand proof, independent of Iwaniec**, awaiting external review/Lean. Removes nonnegativity for this class. |
| **I04** | [Guerra–Kristensen 2022 Proposition 3.7 correction](IWANIEC_MORREY_P2_SIGNED.md): the printed determinant mean is −15, not 1. A corrected three-atom probability law matches matrix/determinant moments at I, has energy zero, and is checked by [rational script](../../research/audit/gk_prop37_exact.py). | **Exact arithmetic control**, repairing the *nonpolyconvexity* witness only. Its atoms are **not an actual gradient law**; nothing about non-QC follows. |
| **I05** | [p>2 hybrid QC lower envelope](IWANIEC_MORREY_GENERAL.md): two Burkholder orientations plus positive powers of affine minor/convex norms give a sound global QC lower bound, provided Burkholder QC is true. [Exact p=6 control](../../research/audit/iwaniec_hybrid_p6_exact.py) refutes completeness of the two *individual* tests. | **Valid sufficient family only, incomplete**. Does not itself classify all p>2 isotropic RC profiles. |
| **I06** | [Exact p=4 no-go](IWANIEC_MORREY_HYBRID_NOGO.md): positive isotropic p-homogeneous globally RC profile with integer Chebyshev coefficients; strict all-r scalar RC certificate uses [standard-library rational Bernstein checker](../../research/audit/iwaniec_hybrid_no_go_exact.py) (12 intervals, depth 6). Positive two-point functional separates **every** hybrid generator and its suprema, gap **356912972869/17832200896512**. | **CLOSED NEGATIVELY:** former conjecture Gₚ that the hybrid envelope touches every isotropic RC profile is **false**, *not* an open gate. The two-point functional has total mass 8/5, so is **not a gradient Jensen violation**. Analytic acoustic-to-global bridge remains a hand argument pending Lean. |
| **I07** | [Open-family upgrade](IWANIEC_MORREY_HYBRID_OPEN.md): strict acoustic and separator margins persist in an open C² neighborhood of the exact profile and an interval of p around 4. | **Hand compactness deduction** from I06; infinite-dimensional class-wide obstruction to *the method*. Not an open family of Morrey counterexamples. |
| **I08** | [Smooth coercive robust L examples](IWANIEC_MORREY_SMOOTH_QC.md): exact four-atom lifted-minor Jensen gap −1/17 for W=1+L+||A||²/8, sustained after smoothing; sharp ε=1/4 global determinant-affine support threshold at zero. | **Exact arithmetic and hand proof**, conditional on the preprint for QC; nonpolyconvexity is NOT non-QC. |
| **I09** | [Global L-cone no-go](IWANIEC_MORREY_CONE_NOGO.md): all positive sums of matrix-transformed/translates of L with polyconvex energies have a strict support-envelope gap on a known anisotropic rank-one-flat RC energy; [acoustic criterion](IWANIEC_MORREY_ACOUSTIC.md) further reduces smooth isotropic RC to scalar inequalities. | **Hand proofs and exact algebra checks**, pending outside review. Another stop rule for positive-support generation, not a Morrey counterexample. |

**Strict local stability of I06.** [Exact acoustic lower-bound certificate](../../research/audit/iwaniec_local_stability_exact.py) proves (D^2F(\operatorname{diag}(1,0))[u\otimes v,u\otimes v]\ge\frac16|u|^2|v|^2). The [frequency-independent hand proof](IWANIEC_MORREY_LOCAL_STABILITY.md) gives a Jensen gap at least (\frac1{24}\fint|D\varphi|^2) for **every** sufficiently small periodic gradient, and similarly on compact families of nonconformal bases. This is a **local-gradient-amplitude theorem**, not a full QC theorem; Lean/review pending.

**Numerical candidate check for I06.** The strict separating measure is not a compatible gradient distribution. The [periodic piecewise-affine search](../../research/experiments/2026-11-22/README.md) parametrizes actual periodic two-component maps on grids 3×3, 4×4 and 6×6, checks both mean gradient and determinant moments, and locally optimizes the energy for five signed-diagonal bases. **No negative Jensen gap was found in the recorded 147 runs.** This is a bounded local experiment, **not proof of quasiconvexity, not an exhaustive search, and not a certified separation**. The [source code](../../research/experiments/2026-11-22/iwaniec_hybrid_pl_search.py) is committed; it requires NumPy, SciPy and PyTorch and does not run under skipped CI.

**I10 — all-amplitude p=4 rank-one closure.**
The former hybrid-cone separating candidate
is now [proved polyconvex at EVERY rank-one base](IWANIEC_MORREY_RANKONE_SUPPORT.md)
by a global determinant-affine minorant,
with an [exact rational Bernstein verifier](../../research/audit/iwaniec_p4_rank_one_polyconvex_exact.py).
This **supersedes** earlier suggestions of
searching for large-amplitude gradient
violations at E=diag(1,0): all actual gradient
energies satisfy Jensen there.
No Iwaniec assumption is used.
Status: hand proof+exact computation, not Lean/refereed.

**I11 — separator unrealizability.**
[Two exact SOS identities](IWANIEC_MORREY_SEPARATOR_NONREALIZABLE.md)
force a matrix probability with the exact
old two signed ratios and fourth-order
weights to obey \(\mathbb E\|A\|_{\rm op}
\le59/60\), contradicting its required
barycenter norm 1. Thus the cone
separator cannot be turned into a
gradient law by simple normalization.
The [verifier](../../research/audit/iwaniec_separator_nonrealizable_exact.py)
is elementary exact rational arithmetic.

**I12 — universal all-p scalar support gate.**
The [single determinant multiplier criterion](IWANIEC_MORREY_GENERAL_SUPPORT_CRITERION.md)
is an iff for a global poly-affine
minorant at every differentiable
nonconformal base. The feasibility
constraints form a compact interval;
failure has a **two-test-point** dual
certificate. It also gives an open
family of p>2 nonconformal base ratios
for which the explicit p4 candidate
and neighboring profiles have global
poly-affine supports. The universal
existence of the multiplier for EVERY
rank-one-convex profile remains **OPEN**.
Wiedemann–Peter 2026 give the
earlier, broader diagonal
characterization of isotropic PC.

**I13 — all-p polyconvex sublevel sets.** By the
[global isotropic level-set note](IWANIEC_MORREY_LEVELSETS.md),
for every nonnegative isotropic p-homogeneous
rank-one-convex F with p>0, **every** sublevel
\(K_c=\{F\le c\}\) is polyconvex. This follows
from the published compact-connected isotropic
set theorem of Conti–De Lellis–Müller–Romeo (2003),
applied to bounded star-shaped truncations.
Consequently F satisfies a **global L∞
quasiconvexity inequality** for all periodic
Lipschitz gradients, but this does NOT imply
ordinary average-energy Jensen. Prior-art
corollary, not new publication-level priority.


**PRIORITY correction to I14 (23 November 2026):**
[Dacorogna–Koshigoe (1993), Theorem 2.1](https://www.numdam.org/item/AFST_1993_6_2_2_163_0/), Theorem 2.1, already establishes
the exact **four-atom signed-diagonal Jensen criterion**
AND the **global diagonal supporting-plane equivalence** for
SO(2)×SO(2)-isotropic energies. Our LP sparsification and scalar
parameter calculations are rederivations/specializations, not new
global theorems. [Source audit](IWANIEC_MORREY_PRIOR_ART_1993.md).

**I14 — four-diagonal-atom global p>2 reduction.**
The [all-class finite-support theorem](IWANIEC_MORREY_FOUR_ATOM.md)
uses Wiedemann–Peter (2026)
plus a four-moment LP extreme-point
argument to show that global PC
for every nonnegative isotropic
RC p-homogeneous F, p>2,
is **equivalent** to universal
three-/four-atom signed-diagonal
Jensen under the exact moments
(mass, first x, first y, xy).
Every one- and two-atom case is
automatic from RC; the 3-atom
case has a covariance-free
one-parameter representation.
The [standard-library rational
reducer](../../research/audit/iwaniec_diagonal_four_atom.py)
verifies exact moment and cost
preservation on 32 cases.
**Status:** global reduction
proved at hand level, exact code
tested; the universal 3-/4-atom
positivity remains **OPEN**.
No equivalence to gradient
realizability or Morrey is claimed.


**I15 — exact positive quartic stabilization cone (23 Nov 2026).**
For all 1≤|γ|≤2, every **nonnegative**
\(P_{\gamma,c}(A)=\|A\|_F^4-
2\gamma\|A\|_F^2\det A+c(\det A)^2\)
is **globally polyconvex**, with sharp
nonnegativity cutoff
\(c\ge4(|\gamma|-1)\). The [exact
positive generator decomposition](IWANIEC_MORREY_QUARTIC_STABILIZATION.md)
also covers a wider |γ|<1 sufficient
cone; positive powers extend all
members to every p≥4. The
[rational algebra checker](../../research/audit/iwaniec_dm_positive_stabilization_exact.py)
passed locally. Classical
polyconvexity of the DM endpoint
is an explicit external input;
the decomposition and composition
proofs are hand-level and unformalized.
**Status:** global infinite-parameter
subclass exclusion, **not** a
general p>2 polyconvexity
or Morrey theorem. No novelty claim.


**I16 — exact all-quartic shear and curvature bounds (23 Nov 2026).**
For every invariant quartic polynomial
\(F=a s^2+b sd+c d^2\), global RC
implies \(a\ge0\), \(|b|\le4a\),
and if a>0,
\(c\ge3b^2/(8a)-2a\).
These follow by shears at I,D and
global convexity of the diagonal slice;
the [exact proof](IWANIEC_MORREY_QUARTIC_SHEAR_BOUND.md)
records all equality/boundary cases.
Together with the previously recorded
positive quartic decomposition,
ALL globally nonnegative RC quartics
with \(|b|\ge2a\) are **globally PC**;
raising to powers yields a class
for EVERY p≥4. This is a
global infinite-parameter subclass,
not every quartic or p>2 F.
Symbolic coefficient identities
are reproducible in
[the checker](../../research/audit/iwaniec_quartic_shear_bound_exact.py).
No Lean/build/priority claim.

**I17 — global quadratic possible Jensen deficit (23 Nov 2026).**
For every nonnegative isotropic globally
RC p-homogeneous F with p≥2 that
is matrix-C² near conformal orientations,
[the analytic estimate](IWANIEC_MORREY_GLOBAL_QUADRATIC_DEFICIT.md)
gives
\(0\le F-QF\le K\sigma_1^{p-2}
(\sigma_1-\sigma_2)^2\)
for ALL matrices. It improves
earlier first-order near-conformal
control, conditional only on the
**published** Guerra–Kristensen
global determinant-power minorant,
not Iwaniec's new preprint.
It gives NO all-matrix QC/PC result:
positive deficit remains possible.
Hand proof; Lean/external review pending.


**I18 — p>2 fractional-power method obstruction (23 Nov 2026).**
The [exact p-interval calculus note](IWANIEC_MORREY_FRACTIONAL_POWER_NOGO.md)
shows the globally nonnegative
polyconvex quartic \(Q=s(s-2d)\)
has \(Q^{p/4}\) **not even rank-one
convex** along diag(1,t) for
**every 2<p<11/4**. At t=1/2
the rank-one second derivative
has sign \(p/4-11/16\).
An [exact rational checker](../../research/audit/iwaniec_fractional_power_no_go_exact.py)
replays the derivative. This is
a general-method no-go only,
not an RC/non-QC example.

**I19 — compatible three-wave heatflow counterexample (23 Nov 2026).**
The [exact full Fourier proof](IWANIEC_MORREY_P4_HEATFLOW_NOGO.md)
constructs an affine+periodic smooth
planar heat trajectory with
\(F(A)=(\det A)^2\) (globally
polyconvex, nonnegative, isotropic,
4-homogeneous), initial energy
31332 and derivative **+920**.
The [standard-library exact checker](../../research/audit/iwaniec_p4_heatflow_three_wave_exact.py)
reproduces the six Fourier modes.
Continuity extends the sign
to determinant powers
\(F_p=|\det A|^{p/2}\) for an
**open interval of p around4**.
This is an explicit homogeneous
instance of earlier H24 and
rules out universal componentwise
heatflow monotonicity, NOT
quasiconvexity, in the p>2 class.
No Lean/CI and no novelty claim.


**I20 — all-p≥4 rational negative-witness semidecision (23 Nov 2026).**
The [global certificate hierarchy](IWANIEC_MORREY_PGE4_EXACT_HIERARCHY.md)
proves that, **within C² signed-singular
profiles**, a violation of the stronger
global polyconvexity conjecture at ANY
real p≥4 can be strictified and
rationalized to a rational p, rational
polynomial h, and ≤4 rational signed-
diagonal atoms. Exact rational acoustic
Bernstein inequalities certify **global
rank-one convexity**, and rational
algebraic root intervals certify strict
failure of minors-Jensen; a
[standard-library checker](../../research/audit/iwaniec_all_p_rational_cert.py)
implements both tests. Five positive
controls p=4,9/2,5,6,10 passed with
two Bernstein leaves; an affine Dirac
law gives no negative certificate.
**Status:** negative semidecision with
no degree cutoff. No complete positive
classification, no nonsmooth density
theorem, no gradient-law/QC witness,
and no Lean proof is asserted.


**I21 — all-p≥4 convex-conjugate and amplitude reduction (23 Nov 2026).**
The [exact analytic note](IWANIEC_MORREY_PGE4_CONJUGATE.md)
restates the global supporting-minor
criterion via the one-variable Fenchel
conjugate \(h^*\), removing the
signed-ratio test variable. For
any **strictly positive** profile
h, an explicit integer radius R
makes all amplitudes a≥R
automatically feasible for every
c in the orientation interval.
A separate all-class limit
argument proves it suffices to
establish global PC for h>0
at each fixed p≥4; no C²
assumption is needed for this
positive reduction. The
[symbolic and exact rational control](../../research/audit/iwaniec_pge4_conjugate_identity.py)
checks the algebra and cutoff.
The remaining compact continuum
support inequalities are
**not proved**, and no uniform R,
novelty claim or Lean formalization
is asserted.


**Decision gate after I06:** Do **not** attempt to prove the
refuted hybrid completeness identity; nor infer
non-quasiconvexity from positive-cone separation,
nonpolyconvexity, or a minors-preserving law.
The unrestricted problem still requires a certified
planar gradient gap for a globally rank-one-convex
integrand, or a universal all-gradient Jensen theorem.
See [the main roadmap](ROADMAP.md).

## Corrections and interpretation rules

1. **B and B₁ are refuted, not pending targets.** H01 gives a fixed point at uniform weights
   for every level-one pair in a particular mold. A can still concern an exceptional slice in
   `(u,v,t)`; it does not imply B by projecting away `t` without additional arguments.
2. **Uniform-weight obstructions are weaker than absence of fixed points.** H02–H05 leave
   nonuniform weights, repeated atoms and limiting laminates available. Likewise, an empty
   value `T(t)` does not exclude a fixed point elsewhere. The original E13 pair even has an
   exact boundary fixed point in the [existing numerical record](../Pedregal/numerics/fixedpoint_exact.py).
3. **The old quadratic gap has the opposite sign.** The historical polynomial checker prints
   `f(F)−average f(F+Du)=−405772`; the current convention gives `J=+405772`. This is a successful
   sanity check, not a quadratic counterexample or an arithmetic error.
4. **The ambient cones differ.** A polynomial LH inequality only on a compact ball is not the
   same fixed-degree condition as global RC. Stabilization can raise degree. Unweighted SOS is a sufficient
   certificate class, not a complete description of RC polynomials. A03 supplies a hierarchy
   complete for some negative witness after strictification; a fixed level remains restrictive.
5. **Archive headings are not current verdicts.** H16's proposed cone inclusion is superseded
   by H23's hand obstruction. H18's bounded coefficient neighborhood is not itself a cone.
   A06 rechecks H19–H25, but independent human review of the analytic arguments remains a
   publication gate.
6. **Quarantined files remain quarantined.** Cassese `penalty_sos_best.npz` has an unacceptable
   Gram matrix; `penalty_barrier_best.npz` is a zero-integrand degeneration. Names containing
   “best” do not confer candidate status. The early general quartic run has a different Gram
   monomial ordering, recorded in its saved data and honored by the current validator.
7. **Do not equate a cutoff base minimum with an exact one.** A01 identifies the missing
   range/tiny-eigenvalue checks. Positive saved minima remain observations, not lower bounds.
8. **Historical paths have moved.** Curated links use `Morrey/Pedregal`, `Morrey/Common` and
   `palomar/<Paper>`. Original notes retain their old paths. Python and prose are not imported
   into the Lean axiom audit merely by appearing in this repository.

The original Pedregal survey reported 40 random empty fibers at each of levels one and two,
one floating exhaustive `315³` level-one shape enumeration for a generic input, and unsuccessful
local fixed-point searches. These are preserved in the [paper report](../Pedregal/REPORT.md)
and its scripts. They motivated A/B/B₁; H01 demonstrates why the numerical absence could not
justify B/B₁. Neither equation counts nor local residual minima certify global infeasibility.

## R01: spatial averaging does not automatically produce rank-one splits

This short calculation reconstructs a point from the prior discussion; no original certificate
file for it was recovered. On the `2π`-periodic torus let
`w(x,y)=(cos(x) sin(y), sin(x) cos(y))`. Then

\[
Dw=\begin{pmatrix}-\sin x\sin y&\cos x\cos y\\
\cos x\cos y&-\sin x\sin y\end{pmatrix}.
\]

Partition the torus into the union of the two diagonal `π × π` squares and the union of the
two off-diagonal squares. Each set has half the area. Using `∫₀^π sin x dx=2` and
`∫₀^π cos x dx=0`, their conditional mean gradients are respectively
`−4I/π²` and `+4I/π²`. Their difference has rank two. Thus this conditional-expectation split
cannot be used as a rank-one laminate split. This rules out the automatic inference from an
arbitrary spatial averaging tree to a laminate; it does **not** rule out every adaptive tree.

## Coverage, provenance and remaining uncertainty

All 36 recovered source artifacts are inventoried in
[source_manifest.json](../../research/source_manifest.json), including ZIP members and duplicate
aliases. Their 139 distinct payloads are preserved: 53 historical files and 86 in the latest
package. The earlier paper audit is already in the repository. ZIP container hashes are
recorded, while their extracted member bytes are retained instead of redundant ZIP copies.

The recovery did not supply every transient optimizer candidate or every earlier chat message.
In particular, discussion-only references to an earlier rejected degree-six candidate and a
buggy early `Pβ` Fourier experiment are not treated here as independently reproduced results.
The saved current searches and checks are the reproducible evidence; missing artifacts confer
no additional support. No literature search can establish from absence alone that these
observations are new; see [SOURCES.md](SOURCES.md).

The unfinished central tasks remain explicit in [ROADMAP.md](ROADMAP.md): construct a valid
global planar counterexample, or prove the all-scale Jensen statement. The finite certificates,
subclasses and method obstructions above are evidence and reusable tools, not a substitute for
either task.
