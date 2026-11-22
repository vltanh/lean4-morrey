# Roadmap to completion

**Status: open.** The positive and negative routes below are alternatives. Neither is completed
by the present ledger. The main task is a statement about every planar gradient and every
rank-one-convex integrand, or one globally certified planar counterexample.

## 1. What counts as completion

| Route | Required mathematical output | Final formal output |
| --- | --- | --- |
| Positive | For every finite-valued rank-one-convex `f : ℝ²ˣ² → ℝ`, every base `F`, and every admissible planar test map `u`, prove `average f(F + Du) ≥ f(F)`. | A proof of `Pedregal.Theorem1_1_part2` or `Pedregal.Theorem1_2`, with an explicit bridge from any alternative definitions. |
| Negative | Exhibit a continuous finite-valued `f : ℝ²ˣ² → ℝ`, prove rank-one convexity globally, and give an actual planar gradient witness with a certified strict negative gap. | A planar theorem asserting continuity, rank-one convexity and failure of quasiconvexity in one of the project's definitions, with the needed bridges. |

The all-level **finite-order** laminate statement is sufficient for the positive route and is
stronger than the Jensen property actually needed. Abandoning that stronger statement is allowed.
Showing that a prescribed finite tree fails is not evidence that its gradient law violates Jensen.

## 2. Immediate priorities after the audit

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
