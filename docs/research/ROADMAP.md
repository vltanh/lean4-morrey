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

## 2. Immediate priorities

The most recent working direction is the counterexample search. The next session should begin
with [EXPERIMENTS.md](EXPERIMENTS.md), its invalid-candidate exclusions, and the exact controls,
not repeat the initial mold experiments.

| Priority | Deliverable | Acceptance / stop rule |
| --- | --- | --- |
| 1 | Replay the archived exact and floating-output checks; preserve the ledger's status distinctions. | All supported checks pass, inputs match their hashes, and failures are investigated before interpreting a new result. This checks the pipeline, not Morrey. |
| 2 | Design one changed search hypothesis outside the already tested degeneracies. | State what mathematical freedom is new, how global rank-one convexity will be certified, the genuine gradient parameterization and a finite run budget. Do not rerun a rejected family solely with more starts. |
| 3 | Escalate any strict negative candidate immediately to independent exact or interval verification. | Both global convexity and the negative integral survive validation; otherwise archive a rejection with its witness. |
| 4 | Develop reusable analytic/Lean bridges independently of search outcomes. | Prove a clearly stated conditional implication without introducing an unproved global feasibility hypothesis as a theorem. |
| 5 | Seek independent mathematical review of the structural hand proofs and any promising global construction. | Audit assumptions, limits, boundary cases and dimensional conventions before claiming a new result. Novelty review is separate. |

There is no justified completion date or finite degree/grid cutoff. A bounded search can end;
the unrestricted mathematical question remains open if it finds nothing.

## 3. Negative route: candidate to theorem

### N1 — Search in a class with a global certificate route

The polynomial reduction in [H07](LEDGER.md#global-reductions) supplies a hand-proof route to
rational polynomial and rational dyadic witnesses if a counterexample exists. It gives no
uniform degree or mesh bound. A Gram/SOS Legendre–Hadamard ansatz is sufficient but incomplete;
failure inside it is not failure of the unrestricted polynomial search.

Useful changes of hypothesis include a polynomial class outside the current SOS representation,
a different anisotropic family with a rigorous global curvature argument, or a structured
gradient geometry not present in the current Fourier/FE trials. Each proposal must explain why
it avoids the [closed routes](#6-routes-that-require-a-new-hypothesis-before-reopening).

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

The source already contains [Sverak.lemma1_witness](../../Morrey/Sverak/Lemma1.lean), which converts
a smooth periodic strict violation for a continuous integrand into a smooth compactly supported
witness, in general dimensions. Reuse it for a smooth planar candidate. For a periodic FE
witness, prove the required smoothing with an error smaller than the gap, or supply a direct
Lipschitz/cutoff bridge. The existing smooth result does not discharge that step automatically.

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
or the all-level finite-order statement. A positive Hessian-measure representation is another
possible target. State the quantifiers over base matrices, integrands, maps and scales explicitly.
If taking limits, specify support bounds, tightness and the convergence that passes the energy.

**Exit:** a precise theorem and a written implication to the planar Morrey statement. The
conic-duality reductions [H10–H12](LEDGER.md#global-reductions) reorganize this target; they do not
produce the positive representing measure.

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
matrix, the needed regularity of finite-valued RC functions, periodic Lipschitz approximation
by dyadic piecewise affine maps with controlled gradients, and convergence of energies. A
weak-limit approach needs its own limiting Jensen theorem. Reuse the existing smooth periodic
cutoff result for the direction it proves.

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
| Cassese formalization | Complete the independent `2 × 3` paper audit on its own branch and connect its definitions. | Higher-dimensional counterexamples do not restrict to planar counterexamples automatically. |

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
| More unstructured starts in the same quartic wells | Latest trials found flat/determinant-square/zero-integrand degeneracies. | Changed variables, geometry, objective or certificate class, with an explicit budget. |

The authoritative result and evidence for each disposition are in [LEDGER.md](LEDGER.md).
Keep this table updated when a hypothesis changes; preserve the previous rejection record.
