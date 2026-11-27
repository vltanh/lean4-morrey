# Structural-quartic audit and an exact all-field endpoint gate

## Audit verdict

The AI-assisted source audit read the complete hand arguments behind H19–H25 and found **no fatal mathematical gap under their stated hypotheses**. Their restrictions are substantial and cannot be discarded to obtain Morrey. The strongest immediate conclusion for the research program is that some of the previously explored routes really are excluded analytically; they should not be reopened by increasing numerical budgets.

This is a mathematical source audit, not a Lean proof or a novelty clearance. The new scalar reduction below was checked by an exact SymPy polynomial identity; its remaining universal inequality is not proved.

### H19: support from a flat entire rank-one line

The separate-convexity lemma is correct. For positive and negative transverse parameters, dividing by that parameter gives respectively convex and concave functions of the line coordinate. Their common derivative limit is affine. The supporting-line inequality is valid for either sign of the transverse coordinate.

At the origin, the Hessian vanishes on the flat rank-one direction. Testing the two rank-one perturbations `E11 + εE12` and `E11 + εE21` forces the two mixed Hessian entries to vanish. Thus `D²g(0)[E11,H] = κ H22`. The explicit decomposition with `H22=1` and `det X=xy` then gives the determinant support; continuity handles `X22=0`.

**Essential hypotheses:** global rank-one convexity; flatness on the *entire* real line, not a segment; differentiability sufficient for the transverse derivative and Hessian calculation. The conclusion is support/quasiconvexity at points on that line. It does not imply global polyconvexity of the function.

### H20: homogeneous rank-one-null rigidity

The divisibility argument is valid over the real determinant hypersurface because its real smooth locus is Zariski dense. The limiting rank-one-line polynomials are convex after division by a positive normalization. Odd determinant multiplicity forces an affine limit; even multiplicity with a positive-degree residual gives two zeros and a positive intermediate value, contradicting convexity. This really proves the stated all-degree classification.

The exposed-ray conclusion for `det²` follows from positivity of a homogeneous RC quartic on every rank-one matrix. The inhomogeneous corollary constrains only the top term, as the ledger already says.

### H21: one determinant support for the singular-zero class

The `C²` hypothesis makes the local quotient by the determinant `C¹`. Although this quotient need not be `C²`, the displayed Hessian formula at the zero hypersurface is still valid: on a rank-one line, `q(B+tH)=t Dq(B)[H]`, and the first-order expansion of the quotient suffices to compute the second derivative. Both signs of the rank-one perturbation force tangential constancy.

The nonzero rank-one locus in `R^{2×2}` is connected (it is the continuous image of `(0,∞)×S¹×S¹`), so the quotient has one constant value there. The rank-one tangent-line support then gives the claimed global determinant lower bound. The result applies at singular bases only.

### H22: rank-one-zero homogeneous quartic SOS

The proof is correct modulo Hilbert's ternary-quartic theorem. The convex first-row and first-column restrictions really are invariant under translation along the flat axis: applying their supporting hyperplanes to arbitrary points on that axis forces the corresponding derivative to vanish. A nonnegative quadratic form with zero diagonal entries in those directions has zero corresponding rows/columns. This justifies the `α(ad)² + ad T₂ + S₄` normal form and subsequent square completion.

Nonnegativity proves Jensen at zero only. A sum of squares is not a proof of quasiconvexity at other bases.

### H23: failure of the proposed generator cone

The compact-base argument is valid: the Hessian integral is strictly positive on every nonzero homogeneous RC quartic. The individual orbit-generator limits with a rank-one zero are convex, because the four matrix-unit values bound the entire linear map and force the determinant scale to zero. Carathéodory bounds the number of terms before passing to a subsequence. Polyconvexity is closed here via its finite Jensen inequalities preserving all minors.

The proof was written for `β≥5/2`, but **it extends to every `β≥2`** once the independently verified sharp rank-one-convexity theorem is supplied. The rest of the obstruction uses only RC, the zero at `E11`, and the nonpolyconvexity support witness, all available for this range. Hence adding more transforms of the same known generators cannot solve the full quartic problem.

### H25: affine planar quadratic-bivector pullbacks

The dimension reduction to the span of four row vectors is sound. The required non-strict Finsler–Thorpe statement is present in the primary source:

Bettiol–Krishnan, *Ricci flow does not preserve positive sectional curvature in dimension four*, Calc. Var. 62, 13 (2023), §2.2, Proposition 2.2:
https://link.springer.com/article/10.1007/s00526-022-02335-z

The source phrases the proposition for an algebraic curvature operator. For arbitrary symmetric quadratic form `Q` on `Λ²R⁴`, first subtract its component along the Hodge star to obtain the Bianchi component. This subtraction is zero on decomposable bivectors. The proposition then supplies a PSD correction by a multiple of the same star. This supplies the short missing explanation between the source's formulation and the archived theorem.

The remaining wedge expansion is correct, and the square root of a PSD quadratic form is a convex seminorm. Thus this entire affine planar pullback class is polyconvex, for every embedding and base. It is not worth further random search in that class. Cassese's quartic does not have this form and is unaffected.

## A clean global endpoint gate for P_beta

Let

`Pβ(a,b,c,d) = (ad−2bc)² + β(b²+c²+d²)²`.

### 1. All parameters reduce to β=2

The added function `R(A)=(b²+c²+d²)²` is convex. Therefore

`Pβ = P₂ + (β−2)R`, for `β≥2`.

If `P₂` is quasiconvex, every rank-one-convex member of this family is quasiconvex. Conversely, if some `Pβ`, `β≥2`, has a negative actual-gradient Jensen gap, the *same* witness has a negative gap for `P₂`, because the Jensen gap of `R` is nonnegative. Hence the entire family's counterexample question is exactly the endpoint's question. Additional searches over β are unnecessary.

### 2. The base hyperplane F22=0 is already safe

At any base `F` with `F22=0`, the restriction `t ↦ P₂(F+tE11)` is constant. H19 therefore proves quasiconvexity at every such base, including full-rank bases with `F12 F21≠0`.

More explicitly, the supporting determinant coefficient is `κ=−4 F12 F21`:

`P₂(F+X) ≥ P₂(F) + DP₂(F)[X] − 4 F12 F21 det X`.

Thus an endpoint counterexample must have `F22≠0`. Homogeneity reduces all remaining bases to `F22=1`: divide the base and test map by `F22`; fourth-degree homogeneity preserves the sign of the gap, even when `F22<0`.

### 3. Eliminate F11 exactly, for every periodic field

Work on the unit torus and use normalized averages `⟨·⟩`. Write

`D(u,v) = [[a,b],[c,e]] = [[u_x,u_y],[v_x,v_y]]`,

so the four means vanish and `⟨ae−bc⟩=0`. Let the normalized base be

`F = [[M,B],[C,1]]`.

Define

`α = ⟨e²⟩`,

`h = ⟨e(ae−2bc−2Bc−2Cb)⟩`,

and

`Cβ = ⟨[a(1+e)−2(B+b)(C+c)]² + β[(B+b)²+(C+c)²+(1+e)²]²⟩`
`     −4B²C² − β(B²+C²+1)²`.

Then the *exact* Jensen gap is

`Jβ(F,u,v) = α M² + 2h M + Cβ`.

No mesh, wave count or finite-size assumption enters this identity. The discrepancy between the pointwise expansion and this formula is

`2M² e + 2M[a + 2(ae−bc) − 2Bc − 2Cb − 2BCe]`,

whose integral vanishes by the gradient mean and determinant identities. An independent exact expansion checks this in [pbeta_schur_reduction_check.py](../../research/audit/pbeta_schur_reduction_check.py).

For `α>0`, the minimizing base entry is `M*=−h/α`, and

`min_M J₂ = C₂ − h²/α`.

Consequently, the entire `Pβ` endpoint question reduces to the following explicit **all-field inequality**:

> For every smooth periodic planar pair `(u,v)` and every real `B,C`, if `⟨v_y²⟩>0`, prove
> `⟨v_y²⟩ C₂ ≥ h²`, or find an actual gradient for which the inequality fails strictly.

A strict failure immediately gives the base `M*=−h/α` and an actual planar negative witness for the globally RC polynomial `P₂`. A proof would close the whole infinite parameter family, but would still not solve Morrey for arbitrary integrands.

### 4. The α=0 boundary is fully understood

If `α=0`, then `v_y=0`, so `v` depends only on `x` and `h=0`. This boundary satisfies Jensen for *every* rank-one-convex integrand, not only `Pβ`:

1. For fixed `x`, the second matrix row is constant in `y`. All variation is in the first row; its two-dimensional affine plane has rank-one differences. Convex Jensen in that plane replaces `(u_x,u_y)` by `(∂x⟨u⟩_y,0)`.
2. After that averaging, the second column is the constant base column. All remaining `x`-variation is in the first column, another rank-one plane. Jensen in `x` gives the base value.

Thus `C₂≥0` at `α=0`. However this does **not** by continuity settle `α↓0` after base minimization, because `M*=−h/α` may diverge. That is a meaningful concentration regime for an analytic attack.

## Direct LH-SOS scope: correction from the parallel certificate audit

The parallel search audit produced an exact ten-square identity for the full Hessian of `P₂`, modulo `8 det(A)det(H)`. On physical rank-one `H` the remainder vanishes. Thus the direct LH-SOS class already contains the sharp endpoint; its true threshold for this family is also `β=2`. The earlier explicit certificate at `5/2` was not the optimal SOS threshold.

The fixed strict Gram margin `Q ⪰ 10⁻⁷ I`, however, excludes this boundary polynomial exactly: a flat direction forces a zero of the LH form at a nonzero monomial vector. A negative example with sufficient strict perturbation might still enter the restricted search, but no uniform margin was justified. The primary certificate artifacts are [pbeta_exact_sos.py](../../research/audit/pbeta_exact_sos.py) and [its exact output](../../research/audit/pbeta_exact_sos.json), produced and checked by the search-audit agent. This finding prevents falsely proposing “leave direct SOS to reach P₂” as the next route.

## Numerical implication and proposed priority

The current `base_min` drops eigenvalues below `1e−13`. For a PSD base Hessian with eigenpair `(λ,w)`, deleting a positive λ loses the possible decrease `(w·h)²/λ`. This makes the computed value an upper approximation to the unrestricted base minimum. It does not fabricate a negative witness, but it can mask a small negative one. The ten 60-digit checks validate selected final fields, not all near-degenerate trajectories.

Do not interpret the repeated numerical floor near 2 as a theorem. Either attack the universal scalar inequality above, or explicitly test a controlled asymptotic family with `α→0` and the exact optimal base retained; avoid merely increasing grid sizes or restarts. The all-field inequality is a sharply defined family-level gate, with either outcome mathematically meaningful. It is not a claim that this is the most likely route to a full Morrey solution.

For the unrestricted problem, the audit supports the completion audit's broader conclusion: retain H19–H25 as valid restricted results and route exclusions, but prioritize a global certificate-complete negative search or a genuinely all-gradient positive representation. Finishing their Lean translations alone will not close the central gap.
