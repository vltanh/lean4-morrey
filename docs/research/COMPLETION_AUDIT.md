# Audit: what can move the planar problem toward completion

**Audit date: 21 November 2026. The planar problem remains unresolved.** This audit
identifies two removable search restrictions, supplies a complete certificate hierarchy for
negative witnesses, and removes an unnecessary compactness condition from the positive route.
It does not produce a planar counterexample or prove the missing universal feasibility theorem.

The source baseline is upstream `cde348ba320b65d902c9f0f782f392e932ba507c`, including the
Cassese merge, combined with the research recorded in PR head
`e7a8fd05d8e2631be97d2259ac8356b0786e93f6`. The audit reads code and mathematical arguments,
adds exact replayable checks, and preserves the original research payloads. It is AI-assisted
review; no independent human review or new Lean proof is claimed.

## 1. Findings ranked by their effect on the next step

| Finding | Consequence | Evidence |
| --- | --- | --- |
| Several base minimizers discard eigenvalues below a cutoff. They do not always check whether the linear term has a component in the discarded space. | A reported optimized gap can miss an arbitrarily large negative correction, or an objective unbounded below. Retain exact/range-sensitive base diagnostics before interpreting new searches. No saved missed counterexample has been established. | A01; [code audit](PIPELINE_AUDIT.md), exact quadratic controls. |
| The sharp quartic `P₂` has an exact ten-square LH identity, but no positive-definite Gram in the current full basis. | Direct SOS already contains this endpoint. The fixed positive Gram margin excludes it. A boundary-capable search is a genuinely changed hypothesis; more starts with the same margin are not. | A02; [identity](../../research/audit/pbeta_exact_sos.json), [checker](../../research/audit/pbeta_exact_sos.py). |
| Norm multipliers on the homogenized LH polynomial give a complete hierarchy after a gap-preserving strict perturbation. | There is a precise certificate format that can represent some negative witness whenever one exists. Completeness requires allowing degree, mesh, rational heights and multiplier order to grow. | A03; [global certificate proof](GLOBAL_CERTIFICATES.md#2-a-complete-norm-multiplier-hierarchy-for-negative-witnesses). |
| Exact positive Hessian representations at every degree automatically have a compatible compactly supported limit. | The positive route has one central unresolved gate: prove universal finite-degree feasibility. Extra consistency and tightness assumptions need not be imposed on the exact certificates. | A04; [radial-moment proof](GLOBAL_CERTIFICATES.md#4-correct-compactness-theorem-for-positive-certificates). |
| Main now contains Cassese's `2 × 3` quartic and general periodic Lipschitz/domain bridges. | Do not spend the next stage rebuilding this infrastructure. Connect a future planar candidate to the existing definitions. | F12–F15; [formal baseline](FORMAL_STATUS.md). |
| The structural exclusions H19–H25 survive the hand audit with their stated hypotheses. | Retire those restricted routes unless a new construction leaves their scope. Their Lean translations would not resolve unrestricted Morrey. | A06; [structural audit](STRUCTURAL_AUDIT.md). |

## 2. The concrete numerical issue

For a fixed field, the relevant quartic searches minimize

`J(F) = c + 2 hᵀF + FᵀKF`, with `K` positive semidefinite for the intended valid inputs.

There are two different cases. If `h` is orthogonal to `ker K`, the minimum is
`c − hᵀK†h`. Otherwise the objective is unbounded below along a kernel direction. Even in the
first case, deleting a small positive eigenvalue `λ` deletes the decrease `(h·w)²/λ`.

The new exact checker verifies all principal minors, computes the kernel/range condition, and
solves the rational linear equations without an eigenvalue cutoff. Its regression controls give:

| Input | Exact conclusion |
| --- | --- |
| `K = diag(1,0)`, `h = (0,1)`, `c = 1` | Unbounded below; the returned finite base already has gap `−1`. |
| `K = diag(1,10⁻¹⁴)`, `h = (0,10⁻⁶)`, `c = 1` | Minimum `−99`, which a `10⁻¹³` cutoff misses. |
| `K = diag(1,0)`, `h = (1,0)`, `c = 2` | Safe singular minimum `1`. |

These are quadratic regression examples, **not actual-gradient counterexamples**. The checker is
new validation infrastructure; the frozen discovery scripts were not silently rewritten or all
their trajectories rerun. Integration into a new search driver remains an explicit roadmap task.

## 3. The strongest unrestricted computational route

For a rational polynomial `P` of degree at most `2m`, homogenize its rank-one Hessian to
`F_P(t,A,a,b)`. Write `Nₓ = t² + |A|²`, `Nₐ = |a|²`, `Nᵦ = |b|²`. The proposed exact format is

$$
(N_xN_aN_b)^k\bigl(F_P-\delta N_x^{m-1}N_aN_b\bigr)=\sum_j q_j^2,
\qquad \delta\in\mathbb Q_{>0}.
$$

This polynomial identity proves global rank-one convexity. The [proof](GLOBAL_CERTIFICATES.md)
uses rational Putinar certificates on a product of spheres, followed by block homogenization.
A small radial perturbation preserves a strict negative Jensen gap and makes the compactified
LH form positive even at infinity. Combined with the existing polynomial/dyadic reduction, it
establishes that **if the planar implication is false, some rational witness has this finite
certificate**. This is an application of established positivity theorems, not a novelty claim.

The implementation checks both a sphere-ideal format and the norm-multiplier identity using
exact rational arithmetic. It constructs the periodic piecewise affine field from nodal data
and evaluates the exact Jensen gap. A nonconvex rank-one-convex control and corrupted identities
exercise both certificate formats. Neither valid LH/gradient control has a negative Jensen gap.

This does not make alternating optimization exhaustive. There is no justified maximum degree,
mesh size, coefficient height or multiplier order. A full enumeration is a negative
semidecision procedure, with no termination guarantee when the implication is true. Practical
searches should use bounded stages and retain the acceptance certificate independently of the
solver. Quartic order one has a 135-dimensional Gram basis, compared with 20 at order zero.

An alternative is to search for a strict local LH certificate on a ball containing the actual
gradient range. The explicit radial tail in [the same proof](GLOBAL_CERTIFICATES.md#3-a-cheaper-alternative-local-certificates-followed-by-a-global-radial-tail)
then supplies global RC while preserving the negative gap. Local positivity alone is not the
final certificate.

## 4. What remains on the positive route

For each compact gradient law `ν` with mean `F`, the unresolved task is to construct, for
**every degree**, a positive measure representing

`∫P dν − P(F) = ∫ D²P(B)[H,H] dμ(B,H)`, where `rank H = 1` and `|H| = 1`.

The new compactness argument shows that exact finite-degree measures need not be chosen
consistently. The quadratic test fixes their mass; fourth powers give tightness; higher radial
moments control the tails and force a limiting support inside `conv(supp ν)`. Polynomial
approximation then gives the all-test-function identity.

This removes a secondary technical gate. It does **not** prove existence of the finite-degree
measures, nor justify limits of arbitrary floating solutions. Universal feasibility is still
the global mathematical problem. More certificates for isolated laws do not close it.

## 5. A subordinate analytic benchmark

The whole family
`Pβ = (ad−2bc)² + β(b²+c²+d²)²`, `β≥2`, reduces to `P₂`. Bases with `F₂₂=0` are covered by
flat-line support; homogeneity normalizes all other bases to `F₂₂=1`. For every actual periodic
field the remaining first base entry `M` can be eliminated exactly:

`J = αM² + 2hM + C₂`, so `min J = C₂ − h²/α` when `α = ⟨v_y²⟩ > 0`.

The [structural audit](STRUCTURAL_AUDIT.md) specifies every term and proves the `α=0` case by
two rank-one-plane Jensen steps. The unresolved inequality `αC₂≥h²` is global in fields.
Its proof would close this family; a strict failure would give a planar counterexample. This
benchmark does not replace the unrestricted certificate route or justify further unstructured
restarts. The near-degenerate limit is relevant because the optimal base can diverge.

## 6. Next work with explicit completion conditions

1. **Integrate exact base recovery into a new driver.** Preserve kernel directions, remove the
   fixed Gram eigenvalue floor, and make covariance penalties optional. Verify reconstructed
   rational candidates by the standalone checker. Stop treating a cutoff minimum as exhaustive.
2. **Run one bounded comparison that changes the certificate freedom.** Compare order zero
   with order one on the same actual-gradient inputs, or use a local-ball certificate with its
   radial extension. Record the precise budget, invalid outputs and actual unpenalized gap.
   A null result does not exclude higher degrees, grids or orders.
3. **Escalate a strict negative immediately.** Require an exact global LH identity, an actual
   periodic map, and an exact negative integral for the same rational polynomial. Reuse the
   existing periodic Lipschitz equivalence for the final quasiconvexity statement.
4. **Keep the positive alternative focused on universal feasibility.** An all-degree
   construction or direct Jensen inequality can complete it; another local grid lemma cannot.
5. **Only then claim closure.** Formalize the actual global theorem or witness, run Lean and
   the axiom audit, verify the definitions, and obtain independent mathematical review.

The full [roadmap](ROADMAP.md) records the two alternative endpoints. Passing code checks or
closing the benchmark family alone is not completion of the planar problem.
