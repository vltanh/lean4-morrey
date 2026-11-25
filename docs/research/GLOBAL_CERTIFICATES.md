# Audit of the global reductions: a complete certificate hierarchy and a compactness correction

**Scope.** Mathematical audit of H07–H12 and the current polynomial certificate search. This is a hand argument using an external rational Positivstellensatz, not a new Lean proof and not a proof or counterexample to Morrey. No optimization campaign was run. The audited search snapshot is PR head `e7a8fd05d8e2631be97d2259ac8356b0786e93f6`; the formal baseline is updated separately in [FORMAL_STATUS.md](README.md#formal-status). The exact certificate interface is implemented in [research/audit](../../research/audit/README.md).

## Findings

1. The rational-polynomial/dyadic reduction H07 is sound as a hand proof after its standard smooth/Lipschitz approximation steps are made explicit. Its global radial stabilization genuinely controls the Hessian outside the approximation ball. It does not provide a uniform degree or mesh bound.
2. The current unweighted LH-SOS class is only the zeroth level of a **complete hierarchy for negative witnesses**. Homogenization and norm multipliers remove this certificate-class restriction. If Morrey is false, some rational counterexample has a finite rational certificate in the hierarchy described below.
3. H12 unnecessarily asks for a compatible all-degree family and additional support control. Arbitrary finite positive Hessian certificates at every degree suffice: degree two fixes mass, radial fourth powers imply tightness, and higher radial moments force the limiting support into the convex hull of the original law. Universal finite-degree feasibility remains unproved.
4. A second computational route is to certify LH positivity only on a ball containing a genuine negative gradient witness, then add an explicitly bounded radial polynomial. A strict local-on-ball counterexample suffices for a global one; the tail can be chosen after discovery.

These are upgrades of the reduction/certificate interface. They remove unnecessary restrictions but do not supply the missing integrand/gradient pair or the universal positive representation.

## 1. Audit of the existing reductions

### H07: polynomial approximation

Write a polynomial as `P₀(A)=Σ c_α A^α` and let `d=deg P₀`, `k=max(d−2,0)`. For any rational `R>0`, the explicit rational bound

$$
M=\sum_{|\alpha|\ge2}|c_\alpha|\,|\alpha|(|\alpha|-1)R^{|\alpha|-2}
$$

satisfies

$$
|D^2P_0(A)[H,H]|\le M(|A|/R)^k|H|^2\qquad(|A|\ge R).
$$

This follows by differentiating each monomial, bounding its remaining entries by `|A|`, each direction entry by `|H|`, and using `|A|/R≥1`. Thus the archived radial stabilizer

$$
Q_m(A)=\frac{(M+1)R^2}{2m}\left(\frac{|A|^2}{R^2}\right)^m,
\qquad 2m-2\ge k,
$$

has Hessian at least `(M+1)(|A|/R)^(2m−2)|H|²`, so `P₀+Q_m` has positive full Hessian outside the ball. Inside, the stabilizer is convex and preserves any strict rank-one Hessian margin. On a smaller ball of radius `r<R`, its magnitude is at most `((M+1)R²/(2m))(r/R)^(2m)`, which tends to zero. There is no omitted annulus where the argument loses control.

The remaining formal work is to assemble the available finite-valued RC regularity and periodic Lipschitz/domain equivalence with mollification, rational `C²` polynomial approximation, radial stabilization and the dyadic interpolation argument; [FORMAL_STATUS.md](README.md#formal-status) lists the existing bridges. A Lipschitz witness should be smoothed with bounded gradients and almost-everywhere or finite-`p` gradient convergence; **uniform gradient convergence of arbitrary Lipschitz maps is not required and should not be asserted**. The archived uniform interpolation estimate is valid for the already-smoothed map.

### H10–H11: duality

The split-defect cone/bipolar statement is correct for continuous RC functions on the stated ball. The local-to-global passage works with a buffer: contract into the original ball, mollify on a slightly larger domain, then use the same radial stabilization.

The fixed-degree Hessian conic duality is correct for `d≥2` and a closed ball with nonempty interior. Unit rank-one directions are compact; evaluation at `|A|²/2` normalizes every generator to one and makes the cone closed. The annihilator is exactly affine functions plus determinant, hence the dimension `binomial(d+4,4)−6`. This is a theorem about polynomials with LH nonnegative **on that ball**, not the globally RC cone of the same degree. Local-to-global extension can increase degree.

A finite-dimensional dual certificate may initially have real algebraic/real atoms and weights. Rationality of arbitrary boundary certificates does not follow merely from rational moment data. The existing explicitly rational certificate is valid on its own; it should not be generalized to all feasible moment vectors without another argument.

## 2. A complete norm-multiplier hierarchy for negative witnesses

### 2.1 Certificate interface

Let `P∈Q[A₁₁,A₁₂,A₂₁,A₂₂]` have degree at most `2m`, with `m≥2`. Put

$$
L_P(A,a,b)=D^2P(A)[a\otimes b,a\otimes b].
$$

Introduce `x=(t,A)∈R⁵` and homogenize in the **base-matrix variables only**:

$$
F_P(t,A,a,b)=t^{2m-2}L_P(A/t,a,b),
$$

interpreted by polynomial expansion also at `t=0`. Its separate homogeneous degrees in `(x,a,b)` are `(2m−2,2,2)`. Define

$$
N_x=t^2+|A|^2,\qquad N_a=|a|^2,\qquad N_b=|b|^2,
\qquad W=N_x^{m-1}N_aN_b.
$$

A sufficient exact certificate is a rational `δ>0`, an integer `k≥0`, and rational polynomials `q_j` satisfying

$$
\boxed{(N_xN_aN_b)^k\bigl(F_P-\delta W\bigr)=\sum_jq_j^2.}\tag{C}
$$

Each `q_j` can be required multihomogeneous of degrees `(m−1+k,1+k,1+k)`. Equivalently, use that full monomial vector and a rational PSD Gram matrix, verified by exact coefficient matching and exact PSD factorization.

**Soundness.** For `t=1` and nonzero `a,b`, the multiplier is strictly positive. Divide (C) to obtain

$$
L_P(A,a,b)\ge\delta(1+|A|^2)^{m-1}|a|^2|b|^2.
$$

The zero-direction cases vanish identically. Therefore the rank-one Hessian is globally nonnegative, and integration on each rank-one line proves global rank-one convexity. No numerical sampling of `A`, `a` or `b` is involved.

For quartics the full Gram sizes are 20 at `k=0`, 135 at `k=1`, and 560 at `k=2`; for degree six they are 60 and 315 at the first two levels. In general the size is

$$
\binom{m+k+3}{4}(k+2)^2.
$$

At `k=0`, dehomogenizing `t=1` recovers the existing unweighted LH-SOS basis. Increasing `k` changes the certificate class, not just the number of optimizer starts.

### 2.2 Why every strict compactified LH form eventually has such a certificate

Consider the product of spheres

$$
K=\{N_x=N_a=N_b=1\}=S^4\times S^1\times S^1.
$$

Suppose `F_P−δW>0` on `K`. All coefficients are rational. Use the rational generators

$$
1-N_x,\ N_x-1,\ 1-N_a,\ N_a-1,\ 1-N_b,\ N_b-1,
\quad 3-N_x-N_a-N_b.
$$

The last is an explicit ball generator, so the hypotheses of Powers' rational version of Putinar's theorem hold. Consequently, on `K`, `F_P−δW` is a sum of squares of rational polynomials; off `K` there are polynomial multiples of the sphere equations. This use of the ball generator avoids any unsupported assumption that an arbitrary real SOS representation has rational coefficients.

The following elementary homogenization step turns the sphere identity into (C):

1. Average the squared-polynomial representation over independent sign changes of the three variable blocks. Since `F_P−δW` is even in each block, it remains unchanged. Orthogonality of the eight sign characters splits each square into squares of its rational parity components. Each resulting polynomial has fixed degree parity in each block.
2. Homogenize each parity component separately in the three blocks by multiplying its lower-degree monomials by integer powers of `N_x,N_a,N_b`. These powers are integral because the degree parities agree. The values on `K` are unchanged.
3. Choose common half-degrees at least as large as the block degrees of every homogenized component and the target half-degrees `(m−1,1,1)`. Multiplying each square by the required powers of the `N`'s preserves the SOS property: each norm power is itself a rational SOS.
4. Both sides are now multihomogeneous of the same block degrees and agree on the product of unit spheres. Scaling every nonzero block to unit norm shows they agree on the open set where all blocks are nonzero; therefore they are identical polynomials. The left-hand side is `N_x^r N_a^s N_b^v(F_P−δW)` for some nonnegative integers `r,s,v`.
5. Choose `k=max(r,s,v)` and multiply by the remaining norm powers. This gives exactly (C).

Thus some finite common multiplier order exists. There is **no uniform bound on that order in this argument**.

### 2.3 Strictification preserves any actual counterexample

Suppose a rational globally RC polynomial `P` and a rational dyadic witness have exact gap `J_P=−Δ<0`. Choose `2m≥deg P`, `m≥2`, and set

$$
R(A)=|A|^2+|A|^{2m},\qquad S=J_R\ge0,
\quad \varepsilon=\frac{\Delta}{4(1+S)},\quad \widetilde P=P+\varepsilon R.
$$

Convexity of `R` and the correct mean gradient give `S≥0`. All values are rational, and

$$
J_{\widetilde P}=-\Delta+\varepsilon S\le-3\Delta/4<0.
$$

The homogenized LH of `P` is nonnegative on `K`: this follows from global RC for `t≠0`, and from continuity for `t=0`. For unit `a,b`, the radial polynomial satisfies

$$
F_R=2t^{2m-2}+2m|A|^{2m-2}
+4m(m-1)|A|^{2m-4}(A:(a\otimes b))^2
\ge 2^{3-m}\quad\text{on }K.
$$

Indeed, `t²+|A|²=1` and `z^(m−1)+(1−z)^(m−1)≥2^(2−m)`. Choose

$$
\delta=\varepsilon\,2^{2-m}>0.
$$

Then `F_Ṕ−δW` is strictly positive on `K`, including the points at infinity `t=0`. The argument of §2.2 gives a rational certificate (C) for `Ṕ` at some finite `k`.

### 2.4 Completeness statement and its limits

Combining H07 with §§2.1–2.3 gives the following valid hand theorem:

> If the finite-valued planar Morrey implication is false, there exist a rational polynomial `P`, a rational base, rational nodal data on some dyadic periodic triangulation, a rational `δ>0`, a finite multiplier order `k`, and a rational certificate (C), such that the exact Jensen gap is strictly negative.

The converse follows from certificate soundness and the admissible witness. Consequently, dovetailing over polynomial degree, dyadic level, rational coefficient heights and multiplier order gives a complete negative-witness enumeration using exact algebraic checks. This replaces general quantifier elimination with a specific sufficient certificate hierarchy that is complete **after a gap-preserving perturbation**.

It is not a finite decision procedure for the positive answer. It gives no useful worst-case bound on degree, mesh, coefficient height, multiplier order or runtime. Ordinary alternating optimization is still not exhaustive even after its certificate class is enlarged. A fixed Gram eigenvalue floor after trace normalization, or a permanently enforced field-covariance barrier, remains an additional restriction and must not be included in a completeness claim. A hierarchy should let artificial margins tend to zero and remove any field exclusion.

The result is an application of established real-algebraic positivity, not a novelty claim for Putinar-type methods.

## 3. A cheaper alternative: local certificates followed by a global radial tail

This is an alternative search architecture, not a second requirement for §2.

Take a rational polynomial `P₀`, a rational actual gradient witness with `J_(P₀)=−Δ<0`, and radii `0<r<R` containing the base and every perturbed gradient in `B_r`. Suppose a finite exact certificate proves

$$
D^2P_0(A)[a\otimes b,a\otimes b]\ge\eta|a|^2|b|^2
\quad (|A|\le R)
$$

for rational `η>0`. For example, on `B_R×S¹×S¹`, one may certify

$$
L_{P_0}-\eta=\sigma_0+\sigma_A(R^2-|A|^2)
+\tau_a(1-N_a)+\tau_b(1-N_b),
$$

with rational SOS `σ₀,σ_A` and arbitrary rational polynomial `τ_a,τ_b`; an explicit redundant ball generator can be included for rational Positivstellensatz completeness. A strict local LH margin ensures a finite-order representation for a smaller chosen rational `η`, so that `L_(P₀)−η` remains strictly positive on the constraint set.

Use the coefficient bound `M` from §1 and choose `m` with `2m−2≥max(deg P₀−2,0)` and

$$
\frac{(M+1)R^2}{2m}(r/R)^{2m}<\Delta/2.
$$

Then `P=P₀+Q_m` is globally strongly RC and

$$
J_P\le J_{P_0}+\sup_{B_r}Q_m< -\Delta/2.
$$

The subtraction of `Q_m(F)≥0` only improves this bound. Every quantity is rational, and an integer `m` satisfying the inequality exists because `r/R<1`. This route allows the discovery polynomial to fail RC far from the observed gradient range; the extension supplies a certified global integrand afterwards. It removes a legitimate search restriction while keeping the final problem unchanged.

## 4. Correct compactness theorem for positive certificates

Let `ν` be a compactly supported probability measure on `R^(2×2)`, with barycenter `F`. Let `R₁={H:rank H=1, |H|=1}`. Suppose that, for every integer `d≥2`, some finite positive measure `μ_d` on `R⁴×R₁` satisfies

$$
\int P\,d\nu-P(F)=\int D^2P(B)[H,H]\,d\mu_d(B,H)
\quad(\deg P\le d).
\tag{H_d}
$$

The measures need not be compatible, and their supports need not be uniformly bounded in advance. Then there is a finite positive measure `μ` supported on
`conv(supp ν)×R₁` representing the same Jensen functional for every `C²` function on a neighborhood of that convex hull.

**Proof.**

1. Taking `P(A)=|A|²/2` shows that every `μ_d` has the same finite mass
   `M=(∫|A|²dν−|F|²)/2`. If `M=0`, `ν=δ_F` and the zero measure works.
2. For `d≥4`, taking `P(A)=|A|⁴` and using `D²P(B)[H,H]≥4|B|²` gives a uniform second-moment bound. Together with compactness of `R₁`, this gives tightness. Extract a weakly convergent subsequence `μ_(d_j)→μ`, with `d_j→∞`; the total mass is preserved.
3. More generally, for every center `C` and integer `k≥1`, the radial test gives, for `d≥2k`,
   $$
   2k\int|B-C|^{2k-2}\,d\mu_d
   \le \int|A-C|^{2k}\,d\nu-|F-C|^{2k}
   \le R_C^{2k},
   $$
   where `R_C=max_{A∈suppν}|A−C|`. Portmanteau passes this upper bound to `μ`.
4. For any `s>R_C`, Markov's inequality gives
   `μ{|B−C|≥s}≤R_C^(2k)/(2k s^(2k−2))→0`. Hence `μ` is supported in every closed ball containing `suppν`. Their intersection is the closed convex hull. It suffices first to use a countable dense set of centers, avoiding an uncountable intersection of exceptional null sets.
5. To pass `(H_d)` to a fixed polynomial `P`, choose a higher radial even power than the growth degree of `D²P`. Its uniform moment bound gives uniform integrability of `D²P(B)[H,H]`; weak convergence with cutoffs then passes the identity. Thus `μ` matches every polynomial.
6. Since both the original law and `μ` now have compact support, polynomial approximation in `C²` on an enclosing ball passes the identity to arbitrary `C²` functions. A function only defined near the convex hull can first be extended as a `C²` function to that ball using a cutoff that is one near the hull.

Therefore the extra compatibility/support gate in the ledger is unnecessary for **exact positive certificates** satisfying `(H_d)`. This does not justify passing from arbitrary small-residual floating certificates: an approximate hierarchy needs quantitative control of mass, high radial moments and errors. And the key assertion that `(H_d)` is feasible for every degree and every genuine planar gradient law remains exactly the unresolved positive direction.

## 5. Recommended next steps

- **Completed in this audit:** H12 now states the exact radial-moment compactness lemma without a separate inter-degree compatibility condition. Universal certificate feasibility remains open.
- **Completed in this audit:** the exact verifier accepts (C) in weighted-square form and a control exercises `k=1`. The [audit package](../../research/audit/README.md) also supplies the Gram-basis builder. Weighted-Gram discovery, exact PSD extraction and integration with a field optimizer remain to implement.
- Before another search campaign, audit the `k=1` class with a fixed small budget and an independently evaluated actual gradient. The reason to do this is new certificate freedom, not a claim that quartics or a fixed grid are complete.
- If the direct weighted hierarchy is too expensive, use local-ball certificate discovery with the explicit radial tail of §3. Do not confuse local positivity alone with the finished global integrand.
- Keep the positive route focused on constructing `(H_d)` uniformly for all gradients/degrees, or a direct all-test-function representation. More certificates for isolated laws do not discharge that task.

## 6. Independent audit of the new exact certificate verifier

The scratch implementation `audit_search_work/sphere_certificate.py` and its two controls were independently checked after this note was drafted. No soundness issue was found. The homogenization exponent `D−|α|` gives total base degree `D−2`; the tensor direction uses row/column indices correctly. Both sphere-ideal and norm-multiplier identities give the coercive global LH bound in §2.1. The nodal witness gradients are exactly those of a continuous periodic affine map on the two equal-area triangles of each grid square, with the correct factor equal to the grid size.

An independent exact test expanded `P(A+λH)` to second order for a polynomial containing mixed cubic and sextic terms, and matched the verifier's homogenization for positive and negative `t` and at `t=0`. Both supplied positive controls passed. These checks validate the certificate algebra and witness realization; the controls do not establish that a searched cone is strictly larger or discover a negative witness.

## Primary sources checked

- Victoria Powers, *Rational Certificates of Positivity on Compact Semialgebraic Sets*, author manuscript dated 3 February 2011, §3 Theorem 6: https://www.math.emory.edu/~vicki/pub/rationalreps.pdf . The published numbering differs; use the version stated. This is the rational Positivstellensatz input in §2.2.
- Victor Magron, *Convergence rates for polynomial optimization on set products*, arXiv:2505.18580v4 (3 June 2026): https://arxiv.org/abs/2505.18580v4 . Its sphere-product hierarchy is relevant prior work; its convergence-rate conclusions are not needed for the proof above and do not bound the unknown Morrey witness degree or mesh.
