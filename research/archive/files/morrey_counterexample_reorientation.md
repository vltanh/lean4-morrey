# Morrey 2×2: counterexample-first reorientation (2026-11-21)

## Status

No rank-one-convex, non-quasiconvex integrand on `R^{2×2}` has been found in this investigation. The `2×2` Morrey problem remains open. Negative numerical gaps from *sampled* rank-one convexity constraints were rejected by a global Hessian test.

## Theorem: every planar affine pullback of a quadratic-minor norm is polyconvex

Let `W` be a real vector space, let `Q` be a quadratic form on `Λ²W` satisfying `Q(x∧y)≥0` for every `x,y∈W`, and set

    G(X)=sqrt(Q(X_1∧X_2)),  X∈R^{2×dim W}.

Then for **every** `M,B∈R^{2×dim W}`, the function

    f(A)=G(M+A B),    A∈R^{2×2},

is **globally polyconvex**. This is independent of the number of columns of `W`.

Proof. Let `V` be the span of the four row vectors `m_1,m_2,b_1,b_2` of `M,B`, so `dim V≤4`. If `dim V≤3`, all bivectors in `Λ²V` are decomposable and `Q|_{Λ²V}` is positive semidefinite. If `dim V=4`, decomposable bivectors are exactly the zero set of the one Plücker quadratic form `J(ω)=ω∧ω`. The Finsler–Thorpe lemma (homogeneous S-lemma with equality) says that a quadratic form nonnegative when `J=0` has `Q+λJ≥0` for some `λ∈R`. Consequently in all cases there is a positive semidefinite quadratic form `Qtilde` on `Λ²V` coinciding with `Q` on decomposable bivectors.

Writing `A=[[a,b],[c,d]]`, the identity

    (M+AB)_1∧(M+AB)_2
      = m_1∧m_2 + c m_1∧b_1 + d m_1∧b_2
        - a m_2∧b_1 - b m_2∧b_2 + (ad-bc) b_1∧b_2

shows that the bivector is affine in `(a,b,c,d,det A)`. Since `sqrt(Qtilde(ω))` is a convex seminorm of ω, `f(A)` is a convex function of `(A,det A)`, i.e. polyconvex. QED.

The Finsler–Thorpe lemma is a classical result, not a new theorem. Reference: Bettiol–Krishnan, *Ricci flow does not preserve positive sectional curvature in dimension four* (2023), Proposition 2.2, https://link.springer.com/article/10.1007/s00526-022-02335-z.

### Application to the Agazzi–Bruno–Guerra–Pasqualotto 2×6 energy

Write the rows of X as `(u,v),(s,t)` with `u,v,s,t∈R³`. The energy in arXiv:2608.12298 is

    G(X)² = |u|²|t|² + |s|²|v|² - 2(u·s)(v·t)
             - 2(u·v)(s·t) + 2(u·t)(s·v).

It has the exact bivector form

    G(X)² = sum_{i,j=1}³ (u_i t_j - s_i v_j)²
               - 2 (u×s)·(v×t).

All terms are quadratic in the entries of the bivector `X_1∧X_2`. Its nonnegativity on decomposable bivectors follows from the nonnegative energy (or directly from the two singular values of `u t^T - s v^T`). Thus **every** function `A↦G(M+AB)` with `M,B∈R^{2×6}` is polyconvex on `R^{2×2}`. No choice of input embedding, reference matrix, amplitude, or periodic test map can produce a Morrey counterexample from this G by *affine planar pullback*.

### Exact symbolic double checks on acoustically degenerate families

With `M=[[−2,0,0,0,0,0],[0,0,0,−2,0,0]]`:

* The ten-parameter *common image* family `B=[[p,m1*w1,m1*w2,r,n1*w1,n1*w2],[q,m2*w1,m2*w2,s,n2*w1,n2*w2]]` has an identity `G(M+AB)² = L(A,det A)² + (w1²+w2²) K(A,det A)²`, where L,K are explicitly affine in `(A,det A)`. Verified by symbolic expansion (zero polynomial remainder) in `morrey_grabovsky_pencil_identity.py`.
* The *common kernel* family `B=[[p,m1,m2,r,λ*m1,λ*m2],[q,n1,n2,s,λ*n1,λ*n2]]` has an exact three-square identity in affine minor functions. Verified by zero polynomial remainder in `morrey_grabovsky_common_kernel_identity.py`.
* For general B, a random 15-case numerical PSD-Gram feasibility test succeeded (maximum reported negative eigenvalues approximately 4e-8 due to floating point). This is **not** the mathematical proof; the Finsler–Thorpe lemma above supplies the proof for all B.

## Other searches

1. Rank-one-convexity imposed at finitely many samples on candidate quartic polynomials produced negative approximate Jensen gaps, but every negative candidate checked failed a separate rank-one Hessian test. One exact rational Hessian witness is in `morrey_false_quartic_exact_witness.py`. The corrected exchange search made the negative gaps disappear.
2. A 2×3 quartic from Gabriele Cassese's Lean-checked 2026 construction, `hδ = q + δ(L+ (22/δ)² P)²`, has *globally* rank-one-convex planar pullbacks `A↦hδ(M+AB)` (the composition of a rank-one convex integrand with a rank-one-preserving affine map). Direct multistart searches with δ=1, five Fourier wave directions, and both zero and nonzero base matrices found no negative Jensen gap. These are numerical tests only. The exact polynomial comes from `Morrey2x3.lean` in https://github.com/Gabriele-Cassese/MorreyTwoComponentsLean.
3. These experiments do not prove the 2×2 Morrey conjecture. They do show that the tested *known higher-dimensional counterexamples* do not immediately descend to a 2×2 counterexample by our affine pullback search.

## What a decisive counterexample must contain

A fully verifiable negative resolution needs (i) an explicit continuous globally rank-one-convex `f:R^{2×2}→R`, (ii) a base `F`, and (iii) a smooth periodic or zero-boundary gradient `Du`, with a **strictly negative** Jensen gap. For polynomial `f`, this could be an exact rational global sum-of-squares/quantifier-elimination certificate for `D² f(A)[a⊗b,a⊗b]≥0`, together with an exact rational dyadic gradient witness and strict negative energy. The search has produced no such pair.

Future work should prioritize the joint search of *new* globally rank-one-convex functions and two-dimensional curl-free gradient fields, not changing grid sizes or Fourier modes within the excluded quaternionic pullback family. A verified counterexample would be a breakthrough; none is claimed here.
