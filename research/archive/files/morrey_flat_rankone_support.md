# Morrey 2×2: Global support at a flat rank-one line

**Status:** Hand proof, not a proof of unrestricted Morrey. Verified the exact algebra of the decomposition with `morrey_rankone_zero_global_check.py`. Potential prior-work overlap has **not** been excluded.

## Main theorem (no polynomial or homogeneity restriction)

Let `f : R^(2×2) -> R` be `C²` and globally rank-one convex. Suppose there are `F` and a nonzero rank-one `B` such that `t -> f(F+tB)` is affine on **all of R**. Then there exists `c ∈ R` with, for every matrix `X`,

    f(F+X) ≥ f(F) + Df(F)[X] + c det(X).                (1)

Consequently, `f` is **polyconvex at F** (it has a global affine support in `(X,det X)`) and thus quasiconvex at `F`. In fact, (1) holds with `F` replaced by any point on the flat line `F+tB`, with the appropriate first derivative and constant.

The theorem applies to arbitrary `C²` integrands; it has no degree, periodic-grid, mold, or Fourier-mode bound.

### Proof

Subtract the affine function `f(F)+Df(F)[X]` and translate by `F`, obtaining `g(X)` with `g(0)=0`, `Dg(0)=0`, and `g(tB)=0` for every real `t`. Composing with invertible left and right changes of coordinates preserves rank-one convexity, zero-line flatness, and the desired determinant support, up to multiplying `c` by a nonzero constant. Thus suppose `B=E11` and write `X=[[a,b],[c,d]]`.

**Lemma (separate convexity).** If `h:R²->R` is `C¹`, separately convex, and `h(x,0)=0` for every `x`, then `k(x)=∂_y h(x,0)` is affine in `x`, and `h(x,y)≥y k(x)` for every `x,y`.

Indeed, `h(x,y)/y` is convex in `x` when `y>0`, and concave when `y<0`. As `y→0` from the two sides, both converge to `k(x)`, making `k` both convex and concave, hence affine. The lower bound is simply the supporting-line inequality for the convex function `y->h(x,y)` at `y=0`.

**Hessian normality.** Write `Q(H,K)=D²g(0)[H,K]`. Rank-one convexity gives `Q(H,H)≥0` for rank-one `H`. Since `g(t E11)=0`, `Q(E11,E11)=0`. The rank-one curves `E11+ε E12` and `E11+ε E21` imply that the corresponding rank-one Hessian quadratics have their minima at `ε=0`, so `Q(E11,E12)=Q(E11,E21)=0`. Therefore for **every** matrix `H`,

    Q(E11,H) = κ H22,       κ = Q(E11,E22).           (2)

Now let `X=[[a,b],[c,d]]` with `d≠0`. Define

    x=a-bc/d,    y=d,
    H=[[bc/d², b/d],[c/d,1]] = (b/d,1)⊗(c/d,1).

The matrix `H` has rank one and `X=x E11+y H`. Also `det X=xy`. Consider `h(s,t)=g(s E11+tH)`. It is separately convex, `h(s,0)=0`, and `∂_t h(0,0)=Dg(0)[H]=0`. By the lemma its derivative along `t=0` is `sκ` because its slope equals `Q(E11,H)=κ` by (2). Hence

    g(X)=h(x,y) ≥ κxy = κ det X.

The set of matrices with `d≠0` is dense; by continuity the inequality extends to all `X`. Undo the initial linear changes of coordinates and the affine subtraction to obtain (1).

Finally, for any smooth compactly supported perturbation `u`, integration gives

    ∫ f(F+Du) ≥ |Ω| f(F) + Df(F)[∫ Du] + c∫ det Du
                = |Ω| f(F)

because the two last integrals vanish by the divergence theorem and the determinant null-Lagrangian identity. This is the quasiconvexity inequality at `F`. QED.

### Consequence: homogeneous rank-one zero

Let `P` be any globally rank-one-convex **homogeneous polynomial of degree at least four** on `R^(2×2)`, and suppose `P(B)=0` for some nonzero rank-one matrix `B`. Homogeneity makes `P(tB)=0` for all `t`. Since `DP(0)=0` and `D²P(0)=0` at degree ≥4, equation (1) gives

    P(A)≥0 for every A.

Therefore `P` satisfies the quasiconvex Jensen inequality at the origin for **every** gradient law (not just dyadic ones). The same conclusion holds for any `C²` even positively `p`-homogeneous rank-one-convex integrand with `p>2`, whose entire line through `B` is zero.

The degree-two exception is essential: `P(A)=det A` is rank-one affine, vanishes on *every* rank-one matrix, and changes sign. Its support has `κ=1`, not zero.

### Scope and next genuinely unresolved gate

The existence of a flat **entire rank-one line** is an essential restriction. For example, the Dacorogna–Marcellini quartic `|A|⁴−(9/4)|A|² det A` is rank-one convex, but on every nonzero rank-one line its quartic leading coefficient is `|B|⁴>0`, so no such line is affine. It can also be negative at some full-rank matrices, even though its quasiconvexity was proved in 2026.

Thus the theorem **does not** show the full quartic cone is quasiconvex. The difficult portion is integrands with no flat rank-one line; precisely those are not reached by this argument. This avoids another level-by-level finite classification but does not repair Pedregal's Proposition 7.1.

## Exact verification

Run `python morrey_rankone_zero_global_check.py`: validates the 2×2 rank-one decomposition and the coefficient inequalities for degree-four diagonal restrictions. The lemma about separate convexity, Hessian normality, and the global support proof are mathematical arguments, not claims of computer-verified analytic formalization.
