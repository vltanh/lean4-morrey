# Global Morrey progress: an explicit open cone of anisotropic, nonhomogeneous, nonpolyconvex quasiconvex quartics

**Date:** November 21, 2026. **Status:** Complete hand proof of the stated subclass; no solution of the unrestricted Morrey problem. This is a quantitative corollary of the 2026 Bruno–Pasqualotto endpoint theorem, not a claim to have established a new open conjecture.

## Theorem

Write a real `2 × 2` matrix as `A=(a,b;c,d)`, and use its Frobenius norm `|A|`. Set

\[
Q(A)=|A|^4-\frac94 |A|^2\det A+\frac1{256}|A|^2.
\]

Let `R` be any real polynomial of total degree at most four:

\[
R(A)=\sum_{|\alpha|\le4}c_\alpha A^\alpha,
\qquad
\delta=\sum_{2\le|\alpha|\le4}|c_\alpha|\le \frac1{4096}.
\]

There is **no restriction** on its constant and linear terms. Put `f=Q+R`. For every bounded Lipschitz domain `Ω⊂R²`, constant matrix `F`, and `u∈W^{1,∞}_0(Ω;R²)`, we have

\[
\frac1{|\Omega|}\int_\Omega[f(F+Du)-f(F)]\,dx
\ \ge\ \frac1{512|\Omega|}\int_\Omega\bigl((1+|F|^2)|Du|^2+|Du|^4\bigr)\,dx.
\tag{1}
\]

The same estimate holds for smooth periodic maps on the unit torus. Consequently every such `f` is **quasiconvex**, hence **rank-one convex**, but **not polyconvex**. This is a full-dimensional coefficient neighborhood (degree≤4 has 70 monomials), with arbitrary anisotropic and nonhomogeneous terms.

## Proof: analytic part

### Input from the literature

Bruno–Pasqualotto (2026), *Quasiconvexity for the Dacorogna–Marcellini Energy*, arXiv:2608.06367, proves that

\[
Q_*(A)=|A|^4-\frac4{\sqrt3}|A|^2\det A
\]

is quasiconvex on all `R^{2×2}`, at every base matrix. We use this as an **external theorem**; the present note does not reproduce its proof. Let `\theta=9\sqrt3/16`. Since `\sqrt3<7/4`, we have `0<\theta<63/64`. Hence

\[
|A|^4-\frac94|A|^2\det A
=(1-\theta)|A|^4+\theta Q_*(A).
\tag{2}
\]

### Strong convexity of the radial quartic

For `H≠0`, set `h=|H|`, `x=(F:H)/h²` and `y=|F|²/h²−x²≥0`. Direct expansion gives

\[
\begin{split}
&|F+H|^4-|F|^4-4|F|^2(F:H)\\
&\qquad=h^4(6x^2+4x+1+2y).
\end{split}
\]

Subtracting `(|F|²+|H|²)|H|²/4` from this yields

\[
\frac{h^4}{4}(23x^2+16x+3+7y)
=\frac{h^4}{4}\left[23\left(x+\frac8{23}\right)^2+\frac5{23}+7y\right]\ge0.
\]

It also holds for `H=0`. Since `∫ Du = 0`, the derivative term disappears on integration. By (2) and quasiconvexity of `Q_*`, the Jensen gap for `Q` is at least

\[
\frac{1-\theta}{4}\int_\Omega(|F|^2|Du|^2+|Du|^4)
+\frac1{256}\int_\Omega|Du|^2
\ >\ \frac1{256}\int_\Omega(1+|F|^2)|Du|^2+\frac1{256}\int_\Omega|Du|^4,
\tag{3}
\]

where we used `1−θ>1/64`.

### Robustness under all degree≤4 perturbations

For each monomial `A^α` of degree `m=|α|=2,3,4`,

\[
|D^2(A^\alpha)(X)[H,H]|\le m(m-1)|X|^{m-2}|H|^2.
\]

The bounds `m(m−1)≤12` and `|X|≤(1+|X|²)/2` imply

\[
|D^2R(X)[H,H]|\le12\delta(1+|X|^2)|H|^2.
\]

Taylor's formula and `2ab≤a²+b²` give

\[
\begin{aligned}
|R(F+H)-R(F)-DR(F)[H]|
&\le 12\delta|H|^2\int_0^1(1-t)(1+|F+tH|^2)\,dt\\
&\le 8\delta(1+|F|^2+|H|^2)|H|^2.
\end{aligned}
\tag{4}
\]

Because `8δ≤1/512`, equations (3)–(4) imply (1). This step uses no finite grid, no polynomial-sampling heuristic, and no fixed-point theorem.

## Proof: nonpolyconvexity via a four-atom measure

Let

\[
I=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad
J=\begin{pmatrix}1/5&0\\0&-1/5\end{pmatrix},\quad
\mu=\frac{\delta_I+\delta_{-I}}{52}
+\frac{25}{52}(\delta_J+\delta_{-J}).
\]

This probability measure has

\[
\int A\,d\mu=0,\quad \int\det A\,d\mu=0,\quad
\int|A|^2\,d\mu=\frac2{13}.
\]

A direct rational calculation shows

\[
\int\Bigl(|A|^4-\frac94|A|^2\det A\Bigr)\,d\mu
=-\frac2{325}.
\]

Hence

\[
\int Q(A)\,d\mu-Q(0)=-\frac2{325}+\frac1{1664}=-\frac{231}{41600}.
\]

Every matrix entry on the four atoms has absolute value at most 1. The affine part of `R` cancels since the barycenter is zero, and the higher-degree part contributes at most `δ`. Therefore

\[
\int f\,d\mu-f(0)
\le-\frac{231}{41600}+\frac1{4096}
=-\frac{7067}{1331200}<0.
\]

If `f` were polyconvex, it could be written `f(A)=\Phi(A,\det A)` with `\Phi` convex on `R⁵`. Jensen's inequality and the preceding moments would imply `∫f dμ≥f(0)`, a contradiction. Thus every `f` in the stated coefficient ball is **nonpolyconvex**. Note that `μ` is *not* a gradient Young measure; it is used only to disprove polyconvexity, and does not contradict quasiconvexity.

## What this achieves—and does not

- **Global**, every base matrix `F` and every Lipschitz test map; no dyadic-level restrictions.
- **All coefficient directions** of the 70-dimensional space of degree≤4 polynomials, including anisotropy and nonhomogeneity.
- A **fully explicit modulus** `1/512` and a **fully explicit nonpolyconvexity witness**.
- **Relies** on the already proved 2026 endpoint theorem and standard convexity. It is a quantitative stability corollary, not claimed to be a new open-problem resolution.
- **Does not establish** that an arbitrary rank-one-convex quartic is quasiconvex. The missing step in Morrey is still a global argument that applies to the whole rank-one-convex cone, including its boundary, rather than a neighborhood of one previously proved energy.

## Independent exact checker

Run `python morrey_global_quartic_open_ball_verify.py`; it checks the rational inequalities and the four-atom witness. Analytic steps (external quasiconvexity and the all-matrices Taylor estimate) are in the hand proof above, not in the Python script.
