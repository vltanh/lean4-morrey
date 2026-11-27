# The general $2\times2$ problem by logic alone: six directions, what each proves, where each stops

*Fourth note in the series. 23 November 2026. Pen-and-paper only; no computation was used.*

**Status.** Morrey's problem on $\mathbb R^{2\times2}$ is **not** solved here. Unlike the earlier notes,
nothing below assumes isotropy or homogeneity: $f$ is an arbitrary rank-one convex function. Each
section is a strategy for the general problem, carried to a rigorous statement and to the point
where it stops. Hand proofs, produced by Claude (Anthropic), not reviewed. Several statements are
probably known; I did not check the literature for them, so no novelty is claimed.

Throughout, a *laminate* is a compactly supported probability measure $\nu$ on $\mathbb R^{2\times2}$
with $\int f d\nu\ge f(\bar\nu)$ for every rank-one convex $f$, where $\bar\nu$ is its barycenter.
Morrey's conjecture says that the gradient distribution of every periodic Lipschitz map is one.

**Standing fact (Q).** A quadratic form on $\mathbb R^{2\times2}$ that is $\ge0$ on rank-one matrices
equals $P+c\det$ with $P$ positive semidefinite (rank-one convex quadratic forms are polyconvex
in dimension $2\times2$; see Dacorogna's book).

## 1. Third-order resonances cannot produce a counterexample

Šverák's $3\times2$ counterexample uses three waves $M_k=v_k\otimes n_k$ with $n_1+n_2+n_3=0$, a point
where the second variation vanishes on all three, and a nonzero cubic term $D^3f[M_1,M_2,M_3]$.

> **Lemma 1.** Let $f\in C^3(\mathbb R^{2\times2})$ be rank-one convex, $A\in\mathbb R^{2\times2}$, and
> let $M_1,M_2,M_3$ be linearly independent rank-one matrices with $D^2f(A)[M_k,M_k]=0$. Assume $\det$
> is nondegenerate on $L=\operatorname{span}\lbrace M_k\rbrace$. Then $D^2f(A)[R,R]=0$ for every rank-one
> $R\in L$, and $D^3f(A)[X,Y,Z]=0$ for all $X,Y,Z\in L$.

*Proof.* By (Q), $D^2f(A)=P+c\det$ with $P\ge0$. Then $P(M_k)=0$, so $L\subset\ker P$, and
$D^2f(A)[R,R]=c\det R=0$ for rank-one $R\in L$. For such $R$ the function
$B\mapsto D^2f(A+B)[R,R]$ is $\ge0$ and vanishes at $B=0$, so its derivative there vanishes:
$D^3f(A)[B,R,R]=0$ for all $B$. For fixed $B$ the symmetric form $(X,Y)\mapsto D^3f(A)[B,X,Y]$ on the
three-dimensional space $L$ vanishes on the null cone of the nondegenerate indefinite form
$q=\det|_L$, hence equals $\lambda(B)q(X,Y)$ with $\lambda$ linear. For $X,Y,Z\in L$, symmetry gives
$\lambda(X)q(Y,Z)=\lambda(Y)q(X,Z)$; choosing $Z$ with $q(Y,Z)=0\ne q(X,Z)$ shows $\lambda(Y)=0$ for
every $Y\in L$. $\blacksquare$

So for a periodic test field with values in $L$ the expansion of $\int f(A+\varepsilon D\varphi)$ has
no terms of order $\varepsilon^2$ (the second variation reduces to $c\int\det D\varphi=0$) or
$\varepsilon^3$. If $f\in C^4$, the order $\varepsilon^4$ term is governed by the quartic form $D^4f(A)$
on $L$, which is itself convex along the null directions of $q$, because $D^4f(A)[B,B,R,R]\ge0$.

**Where it stops.** This is perturbative. It reduces the three-wave question at a degenerate
point to quartic forms on a three-dimensional Lorentzian space. Every such $L$ is the image of
the symmetric matrices under some $A\mapsto PAQ$, so this is the same problem for Hessians of
scalar functions. It says nothing about large amplitudes.

## 2. Continuous martingales: Jensen needs only the determinant

> **Lemma 2.** Let $X_t$ be a bounded continuous martingale in $\mathbb R^{2\times2}$ with
> $d\langle X_{11},X_{22}\rangle=d\langle X_{12},X_{21}\rangle$. Then $f(X_t)$ is a submartingale for every
> rank-one convex $f\in C^2$; in particular the law of $X_T$ is a laminate with barycenter $X_0$.

*Proof.* Itô's formula gives drift $\tfrac12\langle D^2f(X_t),\Sigma_t\rangle$, where $\Sigma_t$ is the
covariance rate. By (Q), $D^2f=P+c\det$, and $\langle\det,\Sigma_t\rangle=0$ is the hypothesis.
$\blacksquare$

In discrete time the analogous condition (each step preserves the mean of $\det$) is far from
sufficient; in continuous time it is, because only second-order information enters.

For a periodic map $\varphi$, the heat extension $X_t=A+D\varphi_{T-t}(B_t)$ (Brownian motion $B$ with
uniform start, $\varphi_s=e^{s\Delta/2}\varphi$) is a martingale from (nearly) $A$ to the gradient
distribution. Its defect is explicit:
$$d\langle X_{11},X_{22}\rangle-d\langle X_{12},X_{21}\rangle
   =\big[\det D(\partial_1\varphi_s)+\det D(\partial_2\varphi_s)\big](B_t) dt .$$
It integrates to zero in space but is not zero pointwise. More generally, for a diffusion with
matrix $a(x,t)\ge0$ and the corresponding space-time extension $U$ of $D\varphi$, the condition reads
$\langle a,Q\rangle=0$ with $Q(e)=\det(\partial_eU)$, a quadratic form in the direction $e$; at the
terminal time it is $Q_x(e)=\det\big(\partial_e D\varphi(x)\big)$.

**Where it stops.** A nonzero $a\ge0$ with $\langle a,Q_x\rangle=0$ exists exactly where $Q_x$ is not
definite. Where $Q_x$ is definite (the gradient field moves through pairwise incompatible matrices
in every direction, as for a conformal map), no local diffusion works. Those regions have to be
connected to the rest non-locally; the only tools known for that are Burkholder-type inequalities.

## 3. Peeling

> **Lemma 3.** Let $\nu$ be a compactly supported probability measure on $\mathbb R^{2\times2}$ and
> $\tau:\operatorname{supp}\nu\to[0,1]$ Borel, with $m(t)=\nu\lbrace\tau>t\rbrace$ absolutely
> continuous, $m(0)=1$, $m(1)=0$. Let $\bar A_t$ be the barycenter of $\nu$ restricted to
> $\lbrace\tau>t\rbrace$. If $\operatorname{rank}(X-\bar A_{\tau(X)})\le1$ for $\nu$-almost every $X$, then $\nu$
> is a laminate.

*Proof.* For $f\in C^1$ rank-one convex put $\Phi(t)=m(t)f(\bar A_t)+\int_{\tau\le t}f d\nu$. With
$r=-m'$ and $\nu_t$ the conditional law given $\tau=t$, one has $m\bar A_t'=r(\bar A_t-\bar\nu_t)$ and
$$\Phi'(t)=r\int\big[f(X)-f(\bar A_t)-Df(\bar A_t)[X-\bar A_t]\big] d\nu_t(X)\ \ge0,$$
because $f$ is convex on the line through $\bar A_t$ and $X$. Hence
$\int f d\nu=\Phi(1^-)\ge\Phi(0)=f(\bar\nu)$. General $f$ follows by mollification. $\blacksquare$

> **Corollary 4.** Let $\Omega$ be a bounded Lipschitz domain, $\tau:\bar\Omega\to[0,1]$ Lipschitz with
> $\tau=0$ on $\partial\Omega$ and $\nabla\tau\ne0$ almost everywhere, and let $B(\cdot)$, $c(\cdot)$ be
> Lipschitz. Then the gradient distribution of $\varphi(x)=B(\tau(x))x+c(\tau(x))$ is a laminate. So
> $\frac1{|\Omega|}\int_\Omega f(D\varphi)\ge f(B(0))$ for **every** rank-one convex $f$.

*Proof.* Each $U_t=\lbrace\tau>t\rbrace$ has affine boundary values $B(t)x+c(t)$, so its average gradient
is $B(t)$, and $D\varphi=B(\tau)+(B'(\tau)x+c'(\tau))\otimes\nabla\tau$ differs from it by a rank-one
matrix. Apply Lemma 3 with the peeling time $\tau(x)$. $\blacksquare$

This contains radial stretchings ($\tau=1-|x|$, $B=\rho(r)/r\cdot I$) and allows arbitrary level
curves and matrix-valued $B$. The same peeling, by strips, handles plane waves on the torus.

**Where it stops.** Generically a map has no closed curve on which it is affine, so it is not of
this form. Applied directly to a generic gradient distribution, Lemma 3 has no admissible start:
the points rank-one connected to the current mean form a curve, and a consistent motion of the
mean exists only under a non-generic condition. Allowing the removed pieces to be laminates
themselves makes the lemma a restatement of the definition.

## 4. A discrete form, and its smallest case

Piecewise affine maps on the regular triangulation of the torus (three edge directions, mesh
$1/N$) approximate every Lipschitz map with convergence of gradients, so Morrey's conjecture is
equivalent to: for every $N$, the gradient distribution of every such map is a laminate. The
triangles form a honeycomb graph, and neighbours differ by a rank-one matrix whose direction is
one of three fixed ones.

> **Proposition 5.** For $N=2$ every such map generates a laminate of order three.

*Proof.* With edge differences $p,q$ and the closedness defect $r$, the eight gradients are
$\pm[a|b]$ with first column $a\in\lbrace p,r-p\rbrace$ and second column $b\in\lbrace q,r-q\rbrace$.
The four matrices with the plus sign form a product set in the two columns, hence carry a
second-order laminate with barycenter $[r/2|r/2]=\tfrac r2\otimes(1,1)$; the other four carry its
mirror image. The two barycenters differ by the rank-one matrix $r\otimes(1,1)$. $\blacksquare$

**Where it stops.** For $N=2$ the triangle type decouples the third wave from the other two.
For $N\ge3$ it does not, and I found no inductive step.

## 5. Two strategies that collapse to polyconvexity

**Partial duality.** $I(\varphi_1,\varphi_2)=\int f(A+D\varphi)$ is convex in $\varphi_1$ for fixed
$\varphi_2$, since a rank-one convex $f$ is convex in each row. Dualizing the scalar convex problem in
$\varphi_1$ turns quasiconvexity into a min–max problem for the partial Legendre transform
$f^{\ast1}(\sigma;r)$ in the first row. The trivial configuration is a saddle point, and the
argument closes, when $f^{\ast1}$ is concave in $r$. Its Hessian in $r$ is minus the Schur complement
of $D^2f$, so this requires $f$ to be convex. Shifting the dual variable by a multiple of $\varphi_2$
extends the argument to $f=$ convex $+ c\det$ and no further.

**Calibrations.** A closed two-form on $\Omega\times\mathbb R^2$ that lies below $f$ on every graph
and agrees with it on the affine graph restricts, at each point of that graph, to a polyaffine
function below $f$ touching at $A$. So it exists only if $f$ is polyconvex at $A$.

## 6. What a proof still needs

Sections 2 and 3 describe the two mechanisms that produce laminates from maps: local splitting
along directions in which the gradient moves by rank-one matrices, and peeling from a boundary
with affine data. Both fail in regions where the gradient field is locally incompatible in all
directions. Section 1 shows that such a failure does not show up at third order. The earlier
notes show that the known quasiconvex functions do not cover it either. A proof has to supply a
non-local mechanism for those regions; a counterexample has to live there. I have neither.
