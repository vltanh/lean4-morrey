# What Burkholder can and cannot certify: attack directions for the signed isotropic case

*Third note in the series after [the $p\ge2$ theorem](IWANIEC_MORREY_PGE2_POLYCONVEXITY.md) and
[its addendum](IWANIEC_MORREY_ISOTROPIC_EXTENSIONS.md). 23 November 2026.*

**Status.** Morrey's problem on $\mathbb R^{2\times2}$ is **not** proved here, and nothing below
comes close. This note records one round of computer-assisted exploration: one positive numerical
observation, one rigorous rigidity lemma that blocks the whole "Burkholder plus polyconvex"
strategy, and a concrete family of integrands on which any proof or counterexample would have to
be tested. Produced by Claude (Anthropic); numerical statements are on finite grids; no
independent review.

Notation as in the earlier notes: profile $h$, $\kappa=(p-2)/p$, $E_t=\operatorname{diag}(1,t)$,
$J=E_{-1}$, mirror Burkholder function $\tilde B(A)=|A|^{p-2}(\kappa|A|^2-\det A)$ with profile
$\kappa-s$. Assumption (B): $B_p$ is quasiconvex (Agazzi et al., arXiv:2609.28311).

## 1. The certificates available

Under (B) the following are quasiconvex: polyconvex functions; $A\mapsto B_p(PAQ)$ for
$P,Q\in GL(2)$; sums, suprema and averages of these. Averaging $B_p(ARD_\mu)$ over rotations $R$,
with $D_\mu=\operatorname{diag}(1,\mu)$, gives a one-parameter family of *isotropic, $p$-homogeneous*
quasiconvex functions $M_\mu B_p$ and $M_\mu\tilde B$ (spherical means; left and right dilations give
the same family). A support at $E_t$ is then sought in the form
$$\sum_j b_j M_{\mu_j}B^{\pm}+k+\beta|z|+\gamma|w|+c\det A\ \le\ F,\qquad b_j,\beta,\gamma\ge0 ,\qquad(1.1)$$
with equality at $E_t$. For fixed $F$ and $t$ the best such support is a linear program.

## 2. Positive observation: the Dacorogna–Marcellini integrands

For $F_\gamma=|A|_F^2(|A|_F^2-2\gamma\det A)$, $p=4$, the addendum showed that plain Burkholder plus
polyaffine supports fail (gap $0.119$ at $t=-0.9$ for $\gamma=2/\sqrt3$). With the family (1.1):

| $\gamma$ | bases $t$ | best support (1.1), after cutting-plane refinement |
| --- | --- | --- |
| $1.05$, $1.1$, $1.13$ | $-0.9$ | gap $0$ to $10^{-15}$, no violated constraint |
| $2/\sqrt3$ (extremal) | $-0.99,-0.9,-0.6,-0.3,0.2,0.45$ | gap $0$ to $10^{-15}$, no violated constraint |

(100 to 120 generators, $\mu\in[e^{-4},1]$; constraints on up to $1201\times1101$ points, amplitudes up
to 300.) Near the anticonformal end the optimal supports use two or three mirror generators with
$\mu$ between $0.58$ and $0.91$ and a polyaffine part with $c<0$.

**Conjecture 1.** Every Dacorogna–Marcellini integrand with $|\gamma|\le2/\sqrt3$ has a support (1.1)
at every matrix. Under (B) this would give their quasiconvexity (the theorem of Bruno–Pasqualotto)
from Burkholder's alone. Not proved here.

## 3. Rigidity: where this strategy cannot work

> **Lemma D.** Let $p>2$, $c>-\kappa$ and $K_c=\lbrace A:\det A\ge-c|A|^2\rbrace$. If $G$ is isotropic,
> positively $p$-homogeneous and rank-one convex with $G\le\tilde B$ on $K_c$, then $G=\tilde B$ on $K_c$.

*Proof.* Let $g$ be the profile of $G$; then $g(s)\le\kappa-s$ on $[-c,1]$, an interval containing
$\kappa$ in its interior. By Proposition C(a) of the addendum, $g(\kappa)\ge0$, so $g(\kappa)=0$. For
$s>\kappa$ the chord slope of the convex function $g$ from $\kappa$ is $g(s)/(s-\kappa)\le-1$, so for
$s'<\kappa$ the chord slope $g(s')/(s'-\kappa)$ is also $\le-1$, that is $g(s')\ge\kappa-s'$. Hence
$g=\kappa-s$ on $[-c,\kappa]$, the line $\kappa-s$ supports $g$, and $g\ge\kappa-s$ everywhere; with
the hypothesis, $g=\kappa-s$ on $[-c,1]$. $\square$

> **Corollary E.** Let $c>0$ and let $F$ be isotropic, positively $p$-homogeneous and rank-one convex,
> with $F=\tilde B$ on $K_c$ and $F(A_0)>\tilde B(A_0)$ at some $A_0\notin K_c$. If $G$ is isotropic,
> $p$-homogeneous and quasiconvex, $P$ is polyaffine and $G+P\le F$, then $G=\tilde B$ on $K_c$ and
> $P\le0$. So a touching support of this kind at $A_0$ requires a quasiconvex $G$ that equals
> $\tilde B$ on $K_c$ and equals $F$ at $A_0$.

*Proof.* Scaling gives $G\le F$, so $G=\tilde B$ on $K_c$ by Lemma D and $P\le F-G=0$ on $K_c$. Since $c>0$, the
cone $K_c$ is symmetric, has interior, and contains matrices with determinants of both signs, so a
polyaffine function that is $\le0$ on it at all scales is a nonpositive constant. $\square$

Such $F$ exist in abundance. A conic program over $C^2$ spline profiles ($p=4$, $c=0.2$) produces
rank-one convex profiles equal to $b(\kappa-s)$ on $[-0.2,1]$ and strictly above it on $[-1,-0.2)$;
rank-one convexity was confirmed by brute force in matrix space ($3\cdot10^5$ rank-one lines, five
step sizes, no negative second difference beyond $10^{-7}$). For one of them the best support (1.1)
at $t=-0.95$ leaves a gap of $0.2516$ out of $h(t)=0.958$, which is exactly $F-b\tilde B$ at the base,
as Corollary E predicts. Non-averaged images $\tilde B(AD_\mu)$, $\tilde B(D_\mu A)$ with a general
polyaffine part, tested on a four-dimensional grid, give the same gap.

**Consequence.** None of the quasiconvex functions considered here certifies these integrands. The strategy "Burkholder plus polyconvex" cannot prove even the isotropic homogeneous
case of Morrey's problem; Conjecture 1 is special to integrands like $F_\gamma$.

## 4. A test problem: the constrained Burkholder inequality

Let $F_c$ be the largest rank-one convex function that is $\le\tilde B$ on $K_c$ (it is isotropic and
$p$-homogeneous, and equals $\tilde B$ on $K_c$). If Morrey's conjecture holds, then for every
Lipschitz $u$ on a domain $\Omega$ with $u=A_0x$ on $\partial\Omega$ and $Du\in K_c$ almost everywhere,
$$\frac1{|\Omega|}\int_\Omega\tilde B(Du) dx\ \ge\ F_c(A_0),$$
while quasiconvexity of $\tilde B$ alone gives only the bound $\tilde B(A_0)$. For $p=4$, $c=0.2$,
$A_0=J$: $\tilde B(J)=1.5$, and a spline profile gives the lower estimate $F_c(J)\ge11.09$. Radial
power maps satisfying the constraint have mean energy at least $48.6$.

A direct search (periodic piecewise affine maps on a $16\times16$ grid, exact energies, L-BFGS,
twelve starts with amplitudes from $0.1$ to $10$) for a map with
$\frac1{|Q|}\int_Q F_c(J+D\varphi)<F_c(J)$ found none: every run ended at $11.085784$, the value at
$J$ to seven digits, most of them at a nontrivial $\varphi$. So the minimum is attained on a flat
set of microstructures, as expected for an envelope, and not undercut. The same search on the
example of Section 3 returned $\varphi=0$ every time.

**Why this is the right target.** A proof of Morrey's conjecture must show that $F_c$ is
quasiconvex, and by Corollary E and the experiments of Section 3 it cannot do so with the
certificates considered here. A
counterexample search has here an explicit gap to aim at, between $\tilde B(A_0)$ and $F_c(A_0)$.
Either outcome would be new; this note provides neither.

## 5. Checks and limits

- Section 2: linear programs with `scipy` (HiGHS); a zero gap means that all sampled constraints
  hold, not that the inequality is proved.
- Section 3: Lemma D and Corollary E are hand proofs. The example profiles are numerical;
  their rank-one convexity is tested, not proved.
- Section 4: $F_c$ is represented by a spline that is rank-one convex to about $10^{-7}$; its value at
  $J$ depends on the spline resolution ($9.12$ with 40 coefficients, $11.09$ with 60), so only the
  inequality $F_c(J)\ge11.09$ is claimed, and that only numerically. The energy search is a local
  method with random starts.

## References

- A. Agazzi et al., Sharp higher integrability theory, Part I, preprint, arXiv:2609.28311.
- G. Bruno, F. Pasqualotto, Quasiconvexity for the Dacorogna–Marcellini energy, preprint,
  arXiv:2608.06367.
