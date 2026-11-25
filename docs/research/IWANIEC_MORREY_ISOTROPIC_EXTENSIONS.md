# Removing hypotheses from the $p\ge2$ polyconvexity theorem: what survives, and where it stops

*Addendum to [the $p\ge 2$ polyconvexity note](IWANIEC_MORREY_PGE2_POLYCONVEXITY.md). 23 November 2026.*

**Status.** Short hand proofs, spot-checked numerically (Section 4). Produced by Claude (Anthropic);
not reviewed by a person, not formalized in Lean, novelty not established.

**What this is not.** The unrestricted statement, that every rank-one convex integrand on
$\mathbb R^{2\times2}$ is quasiconvex, is **not** proved here. Two hypotheses of the main note are
weakened (the exponent, and in part the sign), both only conditionally on an external 2026
preprint. Section 3 records exactly where the method stops and why more of the same will not
reach the general problem.

## 0. Setting

Notation is that of the main note: $F(A)=\sigma_1(A)^p h(\det A/\sigma_1(A)^2)$ is isotropic and
positively $p$-homogeneous with profile $h$ on $[-1,1]$, $E_t=\operatorname{diag}(1,t)$,
$\kappa=(p-2)/p$ (negative when $p<2$), and $\ell_t(s)=h(t)+h'(t)(s-t)$ is the tangent line of $h$
at $t$ (a one-sided derivative is used at kinks and at $t=\pm1$). Rank-one convexity of $F$ gives:

- $h$ is convex on $[-1,1]$, with finite one-sided derivatives at $\pm1$ (Lemma 3(a) of the main note);
- the Baker–Ericksen inequality $p h(t)-2t h'(t)\ge0$ for $|t|<1$ (inequality (5.2) there), and in
  the limit the endpoint inequalities
  $$p h(1)-2h'(1)\ge0,\qquad p h(-1)+2h'(-1)\ge0 .\qquad(0.1)$$

Neither uses a sign condition or a restriction on $p>1$.

**Burkholder-type functions.** For $c_0,m\in\mathbb R$ put
$G_{c_0,m}(A)=|A|^{p-2}\big(c_0|A|^2+m\det A\big)$, where $|A|=\sigma_1(A)$. Its profile is the affine
function $c_0+ms$. The Burkholder integrand is $B_p=G_{|\kappa|,1}$.

**(B) External input.** $B_p$ is quasiconvex on $\mathbb R^{2\times2}$ for every $1<p<\infty$. This is
Corollary 2 of the preprint of Agazzi et al. (arXiv:2609.28311). It is not verified here.

> **Lemma 0.** Assume (B). If $c_0\ge|\kappa| |m|$, then $G_{c_0,m}$ is quasiconvex.

*Proof.* If $m>0$, $G_{c_0,m}=m B_p+(c_0-|\kappa|m)|A|^p$, and $|A|^p$ is convex. If $m<0$, apply
this to $A\mapsto G_{c_0,m}(AJ)=G_{c_0,-m}(A)$, $J=\operatorname{diag}(1,-1)$; quasiconvexity is
invariant under $A\mapsto AJ$. If $m=0$ the function is convex. $\square$

**Support principle.** If $G\le F$, $G$ is quasiconvex and $G(A_0)=F(A_0)$, then $F$ is quasiconvex
at $A_0$. Since $h\ge\ell_t$, one always has $F\ge G_{c_0,m}$ with $c_0=\ell_t(0)$, $m=h'(t)$, with
equality at $E_t$; and $c_0\ge|\kappa||m|$ means exactly $\ell_t(\kappa)\ge0$ and $\ell_t(-\kappa)\ge0$.
So everything below is about the sign of tangent lines at $\pm\kappa$.

## 1. The exponent: $1<p<2$, nonnegative $F$

> **Theorem A.** Let $1<p<2$ and let $F\ge0$ be isotropic, positively $p$-homogeneous and rank-one
> convex on $\mathbb R^{2\times2}$. Then $\ell_t(\kappa)\ge0$ and $\ell_t(-\kappa)\ge0$ for every
> $t\in[-1,1]$. Consequently $F\ge G_{c_0,m}$ with $c_0=\ell_t(0)\ge|\kappa||m|$, $m=h'(t)$, with
> equality at $E_t$; and under (B), $F$ is quasiconvex.

*Proof.* Write $a=|\kappa|=(2-p)/p\in(0,1)$, so that $1+a=2/p$.

*Step 1: $\ell_t(-a)\ge0$ for $t\in[-a,1]$.* Put $\rho(t)=h'(t)(t+a)-h(t)=-\ell_t(-a)$. For
$-a\le t_1<t_2\le1$, convexity gives $h(t_2)-h(t_1)\le h'(t_2)(t_2-t_1)$, hence
$$\rho(t_2)-\rho(t_1)\ge\big(h'(t_2)-h'(t_1)\big)(t_1+a)\ge0 .$$
So $\rho$ is nondecreasing on $[-a,1]$, and by (0.1)
$\rho(1)=\tfrac2p h'(1)-h(1)\le0$. Thus $\rho\le0$ on $[-a,1]$.

*Step 2: $\ell_t(a)\ge0$ for $t\in[-1,a]$.* This is Step 1 for the mirror function $F(AJ)$, whose
profile is $h(-s)$; it uses the second inequality in (0.1).

*Step 3: the remaining ranges.* Let $t\in[-1,-a)$. Then $-a$ lies between $t$ and $a$, so
$\ell_t(-a)$ is a convex combination of $\ell_t(t)=h(t)\ge0$ and $\ell_t(a)\ge0$ (Step 2). Likewise,
for $t\in(a,1]$, $\ell_t(a)$ is a convex combination of $\ell_t(-a)\ge0$ (Step 1) and $h(t)\ge0$.

So $\ell_t(\pm a)\ge0$ for all $t$. The rest is Lemma 0 and the support principle, applied at $E_t$
and transported to every matrix by isotropy and homogeneity ($F$ is quasiconvex at $0$ because
$F\ge0=F(0)$). $\blacksquare$

**Remarks.** (i) Nonnegativity is used only in Step 3. (ii) Polyconvexity is false in this range
($B_p^+$ is not polyconvex at the identity), so quasiconvexity is the right conclusion.
(iii) At conformal matrices this is Theorem 1.2 of Guerra–Kristensen. The all-matrix statement is
what the ledger's [universal isotropic note](IWANIEC_MORREY_UNIVERSAL.md) proposes; the argument
above is an independent proof in a few lines. (iv) The same computation for $p>2$ gives
$\rho(1)\le(p-2)h(1)$, which has the wrong sign: this is why Cases I and II exist in the main note.

> **Corollary B.** For nonnegative, isotropic, positively $p$-homogeneous integrands on
> $\mathbb R^{2\times2}$ with $p>1$, rank-one convexity is equivalent to quasiconvexity:
> unconditionally for $p\ge2$ (they are polyconvex, main note), and under (B) for $1<p<2$.

## 2. The sign condition, $p>2$

A positively $p$-homogeneous function with $p>2$ that takes a negative value has no polyaffine
minorant, so the supports of the main note are unavailable and only quasiconvexity can be asked.

> **Proposition C.** Let $p>2$ and let $F$ be real-valued, isotropic, positively $p$-homogeneous
> and rank-one convex on $\mathbb R^{2\times2}$.
>
> (a) $h(0)\ge0$, and the set $\lbrace h<0\rbrace$ is empty, or $[-1,s_0)$ with $s_0\le-\kappa$, or
> $(s_0,1]$ with $s_0\ge\kappa$. In particular $F\ge0$ on the cone
> $\lbrace |\det A|\le\kappa|A|^2\rbrace$, and $\kappa$ cannot be improved ($F=B_p$).
>
> (b) If $h(t)<0$, then $\ell_t(\kappa)\ge0$ and $\ell_t(-\kappa)\ge0$.
>
> (c) Under (B), $F$ is quasiconvex at every matrix $A$ with $F(A)<0$, and more generally at every
> matrix whose ratio $t=\det A/|A|^2$ satisfies $\ell_t(\pm\kappa)\ge0$.
>
> (d) Under (B), if $F-G_{c_0,m}$ is nonnegative and rank-one convex for some $c_0\ge\kappa|m|$, then
> $F$ is quasiconvex.

*Proof.* (a) The line $\tau\mapsto\tau E_0$ is a rank-one line through $0$, and
$F(\tau E_0)=|\tau|^p h(0)$ by isotropy; convexity forces $h(0)\ge0$. The set $\lbrace h<0\rbrace$ is
an interval (sublevel set of a convex function) not containing $0$; say it lies in $[-1,0)$. If
$h(t)<0$ with $t<0$, the Baker–Ericksen inequality gives $2|t|h'(t)\ge p|h(t)|>0$, so $h$ is
increasing wherever it is negative, and the interval is $[-1,s_0)$. At $t=-1$, (0.1) gives
$h'(-1)\ge\tfrac p2|h(-1)|$, so the tangent line $\ell_{-1}$ vanishes at
$s^\ast=-1+|h(-1)|/h'(-1)\le-1+\tfrac2p=-\kappa$. Since $h\ge\ell_{-1}$ and $\ell_{-1}\ge0$ on
$[s^\ast,1]$, we get $h\ge0$ on $[-\kappa,1]$, that is $s_0\le-\kappa$. The other case is the mirror
image.

(b) In the case $\lbrace h<0\rbrace=[-1,s_0)$ let $-1\le t_1<t_2<s_0$. Both tangent lines are increasing,
$\ell_{t_1}\le h$ gives $\ell_{t_1}(t_2)\le\ell_{t_2}(t_2)$, and the slopes are ordered, so
$\ell_{t_1}\le\ell_{t_2}$ on $[t_2,\infty)$. Hence the zero of $\ell_{t_2}$ is at most the zero of
$\ell_{t_1}$: the zero of the tangent line moves left as $t$ increases. By (a) it starts at
$s^\ast\le-\kappa$, so every $\ell_t$ with $h(t)<0$ vanishes at a point $\le-\kappa$ and is
increasing; therefore $\ell_t(-\kappa)\ge0$ and $\ell_t(\kappa)\ge0$.

(c) By (b) or by assumption, $c_0=\ell_t(0)\ge\kappa|m|$; apply Lemma 0 and the support principle
at $E_t$, then isotropy and homogeneity.

(d) $F-G_{c_0,m}$ is polyconvex by Theorem 1 of the main note, hence quasiconvex, and $G_{c_0,m}$
is quasiconvex by Lemma 0. $\blacksquare$

## 3. Where the method stops

**3.1 Signed integrands, the remaining bases.** What Proposition C leaves open are the matrices
with $F(A)>0$ whose tangent line is negative at $\kappa$ or at $-\kappa$ (Cases I and II of the main
note). There the natural candidates are supports of the form
$$G_{c_0,m}(A)+k+\beta|z|+\gamma|w|+c\det A,\qquad c_0\ge\kappa|m|,\quad\beta,\gamma\ge0,$$
a Burkholder-type function plus (the isotropic hull of) a polyaffine one. For fixed $F$ and base,
the best such support is a linear program. For the Dacorogna–Marcellini integrands
$|A|_F^2(|A|_F^2-2\gamma\det A)$, $p=4$, it gives:

| $\gamma$ | bases $t$ tested | result |
| --- | --- | --- |
| $0.9$, $1$, $1.05$ | ten bases in $[-0.9,0.97]$ | a touching support exists at every base |
| $1.1$ | same | touching except at $t=-0.9$: gap $1.05\cdot10^{-2}$ (with $h(t)=6.86$) |
| $2/\sqrt3$ | same | touching except at $t=-0.9$: gap $1.19\cdot10^{-1}$ (with $h(t)=7.04$) |

So this family of supports is **not** sufficient. It is not a counterexample to anything: these
integrands are quasiconvex for $|\gamma|\le2/\sqrt3$ by the preprint of Bruno–Pasqualotto, proved by
a heat-flow argument and not by supports of this kind. Closing the signed case therefore needs
quasiconvex functions beyond "Burkholder plus polyconvex". For $d=2$ and $p>2$ this is Conjecture 1
of Cassese's preprint, and it stays open here.

**3.2 Isotropy and homogeneity.** Every argument in the main note and in this addendum goes
through the one-variable profile $h$. Without isotropy and homogeneity there is no profile, and
the conclusion "polyconvex" is false (Remark 7.4 of the main note). The only reductions available
are trivial ones: translations, $A\mapsto PAQ$ with $P,Q\in GL(2)$, sums, suprema, and composition
with convex nondecreasing functions all preserve quasiconvexity, so the results extend to the
closure of the isotropic homogeneous class under these operations. A general rank-one convex
function is not in that closure for any reason known to me.

**3.3 Consequence.** The unrestricted planar Morrey problem is untouched. A proof would have to
either produce quasiconvex minorants for an arbitrary rank-one convex function, with no symmetry
to organize them, or prove Jensen's inequality directly for gradient Young measures. Nothing here
does either, and continuing along the present lines (more support families, more exponents) would
enlarge the class but not remove the symmetry assumption.

## 4. Checks

All with the conic description of $C^2$ spline profiles used for the main note (rank-one
convexity imposed at 201 nodes; `cvxpy` with CLARABEL), and `scipy` for the linear programs.

- Theorem A: over the cone of nonnegative rank-one convex profiles, the minimum of $\ell_t(\pm\kappa)$
  over 20 to 39 bases is $0$ up to $10^{-12}$ for $p\in\lbrace 1.2,1.5,1.8\rbrace$. Without the sign
  condition it is negative ($-0.23$ at $p=1.5$ under $|h|\le1$), so Step 3 is needed.
- Proposition C(a): the minimum of $h(s)$ over signed rank-one convex profiles with $|h|\le1$ is $0$
  for $|s|\le\kappa$ and negative for $|s|>\kappa$, for $p\in\lbrace 3,4,6\rbrace$; the minimizers are
  Burkholder profiles.
- Proposition C(b): with $h(t)=-1$ imposed, the minimum of $\ell_t(\pm\kappa)$ is $0$ up to $10^{-10}$
  for $p\in\lbrace 3,4,6\rbrace$.
- Section 3.1: the linear program on a grid of 161 ratios and 140 amplitudes up to 60.

These are spot checks, not an audit. No independent review pass was made for this addendum.

## References

- A. Agazzi et al., Sharp higher integrability theory, Part I: the $L^p$-norm of the
  Beurling–Ahlfors transform, preprint, arXiv:2609.28311.
- G. Bruno, F. Pasqualotto, Quasiconvexity for the Dacorogna–Marcellini energy, preprint,
  arXiv:2608.06367.
- G. Cassese, A solution to Morrey's problem in $\mathbb R^{2\times m}$, preprint, arXiv:2608.03488.
- A. Guerra, J. Kristensen, Automatic quasiconvexity of homogeneous isotropic rank-one convex
  integrands, Arch. Ration. Mech. Anal. 245 (2022) 479–500; arXiv:2112.10563.
