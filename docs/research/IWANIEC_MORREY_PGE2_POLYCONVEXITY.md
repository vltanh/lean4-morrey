# Rank-one convexity implies polyconvexity for nonnegative isotropic $p$-homogeneous integrands on $\mathbb R^{2\times 2}$, $p\ge 2$

*An affirmative answer to Question 1.7 of Guerra and Kristensen. It closes the "Main p>2 gate" of the
[roadmap](README.md#roadmap), which is [ledger](README.md#result-ledger) entry I12.* 23 November 2026.

**Status.** Hand proof, complete and elementary (Sections 3–5 use nothing beyond the definition of
rank-one convexity and one-variable calculus). Every algebraic identity is checked symbolically and
the explicit supports are stress-tested numerically (Section 9). It was produced by
Claude (Anthropic) in an AI-assisted session; it has **not** been reviewed by a person and is
**not** formalized in Lean. A second, independent AI pass refereed this text line by line and
re-tested the supports with its own code (Section 9); its corrections are incorporated. A
literature search found no earlier proof, but novelty has not been established.

**Scope warning.** This settles the polyconvexity question for the *nonnegative, isotropic,
positively homogeneous* class. It does **not** settle Morrey's problem for general integrands on
$\mathbb R^{2\times 2}$, which remains open (Section 8).

## 1. Statement

A function $F:\mathbb R^{2\times 2}\to\mathbb R$ is *isotropic* if $F(QAR)=F(A)$ for all
$Q,R\in SO(2)$, *positively $p$-homogeneous* if $F(\lambda A)=\lambda^pF(A)$ for $\lambda>0$,
*rank-one convex* if $\tau\mapsto F(A+\tau B)$ is convex on $\mathbb R$ whenever
$\operatorname{rank}B=1$, and *polyconvex* if $F(A)=g(A,\det A)$ for a convex
$g:\mathbb R^{5}\to\mathbb R$. A *polyaffine* function is $A\mapsto k+\langle K,A\rangle+c\det A$.

> **Theorem 1.** Let $p\ge 2$ and let $F:\mathbb R^{2\times 2}\to[0,\infty)$ be isotropic,
> positively $p$-homogeneous and rank-one convex. Then $F$ is polyconvex.
>
> More precisely, put $h(t)=F(\operatorname{diag}(1,t))$ for $t\in[-1,1]$. Then $h$ is convex. For
> $t\in(-1,1)$ let $H=h(t)$ and let $m$ be $h'(t)$, or either one-sided derivative if $h$ is not
> differentiable at $t$. With
> $$L=\frac{(1+t)m-pH}{1-t},$$
> $$U=\frac{pH+(1-t)m}{1+t},$$
> $$c^\ast=\min\lbrace U,\max\lbrace L,(p-1)m\rbrace \rbrace ,$$
> one has $L\le U$, and the polyaffine function
> $$P_t(A)=k+u a_{11}+v a_{22}+c^\ast\det A,$$
> where $k=c^\ast t-(p-1)H$, $u=pH-tm-c^\ast t$ and $v=m-c^\ast$, satisfies $P_t\le F$ on
> $\mathbb R^{2\times2}$ and $P_t(\operatorname{diag}(1,t))=F(\operatorname{diag}(1,t))$.
> At $t=\pm1$ the function $h(\pm1)\big[1+\tfrac p2(\pm\det A-1)\big]$ is a polyaffine support of $F$
> at $\operatorname{diag}(1,\pm1)$.

So the determinant multiplier is the "Burkholder value" $(p-1)h'(t)$, clamped to the interval
$[L,U]$. Polyconvexity implies quasiconvexity, hence:

> **Corollary 2.** For nonnegative, isotropic, positively $p$-homogeneous integrands on
> $\mathbb R^{2\times 2}$ with $p\ge 2$: rank-one convex $\iff$ quasiconvex $\iff$ polyconvex.

Theorem 1 is exactly the statement asked for in Question 1.7 of A. Guerra and J. Kristensen,
*Automatic quasiconvexity of homogeneous isotropic rank-one convex integrands*, Arch. Ration. Mech.
Anal. 245 (2022) 479–500, who proved polyconvexity at conformal matrices only. (The number 1.7 refers to the published version.) Neither statement uses the quasiconvexity of the
Burkholder integrand. Known examples show that nonnegativity (for $p>2$), the range $p\ge2$, isotropy
and the dimension cannot be dropped (Remark 7.4).

## 2. Notation

**Conformal coordinates.** Identify $\mathbb R^2$ with $\mathbb C$. For a matrix
$A=(a_{ij})\in\mathbb R^{2\times2}$ put
$$z=\tfrac12\big[(a_{11}+a_{22})+i(a_{21}-a_{12})\big],\qquad
  w=\tfrac12\big[(a_{11}-a_{22})+i(a_{21}+a_{12})\big].$$
Then $A\zeta=z\zeta+w\bar\zeta$, the map $A\mapsto(z,w)$ is a linear isomorphism
$\mathbb R^{2\times 2}\to\mathbb C^2$, and

- $\det A=|z|^2-|w|^2$; the singular values of $A$ are $|z|+|w|$ and $\big||z|-|w|\big|$;
- $\operatorname{rank}A\le 1$ iff $|z|=|w|$. Hence $\tau\mapsto(z_0+\tau\alpha, w_0+\tau\beta)$ is a
  rank-one line iff $|\alpha|=|\beta|\ne0$;
- if $R_\varphi$ is the rotation by $\varphi$, then $R_\varphi AR_\psi$ has coordinates
  $(e^{i(\varphi+\psi)}z, e^{i(\varphi-\psi)}w)$.

Consequently $F$ is isotropic iff $F(A)=\Phi(|z|,|w|)$ for a function $\Phi$ on $[0,\infty)^2$, and
$F$ is positively $p$-homogeneous iff $\Phi(\lambda x,\lambda y)=\lambda^p\Phi(x,y)$. Throughout,
$$x=|z|,\qquad y=|w|,\qquad \sigma=x+y=\sigma_1(A),\qquad \delta=x-y,\qquad \sigma\delta=\det A .$$
The matrix $E_t=\operatorname{diag}(1,t)$ has $(z,w)=(\tfrac{1+t}2,\tfrac{1-t}2)$, so the *profile* is
$$h(t)=F(E_t)=\Phi\big(\tfrac{1+t}2,\tfrac{1-t}2\big),\qquad
  \Phi(x,y)=\sigma^p h(\delta/\sigma),\qquad F(A)=\sigma_1(A)^p h\big(\det A/\sigma_1(A)^2\big).$$

**The number $\kappa$.** Throughout $\kappa=(p-2)/p\in[0,1)$.

**Supports.** A finite-valued $F$ is polyconvex iff for every $A_0$ there is a polyaffine $P$ with
$P\le F$ and $P(A_0)=F(A_0)$ (see Dacorogna's book, Section 5.2, and for rotationally invariant functions Dacorogna–Koshigoe,
Theorem 2.1; a short proof of the direction needed here is in Appendix A).

## 3. Three consequences of rank-one convexity

> **Lemma 3.** Let $F(A)=\Phi(|z|,|w|)$ be finite and rank-one convex. Then:
>
> (a) $t\mapsto F(E_t)$ is convex on $\mathbb R$; in particular $h$ is convex on $[-1,1]$.
>
> (b) For $x_0,y_0\ge 0$, the function $\tau\mapsto\Phi\big(\sqrt{x_0^2+\tau^2},\sqrt{y_0^2+\tau^2}\big)$
> is nondecreasing on $[0,\infty)$.
>
> (c) For $x_0,y_0>0$ and $\theta\in\mathbb R$, the function
> $g(\tau)=\Phi\big(|x_0+\tau e^{i\theta}|, |y_0+\tau|\big)$ is convex on $\mathbb R$.

*Proof.* In coordinates $(z,w)$ the three lines
$\tau\mapsto(\tfrac{1+\tau}2,\tfrac{1-\tau}2)$, $\tau\mapsto(x_0+i\tau, y_0+i\tau)$ and
$\tau\mapsto(x_0+\tau e^{i\theta}, y_0+\tau)$ have directions $(\alpha,\beta)$ with
$|\alpha|=|\beta|$, so they are rank-one lines and $F$ is convex along them. This is (a) and (c).
In (b) the function is in addition even in $\tau$, hence nondecreasing on $[0,\infty)$. $\square$

Part (b) says that $F$ grows along each hyperbola $\lbrace \det=\text{const}\rbrace$ (the Baker–Ericksen
inequality in integrated form). Part (c), together with its mirror image in which $z$ and $w$ are exchanged, is the only
"non-diagonal" information used below.

## 4. A Burkholder-type family

> **Lemma 4.** Let $p>2$ and $c_0,m\in\mathbb R$ with $c_0\ge\kappa|m|$. For $x,y\ge0$ and
> $\lambda>0$ put
> $$Q_\lambda(x,y):=-(p-1)c_0\lambda^p+p\lambda^{p-1}\big[(c_0-\kappa m)x+(c_0+\kappa m)y\big]
>   +(p-1)m\lambda^{p-2}(x^2-y^2).$$
> Then $Q_\lambda(x,y)\le\sigma^{p-1}(c_0\sigma+m\delta)_+$ for all $x,y\ge0$ and all $\lambda>0$.

In matrix terms the right-hand side is $\sigma_1^{p-2} (c_0\sigma_1^2+m\det A)_+$. For
$c_0=\kappa$, $m=1$ it is the positive part $B_p^+$ of the Burkholder integrand in the normalization
of Guerra–Kristensen ($m=-1$ gives its mirror image $B_p^+(AJ)$, $J=\operatorname{diag}(1,-1)$), and the
lemma contains the polyconvexity of $B_p^+$ (their Proposition 1.6).

*Proof.* If $\sigma=0$ then $Q_\lambda=-(p-1)c_0\lambda^p\le0$, so let $\sigma>0$. Note $c_0\ge\kappa|m|\ge0$.
Since $p\kappa=p-2$, we have $p[(c_0-\kappa m)x+(c_0+\kappa m)y]=pc_0\sigma-(p-2)m\delta$, so
$$Q_\lambda=-(p-1)c_0\lambda^p+\lambda^{p-1}\big(pc_0\sigma-(p-2)m\delta\big)+(p-1)m\lambda^{p-2}\sigma\delta,$$
$$\partial_\lambda Q_\lambda=-(p-1) \lambda^{p-3} (\lambda-\sigma) \big(pc_0\lambda+(p-2)m\delta\big).$$
Put $r(\lambda)=pc_0\lambda+(p-2)m\delta$. It is nondecreasing in $\lambda$ (as $c_0\ge0$) and, since
$|\delta|\le\sigma$, $r(\sigma)\ge p\sigma(c_0-\kappa|m|)\ge0$. Hence $\partial_\lambda Q_\lambda\le0$ on
$[\sigma,\infty)$, and there is $\lambda_0\in[0,\sigma]$ with $r\le 0$ on $(0,\lambda_0)$ and $r\ge0$
on $(\lambda_0,\sigma)$, i.e. $Q_\lambda$ is nonincreasing on $(0,\lambda_0)$ and nondecreasing on
$(\lambda_0,\sigma)$. Therefore
$$\sup_{\lambda>0}Q_\lambda=\max\Big\lbrace \lim_{\lambda\downarrow0}Q_\lambda, Q_\sigma\Big\rbrace =\max\lbrace 0, \sigma^{p-1}(c_0\sigma+m\delta)\rbrace ,$$
because $p>2$ (so the limit is $0$) and
$$Q_\sigma=\sigma^p c_0[-(p-1)+p]+\sigma^{p-1}\delta m[-(p-2)+(p-1)]=\sigma^{p-1}(c_0\sigma+m\delta).\qquad\square$$

## 5. Proof of Theorem 1

Let $F$ be as in Theorem 1, with $\Phi$ and $h$ as in Section 2. Being finite and rank-one convex,
$F$ is continuous. By Lemma 3(a), $h$ is convex, continuous and $\ge0$ on $[-1,1]$.

### 5.1 Reduction to the matrices $E_t$

Every $A\neq0$ equals $\lambda R_\varphi E_tR_\psi$ with $\lambda=\sigma_1(A)$ and
$t=\det A/\sigma_1(A)^2\in[-1,1]$. If $P$ is polyaffine, $P\le F$ and $P(E_t)=F(E_t)$, then
$A'\mapsto\lambda^pP(\lambda^{-1}R_{-\varphi}A'R_{-\psi})$ is polyaffine, lies below $F$, and
touches $F$ at $A$. So it suffices to find polyaffine supports at $0$ and at each $E_t$.
If $F(A_0)=0$, then $P\equiv0$ is a support at $A_0$ because $F\ge0$; this covers $A_0=0$ and every
$E_t$ with $h(t)=0$.

### 5.2 The conformal and anticonformal matrices $t=\pm1$

Let $x\ge y\ge0$. Lemma 3(b) with $(x_0,y_0)=(\sqrt{x^2-y^2},0)$ and $\tau=y$ gives
$\Phi(x,y)\ge\Phi(\sqrt{x^2-y^2},0)=h(1) (x^2-y^2)^{p/2}$. Together with $F\ge0$ this is
$$F(A) \ge h(1) (\det A)_+^{p/2}\qquad\text{for all }A,$$
with equality at $E_1=I$. As $r\mapsto r_+^{p/2}$ is convex ($p\ge2$) with slope $p/2$ at $r=1$,
the polyaffine function $P(A)=h(1) [1+\tfrac p2(\det A-1)]$ is a support at $E_1$. The case $t=-1$
follows by applying this to $\tilde F(A)=F(AJ)$, $J=\operatorname{diag}(1,-1)$ (see Case II below).

### 5.3 A point $t\in(-1,1)$ where $h$ is differentiable and $h(t)>0$

(If $h$ is differentiable at $t$ and $h(t)=0$, then $t$ is a minimum point of $h\ge0$, so $h'(t)=0$,
$L=U=c^\ast=0$ and $P_t\equiv0$, which is a support by 5.1.) Fix a $t$ as in the title and write
$$H=h(t)>0,\quad m=h'(t),\quad \ell(s)=H+m(s-t),\quad c_0=\ell(0)=H-tm,\quad
  (x_0,y_0)=\big(\tfrac{1+t}2,\tfrac{1-t}2\big).$$
By convexity $h\ge\ell$ on $[-1,1]$. Since $\Phi(x,y)=\sigma^ph(\delta/\sigma)$, $\Phi$ is
differentiable at $(x_0,y_0)$ and
$$\Phi_x=pH+(1-t)m,\qquad \Phi_y=pH-(1+t)m,\qquad x_0\Phi_x+y_0\Phi_y=pH.\qquad(5.1)$$
In Lemma 3(b) at $(x_0,y_0)$ the arguments are $\sqrt{x_0^2+\tau^2}=x_0+\tau^2/(2x_0)+O(\tau^4)$ and
$\sqrt{y_0^2+\tau^2}=y_0+\tau^2/(2y_0)+O(\tau^4)$; since $\Phi$ is differentiable at $(x_0,y_0)$, the
monotonicity gives $\Phi_x/x_0+\Phi_y/y_0\ge0$, that is
$$C:=pH-2tm \ge 0 .\qquad(5.2)$$
Note $\ell(\pm\kappa)=c_0\pm\kappa m$. At least one of the following holds: $c_0\ge\kappa|m|$
(Case III), or $\ell(-\kappa)<0$ (Case I), or $\ell(\kappa)<0$ (Case II).

**Case III: $\ell(-\kappa)\ge0$ and $\ell(\kappa)\ge0$.** Since $h\ge\ell$ and $h\ge0$, for every
$A$ with coordinates $(z,w)$,
$$F(A)=\sigma^ph(\delta/\sigma) \ge \sigma^{p} \ell(\delta/\sigma)_+=\sigma^{p-1}(c_0\sigma+m\delta)_+ .$$
If $p>2$, Lemma 4 with $\lambda=1$, followed by $|z|\ge\operatorname{Re}z$, $|w|\ge\operatorname{Re}w$
and $\ell(\mp\kappa)\ge0$, gives
$$F(A) \ge P_{\mathrm{III}}(A):=-(p-1)c_0+p \ell(-\kappa)\operatorname{Re}z+p \ell(\kappa)\operatorname{Re}w+(p-1)m\det A .$$
$P_{\mathrm{III}}$ is polyaffine and touches $F$ at $E_t$:
$$P_{\mathrm{III}}(E_t)=-(p-1)c_0+p c_0-(p-2)mt+(p-1)mt=c_0+mt=H.$$
If $p=2$ (so $\kappa=0$ and $c_0=C/2\ge0$), use instead
$$F(A)\ge\sigma^2\ell(\delta/\sigma)=c_0\sigma_1(A)^2+m\det A\ge c_0(2a_{11}-1)+m\det A,$$
which is the same formula $P_{\mathrm{III}}$ (the last step is $\sigma_1(A)\ge|a_{11}|$); here nonnegativity of $F$ is not even
needed.

**Case I: $\ell(-\kappa)<0$** (so $p>2$). *First, $m>0$ and $t>-\kappa$.* Indeed
$m(t+\kappa)=\ell(t)-\ell(-\kappa)>0$. If $m<0$, then $t<-\kappa\le 0$, and (5.2) gives
$pH\ge 2|t||m|$ while $\ell(-\kappa)<0$ gives $H<|m|(|t|-\kappa)$; together
$2|t|/p<|t|-\kappa$, i.e. $\kappa<\kappa|t|$, which is absurd. (So Cases I and II
exclude each other: Case II is the mirror situation $m<0$.)

Define
$$c:=\frac{\Phi_x}{2x_0}=\frac{pH+(1-t)m}{1+t}>0,\qquad
  \gamma:=\Phi_y+\frac{y_0}{x_0}\Phi_x=\frac{2C}{1+t}\ge0,\qquad \alpha:=H-\gamma y_0-ct .$$
(These are the coefficients of the tangent plane at $(y_0,t)$ of $F$ written as a function of
$(|w|,\det A)$.) The following identities and inequalities are elementary; (5.1), (5.2), $m>0$ and
$\ell(-\kappa)<0$ are used.

1. $\gamma y_0+2ct=pH$. Hence $\alpha=ct-(p-1)H$ and
   $$p\alpha+(p-1)\gamma y_0+(p-2)ct=0 .\qquad(5.3)$$
2. $\alpha=-\dfrac{(1-t)C+(p-2)(1+t)H}{2(1+t)}<0$.
3. Put $\mu:=-\dfrac{(p-1)\gamma}{(p-2)c}$. Then
   $$\mu+2=\frac{-2p \ell(-\kappa)}{(p-2)\Phi_x}>0,\qquad
     2t-\mu=\frac{2\big[pH\big((p-1)+(p-2)t\big)-tm\big(p+(p-2)t\big)\big]}{(p-2)\Phi_x} \ge 0 .$$
   (The last numerator equals $t(p-2)\Phi_x+(p-1)C$, which is $\ge0$ when $t\ge0$; when $t<0$ both
   of its displayed terms are $\ge 0$ because $m>0$.) Therefore
   $$\cos\theta:=\frac{\mu+2y_0}{2x_0}=\frac{\mu+1-t}{1+t}\in[-1,1]$$
   defines an angle $\theta$ (indeed $-1\le\cos\theta\le1$ is the same as $-2\le\mu\le2t$).

*Claim: $\alpha+\gamma|w|+c\det A\le F(A)$ for every $A$, with equality at $E_t$.*

Fix $A$ with coordinates $(z_1,w_1)$ and put $x_1=|z_1|$, $y_1=|w_1|$, $d_1=\det A=x_1^2-y_1^2$. For
$\lambda>0$ let
$$\psi(\lambda)=\lambda^p\Big[\alpha+\gamma\frac{y_1}{\lambda}+c\frac{d_1}{\lambda^2}\Big]
  =\alpha\lambda^p+\gamma y_1\lambda^{p-1}+c d_1\lambda^{p-2},$$
so that $\psi(1)=\alpha+\gamma|w_1|+c\det A$. Because $p>2$ and $\alpha<0$, $\psi(\lambda)\to0$ as
$\lambda\downarrow0$ and $\psi(\lambda)\to-\infty$ as $\lambda\to\infty$.

- If $\psi\le0$ on $(0,\infty)$, then $\psi(1)\le0\le F(A)$.
- Otherwise $\psi$ attains a positive maximum at some $\lambda^\ast\in(0,\infty)$, and
  $\psi'(\lambda^\ast)=0$ reads
  $$p\alpha+(p-1)\gamma y^\ast+(p-2)c d^\ast=0,\qquad y^\ast:=y_1/\lambda^\ast,\quad d^\ast:=d_1/{\lambda^\ast}^2 .$$
  Subtracting (5.3): $d^\ast=t+\mu \tau^\ast$ with $\tau^\ast:=y^\ast-y_0$.

  Now consider the rank-one line $A_\tau$ with coordinates $(x_0+\tau e^{i\theta}, y_0+\tau)$ and
  $g(\tau)=F(A_\tau)$. By Lemma 3(c) $g$ is convex. It is differentiable at $0$ with
  $g'(0)=\Phi_x\cos\theta+\Phi_y=\gamma+\mu c$. Hence, for all $\tau$,
  $$g(\tau) \ge H+(\gamma+\mu c)\tau=\alpha+\gamma(y_0+\tau)+c(t+\mu\tau).\qquad(5.4)$$
  Along this line
  $$\det A_\tau=|x_0+\tau e^{i\theta}|^2-(y_0+\tau)^2=t+(2x_0\cos\theta-2y_0)\tau=t+\mu\tau .$$
  At $\tau=\tau^\ast$ the matrix $A_{\tau^\ast}$ therefore has $|w|=|y_0+\tau^\ast|=y^\ast$ and
  $\det=d^\ast$, hence $|z|^2=d^\ast+{y^\ast}^2=(x_1/\lambda^\ast)^2$. So $A_{\tau^\ast}$ and
  $A/\lambda^\ast$ have the same $(|z|,|w|)$, and $g(\tau^\ast)=F(A/\lambda^\ast)={\lambda^\ast}^{-p}F(A)$.
  With (5.4),
  $$F(A)={\lambda^\ast}^{p}g(\tau^\ast) \ge {\lambda^\ast}^{p}\big[\alpha+\gamma y^\ast+c d^\ast\big]=\psi(\lambda^\ast) \ge \psi(1).$$

In both cases $F(A)\ge\alpha+\gamma|w_1|+c\det A$. At $A=E_t$ the right-hand side is
$\alpha+\gamma y_0+ct=H$. This proves the claim. Since $\gamma\ge0$ and $|w|\ge\operatorname{Re}w$,
$$P_{\mathrm{I}}(A):=\alpha+\gamma\operatorname{Re}w+c\det A$$
is a polyaffine support of $F$ at $E_t$ (recall $\operatorname{Re}w=\tfrac12(a_{11}-a_{22})$).

**Case II: $\ell(\kappa)<0$.** Let $J=\operatorname{diag}(1,-1)$ and $\tilde F(A)=F(AJ)$. Since
$(AJ)\zeta=A\bar\zeta=w\zeta+z\bar\zeta$, passing from $A$ to $AJ$ swaps $z$ and $w$. Thus
$\tilde F$ is isotropic, nonnegative, positively $p$-homogeneous and rank-one convex, with
$\tilde\Phi(x,y)=\Phi(y,x)$ and $\tilde h(s)=h(-s)$. Its tangent line at $-t$ is
$\tilde\ell(s)=\ell(-s)$, and $\tilde\ell(-\kappa)=\ell(\kappa)<0$. Case I gives a polyaffine
$\tilde P\le\tilde F$ with $\tilde P(E_{-t})=\tilde F(E_{-t})$. Then $P_{\mathrm{II}}(A):=\tilde P(AJ)$ is
polyaffine ($\det(AJ)=-\det A$), $P_{\mathrm{II}}\le F$, and
$P_{\mathrm{II}}(E_t)=\tilde P(E_{-t})=\tilde F(E_{-t})=F(E_t)$.

### 5.4 Points where $h$ is not differentiable

Let $t_0\in(-1,1)$ be such a point and let $m_0$ be one of the two one-sided derivatives of $h$ at
$t_0$, say $m_0=h'(t_0+)$. A convex function is differentiable off a countable set, so there are
points of differentiability $t_n\downarrow t_0$; then $h(t_n)\to h(t_0)$ and $h'(t_n)\to m_0$. By 5.3,
$P_{t_n}\le F$ and $P_{t_n}(E_{t_n})=h(t_n)$, where $P_{t_n}$ is given by the formula of Theorem 1 (see
Section 6). The coefficients in that formula are continuous in $(t,H,m)$ for $|t|<1$, because
clamping is continuous. Hence $P_{t_n}$ converges locally uniformly to the function $P_{t_0}$ given by
the same formula with $m=m_0$, so $P_{t_0}\le F$ and $P_{t_0}(E_{t_0})=\lim h(t_n)=h(t_0)$. The left
derivative is treated in the same way.

### 5.5 Conclusion

By 5.1–5.4 there is a polyaffine support at every matrix, so $F$ is polyconvex (Appendix A).
That the supports of 5.3 are the functions $P_t$ of Theorem 1 is checked in Section 6. $\blacksquare$

## 6. The support in closed form

For $|t|<1$ let $L=-\Phi_y/(2y_0)$ and $U=\Phi_x/(2x_0)$, which are the expressions in Theorem 1.
Direct computation gives
$$U-L=\frac{2C}{1-t^2}\ge0,\qquad U-(p-1)m=\frac{p \ell(-\kappa)}{1+t},\qquad (p-1)m-L=\frac{p \ell(\kappa)}{1-t}.$$
So Case III is $L\le(p-1)m\le U$, Case I is $(p-1)m>U$, Case II is $(p-1)m<L$, and in each case the
determinant coefficient of the support constructed in 5.3 is
$c^\ast=\min\lbrace U,\max\lbrace L,(p-1)m\rbrace \rbrace$:

| Case | condition | $c^\ast$ | coefficient of $\operatorname{Re}z$ | coefficient of $\operatorname{Re}w$ |
| --- | --- | --- | --- | --- |
| III | $\ell(\pm\kappa)\ge0$ | $(p-1)m$ | $p \ell(-\kappa)$ | $p \ell(\kappa)$ |
| I | $\ell(-\kappa)<0$ | $U$ | $0$ | $2C/(1+t)$ |
| II | $\ell(\kappa)<0$ | $L$ | $2C/(1-t)$ | $0$ |

In all three cases the support is $\alpha+\beta\operatorname{Re}z+\gamma\operatorname{Re}w+c^\ast\det A$
with $\beta=\Phi_x-(1+t)c^\ast\ge0$, $\gamma=\Phi_y+(1-t)c^\ast\ge0$, $\alpha=c^\ast t-(p-1)H$.
Since $\operatorname{Re}z=\tfrac12(a_{11}+a_{22})$ and $\operatorname{Re}w=\tfrac12(a_{11}-a_{22})$,
this is the function $P_t$ of Theorem 1, with $k=\alpha$, $u=\tfrac12(\beta+\gamma)$ and
$v=\tfrac12(\beta-\gamma)$.

**In the notation of the ledger** (the [one-multiplier criterion](IWANIEC_MORREY_GENERAL_SUPPORT_CRITERION.md),
a specialization of the Dacorogna–Koshigoe support criterion): $P_t=G_{t,c^\ast}$,
the orientation interval (2) is $[L,U]$, and inequality (3) holds for every $a\ge0$, $s\in[-1,1]$
with $c=c^\ast$. Hence $c_{\min}(t)\le c^\ast\le c_{\max}(t)$ for every nonnegative rank-one convex
profile, every $p>2$ and every $t$. This is the "universal existence of the multiplier" left open
in ledger entry **I12**.

## 7. Remarks

**7.1 Why it works.** For a positively homogeneous $F\ge0$ and a candidate minorant
$q=\alpha+\gamma|w|+c\det A$ with $\alpha<0$, the inequality $q\le F$ on all of $\mathbb R^{2\times2}$
follows from $q\le F$ on the single surface where $\frac{d}{d\lambda}\lambda^pq(A/\lambda)=0$ at
$\lambda=1$. In the coordinates $(|w|,\det A)$ this surface is a straight line through the base
point, and (5.3) identifies its slope $\mu$. Rank-one lines along which $w$ moves radially are
*also* straight lines in these coordinates, with slopes exactly in
$[-2(x_0+y_0), 2(x_0-y_0)]$. The lower bound $\mu\ge-2(x_0+y_0)$ is exactly the Case I condition $\ell(-\kappa)\le0$, and the upper
bound then follows from (5.2) and $m>0$; so in Case I one convexity inequality along one rank-one
line does everything. When $\mu$ leaves the interval, the Burkholder-type support of Case III takes
over; the changeover is at $\ell(-\kappa)=0$, where both constructions coincide.

**7.2 The support depends only on the 1-jet** $(h(t),h'(t))$. No second-derivative ("acoustic")
condition and no smoothness of $h$ is used. Of the full rank-one convexity only Lemma 3 and its
mirror image are used. For $C^2$ profiles this is no loss: at $E_t$ the Legendre–Hadamard form of an
isotropic function is a quadratic without linear terms in the two cosines $(c_1,c_2)\in[-1,1]^2$ of
the angles between the rank-one direction and $z$, $w$; its minimum over the square is attained at
the centre (Lemma 3(b)) or on the boundary (Lemma 3(c) and its mirror).

**7.3 Generators.** Homogenizing the supports shows that at each differentiability point $F$
dominates, with equality on the ray through $E_t$, one of the polyconvex functions

- $\sigma_1^{p-2} (c_0\sigma_1^2+m\det A)_+$ with $c_0\ge\kappa|m|$ (Burkholder type), or
- the function
  $$\sup_{\lambda>0}\big[\alpha\lambda^p+\gamma\lambda^{p-1}|w|+c\lambda^{p-2}\det A\big]_+$$
  with $\alpha<0$, $\gamma\ge0$, $c>0$ and $(p-1)^2\gamma^2\le4p(p-2)|\alpha|c$, or its mirror image
  under $A\mapsto AJ$.

The last inequality says exactly that the line of Remark 7.1 does not cross the parabola
$\det A=-|w|^2$, i.e. that it is the image of a rank-one line; equality is the Burkholder case. The functions $(\pm\det)_+^{p/2}$ are the members with $\gamma=0$.

**7.4 Sharpness of the hypotheses** (all from the literature).
*Nonnegativity, $p>2$:* the Burkholder integrand $B_p$ and the Dacorogna–Marcellini integrands
$|A|^2(|A|^2-2\gamma\det A)$, $1<|\gamma|\le2/\sqrt3$ ($p=4$; Alibert–Dacorogna), are isotropic,
homogeneous, rank-one convex and not polyconvex. Nonnegativity enters the proof in Case III
($h\ge\ell_+$), in Case I ($\psi\le 0\Rightarrow\psi(1)\le F$) and at $t=\pm1$. It is also necessary: a
positively $p$-homogeneous polyconvex function with $p>2$ is $\ge0$ (scale the support at $0$). For
$p=2$ it is not needed (Remark 7.5).
*$p\ge2$:* for $p<2$, $B_p^+$ is not polyconvex at the identity (Guerra–Kristensen, Remark 1.4(ii)).
*Isotropy and dimension:* according to Guerra–Kristensen, Remark 1.4(iii) and Proposition 1.5
(for the former see also the ledger's note on their Proposition 3.7).
*Homogeneity:* if $f$ is a Dacorogna–Marcellini integrand with $1<|\gamma|\le2/\sqrt3$, then $e^{f}$ is
positive, isotropic and rank-one convex but not polyconvex (take a finitely supported measure that
violates Jensen's inequality for $f$ and rescale it towards $0$).

**7.5 The case $p=2$** needs no sign condition: every isotropic, positively $2$-homogeneous
rank-one convex $F$ satisfies $F\ge c_0\sigma_1^2+m\det A$ with $c_0\ge0$ (Case III), and for
$t=\pm1$ one passes to the limit. This recovers the ledger's "signed $p=2$" statement.

**7.6 Example.** For the ledger's exact $p=4$ profile (entry I06), which the "hybrid" generator
cone does not reach, Theorem 1 gives a global polyaffine support at *every* base (checked
numerically in Section 9); the generators of the second type in 7.3 are what that cone lacks.

**7.7 Related results.** Guerra and Kristensen point out two neighbours of their question: compact
connected isotropic *sets* in $\mathbb R^{2\times2}$ that are rank-one convex are polyconvex
(Cardaliaguet–Tahraoui; Conti–De Lellis–Müller–Romeo), and rank-one convexity implies polyconvexity
for isotropic $0$-homogeneous integrands on matrices with positive determinant (Martin–Ghiba–Neff).
Applied to the sublevel sets of $F$ (ledger entry I13), the set theorem does not give Theorem 1: the
map $A\mapsto(A,\det A)$ is not homogeneous, so supports of a sublevel set do not rescale to supports
of $F$, and on $GL^+(2)$ there is an isotropic rank-one convex function with compact connected
sublevel sets that is not polyconvex (Voss–Ghiba–Martin–Neff). The reduction of polyconvexity of
isotropic functions to diagonal matrices goes back to Dacorogna–Koshigoe in two dimensions (see
also Wiedemann–Peter); Theorem 1 supplies the existence statement that this reduction leaves open.

## 8. What this settles and what it does not

Settled (as hand theorems): Question 1.7 of Guerra–Kristensen; ledger gate **I12** and with it the
"main $p>2$ gate" of the roadmap. Since polyconvexity implies Jensen's inequality for every
minors-preserving probability measure, the three- and four-atom inequalities of **I14** hold in this
class, and so do the support inequalities left open in **I21**, with the common multiplier $c^\ast$ on
the compact annulus of the later zero-amplitude entry; the negative-witness searches **I20**,
**I22**, **I23** look for a counterexample that does not exist.

Not settled:

- **Morrey's problem on $\mathbb R^{2\times2}$** for general (anisotropic or non-homogeneous)
  integrands. Nothing here bears on it beyond Corollary 2. (Cassese's preprint gives homogeneous
  rank-one convex integrands on $\mathbb R^{2\times3}$ that are not quasiconvex and states that the
  $2\times2$ case remains open.)
- Signed isotropic homogeneous integrands with $p>2$. They are never polyconvex if they take a
  negative value, so only quasiconvexity can be asked; quasiconvexity at $0$ is Conjecture 1 of
  Cassese's preprint. Two cases are covered by 2026 preprints: $B_p$ itself (Agazzi et al.) and the
  isotropic quartic polynomials (Bruno–Pasqualotto). The proof above adds one conditional piece: in
  Case III the bound $F\ge\sigma_1^{p-2}(c_0\sigma_1^2+m\det A)$ holds without the sign condition, and
  the right-hand side is quasiconvex as soon as $B_p$ is, so $F$ is then quasiconvex at such $E_t$.
  Cases I–II use $F\ge0$.
- The range $1<p<2$, where polyconvexity fails (Remark 7.4) and quasiconvexity is tied to the
  Burkholder integrand (Guerra–Kristensen, Theorem 1.2; the ledger's conditional route).

## 9. Computer checks

Three scripts were used. They are not committed with this note; they can be added under
`research/audit/`.

- `iwaniec_pge2_polyconvexity_identities.py`
  (needs sympy; seconds). 44 exact symbolic identities: the conformal coordinates, the derivative
  factorization in Lemma 4, (5.1)–(5.3), items 1–3 of Case I, $g'(0)=\gamma+\mu c$, and the formulas
  of Section 6.
- `iwaniec_pge2_polyconvexity_support_check.py`
  (needs numpy; about 8 minutes). For $p\in\lbrace 2.5,3,4,6\rbrace$ and eight to twelve rank-one
  convex integrands per exponent, including the ledger's exact $p=4$ profile and the positive parts
  of the Dacorogna–Marcellini functions up to $\gamma=2/\sqrt3$: brute-force rank-one convexity of
  each example; $P_t\le F$ on fine grids in the ledger's variables $(a,s)$ and on random $2\times2$
  matrices; a link-by-link numerical trace of the Case I argument; controls showing that the
  support fails for profiles that are not rank-one convex and for other choices of the multiplier.
- `iwaniec_pge2_polyconvexity_adversarial_socp.py`
  (needs numpy, scipy and cvxpy with CLARABEL; about 5 minutes). For a fixed base $t$, case and test
  point, the value of $F-P_t$ at the test point is *linear* in the profile $h$, so its minimum over
  all spline profiles satisfying the rank-one convexity conditions is a second-order cone program.
  About 17,600 such programs for $p\in\lbrace 2.5,3,4,6,10\rbrace$: every minimum is $\ge0$ up to
  solver tolerance, and a control with the multipliers of Cases I and III swapped is violated.

In the runs made for this note, the first printed `all 44 symbolic identities verified` and the
other two ended with `OVERALL: PASS`.

**Independent pass.** A separate AI agent, given only this text, re-derived every identity with its
own symbolic code and tested $P_t\le F$ directly on $2\times2$ matrices with its own harness: 590
numerically rank-one convex pairs (exponent, integrand) for ten exponents from $2$ to $10$, about
28,000 base points (including kinks with one-sided derivatives, zeros of $h$, the changeover between
the cases, and $t$ within $10^{-6}$ of $\pm1$) and about 225,000 matrices per base. The worst value of
$F-P_t$ was $-2\times10^{-16}$ in rounding units; functions that failed its rank-one test and
perturbed multipliers ($c^\ast\pm1\%$ of $U-L$) broke the support. Its coarse linear-programming
relaxation produced small negative optima that disappeared under refinement in the one instance it
re-examined; the others were not re-run. Its verdict was "correct modulo fixable gaps", all of them
expository; they are fixed above.

These checks support the proof; they are not part of it.

## Appendix A. Polyaffine supports imply polyconvexity

Let $T(A)=(A,\det A)\in\mathbb R^5$ and suppose that for every $A_0$ there is
$b(A_0)\in\mathbb R^5$ with $F(A)\ge F(A_0)+\langle b(A_0),T(A)-T(A_0)\rangle$ for all $A$. Define
$$g(X)=\inf\Big\lbrace \sum_i\lambda_iF(A_i) : \lambda_i\ge0, \sum_i\lambda_i=1, \sum_i\lambda_iT(A_i)=X\Big\rbrace $$
(finite sums). The convex hull of $T(\mathbb R^{2\times2})$ is $\mathbb R^5$, because
$\tfrac12T(B+C)+\tfrac12T(B-C)=(B,\det B+\det C)$ and $\det C$ is arbitrary; so $g<\infty$. Averaging
the support inequalities gives $g(X)\ge F(A_0)+\langle b(A_0),X-T(A_0)\rangle>-\infty$. Thus $g$ is a
real-valued convex function, and $g(T(A))=F(A)$: "$\le$" is trivial and "$\ge$" is the last
inequality with $A_0=A$. $\square$

## References

- A. Agazzi, K. Astala, R. Bañuelos, G. Bruno, G. Cassese, D. Faraco, A. Guerra, M. Hormozi,
  B. Kirchheim, A. Koski, V. Kovač, J. Kristensen, F. Pasqualotto, I. Prause, E. Saksman,
  V. Šverák, L. Székelyhidi, R. Tione, A. Volberg, H. Yang, Sharp higher integrability theory,
  Part I: the $L^p$-norm of the Beurling–Ahlfors transform, preprint, arXiv:2609.28311.
- J.-J. Alibert, B. Dacorogna, An example of a quasiconvex function that is not polyconvex in two
  dimensions, Arch. Ration. Mech. Anal. 117 (1992) 155–166.
- G. Bruno, F. Pasqualotto, Quasiconvexity for the Dacorogna–Marcellini energy, preprint,
  arXiv:2608.06367.
- P. Cardaliaguet, R. Tahraoui, Equivalence between rank-one convexity and polyconvexity for
  isotropic sets of $\mathbb R^{2\times2}$, Parts I and II, Nonlinear Anal. 50 (2002) 1179–1199 and
  1201–1239.
- G. Cassese, A solution to Morrey's problem in $\mathbb R^{2\times m}$, preprint, arXiv:2608.03488.
- S. Conti, C. De Lellis, S. Müller, M. Romeo, Polyconvexity equals rank-one convexity for connected
  isotropic sets in $\mathbb M^{2\times2}$, C. R. Math. Acad. Sci. Paris 337 (2003) 233–238.
- B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed., Springer 2008.
- B. Dacorogna, H. Koshigoe, On the different notions of convexity for rotationally invariant
  functions, Ann. Fac. Sci. Toulouse Math. (6) 2 (1993) 163–184.
- B. Dacorogna, P. Marcellini, A counterexample in the vectorial calculus of variations, in
  *Material Instabilities in Continuum Mechanics*, Oxford Univ. Press 1988, 77–83.
- A. Guerra, J. Kristensen, Automatic quasiconvexity of homogeneous isotropic rank-one convex
  integrands, Arch. Ration. Mech. Anal. 245 (2022) 479–500; arXiv:2112.10563.
- R. J. Martin, I.-D. Ghiba, P. Neff, Rank-one convexity implies polyconvexity for isotropic,
  objective and isochoric elastic energies in the two-dimensional case, Proc. Roy. Soc. Edinburgh
  Sect. A 147 (2017) 571–597.
- J. Voss, I.-D. Ghiba, R. J. Martin, P. Neff, A rank-one convex, nonpolyconvex isotropic function on
  $GL^+(2)$ with compact connected sublevel sets, Proc. Roy. Soc. Edinburgh Sect. A 152 (2022)
  356–381; arXiv:2009.09690.
- D. Wiedemann, M. A. Peter, Characterization of polyconvex isotropic functions, Calc. Var. Partial
  Differential Equations 65 (2026), article 115.
