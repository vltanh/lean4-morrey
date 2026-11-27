# Removing exact homogeneity: logarithmic scaling and null-Lagrangian drift

27 November 2026. **Hand proof, not a new Lean theorem.** The sole external
quasiconvexity input is the repository's already verified signed homogeneous
isotropic theorem for every positive exponent, recorded in
[the theorem overview](../HomogeneousIsotropic/README.md) and
[Signed/Main.lean](../../Morrey/HomogeneousIsotropic/Signed/Main.lean).
The present argument does not assume differentiability, a sign condition,
a growth bound, or a bound on the complexity of gradient tests.

This closes an entire class without exact homogeneity. It does not establish
quasiconvexity for every nonhomogeneous isotropic rank-one convex function.
Its new assumption is an exact first-order logarithmic scaling law, or,
equivalently in the nontrivial case, homogeneity modulo a determinant drift.

## 1. The theorem

Write $\mathbb M=\mathbb R^{2\times2}$, $d(X)=\det X$, and
$r(X)=|X|_F$, the **Frobenius** norm. Isotropy here means invariance under
independent left and right proper rotations, as in the verified theorem.

**Theorem A (logarithmic degree two).** Let $F:\mathbb M\to\mathbb R$
be finite-valued, isotropic and rank-one convex. Suppose that a real
constant $c$ satisfies

$$
 F(tX)=t^2F(X)+c\,t^2\log(t)\,d(X)
 \qquad(t>0,\ X\in\mathbb M).                         \tag{1}
$$

Then $F$ is quasiconvex at every matrix, for arbitrary bounded compatible
gradient tests. If $c\ne0$, it is not polyconvex.

The conclusion concerns the original signed function $F$, not a positive
reparametrization or a determinant-stabilized replacement. Equation (1)
forces $F(0)=0$. The nonzero-drift class contains functions with arbitrary
angular dependence compatible with rank-one convexity; Section 5 gives an
explicit example outside the previously treated separated-angular class.

The elementary construction used in the proof is valid without isotropy.
Isotropy is used only to apply the verified homogeneous theorem to the
approximants. Thus the construction also transfers any future full
anisotropic homogeneous theorem to this logarithmic class.

## 2. Homogeneous approximants with a second-order curvature repair

Finite rank-one convex functions are locally Lipschitz: they are separately
convex in the four matrix entries, and the usual bounds on a slightly larger
coordinate box bound their one-dimensional slopes on each smaller box.
Choose a Lipschitz constant $L\ge0$ for $F$ on a neighbourhood of the
closed Frobenius unit ball, and put

$$
 M=\max_{|n|_F=1}|F(n)|,\qquad
 K=2L+M+\frac{|c|}{2},\qquad C=\frac K2.
                                                               \tag{2}
$$

For $X\ne0$, define

$$
 H(X)=F(X)-c\,d(X)\log r(X).
$$

Equation (1) says exactly that $H$ is positively 2-homogeneous.
For $0<\varepsilon\le1$, set

$$
\begin{aligned}
 G_\varepsilon(X)
 &=r^\varepsilon\big(c\,d(X)+\varepsilon H(X)\big)
       +C\varepsilon^2r^{2+\varepsilon}\\
 &=\varepsilon r^\varepsilon F(X)
       +c r^\varepsilon(1-\varepsilon\log r)d(X)
       +C\varepsilon^2r^{2+\varepsilon},
\end{aligned}                                                   \tag{3}
$$

and $G_\varepsilon(0)=0$. It is finite, continuous, isotropic and
positively $(2+\varepsilon)$-homogeneous. The important point is that
it is rank-one convex with a correction of order $\varepsilon^2$,
although its first-order variation is the prescribed nonhomogeneous $F$.

### 2.1 Distributional calculation on every rank-one line

Fix a constant rank-one direction $V$ and a line
$X(\tau)=A+\tau V$. Work on an open interval on which $r>0$.
Write

$$
 f(\tau)=F(X(\tau)),\quad q=X:V,\quad
 n=X/r,\quad \alpha=n:V=q/r.
$$

The restriction $f$ is convex. Therefore it is locally Lipschitz,
$f'$ exists almost everywhere, and its distributional second derivative
$f''$ is a nonnegative locally finite Radon measure. Because $V$ has
rank one, $d(X(\tau))$ is affine and $d''=0$.

At each parameter where $f'$ exists, the directional derivative
$D_VF(n)$ exists as well. This does **not** require differentiability
of $F$ in the ambient matrix space. Indeed, at that particular parameter
hold the positive number $r$ fixed, apply (1) to
$X+hV=r(n+(h/r)V)$, and differentiate in $h$. This gives

$$
 F(X)=r^2F(n)+c\,d(X)\log r,\qquad
 f'=rD_VF(n)+c\log r\,d'.                              \tag{4}
$$

In particular $|D_VF(n)|\le L|V|_F$.

For completeness the smooth scalar factors in (3) have derivatives

$$
\begin{aligned}
 (r^\varepsilon)'&=\varepsilon r^{\varepsilon-2}q,\\
 (r^\varepsilon)''&=\varepsilon r^{\varepsilon-2}|V|_F^2
              +\varepsilon(\varepsilon-2)r^{\varepsilon-4}q^2,\\
 \big(r^\varepsilon(1-\varepsilon\log r)\big)'
       &=-\varepsilon^2r^{\varepsilon-2}q\log r,\\
 \big(r^\varepsilon(1-\varepsilon\log r)\big)''
       &=-\varepsilon^2\left[
          r^{\varepsilon-2}|V|_F^2\log r
          +(\varepsilon-2)r^{\varepsilon-4}q^2\log r
          +r^{\varepsilon-4}q^2\right].
\end{aligned}                                                   \tag{5}
$$

The product rule for a smooth factor times a locally Lipschitz convex
function, followed by (4), gives the exact equality of Radon measures

$$
 \boxed{
  (G_\varepsilon\circ X)''
   =\varepsilon r^\varepsilon f''
     +\varepsilon^2r^\varepsilon R_\varepsilon\,d\tau
     +C\varepsilon^2(r^{2+\varepsilon})''\,d\tau,
 }                                                             \tag{6}
$$

where the almost-everywhere defined remainder is

$$
 R_\varepsilon
  =2\alpha D_VF(n)
    +\big(|V|_F^2+(\varepsilon-2)\alpha^2\big)F(n)
    -c\alpha^2\det n.                                         \tag{7}
$$

In particular the singular part of (6) is nonnegative; it has not been
discarded or replaced by an almost-everywhere Hessian test.

Since $|n|_F=1$,

$$
 |\alpha|\le |V|_F,\quad |\det n|\le\tfrac12,
 \quad
 \left||V|_F^2+(\varepsilon-2)\alpha^2\right|
       \le |V|_F^2\qquad(0<\varepsilon\le1).
$$

Consequently

$$
 |R_\varepsilon|\le K|V|_F^2.                                 \tag{8}
$$

The correction has strictly sufficient radial curvature:

$$
 (r^{2+\varepsilon})''
    =(2+\varepsilon)r^\varepsilon|V|_F^2
      +\varepsilon(2+\varepsilon)r^{\varepsilon-2}q^2
    \ge2r^\varepsilon|V|_F^2.                                 \tag{9}
$$

Equations (2), (6), (8), and (9) prove that the second derivative
measure is nonnegative. Thus $G_\varepsilon$ is convex on every
rank-one interval avoiding the origin.

### 2.2 Lines crossing the origin

The first formula in (3), the exact homogeneity of $H$, and its bounded
restriction to the unit sphere give
$G_\varepsilon(X)=O(r^{2+\varepsilon})$ as $r\downarrow0$.
On a line through zero both one-sided derivatives at zero therefore vanish.
The convex restrictions on the two half-lines glue convexly. Lines of zero
direction are constant. This proves **global rank-one convexity** of
$G_\varepsilon$, including all nonsmooth and singular-matrix points.

## 3. Passing the verified homogeneous theorem to the original energy

The signed homogeneous theorem applies to $G_\varepsilon$, since its
degree is $2+\varepsilon>0$, its values are finite, and it is isotropic
and rank-one convex. Thus each $G_\varepsilon$ is quasiconvex.
The determinant is a null Lagrangian, so

$$
 T_\varepsilon(X)=\frac{G_\varepsilon(X)-c\,d(X)}{\varepsilon}
                                                               \tag{10}
$$

is quasiconvex as well. The first formula in (3) gives

$$
 T_\varepsilon
   =r^\varepsilon H
      +c\,d\frac{r^\varepsilon-1}{\varepsilon}
      +C\varepsilon r^{2+\varepsilon}
    \longrightarrow H+c\,d\log r=F.                          \tag{11}
$$

The convergence is locally uniform **including zero**. Here are explicit
uniform bounds justifying that point. On $0<r\le R$, write $r=e^s$
and use $|H(X)|\le Mr^2$, $|d(X)|\le r^2/2$.
The mean-value and integral-remainder estimates for the exponential give

$$
\begin{aligned}
 r^2|r^\varepsilon-1|
   &\le\varepsilon r^2|\log r|
                      \max(1,r^\varepsilon),\\
 r^2\left|\frac{r^\varepsilon-1}{\varepsilon}-\log r\right|
   &\le\frac{\varepsilon}{2}r^2(\log r)^2
                      \max(1,r^\varepsilon).
\end{aligned}                                                   \tag{12}
$$

For $0<\varepsilon\le1$, both right-hand sides are bounded by constants
depending only on $R$, times $\varepsilon$, because
$r^2|\log r|^j\to0$ at zero for $j=1,2$. The last term in (11)
has the same uniform convergence. All functions are assigned value zero
at the origin.

Fix any base and bounded compatible gradient test. Its matrix range is
bounded, so local uniform convergence permits passage to the limit in its
Jensen inequality. This proves Theorem A's quasiconvexity assertion at
every base. No approximation of the test by a bounded number of phases,
waves, or atoms is involved.

### 3.1 Why every nonzero logarithmic drift is nonpolyconvex

A finite polyconvex function on all $\mathbb M$ admits a global
polyaffine lower support, of the form
$a+B:X+b\det X$. This standard finite-valued consequence of convex
support is also the support framework used in
[Polyaffine.lean](../../Morrey/HomogeneousIsotropic/Polyaffine.lean).
To see that a finite convex lift is available on the full minors space,
every $(X,z)$ is the average of two physical points
$(X+Y,\det(X+Y))$, $(X-Y,\det(X-Y))$, with
$\det Y=z-\det X$. Choose, for example,
$Y=\operatorname{diag}(z-\det X,1)$. The linear cofactor terms cancel
when the two determinants are averaged. Thus any convex lift finite on
the physical graph is finite everywhere and has an affine lower support.

If $c\ne0$, choose an invertible $A$ with $c\det A<0$.
By (1),

$$
 \frac{F(tA)}{t^2}=F(A)+c\det A\log t\longrightarrow-\infty
       \qquad(t\to\infty).
$$

The proposed support divided by $t^2$, evaluated at $tA$, converges
to the finite number $b\det A$. It therefore cannot stay below $F$.
This contradiction proves nonpolyconvexity. The same argument does not
require isotropy. In fact it excludes every global polyaffine lower bound,
so no point has a touching polyaffine support.

### 3.2 Quadratic quasiconvexity margins are retained

If, in addition, $F-\lambda|\cdot|_F^2$ is rank-one convex for some
$\lambda\ge0$, it has the same scaling law (1). Applying Theorem A
to this function gives, on a unit-volume periodic cell,

$$
 \int [F(A+Du)-F(A)]\ge\lambda\int |Du|_F^2.
$$

Here the cross term integrates to zero because $\int Du=0$.
This includes nonsmooth functions when the rank-one convexity margin is
stated by subtracting the quadratic, without invoking a pointwise Hessian.

## 4. Two complete scaling classifications

### 4.1 First-order logarithmic homogeneity at any positive exponent

**Theorem B.** Suppose $F:\mathbb M\to\mathbb R$ is finite,
isotropic and rank-one convex, and for some $p>0$ and function
$G:\mathbb M\to\mathbb R$,

$$
 F(tX)=t^p\big(F(X)+\log(t)G(X)\big)
             \qquad(t>0,\ X\in\mathbb M).                    \tag{13}
$$

Then $F$ is quasiconvex. More precisely:

* if $p\ne2$, necessarily $G=0$, so $F$ is exactly homogeneous;
* if $p=2$, necessarily $G=c\det$, and Theorem A applies.

**Proof.** Comparing dilations by $s$, $t$, and $st$, with
$t\ne1$, proves $G(sX)=s^pG(X)$. Taking, for example, $t=e$
in (13) expresses $G$ as a difference of continuous functions, so
$G$ is continuous and isotropic. For every real $\lambda$,

$$
 F+\lambda G=e^{-p\lambda}F(e^\lambda\,\cdot)
$$

is rank-one convex. On any rank-one segment, the convexity gap of
$F+\lambda G$ is an affine function of $\lambda$, nonnegative for
every real $\lambda$. Its slope is zero. Thus $G$ is affine on
every rank-one line.

Here the needed classification of such $G$ is elementary. Separate
affinity in the four entries makes $G$ a multiaffine polynomial.
Affineness on each two-dimensional common-row and common-column plane
eliminates monomials containing two entries from the same row or column.
Only a constant, linear terms, and multiples of $X_{11}X_{22}$ and
$X_{12}X_{21}$ remain. Affinity along the all-ones rank-one direction
makes the last two coefficients opposite. Hence

$$
 G(X)=a+B:X+c\det X.
$$

Isotropy implies $G(-X)=G(X)$, so $B=0$. Positive
$p$-homogeneity and $p>0$ give $a=0$; they give $c=0$
unless $p=2$. Apply the verified homogeneous theorem in the first
case and Theorem A in the second. QED.

This classification also explains why adding higher powers of $\log t$
to a *null-Lagrangian dilation defect* does not produce a larger family:
the cocycle in the next subsection allows only a linear logarithm at
the resonant exponent.

### 4.2 Homogeneity modulo arbitrary null-Lagrangian errors

**Theorem C.** Let $F$ be finite, isotropic and rank-one convex, and
fix $p>0$. Suppose that for every $t>0$, the function

$$
 X\longmapsto F(tX)-t^pF(X)
$$

is affine on rank-one lines, or equivalently is a null Lagrangian on
$\mathbb R^{2\times2}$. Then $F$ is quasiconvex.

**Proof and exact classification.** The preceding elementary
classification and isotropy show that the dilation error has the form
$a(t)+b(t)d(X)$. Evaluation at zero gives
$a(t)=(1-t^p)F(0)$. Set $f=F-F(0)$. Then

$$
 f(tX)=t^pf(X)+b(t)d(X),\qquad
 b(st)=s^pb(t)+t^2b(s).                                      \tag{14}
$$

Continuity of $f$, evaluated at any matrix of determinant one,
gives continuity of $b$. Commuting $s,t$ in (14) yields

$$
 (s^p-s^2)b(t)=(t^p-t^2)b(s).
$$

If $p\ne2$, it follows that
$b(t)=k(t^p-t^2)$ for a fixed real $k$. Therefore
$f+k\det$ is exactly $p$-homogeneous, isotropic, and rank-one
convex. Apply the verified theorem and subtract the null Lagrangian.

If $p=2$, the continuous function $h(t)=b(t)/t^2$ satisfies
$h(st)=h(s)+h(t)$, so $h(t)=c\log t$. Thus $f$ satisfies
(1), and Theorem A followed by addition of the constant $F(0)$
proves the result. QED.

## 5. An explicit nonhomogeneous, nonpolyconvex example

The theorem is not confined to affine-shell profiles or the previous
$U(s)+V(s)\delta+H_0(\delta)$ theorem. Consider

$$
 \boxed{
 F(X)=2|X|_F^2+\det X\log|X|_F
                   +\frac{(\det X)^2}{|X|_F^2}
       \quad(X\ne0),\qquad F(0)=0.
 }                                                            \tag{15}
$$

It is finite, isotropic and satisfies (1) with $c=1$. Here is a
global rank-one curvature proof, not a numerical Hessian sample.
By scaling it suffices to work at $|X|_F=1$. For any rank-one $V$
put $\alpha=X:V$, $d=\det X$, $d'=\operatorname{cof}X:V$.
Then $|d|\le1/2$, $|d'|\le|V|_F$, $|\alpha|\le|V|_F$,
and $d''=0$. Direct differentiation gives

$$
\begin{aligned}
 D^2(d\log r)[V,V]
     &=2\alpha d'+d(|V|_F^2-2\alpha^2),\\
 D^2(d^2/r^2)[V,V]
     &=2(d'-2d\alpha)^2-2d^2|V|_F^2.
\end{aligned}                                                   \tag{16}
$$

The first expression is bounded below by
$-\tfrac52|V|_F^2$, and the displayed square bounds the second by
$-\tfrac12|V|_F^2$. The first term of (15) contributes
$4|V|_F^2$. Hence

$$
 D^2F(X)[V,V]\ge|V|_F^2\qquad(X\ne0,\ \operatorname{rank}V=1).
                                                               \tag{17}
$$

The rank-one curvature expressions scale with degree zero; the
logarithmic extra multiple of $\det$ contributes zero rank-one
curvature. At zero the restriction to any rank-one line has zero
one-sided derivatives, so (15) is globally rank-one convex. Theorem A
proves it quasiconvex and Section 3.1 proves it nonpolyconvex.
Moreover (17) shows that $F-\tfrac12|\cdot|_F^2$ is rank-one convex;
the same origin-gluing argument applies. Section 3.2 therefore gives the
strict all-base estimate
$\int[F(A+Du)-F(A)]\ge\tfrac12\int|Du|_F^2$ for this example.

To compare with the earlier spectral classes, let $s$ be the larger
singular value and $\delta$ the signed smaller singular value.
Then $r^2=s^2+\delta^2$, $d=s\delta$, and the profile of (15) is

$$
 f(s,\delta)=2(s^2+\delta^2)
       +\tfrac12s\delta\log(s^2+\delta^2)
       +\frac{s^2\delta^2}{s^2+\delta^2}.
$$

Its angular second derivatives at two interior points are

$$
 f_{\delta\delta}(2,1)=\frac{662}{125},\qquad
 f_{\delta\delta}(3,1)=\frac{1453}{250}.
                                                               \tag{18}
$$

They differ by $-129/250$. Thus the angular second derivative is
nonzero and depends on $s$; the profile is neither affine in
$\delta$ nor of the form $U(s)+V(s)\delta+H_0(\delta)$.
This is a scope comparison with those two earlier theorems, not an
assertion that no other known construction could prove this example.

More generally the same proof gives rank-one convex examples
$a r^2+c\,d\log r+\eta d^2/r^2$ for
$\eta\ge0$ and $2a\ge\tfrac52|c|+\tfrac12\eta$.
Theorem A covers all angular profiles satisfying (1) and rank-one
convexity, not just this displayed family.

## 6. Evidence, dependence, and the remaining boundary

The new proof is analytical and uses the already verified signed
homogeneous theorem. Its key estimate controls the whole rank-one
convex cone in the logarithmic scaling class, including nonsmooth
functions; it does not infer global rank-one convexity from sampled
Hessians. The [exact symbolic checker](../../research/audit/logarithmic_homogeneity_exact.py)
was run successfully with Python and SymPy. It verifies the scalar product
identities (5)--(7), the positive curvature-measure coefficient, radial
repair identities, scaling covariance and first-order recovery, both
determinant cocycles, an SOS determinant bound, example derivatives (16),
and rational evaluations (18). These checks certify those algebraic
calculations, not the analytic measure argument or a new Lean endpoint.
Two independent agent proof reviews also checked the nonsmooth line argument,
the limit at zero, the classifications, and the scope. No new Lean build
or kernel certification is claimed.

To reproduce the algebra checks from the repository root:

```bash
python3 research/audit/logarithmic_homogeneity_exact.py
```

The first-order drift in (13) is forced to be a null Lagrangian by
rank-one convexity at all scales. This is the reason the second-order
repair in (3) works: after removing the zeroth-order determinant, the
first-order limit retains the desired Jensen inequality. The argument
places this scaling class in the locally uniform closure of positive
multiples of homogeneous isotropic rank-one convex energies plus
null Lagrangians. It does not establish completeness of that closure
or represent an arbitrary nonhomogeneous function by such limits.
General coupled scale-and-shape dependence, removal of both rotation
groups, and unrestricted planar Morrey remain open.

No publication-priority claim is made for this extension. The theorem
and its exact scope are distinct from the previously recorded
[affine-shell theorem](IWANIEC_MORREY_NONHOMOG_SHELL_AFFINE.md),
[separated-angular theorem](IWANIEC_MORREY_NONHOMOG_ANGULAR.md), and
[orientation-preserving volumetric/isochoric split](IWANIEC_MORREY_VOLUMETRIC_SHIELD.md).

Special logarithmic integrands and differentiation of the Burkholder
family at degree two are prior work. In particular Astala, Faraco, Guerra,
Koski and Kristensen, [The local Burkholder functional, quasiconvexity and
Geometric Function Theory](https://arxiv.org/html/2309.03495v2), Section 1.3
and Corollary 8.1, study the operator-norm energy
$\|A\|_{op}^2-(1+\log\|A\|_{op}^2)\det A$ and its Jensen inequality
for positive-orientation homeomorphisms. The present deduction is the
automatic implication for every finite isotropic rank-one convex energy
obeying (1), using the verified signed homogeneous theorem, with arbitrary
bounded gradient tests including changes of determinant sign. The example
above is illustrative, not a claim to have first introduced logarithmic
energies. The literature comparison is not an exhaustive priority audit.
