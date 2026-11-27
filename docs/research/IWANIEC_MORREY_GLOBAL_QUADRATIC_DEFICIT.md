# Global quadratic bound on possible quasiconvexity deficit near conformality, all p≥2

Date: 23 November 2026. **Status:** hand derivation from the *published*
Guerra–Kristensen (2022) conformal determinant-power support theorem.
This is a quantitative inequality for **all** nonnegative isotropic
rank-one-convex positively p-homogeneous 2×2 integrands that are
C² near both conformal orientations. It **does not** prove that the
deficit vanishes, and is not independently reviewed or formalized in Lean.
No novelty/priority beyond the published support theorem is claimed.

## Statement: a single inequality for EVERY integrand, base and test map

Let p≥2 and let \(F:\mathbb R^{2\times2}\to[0,\infty)\) be
finite-valued, globally rank-one convex, invariant under left
and right SO(2), and positively p-homogeneous. Assume additionally
that F is C² in a neighborhood of I and D=diag(1,-1).
Let \(\sigma_1(A)=a\ge b=\sigma_2(A)\ge0\) and
\[
 QF(A)=\inf_\varphi\fint_Q F(A+D\varphi)\,dx
\]
where the infimum is over periodic Lipschitz two-component
displacements (the zero perturbation is admitted).
Then a **finite constant K=K(F,p)** exists such that

\[
\boxed{\quad
0\le F(A)-QF(A)\le
K\,a^{p-2}(a-b)^2 \qquad\forall A\in\mathbb R^{2\times2}.
\quad}                                                     \tag{1}
\]

At A=0, the right-hand side is interpreted as zero.
No degree restriction, sign of determinant, fixed mesh,
finite number of gradients, or small perturbation assumption
is imposed. The estimate is globally valid in matrix amplitude,
with the optimal scale factor dictated by homogeneity.
It is **quadratic** in distance to the conformal/anticonformal
locus, improving the earlier linear all-class estimate
when F is smooth at that locus.

## Source: the universal conformal polyconvex minorant

Guerra–Kristensen (2022), Theorem 1.3/Proposition 3.3,
prove for every such F and p≥2 that
\[
 M_F(A)=F(I)(\det A)_+^{p/2}
        +F(D)(-\det A)_+^{p/2}
 \le F(A)\quad\forall A,
\tag{2}
\]
and \(M_F\) is polyconvex because each scalar power
\(t\mapsto(t_+)^{p/2}\) is convex and nondecreasing.
Consequently \(QF(A)\ge M_F(A)\) everywhere, while
the zero gradient perturbation shows \(QF(A)\le F(A)\).
Thus
\[
 0\le F(A)-QF(A)\le F(A)-M_F(A).                \tag{3}
\]

This is an **external published analytic input**,
not a consequence of the new 2026 Iwaniec preprint.

## Exact one-dimensional proof of the quadratic rate

For a≠0 define the signed ratio \(r=\det A/a^2\in[-1,1]\).
By signed singular-value decomposition,
\[
 F(A)=a^p h(r),\qquad h(r)=F(\mathrm{diag}(1,r)).
\]
Put \(q=p/2\ge1\). Dividing (2) by a^p gives
\[
 h(r)\ge
 \begin{cases}
   h(1)r^q,&0\le r\le1,\\
   h(-1)(-r)^q,&-1\le r\le0.
 \end{cases}                                             \tag{4}
\]
Define the nonnegative difference
\[
g(r)=h(r)-h(1)r^q\ (r\ge0),\qquad
g(r)=h(r)-h(-1)(-r)^q\ (r\le0).
\]
It satisfies \(g(1)=g(-1)=0\).
Since F and M_F are differentiable at I and D
and F−M_F≥0 globally with equality at both,
their first derivatives agree there. Restricting
to diag(1,r) proves
\[
 h'(1)=q\,h(1),\qquad
 h'(-1)=-q\,h(-1),
\]
hence \(g'(1)=g'(-1)=0\).

The profile h is continuous on [-1,1] and C² near
the endpoints, so a **uniform explicit K** can be chosen.
One option is the following (all suprema finite):
\[
\begin{aligned}
M_0&=\sup_{[-1,1]}h,\\
M_2&=\sup_{r\in[-1,-1/2]\cup[1/2,1]}|h''(r)|,\\
M_q&=q(q-1)2^{\max\{0,2-q\}}\max\{h(-1),h(1)\},\\
K&=\max\{4M_0,\ \tfrac12(M_2+M_q)\}.
\end{aligned}                                             \tag{5}
\]
Here h is C² on those closed neighborhoods if necessary
after replacing the threshold 1/2 with any closer-to-one
fixed endpoint neighborhood. For an arbitrary C²-near-endpoint
F with too small a neighborhood, choose a cutoff
\(r_*\in(0,1)\) inside both C² intervals, and change
the elementary constants accordingly.

When \(1/2\le|r|\le1\), Taylor's integral
formula, the zero endpoint value/derivative, and
\(|g''|\le M_2+M_q\) give
\(0\le g(r)\le\tfrac12(M_2+M_q)(1-|r|)^2\).
For \(|r|\le1/2\), since \(M_F\ge0\),
\(g(r)\le h(r)\le M_0\le4M_0(1-|r|)^2\).
Therefore \(g(r)\le K(1-|r|)^2\) globally.

Using \(|r|=b/a\), (3) yields
\[
 F(A)-QF(A)
 \le a^p K(1-|r|)^2
 =K\,a^{p-2}(a-b)^2.
\]
At a=0 both F(0) and QF(0) are zero by
nonnegativity and positive homogeneity. QED.

**Note on the regularity condition.** Smoothness of h
as an abstract one-variable function is **not enough**
to force the endpoint derivatives above: e.g.
\(F(A)=\|A\|_{\rm op}^p\) has h≡1 but is not
differentiable at nonzero conformal matrices.
The theorem explicitly assumes matrix-level C²
at both orientations. Without such regularity,
the published determinant-power lower support
can have a **linear** gap even when F itself
is convex; no unqualified quadratic conclusion
is claimed.

## Research meaning and limits

This is an all-integrand **quantitative** constraint
on any hypothetical p>2 quasiconvexity failure
in the smooth isotropic homogeneous class:
near conformality its energy deficit must be at
most second order in the singular-value gap,
uniformly across all compatible gradients
and oscillation frequencies.

It does **not** show the deficit is zero,
does **not** make each F polyconvex, and
does **not** settle Question 1.7 of
Guerra–Kristensen (2022).
A positive all-matrix theorem would need an
exact compatible cross-level Jensen bound,
not merely estimates vanishing at conformals.

This is a useful universal estimate for the
global program but not presented as a
publication-level breakthrough.
