# All-parameter positive Dacorogna–Marcellini quartic stabilization: an exact polyconvex subcone

23 November 2026. **Mathematical status:** hand proof using a published
polyconvex quartic endpoint and elementary convexity;
replayable rational coefficient identities are provided below.
**Priority:** No novelty is asserted. This is a global analytic
*exclusion of a tempting counterexample family*, not proof
of the general p>2 Guerra–Kristensen question or of Morrey.
No Lean build or independent referee review is claimed.

## Statement

For a real 2×2 matrix A, write
\(s=\|A\|_F^2\ge0\) and \(d=\det A\), so
\(s\ge2|d|\). For real \(\gamma,c\) define
\[
          P_{\gamma,c}(A)=s^2-2\gamma s\,d+c d^2.
\]

**Theorem (exact continuum of PC integrands).**
Set \(g=|\gamma|\), and suppose \(0\le g\le2\).
If
\[
\boxed{
c\ge
\begin{cases}
2(g-1),&0\le g\le1,\\
4(g-1),&1\le g\le2,
\end{cases}}
\tag{1}
\]
then \(P_{\gamma,c}\) is **globally polyconvex**,
nonnegative and rank-one convex on all of
\(\mathbb R^{2\times2}\).
Furthermore, when \(1\le g\le2\), the
lower bound on c is **necessary and sufficient
for nonnegativity**, whether or not RC was assumed:
\[
 \boxed{P_{\gamma,c}\ge0\text{ everywhere}
        \iff c\ge4(g-1).}
\tag{2}
\]
Thus every nonnegative determinant-square stabilization
of the classical Dacorogna–Marcellini quartic with
\(1\le|\gamma|\le2\) is *automatically polyconvex*.

**Corollary (all p≥4, same parameter continuum).**
For every real \(p\ge4\),
\[
          F_{\gamma,c,p}(A)
             =[P_{\gamma,c}(A)]^{p/4}
\tag{3}
\]
is finite, nonnegative, isotropic, positively
p-homogeneous and globally polyconvex (hence QC),
whenever (1) holds. This simultaneously
rules out the full lifted family as a source
of rank-one-convex/nonquasiconvex
counterexamples. The theorem is **not**
for every isotropic p-homogeneous RC F.

## Proof via three global generators

Use the sign \(e=\operatorname{sgn}\gamma\)
(chosen arbitrarily when \(\gamma=0\)).
Introduce
\[
\begin{aligned}
 S(A)&=s^2-2d^2,\\
 Q_e(A)&=s(s-2ed),\\
 R_e(A)&=(s-2ed)^2,\\
 D(A)&=d^2 .
\end{aligned}
\]

All four are globally polyconvex:

- \(S=\sigma_1(A)^4+\sigma_2(A)^4
  =\|A\|_{S_4}^4\) is **convex**, as a positive
  fourth power of the Schatten-4 norm.
- \(Q_e\) is **polyconvex** by the classical
  Dacorogna–Marcellini planar quartic
  criterion: \(s(s-2ed)\) is exactly
  the polyconvex endpoint. See e.g.
  [Rindler's lecture notes](https://warwick.ac.uk/fac/sci/maths/people/staff/filip_rindler/ma4g6_17_ln.pdf),
  Example 4.2, or
  [Sums-of-squares Polyconvexity](https://cmc.deusto.eus/sums-of-squares-polyconvexity/),
  Theorem 2.
- \(R_e\) is **convex**: \(s-2ed\)
  is a sum of two squares of linear
  matrix entries, hence a nonnegative
  convex quadratic, and the square map
  on \([0,\infty)\) is convex increasing.
- \(D=d^2\) is polyconvex, being
  convex as a function of the
  independent determinant minor.

The **exact coefficient identities** are,
for \(0\le g\le1\),
\[
 P_{\gamma,c}
   =(1-g)S+gQ_e+[c+2(1-g)]D,
\tag{4}
\]
and for \(1\le g\le2\),
\[
 P_{\gamma,c}
  =(2-g)Q_e+(g-1)R_e+[c-4(g-1)]D.
\tag{5}
\]
In the corresponding parameter range
every coefficient is nonnegative,
so global polyconvexity follows
from its stability under nonnegative
linear combinations.

Since each displayed generator is
nonnegative, the resulting P is nonnegative.
For necessity in (2), evaluate at
\(A=I\) if \(\gamma\ge0\) and
\(A=\operatorname{diag}(1,-1)\)
if \(\gamma<0\). In both cases
\(s=2\), \(d=e\), hence
\[
P_{\gamma,c}(A)=4-4g+c.
\]
When \(c<4(g-1)\), this is strictly
negative, proving necessity.
At \(g=1\), (4) and (5) agree.

Finally, for \(p\ge4\),
\(x\mapsto(x_+)^{p/4}\) is
convex and nondecreasing on all ℝ.
If \(G(A,\delta)\) is a convex
polyconvex extension of P in
the independent minor variables,
then \((G(A,\delta)_+)^{p/4}\)
is again convex and restricts
to \(P(A)^{p/4}\), because P≥0.
Positive p-homogeneity is immediate.
This proves (3).

The [standard-library rational checker](../../research/audit/iwaniec_dm_positive_stabilization_exact.py)
replays (4)–(5), including boundary
and interior rational controls.
It does **not** replace the stated
analytic proof that Q_e is polyconvex.

## A meaningful global stop rule and open frontier

The **unstabilized** signed Dacorogna–Marcellini
quartic \(s(s-2\gamma d)\) is
rank-one convex but nonpolyconvex
when \(1<|\gamma|\le2/\sqrt3\)
(classical threshold: original DM
parameter \(2\gamma\), PC up
to \(2\), RC up to \(4/\sqrt3\)).
It is *negative* at the corresponding
conformal matrix. This theorem shows
that **the entire nonnegative
determinant-square stabilization**
in that dangerous parameter interval
becomes polyconvex. Adding such a
correction cannot create a nonnegative
isotropic p4 counterexample.

The remaining open problem is
**all nonnegative isotropic p-homogeneous
RC integrands** for every \(p>2\),
including arbitrary nonpolynomial
profiles and parameter regimes not
covered by (1). This excludes
one infinite parametric family,
but is emphatically **not**
a finite exhaustive reduction
of the universal conjecture.

In particular, (1) is merely
sufficient for \(0\le g<1\);
we do **not** assert all nonnegative
RC quartics are polyconvex.
Numerical testing outside (1)
is not a theorem.
