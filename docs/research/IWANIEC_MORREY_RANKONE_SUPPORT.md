# Exact global polyconvex support at ALL rank-one bases of the p=4 hybrid-cone separator

Research: 22 November 2026. **Mathematically closed for the specified explicit integrand**, by an exact rational Bernstein certificate. A standalone checker was executed locally; no Lean translation or independent referee review is claimed. The result is **not** a universal p>2 theorem, but it closes **every rank-one base, including all amplitudes**, for the explicit profile used in the [hybrid generator no-go](IWANIEC_MORREY_HYBRID_NOGO.md).

## 1. The candidate and the surprising positive result

Let
\[
 h(r)=2^{-24}\sum_{j=0}^{12}a_jT_j(r),\qquad
 (a_0,\ldots,a_{12})=(37676885,55559819,22507846,3634764,
 1122809,1068027,57237,275379,623336,96945,-261804,-126467,-6991),
\]
where \(T_j\) are Chebyshev polynomials. Define for \(A\ne0\)
\[
 F(A)=\|A\|_{\rm op}^4 h\left(\frac{\det A}{\|A\|_{\rm op}^2}\right),
 \qquad F(0)=0.
\]
The [previous exact no-go](IWANIEC_MORREY_HYBRID_NOGO.md) established global rank-one convexity and proved that the homogeneous hybrid Burkholder/polyconvex **support cone** does NOT touch F at \(E=\operatorname{diag}(1,0)\).

**Theorem.** Nevertheless **F is polyconvex at E**, and hence (by isotropy and positive homogeneity) **at every rank-one matrix**. Consequently, for *every* zero-boundary or periodic compatible planar gradient,
\[
 \fint_Q F(E+D\varphi)\,dx \ge F(E),
\]
and likewise at every rank-one base. This rules out all-amplitude Morrey witnesses with a rank-one base for this candidate; it is stronger than the earlier small-gradient stability statement.

The proof uses **a nonhomogeneous, global poly-affine support**, which the former homogeneous-generator cone omitted. The two statements are compatible: the old cone is incomplete, but F has additional valid lower supports.

## 2. Explicit support with no unknown coefficients

Exact rational numbers:
\[
 H_0=h(0)=\frac{2139095}{2097152},\qquad
 H_1=h'(0)=\frac{50331651}{16777216}.
\]
Set \(c=7\), \(u=4H_0\), \(v=H_1-7\), and
\[
 \boxed{G(A)= -3H_0+u A_{11}+v A_{22}+7\det A.}\tag{1}
\]
Then
\[
 \boxed{F(A)\ge G(A)\quad\text{for EVERY }A\in\mathbb R^{2\times2},
 \qquad F(E)=G(E)=H_0.}\tag{2}
\]
Because G is affine in the full minor vector \((A,\det A)\), (2) is exactly a global polyconvex support at E. No Iwaniec 2026 claim is required to infer this.

The signed-singular-value inequality behind (2) is particularly simple.
For \(a=\|A\|_{\rm op}\ge0\), \(r=\det A/a^2\in[-1,1]\)
(the a=0 case is separate), complex coefficients
\(Az=a_+z+a_-\bar z\) satisfy
\[
 |A_{11}+A_{22}|\le a(1+r),\qquad
 |A_{11}-A_{22}|\le a(1-r).
\]
Since \(u+v>0\) and \(u-v>0\) exactly, the positive
linear combination gives
\[
        uA_{11}+vA_{22}\le a(u+vr).           \tag{3}
\]
Thus it is sufficient to prove one **bivariate polynomial inequality**
on the half-strip:
\[
\boxed{
 P(a,r):=a^4h(r)+3H_0-u a-v a r-7a^2r\ge0,
 \qquad a\ge0,\ -1\le r\le1.}               \tag{4}
\]
The function P is rational-polynomial because h is rational-polynomial.
At \((a,r)=(1,0)\), P and its two first derivatives vanish.
Equation (4) proves (2) by (3), and equality holds at E.

## 3. Finite exact positivity certificate

The executable source
[research/audit/iwaniec_p4_rank_one_polyconvex_exact.py](../../research/audit/iwaniec_p4_rank_one_polyconvex_exact.py)
verifies every inequality using only Python's standard-library
\`fractions.Fraction\` and integer binomial coefficients:

1. **Global profile floor.** On \([-1,1]\), \(h(r)>1/32\), proved by 3 dyadic Bernstein subintervals.
2. **Tail \(a\ge16\).** The exact bound
\[
 P(a,r)\ge a^4/32 +3H_0-
   (u+|v|)a-7a^2
 \ge a^2-(u+|v|)a+3H_0>0
\]
holds because \(a^4/32\ge8a^2\) and \(16>u+|v|\).
3. **Local square around the unique touching point.** On
\[
 S=[1-1/128,1+1/128]\times[-1/128,1/128],
\]
the exact bivariate Bernstein ranges for the Hessian entries
\(P_{aa},P_{rr},P_{ar}\) satisfy
\[
 P_{aa}\ge11.8822\ldots,\quad
 P_{rr}\ge0.4485\ldots,\quad
 |P_{ar}|\le2.1901\ldots,\quad
 (\inf P_{aa})(\inf P_{rr})-(\sup|P_{ar}|)^2>0.
\]
These displayed decimals are explanatory; the checker tests
**exact rational inequalities**. Thus P is strictly convex on S,
with P(1,0)=0 and zero gradient; P≥0 on S.
4. **Remaining compact rectangle.** The checker begins with the exact
tensor-product Bernstein representation of \(2^{24}P\) on
\([0,16]\times[-1,1]\), bisects rationally, and
requires every Bernstein coefficient **strictly positive**
on every accepted nonlocal box, using the local Hessian test
on boxes inside S. In the verified run:
**178 strictly positive boxes, 6 local boxes, 367 recursion nodes,
maximum depth 21**. The accepted boxes cover the full rectangle.

Together these cover every (a,r) in the half-strip, with **no
floating-point sampling, solver tolerances or finite test-grid
assumption**. The script independently checks the tensor
Bernstein boundary values and the exact rational Hessian bounds.

## 4. Universal rank-one-base support criterion (global reduction)

The argument above yields a useful **if and only if** reduction,
not restricted to this one polynomial.

Fix p>1 and an isotropic p-homogeneous differentiable
\(F(A)=a^ph(r)\) at \(E=\operatorname{diag}(1,0)\),
with \(h(0)=h_0\ge0,\ h'(0)=m\).
For \(c\in\mathbb R\), put \(u=p h_0,\ v=m-c\).
Then F has a **global poly-affine minorant touching at E**
if and only if **there exists c** satisfying
\[
 \boxed{|m-c|\le p h_0,\qquad
 a^p h(r)+(p-1)h_0
 -a\,[p h_0+(m-c)r]-c a^2r\ge0
\quad\forall a\ge0,\ r\in[-1,1].}                    \tag{5}
\]
Necessity: any minor-affine supporting G at E has its matrix
linear coefficient fixed by differentiability of F:
\(\nabla F(E)=\mathrm{diag}(p h_0,m)\);
the determinant derivative at E contributes
\(c\mathrm{cof}(E)=c\,\mathrm{diag}(0,1)\).
Thus its matrix gradient is \(\mathrm{diag}(u,m-c)\),
and its constant is \(-(p-1)h_0\).
The orbit of E under left/right SO(2) rotations forces
\(|m-c|\le u\).
Taking the maximum over the orientation orbit at each (a,r)
gives the scalar inequality. Sufficiency uses the same
signed-singular-value bounds as (3).
This reduction addresses the full class of **smooth isotropic
homogeneous** F and all test matrices, with a single scalar parameter
c rather than arbitrary polyconvex certificates.

**Caveat:** (5) characterizes **poly-affine support at E**
(equivalently finite polyconvex-at-E support, when its convex
lift admits a subgradient), not rank-one convexity or
quasiconvexity of every F. The existence of c for all
rank-one-convex profiles remains **OPEN**.

## 5. Research decision

The exact p=4 function is **not a Morrey counterexample at ANY
rank-one base**. Testing large-amplitude periodic fields at E is
now unnecessary; (2) provides a universal Jensen inequality there.
The old homogeneous hybrid support no-go is valid but **does
not diagnose actual quasiconvexity**. The new viable p>2
direction is **nonhomogeneous determinant-affine supports**,
with a one-parameter universal criterion at rank-one bases.

Next mathematically substantive gates:

- Check whether every nonnegative isotropic p-homogeneous
rank-one-convex F, all p>2, satisfies (5) for some c. A universal
proof would settle *rank-one-base* polyconvexity at once, with
unrestricted exponents and profiles. A counterexample to (5)
would only disprove polyconvexity at rank-one, not Morrey.
- To settle **all matrices**, extend support construction
from rank-one bases to arbitrary signed-singular ratio
\(r_0\in(-1,1)\); or find a genuine compatible gradient
energy gap after certifying rank-one convexity.
- The exact proof is **hand mathematics plus a replayable exact
checker**, not Lean-compiled or independently peer reviewed.
