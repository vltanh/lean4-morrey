# Exact scalar acoustic criterion for isotropic homogeneous planar rank-one convexity

Research date: 22 November 2026. **Status: hand theorem, with symbolic algebra check;
no Lean proof or independent mathematical review.** Related to classical
Knowles–Sternberg/Legendre–Hadamard criteria for isotropic elasticity:
this particular presentation is not claimed novel.

This is a substantial global reduction of the p>2 research gate:
all two-by-two matrices and **all** rank-one directions are replaced by
a **one-dimensional condition** on signed singular-value ratio, plus
two endpoint conditions. It does *not* prove universal quasiconvexity.

## Theorem (real-valued, all p>1)

Fix p>1 and h∈C²([-1,1],ℝ), with derivatives understood one-sided
at the endpoints. For nonzero real two-by-two matrices define

\[
 a=\|A\|_{\rm op}>0,\quad r=\frac{\det A}{a^2}\in[-1,1],
 \quad F(A)=a^p h(r),\quad F(0)=0.
\]

For -1<r<1, abbreviate

\[
\begin{aligned}
 C &=p h-2r h',&
 B&=\frac{C}{1-r^2},\\
 U&=(p-1)C+r^2h'',&
 V&=h'',\\
 T&=rB+(p-2)h'-r h''.
\end{aligned}
\]

**Claim.** F is globally rank-one convex **if and only if**
for every -1<r<1,

\[
\boxed{C\ge0,\quad V\ge0,\quad |T|\le B+\sqrt{UV}}
\tag{A}
\]

and additionally

\[
\boxed{p h(1)-2h'(1)\ge0,\qquad
p h(-1)+2h'(-1)\ge0.}
\tag{B}
\]

Under C,V≥0 and p>1 we have B,U≥0, making the square root valid.
No F≥0 assumption is needed; C(0)≥0 already implies
F≥0 on every rank-one matrix.

## Rank-one Hessian derivation

By SO(2)×SO(2) invariance and positive scaling, it suffices to
study \(A=\operatorname{diag}(1,r)\), |r|<1.
For rank-one \(H=u\otimes v\), with
\[
H=\begin{pmatrix}x&y\\z&w\end{pmatrix},
\quad (x,y,z,w)=(u_1v_1,u_1v_2,u_2v_1,u_2v_2),
\quad xw=yz,
\]
the determinant along A+tH is **exactly**
\(r+t(w+rx)\). The simple leading singular value
\(a(t)=\|A+tH\|_{\rm op}\) satisfies
\[
 a'(0)=x,\quad a''(0)=\frac{y^2+z^2+2ryz}{1-r^2}.
\]
The signed ratio \(r(t)=\det(A+tH)/a(t)^2\) satisfies
\[
 r'(0)=w-rx,\quad
 r''(0)=2rx^2-4xw-2r a''(0).
\]
Chain differentiation of \(a(t)^p h(r(t))\) now yields

\[
\boxed{
D^2F(A)[H,H]
= C\left[(p-1)x^2+\frac{y^2+z^2+2ryz}{1-r^2}\right]
+2(p-2)h' yz+h''(w-rx)^2.}\tag{C}
\]

Re-expressing H=u⊗v gives the **acoustic tensor**:
\[
D^2F(A)[u\otimes v,u\otimes v]=
u^\top
\begin{pmatrix}
 U v_1^2+Bv_2^2 & T v_1v_2\\
 T v_1v_2 & Bv_1^2+Vv_2^2
\end{pmatrix}u.\tag{D}
\]

Equation (D) has a replayable **symbolic verifier**
[research/audit/iwaniec_acoustic_exact.py](../../research/audit/iwaniec_acoustic_exact.py).

PSD for all u,v forces V≥0 and B≥0 by choosing v=(0,1)
and u equal to coordinate vectors; U≥0 follows from p>1.
The determinant of the tensor is
\[
UB\,v_1^4+(UV+B^2-T^2)v_1^2v_2^2+BV\,v_2^4.
\]
For U,V,B≥0 this is nonnegative for all v iff
\(T^2\le(B+\sqrt{UV})^2\). This proves that (A)
is equivalent to **all rank-one Hessian tests at every
matrix with distinct singular values**.

## Endpoints and global sufficiency

Matrices with coincident nonzero singular values are
conformal or anticonformal; the operator norm has a
corner there. At A=I and for rank-one H, let
\(\lambda_{\max}\ge\lambda_{\min}\) be eigenvalues
of \((H+H^\top)/2\). The right-minus-left
directional derivative of \(t\mapsto F(I+tH)\)
is exactly
\[
 [p h(1)-2h'(1)](\lambda_{\max}-\lambda_{\min}).
\]
Nonnegative slope jumps are equivalent to the first
condition of (B). Reflection
\(A\mapsto\operatorname{diag}(1,-1)A\) maps h(r)
to h(-r) and gives the other condition.

For sufficiency, every rank-one line can meet the
nonzero conformal locus at most once per orientation:
the difference of two distinct conformal matrices
of the same orientation is full rank. On the
complement, (A) makes its second derivative nonnegative;
at the exceptional points, (B) gives nonnegative
one-sided slope jumps. A rank-one line through zero
is entirely rank one; on it
\(F(tH)=|t|^p\|H\|_{\rm op}^p h(0)\),
which is convex because C(0)=p h(0)≥0.
Thus F is convex along every rank-one line.
Necessity is the reverse rank-one Hessian and
slope-jump argument. This completes the hand proof.

**Important domain restriction:** h is C² on the *closed*
signed-ratio interval. The result is not yet proved
for nonsmooth h, and it is not a theorem that every
general 2×2 RC integrand is isotropic/homogeneous.
The endpoint patching argument deserves a separate
Lean translation and independent analytic review.

## Curvature-flat supporting theorem for ALL p>2

The scalar criterion yields a genuinely global all-F corollary
for *every* exponent p>2, with **no nonnegativity assumption**.

**Theorem (conditional on global quasiconvexity of p-Burkholder).**
Let F be a finite-valued SO(2)×SO(2)-isotropic, positively
p-homogeneous, globally rank-one-convex 2×2 integrand, p>2,
whose signed-singular profile h is C² on [-1,1].
At any interior signed ratio r₀ satisfying **h''(r₀)=0**,
F is quasiconvex **at every matrix A with r(A)=r₀**.

Indeed, write m=h'(r₀), c=h(r₀)-r₀m,
\(\kappa=(p-2)/p>0\). At h''=0 the acoustic
criterion (A) reduces to
\[
 B\ge0,\qquad
 |\,r_0B+(p-2)m\,|\le B,\quad
 B=\frac{p c+(p-2)r_0m}{1-r_0^2}.
\]
The upper and lower signs, multiplied by
the positive denominators, yield **exactly**
\[
 p c\ge(p-2)m,\qquad p c\ge-(p-2)m,
\]
so \(\boxed{c\ge\kappa|m|}\).
Since rank-one convexity forces h convex, its
tangent line \(\ell(r)=c+mr\) is a
**global minorant** of h on [-1,1].
Putting
\[
 \alpha=\tfrac12(c/\kappa+m)\ge0,\quad
 \beta=\tfrac12(c/\kappa-m)\ge0
\]
gives
\[
  \alpha(\kappa+r)+\beta(\kappa-r)=\ell(r).
\]
The associated matrix integrand
\(\alpha B_p^+(A)+\beta B_p^-(A)\)
is a globally quasiconvex minorant of F
(assuming the 2026 global Burkholder result)
and touches at every A whose signed ratio is r₀.
Therefore F obeys the quasiconvex Jensen
inequality at all those matrices. QED.

**Methodological consequence.** A C² profile
separating the p>2 hybrid support cone from
the rank-one-convex cone can only do so at
ratios where \(h''(r)>0\). This is a
*structural necessary condition* for
failure of this QC support construction,
not an unrestricted Morrey theorem.
If h'' vanishes identically (affine profile),
the entire integrand is a nonnegative
combination of the two p-Burkholder
orientations and is quasiconvex everywhere,
again conditional on Iwaniec 2026.

## Controls and next gate

- \(\|A\|_{\rm op}^p\): h=1, C=p, B=p/(1-r²),
  V=0, T=rB, so (A) is |r|≤1.
- \(\pm\det A\) at p=2: h=±r, all C,B,U,V,T
  vanish and both endpoint inequalities are equalities.
- A nonnegative polyconvex example such as
  \((\det A)_+^{p/2}\) for p≥4 passes the
  conditions (h=(r_+)^{p/2}, C²).

**Global program, not local enumeration:** Prove that
every h satisfying (A)–(B) at p>2 has a touching
quasiconvex support from the
[hybrid Burkholder–polyconvex envelope](IWANIEC_MORREY_GENERAL.md),
or produce an exact separating h disproving
this *specific support-cone completeness*.
This attacks a universal one-variable functional
class with arbitrary p, rather than finitely
many meshes, degrees or configurations.
Even an exact separation of the support cone
does **not** disprove Morrey; a negative gradient
Jensen witness would still be necessary.
