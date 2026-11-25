# The full-rank p>2 poly-affine support gate: one scalar multiplier

22 November 2026. **Status:** universal hand reduction, not a solution of the
Guerra–Kristensen 2022 Question 1.7, and not a Lean theorem. The new
[Wiedemann–Peter (2026)](https://doi.org/10.1007/s00526-025-03222-z)
Theorem 1.4 and Corollary 1.5 reprove/extend a general 2D
isotropic diagonal reduction **already explicit in [Dacorogna–Koshigoe (1993), Theorem 2.1](https://www.numdam.org/item/AFST_1993_6_2_2_163_0/),
Theorem 2.1(ii)–(iv)**. The scalar one-multiplier formula below is
an algebraic specialization of that older poly-affine support criterion,
not a novel discovery of the principle; the theorem below is a more specialized, explicit **pointwise
support and one-parameter feasibility** formulation. No priority
claim is made.

## 1. Theorem: exact nonconformal pointwise poly-affine support

Let p>1 and let h∈C¹([-1,1],ℝ). Define
\(F(A)=a^p h(\det A/a^2)\) for nonzero A with
\(a=\|A\|_{\rm op}\), and F(0)=0.
Fix a signed singular ratio \(t\in(-1,1)\)
and \(E_t=\operatorname{diag}(1,t)\). Write
\(H=h(t)\) and \(m=h'(t)\).

For any real c, define
\[
\begin{aligned}
 u_c&=pH-tm-ct,\qquad v_c=m-c,\\
 k_c&=-(p-1)H+ct,\\
 G_{t,c}(A)&=k_c+u_c A_{11}+v_c A_{22}+c\det A .
\end{aligned}                                                     \tag{1}
\]

**Proposition (exact, all p>1).** There exists a global
poly-affine lower support \(G(A)\le F(A)\) with equality
at \(E_t\) **if and only if** there exists \(c\in\mathbb R\)
such that

\[
\boxed{u_c\ge|v_c|}
\qquad\Longleftrightarrow\qquad
\boxed{
 \frac{(1+t)m-pH}{1-t}
 \le c\le
 \frac{pH+(1-t)m}{1+t}}                            \tag{2}
\]
and, for all \(a\ge0\) and all \(s\in[-1,1]\),
\[
\boxed{
 a^p h(s)+(p-1)H
 -a[pH+m(s-t)]
 +c(a-1)(t-a s)\ge0.}                              \tag{3}
\]
Here \(a=0\) is included by continuity of (3), even
though the signed ratio of the zero matrix is undefined.
Every feasible c proves **polyconvexity at \(E_t\)**,
hence quasiconvexity there for every admissible
planar gradient, of arbitrary amplitude.

**Proof of necessity.** A global poly-affine support
touching at \(E_t\) is of the form
\(k+K:A+c\det A\). Because F is differentiable
at E_t (the leading singular value is simple),
equality at a global minimum of F−G forces
\[
 \nabla F(E_t)=\operatorname{diag}(pH-tm,m)
             =K+c\,\operatorname{cof}(E_t).
\]
Hence K=diag(u_c,v_c) and the touching value
fixes k=k_c. Since F is invariant under
left and right SO(2), the value of the linear
part \(u_c A_{11}+v_c A_{22}\) must attain its
*maximum on the signed-SVD orbit* of E_t at
E_t itself; otherwise G>F at another point
with the same (a,s)=(1,t).
This is exactly \(u_c\ge|v_c|\), yielding (2).
For any matrix on the orbit of diag(a,a s),
the maximal linear part is
\(a(u_c+v_c s)\) when (2) holds. Therefore the
global condition G≤F is equivalent to (3).

**Proof of sufficiency.** For all real A with
signed singular invariants (a,s), one has
\[
 |A_{11}+A_{22}|\le a(1+s),\qquad
 |A_{11}-A_{22}|\le a(1-s).
\]
When \(u_c\pm v_c\ge0\),
\[
u_c A_{11}+v_c A_{22}
\le a(u_c+v_c s).
\]
Subtracting G_{t,c} from F and collecting
terms gives exactly (3). At E_t the
inequality is an equality. Since G is affine
in \((A,\det A)\), it is poly-affine and a
global polyconvex supporting function. QED.

This is an **iff for existence of a global
poly-affine support at the chosen base**.
For standard finite-valued polyconvex
representatives, supporting subgradients
at the lifted point give such a function;
one should keep this regularity/finite-extension
qualification explicit when comparing
alternate definitions of pointwise polyconvexity.

## 2. The remaining universal quantifier is an interval intersection

Define
\[
 A_t(a,s)=a^p h(s)+(p-1)H-a[pH+m(s-t)],
 \quad K_t(a,s)=(a-1)(t-a s).
\]
Then (3) is \(A_t+cK_t\ge0\).
Its **single feasible scalar parameter** lies in
the following exactly specified interval:

\[
\begin{aligned}
c_{\min}(t)&=\max\left\{
 \frac{(1+t)m-pH}{1-t},\
 \sup_{K_t>0}\frac{-A_t}{K_t}\right\},\\
c_{\max}(t)&=\min\left\{
 \frac{pH+(1-t)m}{1+t},\
 \inf_{K_t<0}\frac{A_t}{-K_t}\right\}.
\end{aligned}                                                     \tag{4}
\]

If F is rank-one convex and nonnegative, then
\(A_t\ge0\) **automatically whenever \(K_t=0\)**:
- At a=1, this follows from convexity of h and
  its tangent supporting line at t.
- If t=a s (including s=t/a for a>0), then the
  matrix diag(a,t) is rank-one connected to
  E_t, and \(A_t\) is precisely the convex
  tangent gap along that rank-one line.
- At a=0,t=0, \(A_t=(p-1)h(0)\ge0\).

Under those assumptions, (2)–(3) are
**equivalent** to \(c_{\min}(t)\le c_{\max}(t)\).
The supremum/infimum in (4) are over the
entire continuous half-strip, not finitely
many sampled cells or a finite-degree
assumption.

**Genuine positive completion gate** for
Guerra–Kristensen Question 1.7:
prove, for EVERY nonnegative isotropic
p-homogeneous globally rank-one-convex F
and EVERY p>2 and interior t,
\[
              c_{\min}(t)\le c_{\max}(t),
\]
and handle t=±1 and zero by the
existing conformal and homogeneous arguments.
This would prove global polyconvexity
by global supporting functions. A certified
profile with \(c_{\min}>c_{\max}\) would instead
disprove the *polyconvexity conjecture*,
**not** necessarily quasiconvexity or Morrey.
The 2026 diagonal characterization gives
an independent framework in which to
audit this equivalence.

## 2A. A genuine two-test-point reduction for the negative route

For a globally rank-one-convex h, the scalar acoustic criterion
gives \(C(t)=ph(t)-2th'(t)\ge0\). Thus the
orientation interval \(I_t=[L(t),U(t)]\)
in (2) is **always nonempty**, with the exact width

\[
 \boxed{U(t)-L(t)=\frac{2[ph(t)-2th'(t)]}{1-t^2}\ge0.}
 \tag{6}
\]

This is a useful distinction: for a rank-one-convex
integrand, lack of a global poly-affine support at
a nonconformal base is not a local orientation failure.
It must be caused by a **global test matrix**.

**Finite dual-certificate theorem.**
For a given differentiable isotropic
rank-one-convex p-homogeneous F and \(|t|<1\),
if no determinant multiplier c yields
a global poly-affine support at E_t, then
**one or two** pairs
\((a_j,s_j)\in[0,\infty)\times[-1,1]\)
suffice to certify the incompatibility:
the orientation bounds (2), combined with
the one or two inequalities (3) at these
test points, have **no** real solution c.

**Proof.** The orientation interval \(I_t\)
is nonempty and compact. Each scalar
inequality (3) cuts out a closed interval
or half-line of possible c values,
or all/none of \(\mathbb R\) when its
coefficient is zero. Rank-one convexity
ensures the coefficient-zero cases are
nonnegative, as explained after (4).
If the intersection of \(I_t\) with the
entire family is empty, compactness
implies a finite subfamily has empty
intersection. Intervals in \(\mathbb R\)
have Helly number two: among those
finite interval constraints and \(I_t\),
two already have empty intersection.
Thus at most two scalar test pairs
are needed, with the orientation
interval included as known background.
QED.

This provides a **uniformly finite type of
witness** for disproving poly-affine
support (hence a finite-valued global
polyconvex representative at that base),
independent of the exponent p, profile
degree, or number of rank-one directions.
The test pairs themselves are not
bounded to any fixed rational denominator,
degree or amplitude; no finite exhaustive
algorithm or positive cutoff is claimed.
A missing poly-affine support is not
by itself a failure of quasiconvexity.

**Algebra control:** The independent
[symbolic verifier](../../research/audit/iwaniec_scalar_support_identity.py)
checks the exact scalar identity, equality
at E_t, the orientation bounds, and
interval width. The compactness/Helly
reasoning is a hand argument, not a Lean
theorem.

## 3. Substantial open-family improvement of the exact p=4 candidate

Let h₀ be the exact Chebyshev polynomial
in [the rank-one support certificate](IWANIEC_MORREY_RANKONE_SUPPORT.md),
and write \(F_{p,h}(A)=a^p h(r)\).
There are **δ>0 and ε>0** such that,
whenever
\[
  |p-4|+\|h-h_0\|_{C^2([-1,1])}<\delta
  \quad\text{and}\quad |t|<\varepsilon,
\]
the integrand \(F_{p,h}\) is globally
rank-one convex and **has a global
poly-affine support at E_t**, using
the *same fixed determinant multiplier c=7*
with the other coefficients set by (1).

**Proof.** The exact rational Bernstein
certificate proves h₀>1/32 and strict
acoustic positivity plus endpoint
inequalities across [-1,1]; these open
conditions persist in a sufficiently
small C² profile/exponent neighborhood.
At t=0, the
[global rational certificate](IWANIEC_MORREY_RANKONE_SUPPORT.md)
proves (3) **strictly away** from (a,s)=(1,0)
on [0,16]×[-1,1]. In a small dyadic square
containing (1,0), the Hessian of (3)
in (a,s) is uniformly positive definite;
the exact certificate bounds its determinant
away from zero. The same strict positivity
and local Hessian bounds persist when
p,h,t vary slightly in the stated
topology; (3) and its first derivatives
vanish at the moving contact point
(1,t), so local strict convexity gives
nonnegativity there. Outside the square,
compactness gives a positive minimum
and stability under parameter perturbations.
For sufficiently large a, the uniform
positive bound on h, combined with p>2,
dominates the quadratic, linear and
constant parts of (3); choose a common
tail cutoff. The inequalities
\(u_7\pm v_7>0\) are strict for (4,h₀,0)
and persist. Thus (2)–(3) hold throughout.
The scalar acoustic criterion proves
rank-one convexity throughout the same
small neighborhood. QED.

This is an **open family of p>2 exponents,
profiles and full-rank signed ratios**,
not just one fixed p=4 function and not
just rank-one bases. Through isotropy and
scaling, it gives an open region of
**nonconformal full-rank matrices**
at which every integrand in this
infinite-dimensional class is
polyconvex. It is also a robust
counterexample to the completeness
of the earlier **homogeneous hybrid
support** (which still fails on an
open family). There is no contradiction:
the successful poly-affine supports
are **nonhomogeneous** functions of A.

**Evidence limits:** The central exact
p=4 rank-one certificate is replayable;
the openness argument and the general
pointwise-support iff are mathematical
hand deductions, not independently
reviewed/Lean-checked. No explicit δ or ε
is claimed. No statement here covers
every t, h, or p>2, and it is not a
solution to Question 1.7 or Morrey.
