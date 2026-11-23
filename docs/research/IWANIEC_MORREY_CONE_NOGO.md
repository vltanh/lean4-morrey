# A global no-go for polyconvex + Iwaniec calibrator cones

Research date: 22 November 2026. **Status:** complete hand arguments, exact
rational witnesses; not independently reviewed or formalized in Lean.
The quasiconvexity of L used below is the claim of
[arXiv:2609.28311v2](https://arxiv.org/pdf/2609.28311), Theorem 1.
The obstruction itself requires at most rank-one convexity of L, and the
asymptotic formula below can be checked directly.

**Verdict:** The natural attempt to extend the p=2 signed isotropic
polyconvex-support theorem to unrestricted anisotropic 2×2 integrands by
adding nonnegative combinations of **all matrix translates and
invertible left/right transforms of the Iwaniec integrand L** is
provably **incomplete**. A known rank-one-convex example has an
**exact gap 1 at I** in the resulting lower-envelope hierarchy.
This is *not* a Morrey counterexample and provides a stopping rule
for a specific generator-cone route.

## 1. A genuinely nonpolyconvex quasiconvex generator

The 2026 Iwaniec paper proves quasiconvexity of

\[
 L(A)=
 \begin{cases}
 \det A, & \|A\|_{\rm op}\le1,\\
 2|a_+(A)|-1,&\|A\|_{\rm op}>1,
 \end{cases}
 \qquad A z=a_+(A)z+a_-(A)\overline z.
 \tag{1}
\]

Here \(\|A\|_{\rm op}=|a_+|+|a_-|\).
This L is **not polyconvex at zero**.

**Exact proof.** If a finite-valued polyconvex extension existed with
equality at 0, a subgradient of its convex lifted representative
would give a global poly-affine minorant

\[
 L(A)\ge L(0)+H:A+c\det A=H:A+c\det A
 \qquad\forall A.                                   \tag{2}
\]

Along any rank-one matrix R and sufficiently small t,
\(L(tR)=\det(tR)=0\). Applying (2) at \(tR\)
and \(-tR\) gives \(H:R=0\). Since rank-one
matrices span \(\mathbb R^{2\times2}\), \(H=0\).
Now two exact matrices force contradictory conditions:

- At \(D=\operatorname{diag}(1,-1)\), with
  \(\|D\|_{\rm op}=1\), \(L(D)=\det D=-1\);
  inequality (2) gives \(c\ge1\).
- At \(2I\), with \(\|2I\|_{\rm op}=2\),
  \(a_+(2I)=2\), \(L(2I)=3\) and \(\det(2I)=4\);
  inequality (2) gives \(c\le3/4\).

Thus no such supporting minorant exists and L is
not polyconvex at 0, **assuming only its displayed
elementary definition**, not quasiconvexity.

Since \(L\ge-1\), \(W=1+L\) is everywhere
nonnegative, globally quasiconvex **conditional
on the 2026 theorem**, but nonpolyconvex.
For invertible P,Q, an arbitrary matrix shift C
and \(\lambda>0\), the functions
\[
 W_{P,Q,C}(A)=1+L(P(A-C)Q)
\]
(and their positive scalings) remain globally
quasiconvex, typically anisotropic and
nonhomogeneous, and fail polyconvexity at C.
The invariance under invertible right changes
uses a domain change in the defining gradient
integral; the determinant after a matrix
translation is affine in \((A,\det A)\), so
polyconvexity is also preserved in both
directions. This is a concrete family **outside
the purely polyconvex p=2 orbit**, not a
completeness statement.

## 2. A rank-one-flat test energy

Guerra–Kristensen (2022), Proposition 3.7, gives
the nonnegative rank-one-convex, 2-homogeneous
anisotropic integrand
\[
 T(A)=\max(a,0)\max(d,0)+\tfrac12(b^2+c^2),
 \quad A=\begin{pmatrix}a&b\\c&d\end{pmatrix}.
 \tag{3}
\]

At \(I\), \(T(I)=1\). For every real t, with
\(R=\operatorname{diag}(1,0)\), it has an
**entire rank-one-flat line**
\[
                    T(tR)=0 \qquad(t\in\mathbb R).
 \tag{4}
\]

A corrected exact minors-preserving three-atom
witness from [the signed p=2 audit](IWANIEC_MORREY_P2_SIGNED.md)
shows that every polyconvex \(P\le T\)
satisfies \(P(I)\le0\). Explicitly,
\[
 (w_i,A_i)=
 (1/4,\operatorname{diag}(-2,-2)),
 (3/8,\operatorname{diag}(4,0)),
 (3/8,\operatorname{diag}(0,4)),
\]
whose mean matrix and mean determinant are
\(I\) and 1, respectively, with \(T(A_i)=0\).
For any polyconvex P below T, Jensen on the
minor graph gives
\(P(I)\le\sum_iw_iP(A_i)\le0\).
This does **not** imply T is non-quasiconvex
because the triple is not an actual planar
gradient law.

## 3. A sharp obstruction to all positive Iwaniec-L combinations

Consider any integrand of the form
\[
 G(A)=P(A)+
 \sum_{j=1}^N\alpha_j
 L\big(U_j(A-C_j)V_j\big),                     \tag{5}
\]
where P is **globally polyconvex** (real-valued),
\(\alpha_j\ge0\), and U_j,V_j are invertible
real 2×2 matrices. Finite N is arbitrary,
and arbitrary affine/quasiaffine terms may be
absorbed into P.

**Theorem 3.1.** If \(G(A)\le T(A)\) for every A,
then every coefficient \(\alpha_j\) in (5)
must be zero. Consequently \(G(I)\le0\).

**Proof.** Restrict (5) to the entire rank-one
line \(A=tR\) from (4). Each function
\(t\mapsto P(tR)\) and
\(t\mapsto L(U_j(tR-C_j)V_j)\) is convex
(polyconvexity, respectively rank-one convexity).
Their sum \(G(tR)\) is convex and bounded above
by \(T(tR)=0\) on the **whole real line**;
hence \(G(tR)\) is constant. For a sum of
convex functions with nonnegative coefficients
to be affine, each summand with positive
coefficient must be affine separately
(all Jensen defects are nonnegative).

But \(B_j=U_jRV_j\) has rank one and is
nonzero. Since det B_j=0 and
\(\|B_j\|_{\rm op}>0\), its complex-linear
coefficient satisfies
\[
 |a_+(B_j)|=|a_-(B_j)|=\|B_j\|_{\rm op}/2>0.
\]
For sufficiently large |t| the outer branch
of L applies, and
\[
 L(tB_j-U_jC_jV_j)
  =2|t\,a_+(B_j)-a_+(U_jC_jV_j)|-1
  =\|B_j\|_{\rm op}|t|+O(1).
\]
Thus this function has **opposite nonzero
asymptotic slopes** at ±∞, so it cannot
be affine on the real line. Contradiction
unless \(\alpha_j=0\). All L terms disappear;
then \(G=P\le T\) is polyconvex and
\(G(I)\le0\) by the exact minors Jensen
control above. QED.

**Exact lower-envelope gap.** Include constant
zero as an admissible polyconvex lower bound
(because T≥0) and define
\[
 \mathcal C_L T(I)
  :=\sup\{G(I):G\le T,\ G\text{ as in (5)}\}.
\]
Then
\[
 \boxed{\ \mathcal C_L T(I)=0<1=T(I).\ }       \tag{6}
\]
Adding **pointwise maxima, locally bounded
suprema, or locally uniform limits** to the
admissible lower bounds does not close this
gap: each admissible constituent satisfies
\(G(I)\le0\), and every supremum therefore
also satisfies the bound.

This is a precise **infinite-class no-go**:
all GL transforms, all matrix shifts,
all numbers of positive L terms, arbitrary
polyconvex additions, and all positive-cone
suprema are covered. No finite search could
repair its missing 1-unit support at I.

## 4. Why it matters for the unrestricted Morrey problem

The two facts coexist:

1. Iwaniec supplies explicit globally quasiconvex
   **nonpolyconvex** building blocks, and through
   invertible changes and translations many
   anisotropic and nonhomogeneous ones.
2. The full positive cone of those blocks plus
   **all** polyconvex energies cannot certify
   a simple known anisotropic rank-one-convex
   p=2 energy at a single base matrix.

Therefore, **one should not treat positive-cone
generation from the 2026 L and Burkholder family
as a promising unrestricted proof strategy
without a demonstrably larger generator class**.
The proof only excludes the precisely
defined class (5); it does NOT rule out a
different nonlinear calibration, negative
coefficients justified by independent
quasiconvexity, alternative operators,
or a universal all-gradient argument.

The exact remaining options are:

- A new genuinely nonpolyconvex **QC calibrator
  that is affine along relevant whole rank-one
  flats**, plus a completeness theorem; or
- A direct all-gradient inequality, potentially
  bypassing any global lower-touching cone; or
- A certified negative planar gradient witness
  for some globally rank-one-convex integrand.

The example T is **not asserted non-quasiconvex**,
and (6) does not imply the failure of Morrey.
The unrestricted \(2\times2\) problem remains
open. This note is a research *stop rule* and
a worked-out exact obstruction, not a
completed solution of Morrey.
