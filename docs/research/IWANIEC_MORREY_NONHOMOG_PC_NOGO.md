# Exact globally positive isotropic RC energy that is NOT polyconvex without homogeneity

23 November 2026. **Global counterexample to removing homogeneity from the proposed p≥2 isotropic RC→PC theorem.** This is NOT a counterexample to quasiconvexity or unrestricted Morrey. The rank-one-convex quartic ingredient is classical Dacorogna–Marcellini. The contribution here is an elementary self-contained rank-one Hessian SOS and a **four-atom exact determinant-compatible Jensen violation** for its positive exponential, with a completely rational bound. The witness's underlying quartic moments appeared earlier in ledger H26; there is no novelty claim for this general obstruction.

## Proposition

For \(A\in\mathbb R^{2\times2}\), define
\[
 q(A)=\|A\|_F^4-\frac94\|A\|_F^2\det A,
 \qquad
 W(A)=\exp(q(A)).
\]
Then W is finite, **strictly positive**, invariant under independent left/right SO(2) rotations, and **globally rank-one convex** on all \(\mathbb R^{2\times2}\); however, W is **not polyconvex**, already at the zero matrix. W is not positively homogeneous, so this does NOT contradict the new isotropic theorem.

## 1. Completely explicit global rank-one convexity

Choose a rank-one direction \(H=u\otimes v\neq0\). Normalize and rotate on the left/right by SO(2) so that H becomes a positive multiple of \(E_{11}\); the invariance of q makes this legitimate. Writing
\(A=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\),
direct differentiation yields
\[
\boxed{
\frac14D^2q(A)[E_{11},E_{11}]
=3(a-\tfrac9{16}d)^2+\tfrac{13}{256}d^2
 +(b+\tfrac9{16}c)^2+\tfrac{175}{256}c^2\ge0 .
}
\]
This is an exact SOS, proving q rank-one convex *for every matrix and every rank-one direction* (not just tested directions). Since exp is convex and increasing,
\[
D^2W(A)[H,H]
=W(A)\big(D^2q(A)[H,H]+(Dq(A)[H])^2\big)\ge0.
\]
Therefore W is globally rank-one convex. It is isotropic and positive because q is isotropic and real.

## 2. A fully exact four-atom witness against polyconvexity

Let \(J=\operatorname{diag}(1,-1)\), \(K=J/5\). Take the probability law
\[
 \nu=\frac1{52}(\delta_I+\delta_{-I})
     +\frac{25}{52}(\delta_K+\delta_{-K}).
\]
Its weights sum to 1 and
\[
 \int A\,d\nu=0,\qquad
 \int\det A\,d\nu=
 \tfrac2{52}\det I+\tfrac{50}{52}\det K
 =\tfrac1{26}-\tfrac{25}{26}\tfrac1{25}=0=\det0 .
\]
The exact quartic energies are
\[
 q(I)=-\tfrac12,\qquad
 q(K)=\tfrac{17}{1250},\qquad
 q(0)=0 .
\]
Thus
\[
 \int W\,d\nu
  =\frac1{26}e^{-1/2}+\frac{25}{26}e^{17/1250}.
\]
Use **rational** exponential bounds:
\(e^{1/2}>1+\tfrac12+\tfrac18=\tfrac{13}{8}>\tfrac85\),
so \(e^{-1/2}<\tfrac58\); and for \(0<x<1\),
\(e^x=\sum x^n/n!<\sum x^n=1/(1-x)\).
Hence
\[
\boxed{
\int W\,d\nu
 <\frac1{26}\frac58+
   \frac{25}{26}\frac{1250}{1233}
 =\frac{19705}{19728}<1=W(0).
}
\]
Polyconvex Jensen requires the reverse inequality for any law whose matrix mean and determinant mean equal the minors of its barycenter. Therefore W is **not polyconvex**. No numerical optimization or transcendental approximation was used.

The [exact checker](../../research/audit/iwaniec_nonhomogeneous_positive_nonpc.py) validates the SOS polynomial identity and all rational moments/inequalities. This witness is generally **not a compatible planar gradient Young measure**, so it does not refute Morrey.

## 3. Structural consequence for the unrestricted plan

Even with **nonnegativity and isotropy**, removing positive homogeneity makes the **polyconvex** conclusion false. Moreover, removing **isotropy** while retaining nonnegative p-homogeneity also makes it false: the [corrected Guerra–Kristensen (2022) three-atom witness](IWANIEC_MORREY_P2_SIGNED.md#exact-correction-guerra-kristensen-2022-proposition-37) applies to every p≥2.

Therefore a path to unrestricted \(2\times2\) Morrey cannot be:
"prove RC→PC for the isotropic p-homogeneous class, then simply remove homogeneity and isotropy while keeping PC."
Instead the target has to weaken to **RC→quasiconvexity** and introduce an argument that uses actual gradient compatibility, not merely matrix/determinant moments. This paper's new p≥2 isotropic theorem does not supply such a mechanism.

**Optional additional information, not needed for the no-PC proof:** Bruno–Pasqualotto (2026) claim quasiconvexity of the full Dacorogna–Marcellini quartic rank-one-convex range. Under that published/preprint statement, q is QC, and so is exp∘q by scalar convex Jensen. That further emphasizes that non-PC is not non-QC. This note does not rely on that recent result in its theorem.
