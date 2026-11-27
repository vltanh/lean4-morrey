# Global quartic orbit certificate for Morrey's 2×2 problem

**Date:** 21 November 2026. **Status:** Exact hand proof plus computer-checkable rational certificate for the statements below. **This is not a solution of Morrey's conjecture**: it establishes a computable quasiconvex subcone, not an equality with the rank-one-convex cone.

## 1. Setup and external result

Let \(A=\begin{pmatrix}a&b\\c&d\end{pmatrix}\), \(q=\det A=ad-bc\), \(s=|A|^2=a^2+b^2+c^2+d^2\). For real \(t\), write

\[
 W_t(A)=s^2+4t\,sq+(6t^2-2)q^2.
\]

**External theorem:** Bruno–Pasqualotto, *Quasiconvexity for the Dacorogna–Marcellini Energy*, arXiv:2608.06367 (2026), Appendix A: \(W_t\) is globally quasiconvex whenever \(|t|\le1\). This analytic theorem is not re-proved here.

Quasiconvexity is preserved under \(A\mapsto LAR\), for invertible \(L,R\in GL(2,\mathbb R)\). Indeed, for \(x=Ry\), the test map \(\psi(y)=L u(Ry)\) has \(D\psi(y)=L Du(Ry)R\). Thus every \(W_t(LAR)\), \(|t|\le1\), is quasiconvex, as is every finite nonnegative linear combination.

## 2. Exact 35-generator global cone

There are 35 explicit pairs \((L_i,R_i)\) of **unimodular integer 2×2 matrices**, all but one with entries in \(\{-1,0,1\}\), such that the quartic polynomials

\[
 W_{1/2}(L_i A R_i),\qquad 1\le i\le35,
\]

are linearly independent. Therefore, they form a real basis of the 35-dimensional space \(\mathcal P_4\) of homogeneous quartic polynomials in the four matrix entries.

**Exact finite certificate.** The accompanying JSON lists all 70 matrices and the coefficients of the 35 integral polynomials \(2W_{1/2}(L_i A R_i)\) in the lexicographically indexed quartic monomial basis. An independent SymPy checker recomputes all coefficients and verifies

\[
 \det C\equiv 41797\pmod {104729},\quad C\in\mathbb Z^{35\times35}.
\]

Since the determinant is nonzero modulo a prime, these functions are independent over \(\mathbb Q\), hence over \(\mathbb R\). Every combination \(\sum_i\lambda_i W_{1/2}(L_i A R_i)\), \(\lambda_i\ge0\), is globally quasiconvex. The cone has nonempty interior in coefficient space. No gradient-grid restriction is involved.

**Important limitation:** linear basis membership does not imply membership in the nonnegative cone. For example, the convex quartic \(a^4\) is not a nonnegative combination of these generators: each generator is strictly positive at any nonzero rank-one matrix, whereas \(a^4\) vanishes at some such matrices. Adding the convex cone removes this particular obstruction, but equality with the full rank-one-convex quartic cone remains unproved.

## 3. Hand proof of a uniform orbit-dimension theorem

Define the constant-coefficient differential operator

\[
 \mathcal D=\frac{\partial^2}{\partial a\,\partial d}-\frac{\partial^2}{\partial b\,\partial c}.
\]

For a homogeneous polynomial \(P\) of degree \(n\), a direct product-rule computation gives

\[
 \mathcal D(qP)=q\mathcal DP+(n+2)P.
\]

In particular, \(\mathcal Dq=2\), \(\mathcal D(q^2)=6q\), \(\mathcal Ds=0\), and \(\mathcal D(s^2)=8q\).

Let \(\mathcal H_k=\ker(\mathcal D\colon\mathcal P_k\to\mathcal P_{k-2})\). Every homogeneous quartic \(P\) has the **unique** splitting

\[
 \boxed{P=H_4+qH_2+cq^2,\qquad H_4\in\mathcal H_4,\ H_2\in\mathcal H_2,\ c\in\mathbb R}
\]

where

\[
 c=\frac{\mathcal D^2P}{12},\quad
 H_2=\frac{\mathcal DP-6cq}{4},\quad
 H_4=P-qH_2-cq^2.
\]

Verification gives \(\mathcal DH_4=\mathcal DH_2=0\), and uniqueness follows by applying \(\mathcal D^2\) and then \(\mathcal D\) to any zero decomposition. Since \(\dim\mathcal P_4=35\) and \(\dim\mathcal H_2=9\), it follows that \(\dim\mathcal H_4=25\). Thus we obtain a canonical \(25\oplus9\oplus1\) decomposition.

The chain rule for an invertible change \(g(A)=LAR\) gives

\[
 \mathcal D(P\circ g)=(\det L)(\det R)(\mathcal DP)\circ g.
\]

Therefore each of the three summands \(\mathcal H_4,\ q\mathcal H_2,\ \mathbb R q^2\) is invariant under the \(GL_2\times GL_2\) action.

The family has the following explicit decomposition:

\[
 W_t=\underbrace{s^2-\tfrac43q^2}_{\in\mathcal H_4}
      +\underbrace{4t\,sq}_{\in q\mathcal H_2}
      +\underbrace{(6t^2-\tfrac23)q^2}_{\in\mathbb Rq^2}.
\]

Define \(T_t\) to act as multiplication by \(1,2t,\frac45(9t^2-1)\) respectively on the three invariant summands. Then \(T_{1/2}=\operatorname{id}\), \(T_t\) commutes with the group action, and \(T_tW_{1/2}=W_t\).

Since the 35 matrices \(g_i\) in Section 2 give a basis \(\{g_i\cdot W_{1/2}\}\), the 35 images \(g_i\cdot W_t\) span \(\operatorname{im}T_t\). Every other orbit point is also in this image. Therefore:

\[
 \boxed{\dim\operatorname{span}\{W_t(LAR):L,R\in GL_2(\mathbb R)\}=
 \begin{cases}
 26,&t=0,\\
 34,&t=\pm\frac13,\\
 35,&\text{otherwise}.
 \end{cases}}
\]

No genericity condition on \(L,R\) and no numerical optimization is involved. The one computational input is the independently checked exact rank-35 integer certificate at \(t=1/2\). The split and commutation argument are hand proofs valid for every real \(t\).

## 4. Global route that is still missing

Let \(\mathcal R_4\) be the cone of all globally rank-one-convex homogeneous quartic polynomials on \(\mathbb R^{2\times2}\); let \(\mathcal Q_4\) be the quasiconvex cone. Known implications give \(\mathcal Q_4\subseteq\mathcal R_4\). To close the **quartic** gate by this approach, one could attempt to prove

\[
 \mathcal R_4\subseteq
 \overline{\mathcal C_{\mathrm{conv}}+\mathcal C_{\mathrm{poly}}+
 \operatorname{cone}\{W_t(L\,\cdot\,R):\ |t|\le1,\ L,R\in GL_2\}}\subseteq\mathcal Q_4.
\]

The displayed **first inclusion is unproved**. In particular, the fact that the linear spans agree (Section 2) supplies *no* evidence of nonnegative cone equality. Also, proving even all quartics would not resolve the unrestricted problem; a degree-uniform positive representation or another argument is still required.

A second attempted global route, universal componentwise heat-flow monotonicity, is definitively unavailable: \(f(A)=(\det A)^2+\eta|A|^2\) is polyconvex and strongly rank-one convex, yet there is an explicit periodic two-component test map whose heat-flow energy derivative equals \(20s^4-336\eta s^2>0\) for suitable \(s\). The exact trigonometric verifier is in the bundle. In particular, no universal pointwise nonnegative exact-two-form correction of the type in Bruno–Pasqualotto can exist for **all** rank-one-convex integrands.

## 5. Status and verification

**Proved and exactly checked:** 35-element unimodular quasiconvex basis; full-dimensional positive subcone; exact \(25+9+1\) harmonic decomposition; orbit-dimension formula for all real \(t\); structural failure of linear-span-to-cone reasoning.

**Not proved:** all rank-one-convex quartics are quasiconvex; positive cone inclusion; degree-uniform extension; Morrey's unrestricted \(2\times2\) conjecture.

Run:

```sh
python morrey_verify_quartic_orbit_basis.py
python morrey_quartic_harmonic_verifier.py
python morrey_heatflow_no_go.py
```

The first two check all exact polynomial identities. They require SymPy, and the last requires SymPy for exact trigonometric integration. They do **not** constitute a Lean formalization or an independent verification of the external Bruno–Pasqualotto analytic theorem.
