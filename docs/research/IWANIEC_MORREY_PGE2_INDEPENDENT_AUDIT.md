# Independent mathematical audit of the proposed all-p≥2 isotropic theorem

Date: 23 November 2026. Audited PR #1 head 45e63c34a7878fbf4ee2b46fdb4ad13be0680379, file [IWANIEC_MORREY_PGE2_POLYCONVEXITY.md](IWANIEC_MORREY_PGE2_POLYCONVEXITY.md). **Verdict: no fatal mathematical gap identified in the main proof under exactly its stated hypotheses.** This is independent *AI hand-audit*, reinforced with algebraic/rational checks, **not** human peer review, Lean formalization, or proof of unrestricted planar Morrey. The novelty of the resulting theorem has not been independently established.

## Checklist with precise dependency boundaries

| Proof gate | Logical test | Result |
| --- | --- | --- |
| Signed conformal coordinates | \(A\mapsto(z,w)\) invertible; \(F=\Phi(|z|,|w|)\) by independent SO(2) phase rotations; \(\det A=|z|^2-|w|^2\) | PASS by direct calculation |
| Lemma 3(a),(b),(c) | Paths have directions \((\alpha,\beta)\) with \(|\alpha|=|\beta|\), hence rank one; evenness in (b) gives the monotone radial curve | PASS |
| First-order bound | The radial-curve minimum at 0 gives \(C=ph(t)-2th'(t)\ge0\) at differentiability points | PASS |
| Burkholder-type envelope | Exact derivative \(\partial_\lambda Q_\lambda=-(p-1)\lambda^{p-3}(\lambda-\sigma)[pc_0\lambda+(p-2)m\delta]\) and its signs | PASS |
| Case III | \(h\ge\max(\ell,0)\), and \(c_0\ge\kappa|m|\) makes the real-part coefficients nonnegative; resulting polyaffine support touches | PASS |
| Case I angle | Under \(h(t)>0\), \(\ell(-\kappa)<0\), and \(C\ge0\), prove \(m>0,\alpha<0,\gamma\ge0,c>0,-2\le\mu\le2t\) | PASS; independently rederived below |
| Case I global inequality | The positive maximum of \(\psi(\lambda)=\lambda^p[\alpha+\gamma|w|/\lambda+c\,\det A/\lambda^2]\) yields \((y^\ast,d^\ast)\) lying on a rank-one curve from \(E_t\), whose tangential Jensen inequality bounds every matrix A | PASS |
| Case II | Reflection \(A\mapsto AJ\) swaps the conformal components; preserves SO(2)-bi-invariance after conjugating rotations, and preserves rank-one convexity | PASS |
| Boundary and nonsmooth | Conformal determinant-power support for p≥2; zero support at F=0; convex h with one-sided derivatives approximated by differentiability points | PASS |
| From touching supports to PC | Appendix A's finite convex lift via \(\frac12T(B+C)+\frac12T(B-C)=(B,\det B+\det C)\) fills \(\mathbb R^5\); a single global support bounds the lift below | PASS |

## Short independent derivation of the only genuinely hard step (Case I)

For \(p>2\), fix \(-1<t<1\), \(H=h(t)>0\), \(m=h'(t)\), \(\kappa=(p-2)/p\), \(C=pH-2tm\ge0\). Suppose the supporting line \(\ell(s)=H+m(s-t)\) obeys \(\ell(-\kappa)<0\). Then \(m(t+\kappa)>H>0\). If \(m<0\), necessarily \(t<-\kappa\). Combining \(C\ge0\) with \(\ell(-\kappa)<0\) gives \(2|t|/p<|t|-\kappa\), hence \(\kappa<\kappa|t|\), impossible. Thus \(m>0\) and \(t>-\kappa\).

In conformal polar coordinates let \(x_0=(1+t)/2,\ y_0=(1-t)/2\), \(\Phi_x=pH+(1-t)m>0\), and set
\[
 c=\frac{\Phi_x}{1+t}>0,\quad
 \gamma=\frac{2C}{1+t}\ge0,\quad
 \alpha=ct-(p-1)H,\quad
 \mu=-\frac{(p-1)\gamma}{(p-2)c}.
\]
Exact algebra gives
\[
 \alpha=-\frac{(1-t)C+(p-2)(1+t)H}{2(1+t)}<0,
 \qquad
 \mu+2=\frac{-2p\,\ell(-\kappa)}{(p-2)\Phi_x}>0.
\]
Also
\[
 2t-\mu=\frac{2N}{(p-2)\Phi_x},\quad
 N=pH[(p-1)+(p-2)t]-tm[p+(p-2)t].
\]
For \(t<0\), **both summands in this expression for N are positive**; for \(t\ge0\), the equivalent \(N=t(p-2)\Phi_x+(p-1)C\ge0\). Consequently \(-2<\mu\le2t\), so an angle \(\theta\) with \(\cos\theta=(\mu+1-t)/(1+t)\) exists.

For arbitrary A with conformal-coordinate magnitudes \(x_1,y_1\), determinant \(d_1\), put
\[
\psi(\lambda)=\alpha\lambda^p+\gamma y_1\lambda^{p-1}+cd_1\lambda^{p-2}.
\]
Since \(p>2,\alpha<0\), \(\psi(0+)=0\) and \(\psi(\infty)=-\infty\). When \(\sup\psi>0\), an interior maximizer \(\lambda^\ast\) satisfies
\[
 p\alpha+(p-1)\gamma y^\ast+(p-2)c d^\ast=0,\qquad
 (y^\ast,d^\ast)=(y_1/\lambda^\ast,d_1/\lambda^{\ast2}).
\]
The same stationarity relation at the touching base is
\(p\alpha+(p-1)\gamma y_0+(p-2)ct=0\). Subtracting shows
\[
 d^\ast=t+\mu(y^\ast-y_0).
\]
The rank-one line \(z_\tau=x_0+\tau e^{i\theta}, w_\tau=y_0+\tau\) has
\(\det A_\tau=t+\mu\tau\). At \(\tau^\ast=y^\ast-y_0\), its w modulus is exactly \(y^\ast\), and its determinant is \(d^\ast\). Therefore its z modulus equals \(x_1/\lambda^\ast\). **Isotropy is used at precisely this step**: \(F(A_{\tau^\ast})=F(A/\lambda^\ast)\), although their phases can differ.

By the rank-one tangent inequality and \(g'(0)=\gamma+\mu c\),
\[
 F(A_{\tau^\ast})
 \ge H+(\gamma+\mu c)\tau^\ast
 =\alpha+\gamma y^\ast+c d^\ast.
\]
Multiply by \(\lambda^{\ast p}\) and use \(\psi(\lambda^\ast)\ge\psi(1)\):
\(F(A)\ge\alpha+\gamma|w(A)|+c\det A\).
If \(\sup\psi\le0\), the same bound is immediate from \(F\ge0\).
Finally \(\gamma\ge0\) permits replacement of \(|w|\) by \(\Re w\), producing the claimed polyaffine support. Case II follows by reflection. This argument has **no finite-amplitude hypothesis** and handles arbitrarily large/small A.

For Case III, the \(\lambda\)-derivative above and \(c_0\ge\kappa|m|\) imply that its only possible maximum is an endpoint \(\lambda\downarrow0\) or \(\lambda=\sigma\). As \(p>2\), they give \(0\) and \(\sigma^{p-1}(c_0\sigma+m\delta)\), respectively. This is exactly the claimed global envelope. The p=2 case uses the convex square of \(\sigma_1\) instead.

## Independent reproducibility

[Standalone checker](../../research/audit/iwaniec_pge2_independent_logic_audit.py) uses SymPy for the **16** core identities, symbolic Burkholder derivative, a deterministic rational sweep of 76,915 admissible first-order triples in all three cases, and exact case classification on all three branches. A **separate local** signed-ratio grid on known nonnegative polyconvex profiles was also run, but is not included in this checker. Both passed locally. Numerical controls are **not** a universal proof; the positive verdict above rests on the displayed hand derivation, one-variable calculus and rank-one convexity.

A pointwise support \(P_t\) is valid at every base only under the proof's actual **nonnegative, SO(2)×SO(2)-isotropic, positively homogeneous, globally rank-one-convex** hypotheses. Nothing here establishes rank-one convexity ⇒ **quasiconvexity** for arbitrary anisotropic/nonhomogeneous 2×2 energies.

## Why this does NOT solve unrestricted Morrey

The proof uses two genuinely restrictive facts that cannot be deleted mechanically:

1. **Isotropy:** same \((|z|,|w|)\) implies same F value at \(\tau^\ast\), even when the phases differ. This identity is false for a general anisotropic F.
2. **Homogeneity:** the arbitrary matrix is pulled back to a stationary rank-one line via \(\psi(\lambda)\). Without \(F(\lambda A)=\lambda^pF(A)\), that rescaling does not preserve F.

Moreover, **polyconvexity itself is a false target** after removing either hypothesis. The corrected three-atom Guerra–Kristensen counterexample in [IWANIEC_MORREY_P2_SIGNED.md](IWANIEC_MORREY_P2_SIGNED.md) handles nonnegative anisotropic homogeneous rank-one-convex functions for every p≥2. The [explicit positive isotropic nonhomogeneous counterexample](IWANIEC_MORREY_NONHOMOG_PC_NOGO.md) removes the other hypothesis. Neither is a counterexample to quasiconvexity. To prove unrestricted Morrey one needs an additional **phase-sensitive, scale-sensitive quasiconvexity argument**, not an iteration of this polyconvex support theorem.

**Audit conclusion:** The new isotropic p≥2 proof is a credible completed hand argument with no logical gap located here, but it is a major claimed result whose formal status remains **unverified in Lean and unreviewed by an independent mathematical referee**. Do not mark the unrestricted Morrey problem closed or report a publication-level theorem as accepted.
