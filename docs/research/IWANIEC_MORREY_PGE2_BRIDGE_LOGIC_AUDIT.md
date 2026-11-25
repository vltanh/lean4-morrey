# Independent logic re-audit: isotropic p≥2 proof and the unrestricted Morrey bridge

Date: 23 November 2026. This is an additional **AI-assisted mathematical audit**, **not** independent human refereeing, a Lean kernel proof, or a solution of unrestricted 2×2 Morrey. Reviewed branch head before editing: \`4bf5a73bbe3159381891833d03c7c25a4cdf1741\`. Existing proof: [IWANIEC_MORREY_PGE2_POLYCONVEXITY.md](IWANIEC_MORREY_PGE2_POLYCONVEXITY.md).

## Logical verdict on the proposed p≥2 theorem

**No fatal inference was found in the three-case construction** after checking the full detailed proof, its first-order assumptions, and the edge cases below. This raises confidence in the *hand-level* conclusion
\[
 F:\mathbb R^{2\times2}\to[0,\infty),\ 
 SO(2)\times SO(2)\hbox{-isotropic},\
 p\hbox{-homogeneous},\ p\ge2,\ RC
 \ \Longrightarrow\ PC .
\]
Do **not** present this as independently accepted or Lean-verified. The stronger claim of novelty relative to the literature also remains unverified.

### Check A: algebra is genuinely global

In conformal variables \(z,w\), a rank-one direction is any \((\alpha,\beta)\) with \(|\alpha|=|\beta|\). Therefore the curves used in Lemma 3 are genuine whole rank-one lines. For \(|t|<1\) at a differentiable profile point, the non-diagonal radial line forces
\[
 C=ph(t)-2th'(t)\ge0.
\]
In Case I \(H=h(t)>0\), \(m=h'(t)\) and \(\ell(-\kappa)=H-m(t+\kappa)<0\), where \(\kappa=(p-2)/p\). These imply \(m>0\) and \(t>-\kappa\), as checked by contradiction against \(C\ge0\).

Writing
\[
 x_0=(1+t)/2,\ y_0=(1-t)/2,\quad
 \Phi_x=pH+(1-t)m,\quad c=\Phi_x/(1+t),\
 \gamma=2C/(1+t),\
 \alpha=ct-(p-1)H,\
 \mu=-\frac{(p-1)\gamma}{(p-2)c},
\]
direct symbolic cancellation confirms *seven* identities in the accompanying independent checker: tangent stationarity, negativity of α, both angle endpoints, tangent contact, slope derivative and interval width. The angle bounds \(-2\le\mu\le2t\) follow from \(\ell(-\kappa)<0,C\ge0,m>0\) and ensure a valid rank-one line.

For every matrix A, the scale polynomial
\[
\psi(\lambda)=\alpha\lambda^p+\gamma|w(A)|\lambda^{p-1}
 +c\det(A)\lambda^{p-2}
\]
has the exact required endpoint behavior when \(p>2,\alpha<0\). If \(\sup\psi>0\), it has an interior maximum; stationarity places the normalized pair \((|w(A)|/\lambda,\det A/\lambda^2)\) on a **rank-one line through \(E_t\)**. Isotropy identifies the energy of that line point with that of \(A/\lambda\), and homogeneity transfers back to A. In Case III, the Burkholder-type envelope follows by the *exact λ-derivative factorization*, including the limit at λ=0. Case II is a reflected Case I and uses \(J R J\in SO(2)\) to preserve isotropy.

Nondifferentiable interior profile points are handled by one-sided convex derivatives and a limit of supports at differentiability points. Zero values admit the zero minorant. Conformal bases use determinant-power support for p≥2. Pointwise global touching minorants imply polyconvexity by the standard convex lift construction.

### Check B: explicit boundary of any attempted generalization

The proof uses two **structurally non-removable inputs**:

1. Isotropy converts equality of \((|z|,|w|)\) into equality of **energies** on a specially chosen rank-one line. For anisotropic F, that step is invalid.
2. Homogeneity converts \(\psi(\lambda)\) into the energy of \(A/\lambda\). For general F, stationarity under λ does **not** permit the same energy rescaling.

Moreover, the *polyconvexity conclusion itself is false* even if **nonnegativity, SO(2)×SO(2) isotropy, analytic smoothness, coercivity and global uniform rank-one ellipticity** are kept while only homogeneity is dropped. The [exact example](IWANIEC_MORREY_NONHOMOG_PC_NOGO.md) is
\[
q(A)=\|A\|_F^4-\tfrac94\|A\|_F^2\det A,\quad
W(A)=e^{q(A)}+\tfrac1{1000}\|A\|_F^2.
\]
After rotating a rank-one direction to \(E_{11}\), the exact identity
\[
\frac14D^2q(A)[E_{11},E_{11}]
 =3(a-\tfrac9{16}d)^2+\tfrac{13}{256}d^2
 +(b+\tfrac9{16}c)^2+\tfrac{175}{256}c^2
\]
proves global RC; exponentiation and the quadratic term preserve it, with a strict margin. A four-atom measure at \(\pm I,\pm J/5\), with weights \((1/52,1/52,25/52,25/52)\), has both matrix and determinant mean zero but a strict *polyconvex* Jensen violation, proven with rational upper bounds. The accompanying exact checker replays both identities and the rational deficit.

**Crucial boundary:** These four atoms are *not asserted to be an actual compatible planar gradient law*. Therefore this example is **not a counterexample to quasiconvexity** or Morrey; it only disproves any proposed unrestricted extension with PC as the conclusion. The published Guerra–Kristensen anisotropic nonnegative homogeneous non-PC construction gives a complementary obstruction when isotropy is dropped.

### Check C: what is left for *unrestricted* planar Morrey

The unrestricted theorem must say **RC⇒QC** for arbitrary finite-valued \(F:\mathbb R^{2\times2}\to\mathbb R\). The existing isotropic proof and any of its polynomial/Haar-average variants do not provide the missing **phase-sensitive and scale-sensitive compatible-gradient Jensen bound**. Rotational averaging preserves RC but cannot be inverted to recover inequalities for the original F. In particular, proving further isotropic exponents, perturbing within an isotropic cone, or invoking minor-preserving four-atom Jensen are **not** completion gates for unrestricted Morrey.

A logically correct unrestricted negative route already exists in [GLOBAL_CERTIFICATES.md](GLOBAL_CERTIFICATES.md): a genuine counterexample can be strictified, approximated by a globally RC rational polynomial, and accompanied by a rational finite PL gradient witness and exact sum-of-squares/norm-multiplier certificate. That is a **complete negative semidecision**, not a finite positive proof or a bound on degree/mesh. Conversely, a positive answer requires a universal gradient-Young-measure Jensen theorem, not mere nonemptiness of an unbounded hierarchy.

**Decision:** Treat the new p≥2 isotropic theorem as a plausible important hand proof awaiting Lean/human review. Keep the unrestricted Morrey gate explicitly **OPEN**. Do not claim that the three-case supports can be extended to arbitrary F without replacing both isotropy and homogeneity by genuinely new analytic principles.

## Independent exact audit control

[One-file check](../../research/audit/iwaniec_pge2_bridge_audit_exact.py) rederives seven central Case I symbolic identities; verifies the fully expanded global rank-one-Hessian sum of squares for the nonhomogeneous example; and verifies its exact four-atom rational upper gap. The check **does not** prove universal quantifiers or a general quasiconvexity statement. It provides regression controls for two logically separate claims.

Evidence: the script was executed locally with SymPy and passed each asserted identity. No CI/Lean build or human review is claimed.
