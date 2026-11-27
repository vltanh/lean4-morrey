# Iwaniec and planar Morrey: exact connection and a calibration route

Research date: 22 November 2026. Source: Agazzi et al., *Sharp Higher Integrability Theory, Part I: The L^p-norm of the Beurling--Ahlfors transform*, [arXiv:2609.28311v2](https://arxiv.org/abs/2609.28311v2) (8 October 2026).

**Verdict.** The Iwaniec paper does **not** give a counterexample to Morrey's 2 × 2 implication, and it does **not** prove that implication. Its Theorem 1 claims quasiconvexity of one special integrand; Corollary 2 claims quasiconvexity of the Burkholder family and the sharp Beurling--Ahlfors norm. The universal question for every finite-valued rank-one-convex integrand remains open. This note derives a reusable (conditional) calibration scheme, not a Morrey completion.

Evidence levels: **SOURCE** = a statement in the cited preprint; **ALGEBRA** = an explicit direct derivation below; **CONDITIONAL** = a consequence of the preprint's constrained-projection Lemma 4, not independently formalized here; **OPEN** = a universal theorem still missing. None of the new claims in this note has been implemented or kernel-checked in Lean.

## 1. Which implication goes in which direction?

Morrey asks whether for every finite-valued rank-one-convex f on real 2 × 2 matrices and all admissible planar gradient laws,

\[
    \int_Q f(A+D\varphi)\,dx \geq f(A).
\]

Iwaniec's conjecture asserts for the Beurling--Ahlfors transform S and every 1 < p < infinity,

\[
  \|S\|_{L^p(\mathbb C)\to L^p(\mathbb C)}
     =p^*-1,\qquad p^*=\max\{p,p/(p-1)\}.
\]

The Burkholder energies B_p are a distinguished family of rank-one-convex planar integrands. The known reduction yields:

\[
  \text{universal planar Morrey implication}
  \Longrightarrow \text{quasiconvexity of the relevant Burkholder energies}
  \Longrightarrow \text{Iwaniec's sharp operator-norm estimate}.
\]

The paper obtains the latter conclusions **directly**, without universal Morrey. Neither the exact norm nor quasiconvexity of all B_p supplies a representation of an *arbitrary* rank-one-convex f by these energies. Consequently:

- Had the sharp Iwaniec norm estimate been **false**, that would have refuted the universal planar Morrey implication by contraposition of the established reduction.
- Its claimed **truth** neither refutes nor establishes Morrey.
- Cassese's explicit 2 × 3 counterexample in this repository, and Šverák's 3 × 2 example, do not become 2 × 2 counterexamples after this result.

Do not conflate rank-one convexity with polyconvexity, or the cone of Burkholder/related energies with all rank-one-convex integrands.

## 2. The integrand actually treated in the new proof (SOURCE)

Identify real 2 × 2 maps with complex maps Az = a_+ z + a_- \overline z.
Then \(\|A\|_{\mathrm{op}}=|a_+|+|a_-|\) and \(\det A=|a_+|^2-|a_-|^2\).
Theorem 1 concerns the finite-valued integrand

\[
L(A)=
\begin{cases}
\det A,&\|A\|_{\mathrm{op}}\leq1,\\
2|a_+|-1,&\|A\|_{\mathrm{op}}>1.
\end{cases}
\]

The threshold uses the **operator norm**, not the Frobenius norm.
The paper claims for every A and smooth periodic \(\varphi:Q\to\mathbb R^2\),

\[
 \int_Q[L(A+D\varphi)-L(A)]\,dx\geq0,\qquad Q=\mathbb R^2/\mathbb Z^2.
\]

Corollary 2 claims the same quasiconvexity inequality for each B_p and concludes \(\|S\|_p=p^*-1\) using the cited prior reduction. This is a family of **positive Jensen inequalities**, not a rank-one-convex/non-quasiconvex witness. Treat the recent preprint's claims as claims until an independent complete proof audit or formalization is available.

## 3. Exact algebra and the moving calibration (ALGEBRA + SOURCE)

Write A with row vectors \(A^1,A^2\). For \(z\in\mathbb R^2\), let

\[
G_z(A)=\det(z,A^2)+z\cdot(A^1-z),\qquad
F(A)=\sup_{|z|=1}G_z(A).
\]

Every fixed-z function G_z is **affine in A**; therefore

\[
F(A)=|A^2+JA^1|-1=2|a_+|-1
\]

is convex, with J the quarter-turn matrix. The direct factorization

\[
\det A-F(A)=
(1-|a_+|-|a_-|)(1-|a_+|+|a_-|)
\]

together with \(|a_+|-|a_-|\leq |A^1|\leq |a_+|+|a_-|\)
shows that

\[
L(A)=\sup_{z\in Z(A^1)}G_z(A),\quad
Z(a)=\mathbb S^1\cup
\begin{cases}\{a\},&|a|\leq1,\\\varnothing,&|a|>1.\end{cases}
\]

In particular \(L\geq F\) everywhere and \(L(A)\geq\det A\) whenever \(|A^1|\leq1\). If \(\|A\|_{\rm op}>1\), then \(L(A)=F(A)\), and ordinary convex Jensen gives quasiconvexity at A.

The nontrivial case is \(\|A\|_{\rm op}\leq1\). Write \(u=Ax+\varphi\), project the first scalar component \(u^1\) to a gradient-constrained scalar function \(w\) with \(|Dw|\leq1\), and set \(z(x)=Dw(x)\). The preprint's Lemma 4 gives:

\[
 Dw=Du^1\quad\text{or}\quad |Dw|=1\quad\text{a.e.},\qquad
 \int_Q Dw\cdot(Du^1-Dw)\,dx\geq0.
\]

Thus \(z(x)\in Z(Du^1(x))\), so \(L(Du)\geq G_{Dw}(Du)\) pointwise.
Because the determinant is a null Lagrangian, periodicity gives

\[
 \int_Q\det(Dw,Du^2)\,dx=\det A.
\]

This yields an **exact nonnegative-defect decomposition**, not just a heuristic:

\[
\begin{aligned}
 \int_Q L(Du)\,dx-L(A)
 &=\int_Q\big[L(Du)-G_{Dw}(Du)\big]\,dx\\
 &\quad+\int_Q Dw\cdot(Du^1-Dw)\,dx\ \geq0.
\end{aligned}
\]

The first term is pointwise nonnegative; the second is nonnegative after integration. The equality uses \(L(A)=\det A\) in the interior-base case.

**Independently checkable substep (ALGEBRA).** In Lemma 4, let \(\zeta\) be the L² projection of the periodic perturbation \(\eta\) onto the closed convex set \(C=\{\xi:p+D\xi\in K\text{ a.e.}\}\), with K compact convex and \(p\in K\). The periodic heat semigroup \(P_t\) preserves C: \(p+D(P_t\zeta)=P_t(p+D\zeta)\in K\). Projection orthogonality therefore gives

\[
 \int_Q(\eta-\zeta)(P_t\zeta-\zeta)\,dx\leq0.
\]

Dividing by t and using the self-adjoint heat semigroup limit in H¹ gives

\[
 \int_Q D\zeta\cdot D(\eta-\zeta)\,dx\geq0,
\]

which is precisely the integral sign required above. This argument checks the **integrated sign** conditional on existence of the L² projection and preservation of C. The separate **contact/selection assertion** \(Dw=Dv\) or \(Dw\in\partial K\) must also be established; the heat-semigroup argument alone does not prove it.

## 4. A general convex-body sufficient criterion (CONDITIONAL)

Lemma 4 in the preprint is stated for *any* nonempty compact convex \(K\subset\mathbb R^2\), not only the unit disk. This immediately gives a useful abstract calibration theorem.

For an arbitrary such K define

\[
F_K(M):=\max_{z\in\partial K}
 \{\det(z,M^2)+z\cdot(M^1-z)\}.
\]

F_K is finite and convex, being a supremum of affine functions. Suppose an integrand f satisfies

\[
f(M)\geq F_K(M)\quad\text{for every M},\qquad
f(M)\geq\det M\quad\text{when }M^1\in K.
\]

At any base A with \(A^1\in K\) and \(f(A)=\det A\), the constrained projection for \(u^1\) selects \(Dw\in\partial K\) or \(Dw=Du^1\). In either case \(f(Du)\geq G_{Dw}(Du)\); integrating yields \(\int f(Du)\geq\det A=f(A)\).
At any base with \(f(A)=F_K(A)\), simply use \(f\geq F_K\) and convex Jensen.

**Concrete entire family (derived, conditional on the projection lemma):**

\[
L_K(M)=
\begin{cases}
 \max\{\det M,F_K(M)\},&M^1\in K,\\
 F_K(M),&M^1\notin K.
\end{cases}
\]

Every \(L_K\) is quasiconvex if Lemma 4 holds as stated. At the boundary \(M^1\in\partial K\), the identity \(G_{M^1}(M)=\det M\) implies \(F_K(M)\geq\det M\), so the two branches agree continuously. The original L is exactly \(L_{\overline B_1}\). For a disk of radius r>0, \(L_{\overline B_r}(A)=r^2L(A/r)\). Nonsymmetric compact convex bodies are also allowed.

This is an infinite family of positive examples and a reusable proof template; **it is not a classification of all rank-one-convex integrands**. No novelty or independent publication claim is made for this direct consequence of the cited lemma. Its proof is hand-level and conditional on the lemma, not a Lean theorem.

Additional safe closure: positive sums of these quasiconvex functions, convex integrands, affine functions, determinants, translated versions, and invertible linear changes of input variables remain quasiconvex under the usual domain-change assumptions. Such cones provide *exclusions* for a counterexample search, never counterexamples.

## 4A. Conformal Morrey for EVERY nonnegative isotropic homogeneous integrand

A substantially stronger consequence than the special convex-body constructions above comes
from **Guerra–Kristensen**, *Automatic quasiconvexity of homogeneous isotropic rank-one convex
integrands*, [arXiv:2112.10563](https://arxiv.org/abs/2112.10563), published in
*Archive for Rational Mechanics and Analysis* **245** (2022), 479–500.
Its Theorem 1.2 was *conditional* on the Burkholder quasiconvexity conjecture
when 1<p<2. Corollary 2 of [arXiv:2609.28311v2](https://arxiv.org/abs/2609.28311v2)
supplies precisely that missing hypothesis.

**Corollary (derived from those two papers).** Let p>1 and let
F:ℝ²ˣ²→[0,∞) be any globally rank-one-convex integrand satisfying
F(QAR)=F(A) for Q,R∈SO(2) and F(tA)=t^pF(A) for all t>0.
Then F is quasiconvex at **every** conformal/anticonformal matrix
A=tQ with t≥0 and Q∈O(2), including A=0. The class quantifier
is universal; no degree bound, number of terms, or mesh cutoff is assumed.
It is *not* a statement about arbitrary nonconformal base matrices.

For p≥2 this was already unconditional in Guerra–Kristensen
Theorem 1.3 (in fact polyconvex at conformal matrices). For 1<p<2,
their Theorem 1.2 applies once the 2026 paper's Burkholder
quasiconvexity claim is accepted.

### Exact normalization and an explicit global minorant

The 2022 Burkholder convention for 1<p<2 is
\[
 b_p(A)=\big[(2/p-1)\|A\|_{\rm op}^2+\det A\big]\|A\|_{\rm op}^{p-2},
 \qquad b_p(0)=0.
\]
The 2026 convention, writing Az=a_+z+a_-\bar z, satisfies the
**positive-scalar identity**
\[
 B_p^{2026}(A)
 =\big[(p-1)^{-1}|a_+|-|a_-|\big](|a_+|+|a_-|)^{p-1}
 =\frac{p}{2(p-1)}b_p(A).
\]
This identification matters: the p>2 conventions in the two papers
differ in orientation, but the older p≥2 theorem does not need Iwaniec.

Set D=diag(1,-1), c_+=(p/2)F(I) and c_-=(p/2)F(D).
For 1<p<2 define
\[
\boxed{H_{p,F}(A)=\max\{0,c_+b_p(A),c_-b_p(DA)\}.}
\]
Then (i) H is quasiconvex on **all** ℝ²ˣ², (ii) H≤F pointwise
on **all** ℝ²ˣ², and (iii) H(A)=F(A) whenever A is conformal or
anticonformal. Consequently, at arbitrary matrices A,
\[
 \int_Q F(A+D\varphi)\,dx\ \ge H_{p,F}(A),
\]
and at conformal A this lower bound equals F(A).

**Proof and hypotheses.** Both c_±≥0 by F≥0.
Guerra–Kristensen Theorem 4.2 states that every isotropic 2×2
rank-one-convex positively p-homogeneous integrand with F(I)>0,
normalized by c_+=F(I)/b_p(I), satisfies F≥c_+b_p globally;
indeed b_p(I)=2/p. If F(I)=0 the same inequality is trivial from
F≥0. Apply the same argument to the reflected integrand A↦F(DA):
reflection preserves rank-one convexity, p-homogeneity, and
SO(2)×SO(2)-isotropy, and yields F≥c_-b_p(D·).
The 2026 result makes b_p quasiconvex; output reflection
preserves quasiconvexity. A pointwise maximum of finitely many
quasiconvex integrands is quasiconvex, hence so is H.
For Q∈SO(2), \(\|Q\|_{\rm op}=1\), \(\det Q=1\) and
\(b_p(Q)=2/p\), whereas \(b_p(DQ)=2/p-2<0\).
Thus at A=tQ the first branch gives c_+b_p(A)=t^pF(I)=F(A);
the negative-orientation branch is analogous. At zero all terms
vanish by p-homogeneity. This proves all three properties.

For p≥2 an already-known **global polyconvex minorant**, again
touching at every conformal matrix, is
\[
 H_{p,F}(A)=F(I)(\det A)_+^{p/2}
           +F(D)(-\det A)_+^{p/2}\le F(A).
\]
This follows from Guerra–Kristensen's monotonicity argument
(Theorem 1.3 and its proof); p/2≥1 makes H convex as a function
of det, hence polyconvex. Its touching property uses isotropy
and p-homogeneity.

The two formulae give an **explicit global quasiconvex support for
every F in the indicated class**, even at nonconformal matrices,
but do not show F itself quasiconvex there. This is the strongest
direct all-F statement identified from the two papers. It has
a universal integrand quantifier but still imposes isotropy,
homogeneity, nonnegativity and a conformal base for equality.
No claim of novelty beyond combining the known theorems is made.

### Lean research gate

Formalize (1) the scalar identity between Burkholder conventions;
(2) the all-F extremality inequality of Guerra–Kristensen
Theorem 4.2; (3) quasiconvexity preservation under reflection,
nonnegative scaling and finite pointwise maxima; and (4)
pointwise minorant and exact touching on CO(2). Instantiate the
quasiconvex Burkholder premise only when the new 2026 theorem
has been independently formalized. A conditional Lean theorem
with the two source results as explicit hypotheses is a legitimate
near-term output; it is **not** an unconditional formal proof.
The unresolved unrestricted gate is the same as in the
[roadmap](README.md#roadmap): an all-rank-one-convex Jensen theorem or
a globally certified planar counterexample.

## 5. Why this does not repair Pedregal or close the Morrey roadmap

Pedregal tries to represent **every** planar gradient law as a laminate via a fixed-point construction; this repository proves the required general nonemptiness claim false. The Iwaniec proof instead assigns a *spatially varying calibrating gradient* to an integrand with a special support envelope. It does not require a finite splitting tree and does not assert that every gradient law is a laminate.

The missing universal step is a theorem asserting that **every** rank-one-convex f admits enough of these compatible moving supporting/calibrating fields, or a different all-gradient Jensen theorem. Rank-one convexity by itself gives only rank-one-line Jensen inequalities, not the displayed global pointwise support inequalities. In particular, universally postulating global determinant-affine supports would be too strong: rank-one-convex but nonpolyconvex planar examples are known and documented in the ledger.

Conversely, any proposed *negative* candidate still needs an actual 2 × 2 periodic/compactly supported gradient witness, a strict Jensen gap, and a global rank-one-convexity certificate, as specified in the [roadmap](README.md#roadmap). This paper supplies none of these.

## 6. Concrete Lean and research gates

| Gate | Target | Completion criterion |
| --- | --- | --- |
| I1 | Formalize matrix-to-complex coefficients, operator norm, G_z, F and L | Verify the factorization, support representation, continuity and convexity of F, including all equality cases at the norm boundary. |
| I2 | Formalize the constrained L² projection onto periodic scalar gradient bounds in compact convex K | Prove nonemptiness, L² closedness, projection existence, and the **pointwise contact alternative**, not merely existence of a minimizer. |
| I3 | Derive the integrated projection sign | Use heat-semigroup invariance (above) or an independently justified proof; keep H¹ limits and torus mean conditions explicit. |
| I4 | Formalize the determinant null-Lagrangian cross term and the exact defect decomposition | Produce a proof of the periodic quasiconvexity of L, then the conditional general L_K theorem with all quantifiers. |
| I5 | Reuse existing periodic Lipschitz/domain bridges; audit the cited Burkholder implication | State which part is proved in Lean and which external harmonic-analysis input is assumed. Do not label norm control as a Morrey proof. |
| M | Recover universal Morrey | **OPEN:** a universal calibration/lamination/Jensen theorem for arbitrary rank-one-convex f, or a globally certified negative planar witness. Nothing in I1–I5 supplies M automatically. |

Recommended order: do I1–I4 as a self-contained bounded formalization of the new paper **only if** the goal includes formalizing Iwaniec; do not divert the main unrestricted Morrey effort to infinitely many special K examples. The general convex-body formulation should be recorded once and treated as a reusable sufficient criterion.

## 7. Sources and qualification

1. Agazzi et al., [arXiv:2609.28311v2](https://arxiv.org/abs/2609.28311v2), Theorem 1, Corollary 2, Lemmas 3–4: source of the L and B_p quasiconvexity claims, support formula, and projection lemma.
2. Astala–Iwaniec–Prause–Saksman, *Burkholder integrals, Morrey's problem and quasiconformal mappings*, JAMS 2012: earlier link of Burkholder-type integrands to Morrey/Iwaniec.
3. [Pedregal audit](../Pedregal/REPORT.md), [research ledger](README.md#result-ledger), [completion roadmap](README.md#roadmap), [Cassese audit](../Cassese/README.md): the existing repository's status and known limitations.

**Validation status:** Source and the stated intermediate formulas were inspected; the projection contact alternative, the paper's full norm-corollary reduction, and this new general-K deduction were not independently compiled, checked in Lean, or submitted to a journal. No CI job or numerical search was run for this documentation-only commit.
