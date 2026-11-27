# PRIORITY CORRECTION: the four-diagonal-atom theorem is from 1993

Date of audit: 23 November 2026. Primary source:
Bernard Dacorogna and Hideyuki Koshigoe,
*On the different notions of convexity for rotationally invariant functions*,
Annales de la Faculté des Sciences de Toulouse, **2** (1993), 163–184,
[Numdam article](https://www.numdam.org/item/AFST_1993_6_2_2_163_0/),
[original PDF](https://www.numdam.org/article/AFST_1993_6_2_2_163_0.pdf).

**This note corrects priority and describes the remaining work; it is
not a new mathematical proof of Morrey or the p>2 isotropic question.**

## What the 1993 theorem already proves

The source explicitly assumes
\(F(UAV)=F(A)\) for \(U,V\in SO(2)\) (assumption (H), p. 164).
Theorem **2.1**, pp. 169–170, proves the following four statements
are equivalent for a finite real-valued isotropic function:

1. F is globally polyconvex on all real 2×2 matrices.
2. Its signed-diagonal restriction is polyconvex.
3. The Jensen inequality holds for **every minors-preserving
probability law on at most four diagonal matrices**.
4. Every diagonal base admits a global *diagonal* poly-affine
minorant: \(F(D)\ge F(E)+\alpha(D_{11}-E_{11})
+\beta(D_{22}-E_{22})+\gamma(\det D-\det E)\).

The paper **explicitly writes the four-atom bound** and the
supporting-plane statement, not merely an abstract dimensional
reduction. In particular, our claim that four atoms followed
from Wiedemann–Peter (2026) and an elementary LP argument
is mathematically sound but **not a new finite reduction**.
Wiedemann–Peter's 2026 paper itself cites the earlier 2D
isotropic diagonal theorem (its discussion before Theorem 1.4).

Our explicit rational four-moment sparsifier remains useful
engineering for certificates, but should not be advertised
as a novel theorem. The fact that any rank-one-connected
pair in a minors-preserving law can be merged without
increasing rank-one-convex energy is an elementary further
specialization; the reduction to pairwise rank-two-separated
three-/four-atom laws should be regarded as elementary
reformulation, **not** a new solution of the global problem.

## Pointwise support: what is and is not new

The one-multiplier criterion in
[IWANIEC_MORREY_GENERAL_SUPPORT_CRITERION.md](IWANIEC_MORREY_GENERAL_SUPPORT_CRITERION.md)
is a *concrete algebraic specialization* of item 4 above
to a differentiable isotropic p-homogeneous profile
\(F(A)=a^p h(\det A/a^2)\) at
\(E_t=\operatorname{diag}(1,t)\).
Differentiability pins the first two linear coefficients
of a supporting plane, leaving its determinant multiplier
\(c\). The resulting scalar inequality and explicit
interval are algebraically correct under the stated
hypotheses, but **the global supporting-plane concept
and its equivalence to polyconvexity are already in 1993**.

The two-test-point interval infeasibility observation
uses elementary one-dimensional Helly/interval logic.
It is a useful discovery/checking format, not by itself
a fundamentally new reduction of an infinite-dimensional
calculus-of-variations conjecture.

## Genuinely open mathematical step after this audit

Let p>2 and F be any globally finite, nonnegative,
SO(2)×SO(2)-isotropic, positively p-homogeneous
rank-one-convex integrand on real 2×2 matrices.

* Prove the Dacorogna–Koshigoe four-atom Jensen inequality
  for **all** minors-preserving signed-diagonal laws,
  uniformly in F and p; or give a certified counterexample
  to that **polyconvexity** claim.
* The smaller pairwise-unconnected three- and four-atom
  classes are simply a reformulation of that universal
  quantifier. They still involve continuous unbounded
  parameters. There is **no finite enumeration** of them.
* A four-atom failure is not by itself a violation of
  quasiconvexity/Morrey; for Morrey one additionally needs
  an actual compatible planar gradient field and
  global rank-one convexity.

The 2026 Iwaniec–Burkholder result addresses
quasiconvexity of special integrands; it does
**not** supply the missing 1993 four-atom inequality
for every nonnegative isotropic p>2 integrand.

**Evidence:** Checked the original printed PDF, including
assumption (H) on p.164 and Theorem 2.1 on pp.169–170,
and compared to Wiedemann–Peter (2026), Theorem 1.4.
No Lean build or independent review of any new hand
proof is claimed by this priority correction.
