# Audit of the exponent interval (0,2]: novelty and genuine extension targets

Research date: 22 November 2026. **Status:** literature-backed priority correction
and one elementary general-dimension proof; no Lean compilation or independent
review of the proposed p∈(1,2) and p=2 class-wide hand proofs.
The unrestricted planar Morrey problem remains open.

## Scope and honest novelty verdict

| Exponents | Exact result/status | Novelty verdict |
| --- | --- | --- |
| 0<p<1 | **Unconditionally F≡0** for every finite-valued globally rank-one-convex positively p-homogeneous F, in **any finite matrix dimension**, even without isotropy or nonnegativity (proof below) | Elementary, not a meaningful Morrey advance |
| p=1 | In 2×2, every isotropic positively 1-homogeneous rank-one-convex F is globally **convex**, including real-valued/signed F | **Already Dacorogna (1989)**, explicitly recorded in Jan Kristensen's teaching slides; not novel |
| 1<p<2 | **Candidate:** every globally nonnegative isotropic p-homogeneous rank-one-convex F is quasiconvex at **all** matrices, with a representation as a supremum of nonnegative reflected Burkholder combinations | Potentially useful all-matrix extension of Guerra–Kristensen (2022) Theorem 1.2, which says only *at conformal matrices*; depends on the 2026 Iwaniec/Burkholder proof and requires independent audit/Lean |
| p=2 | **Candidate:** every real-valued (no F≥0 assumption) isotropic 2-homogeneous rank-one-convex F is globally **polyconvex** (see signed p=2 note) | Stronger conclusion than 2022 conformal-base theorem and removes nonnegativity; hand proof short, priority and external review unverified |
| p>2 | All-matrix isotropic p-homogeneous RC→QC remains open in this research; the proposed hybrid Burkholder+polyconvex **support-completeness** route was refuted exactly | No claim of an all-p solution |

**Sources and comparison:**
- A. Guerra and J. Kristensen, *Automatic quasiconvexity of homogeneous isotropic rank-one convex integrands*, [arXiv:2112.10563](https://arxiv.org/pdf/2112.10563), published 2022: Theorem 1.2 covers conformal bases for 1<p<2 if Burkholder is QC; Theorem 4.2 proves the relevant extremality. It does **not** state the all-matrix result in its main theorem.
- Agazzi et al., [arXiv:2609.28311v2](https://arxiv.org/pdf/2609.28311v2), 8 October 2026: Corollary 2 **claims** global quasiconvexity of all Burkholder Bₚ, including 1<p<2. This is the substantive external input.
- Jan Kristensen, *From Ornstein's non-inequalities to rank-one convexity* (lecture notes), [PDF](https://users.sussex.ac.uk/~gk207/APDE_slides_kristensen.pdf): a dedicated slide explicitly attributes to **Dacorogna (1989)** that isotropic 1-homogeneous rank-one convex F on 2×2 is convex. Do not claim this endpoint as new.
- [Our all-matrix hand proof](IWANIEC_MORREY_UNIVERSAL.md) and [signed p=2 hand proof](IWANIEC_MORREY_P2_SIGNED.md). Neither has an independent Lean check, mathematical referee report, nor novelty clearance.

## Elementary general-dimension theorem for 0<p<1

**Theorem.** Let E be a finite-dimensional space of real matrices of any shape.
If F:E→ℝ is finite-valued, globally rank-one convex, and
\(F(tA)=t^pF(A)\) for every t>0 and some 0<p<1, then F≡0.

**Proof.** Finite rank-one convex functions on the full matrix space
are locally bounded and continuous (separate convexity along all
coordinate rank-one directions suffices). By compactness of
the unit sphere, there exists M such that
\[
   |F(A)|\le M\|A\|^p
\]
for every A, where F(0)=0 by homogeneity and finiteness.

For each matrix A and rank-one R, the entire real-line
function \(g(s)=F(A+sR)\) is convex and satisfies
\[
 |g(s)|\le M(\|A\|+|s|\|R\|)^p=o(|s|)
 \qquad(s\to\pm\infty).
\]
An everywhere-finite convex real function with
sublinear growth in *both directions* is constant:
a nonzero secant slope would force linear growth
at one infinity. Thus F is constant on every
rank-one affine line. Coordinate matrices
\(E_{ij}\) have rank one and span the entire
matrix space; changing coordinates one at a
time shows F is globally constant. Positive
homogeneity forces that constant to be zero.
QED.

This theorem has no symmetry or sign assumptions.
It applies to arbitrarily many rows and columns;
the "0<p<1" part of the interval offers no
nontrivial Morrey content and should not be
used to inflate the scope or novelty of the result.

## Strong structural target for 1<p<2

For each nonzero A, put \(a=\|A\|_{\rm op}\),
\(r=\det A/a^2\in[-1,1]\).
Let \(k=2/p-1>0\) and
\[
  b_p^\pm(A)=a^p(k\pm r),\qquad b_p^\pm(0)=0.
\]
The previously proposed result actually asserts
more than quasiconvexity: **a global supporting-generator
representation**
\[
 F(A)=\sup\big\{\alpha b_p^+(A)+\beta b_p^-(A):
       \alpha,\beta\ge0,\quad
       \alpha b_p^++\beta b_p^-\le F\ \text{everywhere}\big\}.
\]
At every nonzero A, a subgradient \(m\) of the
nonnegative convex signed-singular profile
\(h(r)=F(\operatorname{diag}(1,r))\) provides
\(c=h(r)-rm\ge k|m|\) and
\(\alpha=(c/k+m)/2,\ \beta=(c/k-m)/2\).
The corresponding global minorant touches F
at A. Endpoints have the one-sided supporting
barriers recorded in the universal note; at
A=0 take the zero support. Conversely,
nonnegative combinations of the two bₚ
orientations are rank-one convex, and
pointwise suprema preserve rank-one convexity.
If both bₚ are globally quasiconvex (2026 claim),
the representation yields F quasiconvex *everywhere*.

**Priority assessment:** the supporting-line algebra is short
and uses ideas already present in 2022; the *all-integrand,
all-base* conclusion and representation are mathematically
stronger than the conformal theorem but should be presented
as **candidate corollaries** pending a careful check of
the generator signs, all endpoint cases, and prior
literature. Never present the elementary (0,1] endpoints
as the novelty.

## What would genuinely improve the result?

1. **Remove nonnegativity** for 1<p<2, or exhibit
   a precise signed counterexample to the generator
   representation. A real-valued signed p-homogeneous
   RC function need not be nonnegative (Burkholder
   itself changes sign), and the current supporting
   lemma uses h≥0 in essential cases.
2. **Finish p>2 by a new principle.** The old
   two-Burkholder/positive-polyconvex hybrid cone
   provably fails on an open set of globally RC
   profiles; adding more functions of the same
   type or searching more p-cases cannot repair it.
   Prove a stronger all-gradient inequality or
   discover a genuinely larger QC calibrator
   mechanism.
3. **Relax isotropy or positive homogeneity** only
   with a global representation theorem retaining
   touching at every matrix; GL transforms of
   special examples alone cannot supply this.
4. **Formalize and externally review** the 1<p<2
   all-matrix generator representation and p=2
   signed polyconvexity theorem. A short proof
   still requires correct hypotheses and a
   novelty audit.

**Assessment:** The proof length is
"straightforward once the Burkholder theorem
is granted"; the conditional class-wide
all-matrix conclusion is potentially
**substantial**. Neither statement is the
unrestricted Morrey problem, and no
general p>2 result is claimed here.
