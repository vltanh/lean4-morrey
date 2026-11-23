# Exact distinction at three atoms: polyconvex Jensen vs genuine gradient Young measures

Research date: 23 November 2026. **A source-backed synthesis of established
rigidity theory, not a new proof of Morrey or the p≥4 polyconvexity
question.** No Lean compilation or independent formalization is claimed.

## 1. Universal theorem for all integrands and exponents

**Theorem.** Let \(\mu\) be a *homogeneous* \(W^{1,\infty}\) gradient
Young measure on real \(2\times2\) matrices with at most **three**
atoms. Then \(\mu\) is a laminate in the Jensen sense:
for every finite-valued continuous rank-one-convex integrand F,
\[
       F\bigl(\langle\mu,\mathrm{id}\rangle\bigr)
       \le\langle\mu,F\rangle.
\]
No nonnegative, isotropic, homogeneous or \(p\ge4\) hypothesis
is needed. In particular, a genuine planar Morrey counterexample
cannot arise from a homogeneous gradient Young measure supported on
only one, two, or three matrices.

**Proof, separated by support geometry.**

* If \(\mu\) is Dirac, the assertion is trivial. For a two-atom
  measure \(\mu=w\delta_A+(1-w)\delta_B\), gradient compatibility
  gives the determinant null-Lagrangian identity
  \(w\det A+(1-w)\det B=\det(wA+(1-w)B)\).
  For 0<w<1 this is precisely \(w(1-w)\det(A-B)=0\).
  Thus A−B has rank ≤1 and rank-one Jensen applies.

* With three positive-weight distinct atoms, suppose a pair,
  say A₁,A₂, has rank-one difference. Merge them into
  \(B=(w_1A_1+w_2A_2)/(w_1+w_2)\), with weight
  \(v=w_1+w_2\). The determinant is affine on
  the rank-one segment, so this merge preserves
  **both** the matrix barycenter and determinant moment.
  The same two-atom identity then forces
  \(\det(B-A_3)=0\). Hence the law is realized
  as a **two-step finite-order laminate**, and
  rank-one Jensen holds.

* If all three differences have rank two, **Šverák's
  three-gradient rigidity theorem** says a \(W^{1,\infty}\)
  gradient Young measure supported on those three
  incompatible matrices must be Dirac.
  Equivalently, uniformly Lipschitz gradient sequences
  approaching such a three-well set converge in
  measure to a constant gradient. See Müller,
  *Variational models for microstructure and phase
  transitions* (1998), Theorem 2.5(ii), citing
  Šverák; and Bhattacharya–Firoozye–James–Kohn,
  *Restrictions on microstructure* (1994),
  Result 1.9. The necessary generated-sequence
  hypothesis is exactly the \(W^{1,\infty}\)
  gradient Young measure assumption.

All cases give Jensen for every rank-one-convex F.
This is a combination of published rigidity with
the elementary pair-merge calculation, **not**
a new classification theorem. QED.

## 2. Exact three-atom countercontrol to minors-only inference

Let \(w_i=1/3\) and take the three diagonal atoms
\[
 A_1=\operatorname{diag}(0,-3/2),\quad
 A_2=\operatorname{diag}(3/4,9/4),\quad
 A_3=\operatorname{diag}(9/4,-3/4).
\]
Exact rational arithmetic gives
\[
 \sum_iw_i A_i=\operatorname{diag}(1,0),\qquad
 \sum_iw_i\det A_i=0=\det\operatorname{diag}(1,0),
\]
while all \(\det(A_i-A_j)\ne0\), namely
\(45/16,\ 27/16,\ -9/2\).
The corresponding three-point probability
law is **minor-compatible** but is **NOT**
a nontrivial homogeneous \(W^{1,\infty}\)
gradient Young measure, by the theorem above.

[Exact standard-library checker](../../research/audit/iwaniec_three_atom_gradient_rigidity_control.py)
verifies the barycenters and three determinants.
The Young-measure non-realizability is a
**separate published mathematical theorem**;
no finite arithmetic check alone can prove it.

## 3. Research consequences for p≥4 and Morrey

There are **two distinct targets**.

**Stronger isotropic polyconvexity question
(Guerra–Kristensen, p≥4).**
The exact Dacorogna–Koshigoe 1993 criterion
still includes **three- and four-atom**
minors-compatible diagonal probability laws.
A strict three-atom energy violation would
refute this stronger *polyconvexity* claim.
Our theorem does NOT remove three atoms
from the polyconvexity test; such laws
need not be actual gradient laws.

**Original planar Morrey (quasiconvexity).**
Any putative counterexample detected via
a finite atomic actual gradient Young
measure must use **at least four atoms**,
or else have non-atomic support.
Even at four atoms, nontriviality and
absence of rank-one pairs do **not**
establish failure of the rank-one-convex
Jensen inequality: an abstract laminate
may be an infinite-order limit, despite
the lack of finite splitting pairs.

The four-gradient constructions in
Müller's 1998 lecture notes, §2.5,
building on Tartar/Bhattacharya et al.,
show that nontrivial compatible
microstructure **can** occur with four
pairwise rank-two separated wells.
This illustrates the sharp
three-to-four support threshold
for nontrivial microstructures,
not a disproof of Morrey.

**Stop rule:** Do not promote a minors-preserving
T3 law to a compatible gradient witness;
do not promote a four-atom incompatible
gradient law automatically to a nonlaminate;
and do not claim the stronger p≥4
polyconvexity conjecture has been reduced
to four atoms *only*. Its published test
still includes three.

## Primary sources

1. V. Šverák, *On Tartar's conjecture*,
   Ann. Inst. H. Poincaré Anal. Non Linéaire 10 (1993), 405–412;
   the three-gradient rigidity follows from
   the 1991–93 results summarized in the sources below.
   [Journal abstract](https://ems.press/journals/aihpc/articles/4076997).
2. S. Müller, *Variational models for microstructure and
   phase transitions* (1998),
   [Theorem 2.5(ii), §2.4](https://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.010/Microstructures__Mueller__4_.pdf).
3. K. Bhattacharya, N. Firoozye, R. James and R. Kohn,
   *Restrictions on microstructure*,
   Proc. R. Soc. Edinburgh A 124 (1994), 843–878,
   [DOI](https://doi.org/10.1017/S0308210500022381),
   Result 1.9 and four-gradient constructions.
4. B. Dacorogna and H. Koshigoe,
   *On the different notions of convexity for rotationally
   invariant functions* (1993),
   [Theorem 2.1](https://www.numdam.org/item/AFST_1993_6_2_2_163_0/):
   four-diagonal-atom **polyconvexity**, not
   a theorem about all gradient laws.
