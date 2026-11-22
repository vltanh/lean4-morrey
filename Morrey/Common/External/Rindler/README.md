# Rindler and Dacorogna: rank-one convex functions and quasiconvexity

**Sources.** Cited by the paper: F. Rindler, *Calculus of variations*, Universitext, Springer 2018,
Lemma 5.6 and Propositions 5.1, 5.3; B. Dacorogna, *Direct methods in the calculus of variations*, 2nd
ed., Springer 2008 ([D08]; read), Propositions 5.11 and 5.13 (pp. 172–174). The first edition of
Rindler's book was not obtained; the second one (Graduate Texts in Mathematics 310, Springer, 2026;
[R2]) was read, and the numbers are matched by content: Lemma 5.6 is Lemma 5.9 of [R2] (pp. 114–115),
and Propositions 5.1, 5.3 are taken to be Lemma 5.2 (i) (the domain, p. 106) and Proposition 5.6
(quasiconvex ⇒ rank-one convex, pp. 111–113).

**Statements used by Cassese.**

- Lemma 2.1 (TeX lines 468–470), citing Rindler, Lemma 5.6: a rank-one convex integrand is locally
  Lipschitz. It is proved for every real-valued rank-one convex function: Propositions 2.4, 2.5 and the
  envelopes apply it to an infimum `G` before `G` is known to be an integrand (inventory E21).
  Rindler's definition of rank-one convexity also asks for local boundedness and Borel measurability.
- Lemma 2.2 (TeX lines 471–488), citing Rindler, Propositions 5.1, 5.3, and Dacorogna 2008,
  Propositions 5.11, 5.13, together for the whole lemma: a quasiconvex integrand is rank-one convex
  ([R2], Proposition 5.6); quasiconvexity at a matrix does not depend on the bounded open domain of the
  test maps ([D08], Proposition 5.11; [R2], Lemma 5.2 (i), for Lipschitz domains); and it can be tested
  with periodic Lipschitz maps on the torus `𝕋^m` ([D08], Proposition 5.13; in [R2] an exercise, Problem
  5.2). The domain must be nonempty, which neither the paper nor [D08] says.

**Lean.** [`Lemmas.lean`](Lemmas.lean): `External.Rindler.lemma5_6` (Lemma 2.1),
`External.Rindler.rankOneConvex_of_quasiconvex`, `External.Rindler.quasiconvexAtOn_iff` and
`External.Rindler.quasiconvexAtOn_iff_periodic` (Lemma 2.2), for lower semicontinuous, locally
bounded integrands (Cassese's integrands; the sources: Borel and locally bounded), with quasiconvexity
in the textbook form of the package `CalculusOfVariations`, each proved from the package's statement of
the same name ([lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations)).

**Proofs.** The sources'. Lemma 2.1: [R2], Lemma 5.9, with its bound (5.9): along rank-one lines (5.10),
then the singular value decomposition and the Cauchy–Schwarz inequality. "Quasiconvex ⇒ rank-one
convex": [R2], Proposition 5.6: laminates on a cube with faces orthogonal to the rank-one direction,
multiplied by cut-offs, with a diagonal choice of the two indices. Domain independence: [D08],
Proposition 5.11 (and [R2], Lemma 5.2 (i)): extend by zero, translate and scale. Periodic test maps:
[D08], Proposition 5.13: rescaled periodic maps and cut-offs near the boundary.

**Departures.** None in the arguments. Gap fills: the local boundedness of a rank-one convex function,
which in [R2] is part of the definition (p. 111 refers to Kirchheim–Kristensen for it), by convexity in
each entry; and the vanishing of the gradient of a Lipschitz map almost everywhere on its zero set,
needed for test maps that only vanish outside an arbitrary bounded open set. In [R2], (5.10) is printed
with absolute values, which are right when `f (B) ≤ f (A)`; otherwise `A` and `B` are exchanged. The
second part of Lemma 5.9 (functions of `p`-growth) is not formalized.

**Who uses them.** Cassese's toolkit (Propositions 2.1–2.5, [`Morrey/Cassese/Toolkit.lean`](../../../Cassese/Toolkit.lean)),
the lifting of witnesses to larger matrices ([`Morrey/Cassese/Lifting.lean`](../../../Cassese/Lifting.lean)),
and the bounds on `C^{qc}` by periodic test maps (Propositions 6.1, 7.2), and through these most
results of the paper; Lemma 2.1 also gives the continuity of `F` in Corollary 1.6.
