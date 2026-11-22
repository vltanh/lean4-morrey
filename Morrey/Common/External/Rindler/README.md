# Rindler and Dacorogna: rank-one convex functions and quasiconvexity

**Sources.** Cited by the paper: F. Rindler, *Calculus of variations*, Universitext, Springer 2018,
Lemma 5.6 and Propositions 5.1, 5.3; B. Dacorogna, *Direct methods in the calculus of variations*, 2nd
ed., Springer 2008 ([D08]; read), Propositions 5.11 and 5.13 (pp. 172–174). The first edition of
Rindler's book was not obtained; the second one (Graduate Texts in Mathematics 310, Springer, 2026;
[R2]) was read, and the results are matched by content: Lemma 5.6, as the paper quotes it, is Lemma 5.9
of [R2] (pp. 114–115); the assertions of Lemma 2.2 are its Proposition 5.6 (quasiconvex ⇒ rank-one
convex, pp. 111–113) and Lemma 5.2 (i) (the domain, p. 106). [R2]'s own Proposition 5.1 is "all convex
functions are quasiconvex" (p. 105), so whether the first edition's numbers 5.1 and 5.3 are these results
could not be checked. (Theorem 5.16 and Proposition 5.18, cited in the introduction, TeX line 80, are
context and not formalized.)

**Statements used by Cassese.**

- Lemma 2.1 (TeX lines 468–470), citing Rindler, Lemma 5.6: a rank-one convex integrand is locally
  Lipschitz. It is proved for every real-valued rank-one convex function: in Proposition 2.4 the paper
  uses the real-valued rank-one convex infimum `G` as a minorant without showing that it is an integrand
  (inventory E21), and the formal proofs of Propositions 2.4, 2.5 and of the envelope steps get its
  continuity from this lemma. Rindler's definition of rank-one convexity also asks for local boundedness
  and Borel measurability.
- Lemma 2.2 (TeX lines 471–487), citing Rindler, Propositions 5.1, 5.3, and Dacorogna 2008,
  Propositions 5.11, 5.13, together for the whole lemma: a quasiconvex integrand is rank-one convex
  ([R2], Proposition 5.6); quasiconvexity at a matrix does not depend on the bounded open domain of the
  test maps ([D08], Proposition 5.11; [R2], Lemma 5.2 (i), for Lipschitz domains); and it can be tested
  with periodic Lipschitz maps on the torus `𝕋^m` ([D08], Proposition 5.13; in [R2] an exercise, Problem
  5.2). The last two are stated at one matrix, as in the paper; the sources state them for functions
  quasiconvex at every matrix, and their proofs fix the matrix. The domain must be nonempty, which neither
  the paper nor [D08] says.

**Lean.** [`Lemmas.lean`](Lemmas.lean): `External.Rindler.lemma5_6` (Lemma 2.1, for every real-valued
rank-one convex function), from the package's `RankOneConvex.locallyLipschitz`; and
`External.Rindler.rankOneConvex_of_quasiconvex`, `External.Rindler.quasiconvexAtOn_iff`,
`External.Rindler.quasiconvexAtOn_iff_periodic` (Lemma 2.2), for Borel measurable, locally bounded
functions, as in the sources (Cassese's integrands are lower semicontinuous and locally bounded), from
the package's statements of the same names. Quasiconvexity is in the textbook form of the package `CalculusOfVariations`
([lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations)).

**Proofs.** The sources'. Lemma 2.1: [R2], Lemma 5.9, with its bound (5.9): along rank-one lines (5.10),
then the singular value decomposition and the Cauchy–Schwarz inequality. "Quasiconvex ⇒ rank-one
convex": [R2], Proposition 5.6: laminates on a cube with faces orthogonal to the rank-one direction,
multiplied by cut-offs, with a diagonal choice of the two indices. Domain independence: [D08],
Proposition 5.11 (and [R2], Lemma 5.2 (i)): extend by zero, translate and scale. Periodic test maps:
[D08], Proposition 5.13: rescaled periodic maps and cut-offs near the boundary. A slip of [R2], Lemma
5.2 (i): the proof tests the second domain only with scaled copies of maps on the first; a copy of the
second domain is to be put into the first, as in [D08].

**Departures.** None in the arguments. Gap fills: the local boundedness of a rank-one convex function,
which in [R2] is part of the definition (p. 111 refers to Kirchheim–Kristensen for it), by convexity in
each entry; and the vanishing of the gradient of a Lipschitz map almost everywhere on its zero set,
needed for test maps that only vanish outside an arbitrary bounded open set. In [R2], (5.10) is printed
with absolute values, which are right when `f (B) ≤ f (A)`; otherwise `A` and `B` are exchanged. The
second part of Lemma 5.9 (functions of `p`-growth) is not formalized.

**Who uses them.** Cassese's toolkit (Propositions 2.1–2.5, [`Morrey/Cassese/Toolkit.lean`](../../../Cassese/Toolkit.lean)),
the lifting of witnesses to larger matrices ([`Morrey/Cassese/Lifting.lean`](../../../Cassese/Lifting.lean)),
and the bounds on `C^{qc}` by periodic test maps (Propositions 6.1, 6.6, 7.2), and through these most
results of the paper; Lemma 2.1 also gives the continuity of `F` in Corollary 1.6.
