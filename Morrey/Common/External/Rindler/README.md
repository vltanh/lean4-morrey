# Rindler and Dacorogna: rank-one convex functions and quasiconvexity

**Sources.** F. Rindler, *Calculus of variations*, Springer 2018, Lemma 5.6 and
Propositions 5.1, 5.3; B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed.,
Springer 2008, Theorem 2.31 and Propositions 5.11, 5.13 (both paywalled, not consulted). The
arguments used: S. Müller, *Variational models for microstructure and phase transitions*, lecture
notes, MPI MiS Leipzig, 1998 (read).

**Statements used by Cassese.**

- Lemma 2.1 (Rindler, Lemma 5.6): a rank-one convex integrand is locally Lipschitz. It is proved
  for every real-valued rank-one convex function, as in Rindler: Propositions 2.4, 2.5 and the
  envelopes apply it to an infimum `G` before `G` is known to be an integrand (inventory E21).
- Lemma 2.2 (Rindler, Propositions 5.1, 5.3, and Dacorogna 2008, Propositions 5.11, 5.13, cited
  together for the whole lemma): a quasiconvex integrand is rank-one convex; quasiconvexity at a
  matrix does not depend on the bounded open domain of the test maps (nonempty, which the paper
  does not say); and it can be tested with periodic Lipschitz maps on the torus `𝕋^m`. The books
  were not consulted; which cited result gives which assertion is not verified (see the module
  docstring).

**Lean.** [`Lemmas.lean`](Lemmas.lean): `External.Rindler.lemma5_6` (Lemma 2.1),
`External.Rindler.rankOneConvex_of_quasiconvex`, `External.Rindler.quasiconvexAtOn_iff` and
`External.Rindler.quasiconvexAtOn_iff_periodic` (Lemma 2.2), for lower semicontinuous, locally
bounded integrands, with quasiconvexity in the textbook form of the package
`CalculusOfVariations`, each proved from the package's statement of the same name.

**Proofs** (the books were not accessible; named arguments from Müller's notes). Lemma 2.1:
Definition 4.2, Remark 3 (a rank-one convex function is convex in each entry, and a separately
convex function is locally Lipschitz). "Quasiconvex ⇒ rank-one convex": Lemma 4.3 (laminates on a
cube with faces orthogonal to the rank-one direction, after an orthogonal change of variables).
Domain independence: Definition 4.2, Remark 2 (extend by zero, translate and scale the domain),
with the vanishing of the gradient of a Lipschitz map almost everywhere on its zero set in place of
Müller's assumption `|∂U| = 0` (a gap fill). Periodic test maps: Proposition 4.19 (a cut-off near
the boundary and a rescaled periodic map).

**Who uses them.** Cassese's toolkit (Propositions 2.1–2.5, [`Morrey/Cassese/Toolkit.lean`](../../../Cassese/Toolkit.lean)),
the lifting of witnesses to larger matrices ([`Morrey/Cassese/Lifting.lean`](../../../Cassese/Lifting.lean)),
and the bounds on `C^{qc}` by periodic test maps (Propositions 6.1, 7.2), and through these most
results of the paper; Lemma 2.1 also gives the continuity of `F` in Corollary 1.6.
