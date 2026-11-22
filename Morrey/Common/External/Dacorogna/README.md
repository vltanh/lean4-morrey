# Dacorogna: rank-one affine functions and quadratic forms

**Source.** B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer 2008,
Theorems 5.20 and 5.25 (i) (paywalled, not consulted).

**Statements used by Cassese** (proof of Proposition 5.1 only).

- Theorem 5.20: a continuous rank-one affine `f : ℝ^{d×m} → ℝ` is an affine combination of the
  minors of its argument.
- Theorem 5.25 (i): a rank-one convex quadratic form is quasiconvex.

**Lean.** [`Minors.lean`](Minors.lean): the proposition `External.Dacorogna.RankOneAffineMinors`
(Theorem 5.20, (iii) ⇒ (iv)), proved by `rankOneAffineMinors_holds`;
`External.Dacorogna.minor3_quasiaffine` (Theorem 5.20, the `3 × 3` minors are quasiaffine); and
`External.Dacorogna.quadraticForm_quasiconvex` (Theorem 5.25 (i)). All three are proved from the
package `CalculusOfVariations` (`Minors/RankOneAffine.lean`, `Minors/Quasiaffine.lean`,
`QuadraticForm/Quasiconvex.lean`).

**Proofs** (the book was not accessible; named arguments). Theorem 5.20, (iii) ⇒ (iv): the proof
of S. Conti, G. Dolzmann, B. Kirchheim and S. Müller, J. Eur. Math. Soc. 8 (2006), Appendix,
Theorem 6.1 (open): vanishing of the derivatives along rank-one directions, (6.1)–(6.2), their
Proposition 6.2, Taylor's formula, and the uniqueness of alternating forms; their distributional
derivatives are taken as classical derivatives of mollifications. The package also proves the
statement without continuity, by an elementary argument of its own (not used here). Minors are quasiaffine: C. B. Morrey, Pacific J.
Math. 2 (1952), Lemma 5.1 (divergence identities for smooth maps, then mollification). Theorem
5.25 (i): Morrey 1952, Theorem 5.2: the linear term integrates to zero, and the quadratic term is
nonnegative under the Legendre–Hadamard condition, for smooth maps (here by Plancherel's formula
for Schwartz functions) and then for Lipschitz maps (here by mollification).

**Who uses them.** Cassese's Proposition 5.1 (`Cassese.proposition5_1`,
[`Morrey/Cassese/TwoByThree/Folklore.lean`](../../../Cassese/TwoByThree/Folklore.lean)). The other
direction of Theorem 5.20, that minors are quasiaffine, which the paper also uses there, is
`minor3_quasiaffine`.
