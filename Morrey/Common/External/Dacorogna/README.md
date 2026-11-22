# Dacorogna: rank-one affine functions and quadratic forms

**Source.** B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer 2008,
Theorems 5.20 and 5.25 (i).

**Statements used by Cassese** (proof of Proposition 5.1 only).

- Theorem 5.20: a continuous rank-one affine `f : ℝ^{d×m} → ℝ` is an affine combination of the
  minors of its argument.
- Theorem 5.25 (i): a rank-one convex quadratic form is quasiconvex.

**Lean.** [`Minors.lean`](Minors.lean): the proposition `External.Dacorogna.RankOneAffineMinors`
(Theorem 5.20), proved by `rankOneAffineMinors_holds`, and
`External.Dacorogna.quadraticForm_quasiconvex` (Theorem 5.25 (i)). [`Plancherel.lean`](Plancherel.lean):
the Fourier inequality `∫ Q (∇φ) ≥ 0` behind Theorem 5.25 (i).

**Proofs.** Theorem 5.20 (the direction (iii) ⇒ (iv)): by induction on the number of rows, in the
classical spirit of Ball–Currie–Olver (Dacorogna's own proof could not be consulted offline); a
rank-one affine function is affine in each row, and the minors are rank-one affine by the matrix
determinant lemma; continuity is not needed. Theorem 5.25 (i): Dacorogna's Fourier–Plancherel
argument, `∫ Q (∇φ) = 4π² ∫ [Q (Re φ̂ ⊗ ξ) + Q (Im φ̂ ⊗ ξ)] dξ ≥ 0` by the Legendre–Hadamard
condition. Departure from the source (Mathlib has Plancherel's theorem for Schwartz functions, not
the rule `𝓕 (∂_k φ) = 2πi ξ_k 𝓕 φ` for Sobolev maps): the inequality is proved for smooth
compactly supported maps and extended to Lipschitz ones by mollification.

**Who uses them.** Cassese's Proposition 5.1 (`Cassese.proposition5_1`,
[`Morrey/Cassese/TwoByThree/Folklore.lean`](../../../Cassese/TwoByThree/Folklore.lean)). The other
direction of Theorem 5.20, that minors are quasiaffine, which the paper also uses there, is proved
in [`Morrey/Cassese/TwoByThree/Folklore/NullLagrangian.lean`](../../../Cassese/TwoByThree/Folklore/NullLagrangian.lean).
