# Dacorogna: rank-one affine functions and quadratic forms

**Source.** B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer 2008
(read), Theorem 5.20 (p. 179; proof pp. 181–191), with Theorem 8.35 (pp. 409–411), and Theorem 5.25 (i)
(p. 191; proof pp. 192–194).

**Statements used by Cassese** (proof of Proposition 5.1 only, TeX lines 1409–1413).

- Theorem 5.20: for `f : ℝ^{N×n} → ℝ` the following are equivalent: (i) `f` is quasiaffine; (ii) `f` is
  rank-one affine; (ii′) `f ∈ C¹` and `f (ξ + a ⊗ b) = f (ξ) + ⟨∇f (ξ); a ⊗ b⟩`; (iii) `f` is polyaffine;
  (iii′) `f` is an affine combination of the minors. No continuity is assumed. The paper uses (ii) ⇒
  (iii′) ("`Q` is rank-one affine and hence … a linear combination of minors") and, without saying so,
  that the minors are quasiaffine.
- Theorem 5.25 (i): a quadratic form is rank-one convex if and only if it is quasiconvex. The paper uses
  "rank-one convex ⇒ quasiconvex".

**Lean.** [`Minors.lean`](Minors.lean): the proposition `External.Dacorogna.RankOneAffineMinors`
(Theorem 5.20, (ii) ⇒ (iii′), with no continuity, as in the book), proved by
`rankOneAffineMinors_holds`; `External.Dacorogna.minor3_quasiaffine` (Theorem 5.20, the `3 × 3` minors
are quasiaffine, on the unit cube, for Lipschitz test maps); and
`External.Dacorogna.quadraticForm_quasiconvex` (Theorem 5.25 (i), for a bilinear form `Q` and
`A ↦ Q (A, A)`). All three are proved from the package `CalculusOfVariations`
([lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations):
`Minors/RankOneAffine.lean`, `Minors/Quasiaffine.lean`, `QuadraticForm/Quasiconvex.lean`).

**Proofs.** The book's. Theorem 5.20, (ii) ⇒ (iii′) (pp. 181–191): induction on the number of rows with
(5.42)–(5.44), and Lemma 5.24. Minors are quasiaffine: the proof of Theorem 8.35 (ii) (expansion into
mixed minors, which are divergences, and density), for `3 × 3` minors and an affine map plus a test map.
Theorem 5.25 (i): Lemmas 5.27 and 5.28 (the linear term integrates to zero; Plancherel's formula and the
Legendre–Hadamard condition).

**Departures.** In the proof of (ii) ⇒ (iii′) the book has gaps and slips, repaired along its lines
(reason 1; details in the module docstring of the package's `Minors/RankOneAffine.lean`):

- the step (ii) ⇒ (ii′), `f ∈ C¹`, is not justified as written, and is not needed: the proof uses only
  that `f` is affine along rank-one lines;
- Lemma 5.24, Part 2: `g = Σ_β X_β` and the rank-one affinity of the forms `X_β` of (5.47) fail for
  `n > s + 1` (every term is counted `n − s` times); the columns are restricted to the `(s + 1)`-set
  first;
- the `t²` coefficients displayed on p. 190 omit terms, and with `b` supported on two columns they do not
  determine all the coefficients claimed to vanish; the test matrices have the two columns zero, and
  `b` is arbitrary;
- the rank-one affinity of `χ` and of the entries of `ψ`, and the case of a general set of rows, are
  written out.

For Theorem 5.25 (i), Plancherel's formula is applied to smooth maps, and the inequality passes to
Lipschitz maps by mollification; the book applies it to the Lipschitz map itself. For Theorem 8.35 (ii),
only `3 × 3` minors, which the paper needs.

**Who uses them.** Cassese's Proposition 5.1 (`Cassese.proposition5_1`,
[`Morrey/Cassese/TwoByThree/Folklore.lean`](../../../Cassese/TwoByThree/Folklore.lean)).
