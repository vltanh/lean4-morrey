# Osękowski: sharp inequalities for differentially subordinate martingales

**Source.** A. Osękowski, *Sharp Martingale and Semimartingale Inequalities*, Monografie Matematyczne
72, Birkhäuser 2012 (read):

- Theorem 3.5 (p. 53; proof pp. 53–59), with Theorems 2.2 and 2.7 and §2.3 (pp. 11, 16–17, 21–22)
  and the functions of pp. 26–30;
- Theorem 8.6 (p. 413; proof pp. 414–415);
- Theorem 3.34 and Remark 3.8 (p. 137) with p. 138;
- Theorem 3.24 (pp. 120–121).

**Statements used by Cassese.**

- Theorem 2.3 (TeX lines 721–739), citing `[osekowski, Theorems 3.5, 8.6]`. (1), Burkholder's
  inequality: for martingales `X`, `Y` with values in a separable Hilbert space, started at `0` (the
  paper's convention, TeX lines 389–390), with `‖dX_n‖ ≤ ‖dY_n‖`, and `p ∈ (1, ∞)`,
  `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}`, `p* = max (p, p / (p − 1))`. (2), the square function
  inequality: `(p* − 1)⁻¹ ‖𝒮_n X‖_{L^p} ≤ ‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`.
- The sharpness of `p* − 1` for dyadic `±1`-transforms, proof of Corollary 6.3 (TeX lines 2624–2633).
  The paper names no source for it: "by choosing the martingale-transform pair suitably (see also
  [Cassese 2025])". Theorem 2.3 of that paper (*Martingales, laminates and minimal Korn inequalities*,
  arXiv:2512.02784; J. Math. Pures Appl. 213 (2026)) quotes Burkholder's inequality from D. L.
  Burkholder, *Boundary value problems and sharp inequalities for martingale transforms*, Ann. Probab.
  12 (1984), 647–702, "see [Osękowski 2012] for an exposition", and says that it is sharp, "that is to
  say, no smaller constant works among martingales defined on dyadic trees such that `‖dX_i‖ = ‖dY_i‖`"
  (its dyadic trees may split with any weights; the Rademacher martingales of Corollary 6.3 split with
  weights `1/2`). In the form needed, it is Theorem
  3.5 with Remark 3.8 and p. 138 of the book: the best constants of `±1`-transforms are the best ones
  already for dyadic martingales.
- Proposition 2.6 (TeX lines 768–787), citing `[osekowski, Theorem 3.24]`: a Banach space in which
  differentially subordinate martingales satisfy `‖X_n‖_{L^p} ≤ β_p ‖Y_n‖_{L^p}` is isomorphic to a
  Hilbert space `H`, with Banach–Mazur distance `d (X, H) ≲_p β_p`. Context only: no proof of the paper
  uses it. Theorem 3.24 concludes only that the space is isomorphic to a Hilbert space; the bound on
  the distance, and the paper's remark that it cannot be improved, are not in it.

**Lean.**

- [`Inequality.lean`](Inequality.lean), for real Hilbert spaces and Mathlib's
  `MeasureTheory.Martingale`: `External.Osekowski.theorem3_5` (the inequality of Theorem 3.5 (ii) in
  the book's form, with `‖g_0‖ ≤ ‖f_0‖`), `External.Osekowski.inequality` (Cassese's (1));
  `External.Osekowski.theorem8_6` ((8.28), for martingales started at `0`),
  `External.Osekowski.squareFunction` (Cassese's (2)).
- [`Sharpness.lean`](Sharpness.lean): `dyadicUMDConst_real`, `dyadicUMDConst_of_innerProductSpace`,
  `umdConst_of_innerProductSpace` (all the constants are `p* − 1`, for a nontrivial real Hilbert space),
  `exists_lt_lpNorm_transform` (the form Corollary 6.3 uses).
- [`HilbertCharacterization.lean`](HilbertCharacterization.lean): the proposition
  `External.Osekowski.HilbertCharacterization` (Proposition 2.6), with no proof, a hypothesis of no
  statement.

**Constants.** `p* − 1`, as in the book, in all of them.

**Proofs.** In the package `BanachProbability`
([lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability),
`Martingale/Osekowski/` and `Martingale/Burkholder/Inequality.lean`), by the book's arguments:

- Theorem 3.5 (ii), the inequality: the integration method (§2.3, pp. 53–54 and 58). Theorem 2.7
  (Burkholder's method) is applied to the simple functions `U₁` (3.6) and `U_∞` (3.12), Burkholder's
  function is an integral of one of them (`1 < p < 2`, `p > 2`), and Fubini's theorem is justified by
  (3.14), (3.15). `p = 2` is orthogonality.
- Theorem 3.5 (ii), "the constant is the best possible", and the dyadic case: the second approach
  (pp. 56–57) for `1 < p ≤ 2` and the duality of p. 59 for `p > 2`, run on the function `W⁰` of the
  proof of Theorem 3.34, that is on dyadic pairs only, instead of on `U⁰` and then Theorem 3.34
  (which is not formalized; `W⁰` has the properties of `U⁰` that the argument uses).
- Theorem 8.6, (8.28): Theorem 3.5 applied, in `ℓ² (H)`, to `(X_m, 0, …)` and `(dX_1, …, dX_m, 0, …)`
  (p. 414, with §2.1.3, p. 16).

**Differences and repairs.** In the statements:

- a fixed time `n` instead of `sup_n ‖·‖_{L^p}`, which is equivalent;
- (8.28) for martingales started at `0`;
- no separability of the Hilbert space;
- for the sharpness, transforms by *predictable* signs of Paley–Walsh martingales, as in Cassese's
  Definition 2.5, where the book has a deterministic sequence of signs, and one sign for each Haar
  function (Theorem 3.34, (3.214), p. 137; Remark 3.8, p. 138, for the Hilbert-space-valued case):
  on the sign cube a coefficient and a sign for each Haar function are a predictable `φ_k` and a
  predictable `σ_k`.

In the proofs: the second approach is run on `W⁰` (above), which the book uses for the
dyadic case. The slips of the book on the pages listed above are repaired along its lines, and each is
noted in the package:

- p. 11, the splice of two pairs with deterministic signs;
- pp. 27 and 29, signs;
- p. 30, a missing absolute value;
- p. 54, the order of the convex and the concave part of `F` and the constant of the integral
  formula;
- p. 56, `x / (2x + 1)` for `x / (2x − 1)`;
- p. 57, (3.66) for (3.65).

With the right order of its parts, the majorization `U_p ≥ V_p` (p. 54) also needs the sign of `F`
at an endpoint, which the book does not mention: it is (1.11) of Burkholder 1988, whose proof of the
same majorization (1.10) the package uses for this step. The two integral formulas for Burkholder's
function (pp. 54 and 58), stated without proof, are proved. Theorem 3.5 (i) (`p ≤ 1`) and the
sharpness clauses of Theorem 8.6 are not formalized: the paper does not use them.

**Who uses them.** Cassese's Theorem 2.3 is stated in the paper's terms in
[`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean) (`burkholderInequality_holds`,
`burkholderSquareFunction_holds`). They are used as follows:

- the inequality is used by Lemma 5.1 (1), (2) (and so in the proofs of Theorem 1.3 (a), (b) and of
  Corollaries 5.2–5.4) and by Proposition 7.1 (Section 7, and so Theorem 7.1, Theorem 1.5 and
  Corollary 1.6);
- the square function inequality, in `S_2^{d×d}`, is used by Proposition 6.5 (and so Theorem 1.4
  for general `p` and Corollary 6.1).

The sharpness is `Cassese.BurkholderSharpness`, `burkholderSharpness_holds`
([`Morrey/Cassese/Square/Sharpness.lean`](../../../Cassese/Square/Sharpness.lean)), used by the lower bound of Corollary 6.3
(`Cassese.corollary6_3_lower`).

None of these is a hypothesis of any statement. `HilbertCharacterization` is used by nothing.
