# HNVW: Hytönen, van Neerven, Veraar, Weis, *Analysis in Banach Spaces*

**Sources.** T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I:
Martingales and Littlewood–Paley Theory*, Springer 2016 (HNVW I; read): Proposition 4.2.3 (p. 282),
Theorem 4.2.5 (p. 282), Theorem 4.2.7 (p. 283), Theorem 4.5.6 (p. 332), Corollary 5.7.6 (pp. 462–463),
with what their proofs use; *Volume II: Probabilistic Methods and Operator Theory*, Springer 2017 (HNVW
II; read): Theorem 6.2.4 (pp. 21–22), with Theorem 6.2.2 and Lemma 6.2.3.

**Statements used by Cassese** (`p* = max (p, p / (p − 1))`, `UMD_p` as in his Definition 2.5), and the
book's.

- Proposition 2.7 (1) (TeX lines 829–831), Theorem 4.2.7: `UMD_{p₀}` for one `p₀ ∈ (1, ∞)` gives
  `UMD_p` for all `p ∈ (1, ∞)`, and `UMD₂ (X) / 200 ≤ UMD_p (X) ≤ 100 p* UMD₂ (X)`. The book:
  `UMD_p (X) ≤ 100 (p/q + p'/q') UMD_q (X)` for all `p, q`, in particular
  `UMD₂ (X) / 200 ≤ UMD_p (X) ≤ 50 (p + p') UMD₂ (X)`, and `50 (p + p') ≤ 100 p*`.
- Proposition 2.7 (4) (TeX lines 837–841), Theorem 4.2.5: `UMD_p^{dyad} (X) = UMD_p (X)`.
- Proposition 2.7 (6) (TeX lines 857–869), Theorem 4.5.6: `X` is `UMD_p` if and only if some `U` with
  `U (0, 0) = 0`, `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p` is zig-zag concave (`|ε| ≤ 1`); then
  `β ≥ UMD_p (X)`. The book asks the concavity for the signs `|ε| = 1` only, not `U (0, 0) = 0`, and
  `β ≥ 1`, and adds that the infimum of these `β` is `UMD_p (X)`.
- Proposition 2.8 (TeX lines 875–896), Proposition 4.2.3 with Cox–Veraar: decoupling. The book's
  proposition is the randomised UMD property, of which Cassese's statement is the case of Paley–Walsh
  martingales; it is proved in [`../CoxVeraar`](../CoxVeraar) (`External.CoxVeraar.decoupling`) and not
  repeated here.
- Proposition 6.4 (TeX lines 2314–2321), Theorem 6.2.4 of HNVW II: for `p, q ∈ (1, ∞)` and every
  Banach space, `‖Σ ε_i x_i‖_{L^p} ≤ k_{p,q} ‖Σ ε_i x_i‖_{L^q}`. The book adds, for real signs and
  `1 < p < q < ∞`, `k_{q,p} ≤ √((q − 1) / (p − 1))` (and the exponents `≤ 1`). The paper leaves the bound
  out, but Remark 6.3 (TeX lines 2425–2438) and the case `q = ∞` of Proposition 6.5 (TeX lines 2477–2479)
  use it (inventory E27).
- The proof of Proposition 7.2 (TeX lines 2832–2835), Corollary 5.7.6, "the standard transference
  identity for homogeneous multipliers": `‖𝓑^k‖_{L^p (ℝ²)} ≤ ‖𝓑^k‖_{L^p_0 (𝕋²)}`, `k ≥ 1`, `𝓑` the
  Beurling–Ahlfors transform. The book: for `m` homogeneous of degree `0` and continuous off `0`, with
  `m (0)` its mean over the unit sphere, the norms of `T_m` on `L^p (ℝ^d)`, `L^p_0 (𝕋^d)` and `L^p (𝕋^d)`
  are equal; only the inequality from the torus (`L^p_0`) to the plane is used, in which `m (0)` plays no
  role, and it is arbitrary in Lean.

Cited for context only, and not formalized: Volume I, Chapters 1 and 2 (TeX line 411, Bochner spaces)
and Section 3.1.b (TeX line 663, Rademacher variables); Volume III, Corollary 13.2.10 (a remark, TeX line
1205).

**Lean.** Real Banach spaces, `BanachProbability.umdConst` (predictable signs, any filtration of a
probability space, martingales started at `0`), Paley–Walsh martingales on the sign cube `{±1}^N`:

- [`Extrapolation.lean`](Extrapolation.lean): `External.HNVW.theorem4_2_7_general` (the book's
  inequality) and `theorem4_2_7` (Cassese's form);
- [`DyadicUMD.lean`](DyadicUMD.lean): `theorem4_2_5` (`dyadicUMDConst X p = umdConst X p`);
- [`ZigZag.lean`](ZigZag.lean): `theorem4_5_6` (Cassese's form: the equivalence, and every admissible
  `β` bounds `UMD_p (X)`) and `theorem4_5_6_isLeast` (the book's final clause, with its functions, for
  `X ≠ 0`; that the infimum is attained is in the book's proof);
- [`KahaneKhintchine.lean`](KahaneKhintchine.lean): `theorem6_2_4_hypercontractive`
  (`√((q − 1) / (p − 1))`, `1 < p ≤ q`, any seminorm), `theorem6_2_4_seminorm` and `theorem6_2_4`
  (normed spaces), with `κ_{p,q} = max (1, √((p − 1) / (q − 1)))`;
- [`Transference.lean`](Transference.lean): `transference` (`‖T_m‖_{L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²)}`,
  `1 < p < ∞`, for `m : ℂ → ℂ` continuous off `0` and homogeneous of degree `0`) and
  `transference_beurlingPow`, `m (ξ) = (ξ̄ / ξ)^k`.

**Constants.** The book's: `100 (p/q + p'/q')`, `200`; the equality of the constants; `β`;
`√((q − 1) / (p − 1))`; `1`. (For Theorem 4.2.7 the proof gives `80 (p/q + p'/q')`, as in the book.)

**Proofs.** The book's, in the packages. From `BanachProbability`
([lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability)):

- Theorem 4.2.7, from `umdConst_le_mul_umdConst`, `umdConst_lt_top_of_lt_top`, `umdConst_two_le_mul`,
  `umdConst_le_mul_umdConst_two`: the good-λ inequality for one transform of Paley–Walsh martingales
  (Lemmas 3.5.13, 3.5.14), its integration (Lemma 3.5.15, (3.59)), Doob's inequality and the adjoint
  (Lemma 3.5.3) give (3.49) of Theorem 3.5.4 (pp. 229–234); then Lemma 4.2.8 and Theorem 4.2.5.
- Theorem 4.2.5, from `dyadicUMDConst_eq_umdConst`: by the book's *alternative* proof (p. 334, "The
  result provides an alternative proof of Theorem 4.2.5"; due to Burkholder 1986, p. 355), Theorem
  4.5.6, (2)⇒(3)⇒(1). The proof printed at Theorem 4.2.5 (pp. 284–285), by approximation with
  Paley–Walsh martingales (Theorem 3.6.1, after Maurey), is not the one followed.
- Theorem 4.5.6, from `umdConst_lt_top_iff_exists_isZigZagConcave`, `umdConst_le_of_isZigZagConcave`,
  `isLeast_umdConst_isSignZigZagConcave`: pp. 330–337, with Lemmas 4.5.2, 4.5.4, 4.5.5 and 3.6.17.
- HNVW II, Theorem 6.2.4, from `kahaneKhintchine_hypercontractive`, `kahaneKhintchine`: the
  hypercontractivity of the discrete heat semigroup (Theorem 6.2.2), tensorised from Bonami's two-point
  inequality (Lemma 6.2.3) with values in `L^q`.

From `HarmonicAnalysis` ([lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis)):
Corollary 5.7.6, from `multiplierNorm_le_torusMultiplierNorm`, `beurlingPowNorm_le_torusBeurlingPowNorm`:
Proposition 5.7.4 (pp. 460–462) for a homogeneous symbol, with the density of Proposition 2.4.23 and
Lemma 5.7.5 (Poisson summation). Neither package's source contains a `sorry`.

**Departures.** None in the arguments. The statements are for Cassese's `UMD` constants: predictable
signs, probability spaces, martingales started at `0`. The book's are for deterministic signs (its
Theorem 4.2.25 shows that predictable signs have the same constants) and σ-finite spaces, over real or
complex scalars; the arguments are the same, except that the reductions (4.32), (4.33) for `f_0 ≠ 0` are
not needed. Cassese's form of Theorem 4.2.7 is weaker than the book's, and his form of Theorem 4.5.6
neither implies nor is implied by the book's: his functions are concave for all `|ε| ≤ 1`, for which the
multipliers of the proof of (2)⇒(3) are constants in `[−1, 1]` instead of signs. Slips of the book are
repaired along its lines, and noted in the docstrings of the packages: the order of two steps in the
proof of Theorem 4.5.6 (Lemma 4.5.2 is applied before the function is known to be finite), the first
index in Lemma 3.5.14, a constant in Lemma 6.2.3 and the case `q = 1` in Theorem 6.2.4 of Volume II, the
centred cell and the range of `p` in Lemma 5.7.5, and, in Proposition 5.7.4, the missing hypotheses, the
interchanged `ε^{d/p}`, `ε^{d/p'}`, and the norming of `T_m f` (the book leaves the closing density and
duality to the reader; here the limit in `f` is taken in the pairing, before duality).

**Who uses it.** In [`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean),
`Cassese.hnvwExtrapolation_holds` is used by `Cassese.umdEllq_lt_top` (the paper's proof of Theorem
1.2, `Cassese.theorem1_2`) and Proposition 6.5; `Cassese.kahaneKhintchine_holds` by (31), so by
Propositions 6.2, 6.5, Theorem 1.4, Corollary 6.1; `Cassese.kahaneKhintchineHypercontractive_holds`
(from `theorem6_2_4_hypercontractive`) by Remark 6.3 and Proposition 6.5 (through `square_eq31_two` and
`square_eq31_q` in `Morrey/Cassese/Square.lean`; Theorem 1.4 uses Proposition 6.5 only at `q = 4` and
does not need it); `Cassese.hnvwTransference_holds` by Proposition 7.2, Theorem 7.1, Corollary 7.2,
Theorem 1.5, Corollary 1.6. No proof uses `hnvwDyadicUMD_holds` or `hnvwZigZag_holds`; Proposition 2.8
is from [`../CoxVeraar`](../CoxVeraar). None is a hypothesis of any statement.
