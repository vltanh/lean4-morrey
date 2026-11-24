# Yaroslavtsev: complex UMD constants

**Source.** I. Yaroslavtsev, *Even Fourier multipliers and martingale transforms in infinite
dimensions*, Indag. Math. 29 (2018), 1290–1309 (arXiv:1710.04958; §3 read), Lemma 3.2 and
Proposition 3.7. Lemma 3.2 has no proof there: it is "proven in" T. Hytönen, J. van Neerven, M. Veraar,
L. Weis, *Analysis in Banach Spaces. Volume I*, Springer 2016 (HNVW I; read), Proposition 4.2.10
(p. 286). (Theorem 3.4, cited in Remark 4.1, TeX line 1029, is context and not formalized.)

**Statements used by Cassese.**

- Proposition 2.7 (5), Lemma 3.2 (TeX lines 842–856): for a complex UMD space `X` and
  `p ∈ (1, ∞)`, the best constant `UMD_{ℂ,p} (X)` in `‖Σ_k λ_k dY_k‖_{L^p} ≤ β_p ‖Y_n‖_{L^p}`, over
  `X`-valued martingales `Y` and predictable unimodular `λ_k`, satisfies
  `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`. Yaroslavtsev's Lemma 3.2 is
  `β^{{−1,1}}_{p,X} ≤ β^D_{p,X} = β_{p,X} ≤ (π / 2) β^{{−1,1}}_{p,X}` for deterministic multipliers (`D`
  the closed unit disc), as is HNVW's; predictable ones have the same constants (HNVW I, Theorem
  4.2.25, pp. 300–301).
- Proposition 2.7 (6), the complex half, Proposition 3.7 with HNVW I, Theorem 4.5.6 (TeX lines
  857–869): `X` is `UMD` if and only if there is `U` with `U (0, 0) = 0`,
  `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p` and `z ↦ U (x + z, y + ε z)` concave for every `ε` in the closed unit
  disc; then `β ≥ UMD_p (X)` and `β ≥ UMD_{ℂ,p} (X)`. Yaroslavtsev states it for multipliers in a convex, bounded, closed
  set `A ⊂ 𝕂` with at least two points (the assumption of his §3.2), without `U (0, 0) = 0`, and adds that
  the smallest admissible `β` is the constant; the case used is the closed unit disc.

**Lean.** [`ComplexUMD.lean`](ComplexUMD.lean), for a complex Banach space `X` and `p ∈ (1, ∞)`,
with `UMD_p (X)` the constant of `X` as a real space (`BanachProbability.umdConst`) and
`UMD_{ℂ,p} (X) = BanachProbability.complexUMDConst X p` (predictable unimodular multipliers,
general filtrations):

- `External.Yaroslavtsev.lemma3_2`: `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`;
- `External.Yaroslavtsev.proposition3_7`: for `β > 0` and `U` zig-zag concave in the complex sense
  (`BanachProbability.IsComplexZigZagConcave p β U`), `UMD_{ℂ,p} (X) ≤ β`;
- `External.Yaroslavtsev.proposition3_7_iff`: `UMD_{ℂ,p} (X) < ∞` if and only if such a `U` exists for
  some `β > 0`.

**Constants.** `π / 2`, as in both sources; `β`.

**Proofs.** In the package `BanachProbability`
([lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability)). Lemma 3.2,
`BanachProbability.umdConst_le_complexUMDConst_le`, by the proof of HNVW I, Proposition 4.2.10:

- real signs are unimodular;
- complex numbers `α_1, …, α_n` of modulus at most one are `(π / 2) Σ_j λ^{(j)} ε^{(j)}` with
  `ε^{(j)} ∈ {±1}^n` and `Σ_j |λ^{(j)}| ≤ 1` (Proposition 3.2.14 with Lemma 3.2.15 and (3.21),
  (3.22)), and the triangle inequality concludes for deterministic multipliers;
- Theorem 4.2.25 (incremental filtrations, Lemma 3.6.18) concludes for predictable multipliers.

Proposition 3.7, `BanachProbability.complexUMDConst_le_of_isComplexZigZagConcave` and
`complexUMDConst_lt_top_iff_exists_isComplexZigZagConcave`: Yaroslavtsev's proof "repeats the one
given in" HNVW I, Theorem 4.5.6, with multipliers in `A` (only the finiteness of `U` is argued anew,
for a general `A`), and the package's is HNVW's, over `ℝ` and `ℂ` at once, with multipliers in the
closed unit ball (see [`../HNVW`](../HNVW)). The package's source contains no `sorry`.

**Departures.** None in the arguments. As everywhere in the package, the spaces are probability spaces
and the martingales start at `0`, so the term `v_0 f_0` of HNVW's transforms vanishes. In Lemma 3.6.18
(iii) the printed range of `k` is corrected.

**Who uses it.** In [`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean),
Cassese's `YaroslavtsevComplexUMD` is derived from `lemma3_2` by
`Cassese.yaroslavtsevComplexUMD_holds`, and the complex half of `HNVWZigZag` (the equivalence, with
`UMD_p (X)` of `X` as a real space, and the two bounds) from `proposition3_7_iff`, `proposition3_7` and
`lemma3_2` by `Cassese.hnvwZigZag_holds`. The first is used by `Cassese.umdEllq_lt_top`
(`UMD_{ℂ,p} (ℓ_q) < ∞`) in the paper's proof of Theorem 1.2 (`Cassese.theorem1_2`), which does not take it
as a hypothesis; the second is used by no proof.
