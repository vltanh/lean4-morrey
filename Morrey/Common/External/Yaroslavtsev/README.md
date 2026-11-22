# Yaroslavtsev: complex UMD constants

**Source.** I. Yaroslavtsev, *Even Fourier multipliers and martingale transforms in infinite
dimensions*, Indag. Math. 29 (2018), 1290–1309 (arXiv:1710.04958), Lemma 3.2 and Proposition 3.7.
Only the statements of these two results were read. Lemma 3.2 has no proof there: it is quoted as
"proven in" HNVW I, Proposition 4.2.10, which was not accessible.

**Statements used by Cassese.**

- Proposition 2.7 (5), Lemma 3.2 (TeX lines 842–856): for a complex UMD space `X` and
  `p ∈ (1, ∞)`, the best constant `UMD_{ℂ,p} (X)` in `‖Σ_k λ_k dY_k‖_{L^p} ≤ β_p ‖Y_n‖_{L^p}`, over
  `X`-valued martingales `Y` and predictable unimodular `λ_k`, satisfies
  `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`.
- Proposition 2.7 (6), the complex half, Proposition 3.7 with HNVW I, Theorem 4.5.6 (TeX lines
  857–869): if `U (0, 0) = 0`, `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p` and `z ↦ U (x + z, y + ε z)` is
  concave for every `ε` in the closed unit disc, then `β ≥ UMD_{ℂ,p} (X)`. Yaroslavtsev states it
  for multipliers in any set `A ⊂ 𝕂`; the case used is the unit disc.

**Lean.** [`ComplexUMD.lean`](ComplexUMD.lean), for a complex Banach space `X` and `p ∈ (1, ∞)`,
with `UMD_p (X)` the constant of `X` as a real space (`BanachProbability.umdConst`) and
`UMD_{ℂ,p} (X) = BanachProbability.complexUMDConst X p` (predictable unimodular multipliers,
general filtrations):

- `External.Yaroslavtsev.lemma3_2`: `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`;
- `External.Yaroslavtsev.proposition3_7`: for `β > 0` and `U` zig-zag concave in the complex sense
  (`BanachProbability.IsComplexZigZagConcave p β U`), `UMD_{ℂ,p} (X) ≤ β`.

**Proof.** In the package `BanachProbability`
([lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability), commit `250cd49`).
Lemma 3.2,
`BanachProbability.umdConst_le_complexUMDConst_le`, by the standard averaging argument in place of
the inaccessible HNVW I, Proposition 4.2.10: real signs are unimodular, and for `|λ| = 1`,
`(1/2π) ∫ sgn cos (arg λ − φ) e^{iφ} dφ = (2/π) λ`, with the integral replaced by Riemann sums
over equally spaced angles so that no joint measurability is needed. Proposition 3.7,
`BanachProbability.complexUMDConst_le_of_isComplexZigZagConcave`, by Burkholder's argument:
midpoint concavity integrated along complex Paley–Walsh transforms on the sign cube, then the
complex form of Maurey's theorem. The package's source contains no `sorry`.

**Who uses it.** In [`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean),
Cassese's `YaroslavtsevComplexUMD` is derived from `lemma3_2` by
`Cassese.yaroslavtsevComplexUMD_holds`, and the complex half of `HNVWZigZag` from `proposition3_7`
by `Cassese.hnvwZigZag_holds` (with `External.HNVW.theorem4_5_6`). The first is used by
`Cassese.umdEllq_lt_top` (`UMD_{ℂ,p} (ℓ_q) < ∞`) in the paper's proof of Theorem 1.2
(`Cassese.theorem1_2`), which does not take it as a hypothesis; the second is used by no proof.
