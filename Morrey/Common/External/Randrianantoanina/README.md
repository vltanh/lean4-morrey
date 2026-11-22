# Randrianantoanina: Schatten classes are UMD, uniformly in the dimension

**Source.** N. Randrianantoanina, *Non-commutative martingale transforms*, J. Funct. Anal. 194
(2002), 181–212 (arXiv:math/0111264), read for §§2–4: Theorem 3.1 (weak type `(1, 1)` of
non-commutative martingale transforms, constant `14√3/3 + 28`), Theorem 4.3
(`c_p ≤ C p² / (p − 1)` for transforms by signs; the case `p < 2` "by interpolation" from
Theorem 3.1 and `L²`, the case `p > 2` by duality), Corollary 4.5
(`C_p (L^p (M, τ)) ≤ C p² / (p − 1)`) and Remark 4.6 (1) (`C_p (S^p)` and `C₂ (S^p)` are `O (p)` as
`p → ∞`; for `C₂` with the source's Theorem 4.2, the extrapolation theorem it quotes from Pisier).

**Statement used by Cassese.** Proposition 2.7 (2) (TeX lines 832–834), citing Corollary 4.5: for
`q ∈ (1, ∞)`, `UMD₂ (S_q (ℓ₂ (ℕ))) ≤ C (q* − 1)` with an absolute constant `C` (a footnote says that
`C = 140` suffices). It is used for the subspaces `S_q^{d×d}`, uniformly in `d`; the proof of
Proposition 6.2 recalls it as `UMD₂ (S_q^{d×d}) ≲ q` for `q ≥ 2` (TeX lines 2330–2331).

**Lean.** [`SchattenUMD.lean`](SchattenUMD.lean), for real square matrices with the Schatten norm
(`BanachProbability.SchattenSpace q n n`) and `UMD = BanachProbability.umdConst`:

- `External.Randrianantoanina.corollary4_5`: there is an absolute `C > 0` with
  `UMD_q (S_q^{n×n}) ≤ C q² / (q − 1)` for every `q ∈ (1, ∞)` and every finite `n`;
- `External.Randrianantoanina.remark4_6`: there is an absolute `C > 0` with
  `UMD₂ (S_q^{n×n}) ≤ C (q* − 1)` for every `q ∈ (1, ∞)` and every `n`, the form Cassese quotes.

**Proof.** `BanachProbability.umdConst_schattenSpace_le` (`UMD_q (S_q) ≤ K q*`, and
`q* ≤ q² / (q − 1)`) and `BanachProbability.umdConst_two_schattenSpace_le` in the package
`BanachProbability` (`lean4-banach-probability`, required by path at
`../lean4-banach-probability` while it is developed), by the source's argument on the
finite-dimensional algebra `ℓ^∞ ({±1}^N) ⊗ M_n (ℝ)` with scalar predictable signs: Cuculescu's
projections and the weak type `(1, 1)` (Theorem 3.1, with a rank count in place of the generalized
singular values of Lemma 3.2, which gives the constant `52`); Marcinkiewicz interpolation and
duality (Theorem 4.3, whose interpolation step, not detailed in the source, is carried out in three
ranges of exponents so that the constant stays uniform near `q = 2`); the Hermitian dilation for
non-symmetric matrices; Maurey's theorem (HNVW I, Theorem 4.2.5) for general filtrations; and
extrapolation to the exponent `2` (HNVW I, Theorem 4.2.7). The package's source contains no
`sorry`.

**Who uses it.** Cassese's `RandrianantoaninaSchattenUMD`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)) is derived from `remark4_6`
by `Cassese.randrianantoaninaSchattenUMD_holds` there. Proposition 6.2, Remark 6.3 and
Proposition 6.5 (`q < ∞` and `q = ∞`, with extrapolation to `UMD_p`) use it, and through them
Theorem 1.4 and Corollary 6.1; none of them takes it as a hypothesis. `corollary4_5` is used by no
proof.
