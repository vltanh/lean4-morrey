# Borell: hypercontractivity of vector-valued Rademacher sums

**Sources.** C. Borell, *On the integrability of Banach space valued Walsh polynomials*, Séminaire
de Probabilités XIII, Lecture Notes in Math. 721 (1979), 1–3 (read: Numdam,
https://www.numdam.org/item/SPS_1979__13__1_0/), Theorem 1.1 and its proof (§2). The two results
Borell cites without proof are proved by the arguments of R. O'Donnell, *Analysis of Boolean
Functions*, Cambridge University Press 2014 (read; arXiv:2105.10386): the elementary two-point
inequality (Borell cites L. Gross, Amer. J. Math. 97 (1975), Theorem 3, and W. Beckner, Ann. of
Math. 102 (1975), p. 180, neither obtained) by O'Donnell's §10.1 for nonnegative functions, after
S. Janson (A. Bonami, *Étude des coefficients de Fourier des fonctions de `L^p (G)`*, Ann. Inst.
Fourier 20 (1970)), and his Exercise 9.7 for all real ones; the Segal lemma (Beckner, Lemma 2) by
the induction of O'Donnell's Exercise 10.3 with Minkowski's inequality (Exercise 10.1).

**Statement used by Cassese.** None by name. Cassese's Proposition 6.4 (TeX lines 2314–2321,
HNVW II, Theorem 6.2.4) names only constants `k_{p,q}`, but Remark 6.3 (TeX lines 2425–2438) and
the case `q = ∞` of Proposition 6.5 (TeX lines 2477–2479: "all the implied multiplicative constants
in the above inequalities are at most polynomial in `q`") use (31) with constants that grow at most
polynomially in `q`, which needs `k_{q,p}` to. The paper names no source for this growth
(inventory E27). The standard bound is Borell's:
`‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1)) ‖Σ ε_i x_i‖_{L^p}` for `1 < p ≤ q < ∞`.

**Lean.** [`Hypercontractivity.lean`](Hypercontractivity.lean), for any seminorm `S` on a real
vector space (no completeness):

- `External.Borell.hypercontractive_affine`: for `1 < p ≤ q`, `ρ = √((p − 1) / (q − 1))`, `c` and
  `x_1, …, x_n`, `‖c + ρ Σ ε_i x_i‖_{L^q} ≤ ‖c + Σ ε_i x_i‖_{L^p}` (the noise operator `T_ρ` on
  Walsh polynomials of degree at most `1`);
- `External.Borell.kahaneKhintchine_hypercontractive`: its case `c = 0`, the bound above.

**Proof.** `BanachProbability.hypercontractive_affine` and
`BanachProbability.kahaneKhintchine_hypercontractive` in the package `BanachProbability`
(`lean4-banach-probability`, required by path at `../lean4-banach-probability` while it is
developed), by Borell's argument (§2), step by step: Borell's operator
`K̄ g (x) = E_y [(1 + ρ x y) g (y)]` on functions of one sign and its tensor powers `⊗ⁿ K̄`
(`kBar`, `kBarTensor`); the elementary inequality `‖K̄ g‖_{L^q} ≤ ‖g‖_{L^p}` for real `g`
(`kBar_twoPoint`); `‖(⊗ⁿ K̄) f‖_{L^q} ≤ ‖f‖_{L^p}` for real `f`, which Borell obtains by the Segal
lemma (`kBarTensor_lpNorm_le_real`); the positivity of the kernel, which carries it to `E`-valued
`f` (`seminorm_kBarTensor_le`, `kBarTensor_lpNorm_le`); and `(⊗ⁿ K̄) e_α = ρ^{|α|} e_α` for
`|α| ≤ 1`, `(⊗ⁿ K̄) (c + Σ ε_i x_i) = c + ρ Σ ε_i x_i` (`kBarTensor_affine`). The scalar two-point
inequality for nonnegative functions (`twoPoint`) follows O'Donnell's proof: the even binomial
series for `1 < p ≤ q ≤ 2`, duality for `2 ≤ p ≤ q` (O'Donnell's Proposition 9.19), and the
semigroup property through `L²` for `p < 2 < q`. Only the degree `d ≤ 1` of Borell's Theorem 1.1
is formalized (Borell's `λ` at its largest value `√((p − 1) / (q − 1))`), which is all Cassese
uses; the degrees `d ≥ 2`, the closure `W̄_d (E)` and the exponential integrability are not. The
package's source contains no `sorry`.

**Who uses it.** Cassese's `KahaneKhintchineHypercontractive`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)) is derived from
`kahaneKhintchine_hypercontractive` by `Cassese.kahaneKhintchineHypercontractive_holds` there. It
is used only by `Cassese.remark6_3`, `Cassese.proposition6_5_infty` and so
`Cassese.proposition6_5`, through `square_eq31_two` and `square_eq31_q` in
`Morrey/Cassese/Square.lean`; none of them takes it as a hypothesis. Theorem 1.4 uses
Proposition 6.5 only at `q = 4` and does not need it. The package's Kahane–Khintchine inequality
(HNVW II, Theorem 6.2.4, in [`../HNVW`](../HNVW)) is proved from the same bound.
