# Borell: hypercontractivity of vector-valued Rademacher sums

**Sources.** C. Borell, *On the integrability of Banach space valued Walsh polynomials*, Séminaire
de Probabilités XIII, Lecture Notes in Math. 721 (1979), not consulted. The argument is taken
from R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press 2014, §10.1
(read), which credits vector-valued hypercontractivity to Borell; the scalar two-point inequality
is A. Bonami's (*Étude des coefficients de Fourier des fonctions de `L^p (G)`*, Ann. Inst. Fourier
20 (1970)), in O'Donnell's proof after S. Janson.

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
(`lean4-banach-probability`, required by path at `../lean4-banach-probability-int` while it is
developed). The scalar two-point inequality, for nonnegative two-point functions, follows
O'Donnell's proof: the even binomial series for `1 < p ≤ q ≤ 2`, duality for `2 ≤ p ≤ q`
(O'Donnell's Proposition 9.19), and the semigroup property through `L²` for `p < 2 < q`. Its
passage to seminormed spaces through the triangle inequality, and the tensorisation over the
signs by induction on their number, are the standard argument. The package's source contains no
`sorry`.

**Who uses it.** Cassese's `KahaneKhintchineHypercontractive`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)) is derived from
`kahaneKhintchine_hypercontractive` by `Cassese.kahaneKhintchineHypercontractive_holds` there. It
is used only by `Cassese.remark6_3`, `Cassese.proposition6_5_infty` and so
`Cassese.proposition6_5`, through `square_eq31_two` and `square_eq31_q` in
`Morrey/Cassese/Square.lean`; none of them takes it as a hypothesis. Theorem 1.4 uses
Proposition 6.5 only at `q = 4` and does not need it. The package's Kahane–Khintchine inequality
(HNVW II, Theorem 6.2.4, in [`../HNVW`](../HNVW)) is proved from the same bound.
