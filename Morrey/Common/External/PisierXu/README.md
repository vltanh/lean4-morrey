# Pisier–Xu: the non-commutative Khintchine inequality

**Sources.** G. Pisier, Q. Xu, *Non-commutative `L^p`-spaces*, Handbook of the Geometry of Banach
Spaces, Vol. 2, North-Holland 2003, 1459–1517, Theorem 6.1, cited by Cassese with F. Lust-Piquard,
*Inégalités de Khintchine dans `C_p` (`1 < p < ∞`)*, C. R. Acad. Sci. Paris Sér. I Math. 303 (1986),
289–292, and F. Lust-Piquard, G. Pisier, *Non commutative Khintchine and Paley inequalities*, Ark.
Mat. 29 (1991), 241–260. The Handbook chapter (read, p. 1486) states the theorem, for semifinite von
Neumann algebras and `1 ≤ p < ∞`, and gives no proof: it refers to Lust-Piquard 1986, where the result
was first proved for the Schatten classes and `1 < p < ∞`, and to Lust-Piquard–Pisier 1991 for the
general statement; for `p ≥ 2` its upper constant `B'_p` depends only on `p`, and is "of order `√p` (the
best possible)" (Remark (i)), with a reference to G. Pisier, Astérisque 247 (1998), p. 106.
Lust-Piquard–Pisier 1991 and Astérisque 247, pp. 101–108, were read; Lust-Piquard 1986 was not
obtained. The proof of the upper bound here does not follow them. It follows L. Mackey, M. I. Jordan,
R. Y. Chen, B. Farrell, J. A. Tropp, *Matrix concentration inequalities via the method of exchangeable
pairs*, Ann. Probab. 42 (2014) (arXiv:1201.6002; read).

**Statement used by Cassese.** Proposition 6.3 (TeX lines 2300–2311): for `q ∈ [2, ∞)`, normal
`d × d` matrices `x_1, …, x_n` and independent Rademacher signs `ε_i`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≲ √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`. With
Proposition 6.4 it gives (31) (TeX lines 2322–2328). (The remark at TeX lines 2416–2421, on
noncommutative square function inequalities, is context and not formalized.)

**Lean.** [`Khintchine.lean`](Khintchine.lean), for real square matrices, with
`‖(Σ y_i)^{1/2}‖_{S_q}` written `‖Σ y_i‖_{S_{q/2}}^{1/2}` (`Σ y_i` positive semidefinite):

- `External.PisierXu.theorem6_1_lower`: for `q ≥ 2`, both the row and the column square function
  are at most `(E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q}`, with constant `1` and no normality;
- `External.PisierXu.theorem6_1_upper`: for `q ≥ 2`, `(E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q}` is at most
  `√(2 (q − 1))` times the larger of the two square functions;
- `External.PisierXu.theorem6_1`: the form Cassese quotes, for normal `x_i`, with lower constant `1`
  and upper constant `C √q`, `C = √2`.

**Proof.** `BanachProbability.ncKhintchine_lower_row`, `ncKhintchine_lower_col`,
`ncKhintchine_upper` and `pisierXu_khintchine` in the package `BanachProbability`
([lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability)).
The Handbook chapter has no proof; the upper bound is proved by Mackey et al.'s method of
exchangeable pairs, §7 (Corollary 7.3, the matrix Khintchine inequality for Hermitian matrices,
constant `√(q − 1)` for `q ≥ 3`; Remark 7.2, constant `√(2 (q − 1))` for `2 < q < 3`, whose variant
of the mean value trace inequality the source does not prove and the package proves), and §8 (the
Hermitian dilation for general square matrices). The lower bound is the standard convexity
argument: `E [Sᵀ S] = Σ x_iᵀ x_i` for `S = Σ ε_i x_i`, Jensen's inequality and the convexity of
`‖·‖_{S_{q/2}}` on positive semidefinite matrices, as in Lust-Piquard–Pisier 1991, (I.5)–(I.7). The
package's source contains no `sorry`.

**Constants.** Lower constant `1`, as in (6.4); upper constant `√(2 (q − 1)) ≤ √2 √q`, of the order `√q`
that the paper states (the source: `B'_p`, "of order `√p`").

**Departures.** The argument for the upper bound is not that of the cited works (Lust-Piquard–Pisier: a
lacunary sequence in place of the signs, a factorization of matrix-valued `H¹` functions, and duality;
Astérisque 247 for the order `√q`).

**Who uses it.** Cassese's `PisierXuKhintchine`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)) is derived from
`theorem6_1` by `Cassese.pisierXuKhintchine_holds` there. It is used by (31)
(`Cassese.equation31`) and by its versions with tracked constants (`square_eq31_two`,
`square_eq31_q` in `Morrey/Cassese/Square.lean`), hence by Proposition 6.2, Remark 6.3,
Proposition 6.5, Theorem 1.4 and Corollary 6.1; none of them takes it as a hypothesis.
`theorem6_1_lower` and `theorem6_1_upper` are used by no proof.
