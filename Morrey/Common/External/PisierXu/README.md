# Pisier–Xu: the non-commutative Khintchine inequality

**Sources.** G. Pisier, Q. Xu, *Non-commutative `L^p`-spaces*, Handbook of the Geometry of Banach
Spaces, Vol. 2, North-Holland 2003, 1459–1517, Theorem 6.1, cited by Cassese with F. Lust-Piquard,
*Inégalités de Khintchine dans `C_p` (`1 < p < ∞`)*, C. R. Acad. Sci. Paris Sér. I Math. 303 (1986),
289–292, and F. Lust-Piquard, G. Pisier, *Non commutative Khintchine and Paley inequalities*, Ark.
Mat. 29 (1991), 241–260. The Handbook chapter was not accessible, and the proof does not rest on the
two articles. It follows L. Mackey, M. I. Jordan, R. Y. Chen, B. Farrell, J. A. Tropp, *Matrix
concentration inequalities via the method of exchangeable pairs*, Ann. Probab. 42 (2014)
(arXiv:1201.6002), which was read.

**Statement used by Cassese.** Proposition 6.3 (TeX lines 2300–2311): for `q ∈ [2, ∞)`, normal
`d × d` matrices `x_1, …, x_n` and independent Rademacher signs `ε_i`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≲ √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`. With
Proposition 6.4 it gives (31) (TeX lines 2322–2328).

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
(`lean4-banach-probability`, required by path at `../lean4-banach-probability-int` while it is
developed). The Handbook being inaccessible, the upper bound is proved by Mackey et al.'s method of
exchangeable pairs, §7 (Corollary 7.3, the matrix Khintchine inequality for Hermitian matrices,
constant `√(q − 1)` for `q ≥ 3`; Remark 7.2, constant `√(2 (q − 1))` for `2 < q < 3`, whose variant
of the mean value trace inequality the source does not prove and the package proves), and §8 (the
Hermitian dilation for general square matrices). The lower bound is the standard convexity
argument: `E [Sᵀ S] = Σ x_iᵀ x_i` for `S = Σ ε_i x_i`, Jensen's inequality and the convexity of
`‖·‖_{S_{q/2}}` on positive semidefinite matrices. The package's source contains no `sorry`.

**Who uses it.** Cassese's `PisierXuKhintchine`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)) is derived from
`theorem6_1` by `Cassese.pisierXuKhintchine_holds` there. It is used by (31)
(`Cassese.equation31`) and by its versions with tracked constants (`square_eq31_two`,
`square_eq31_q` in `Morrey/Cassese/Square.lean`), hence by Proposition 6.2, Remark 6.3,
Proposition 6.5, Theorem 1.4 and Corollary 6.1; none of them takes it as a hypothesis.
`theorem6_1_lower` and `theorem6_1_upper` are used by no proof.
