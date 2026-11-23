# Pisier–Xu: the non-commutative Khintchine inequality

**Sources.** G. Pisier, Q. Xu, *Non-commutative `L^p`-spaces*, Handbook of the Geometry of Banach
Spaces, Vol. 2, North-Holland 2003, 1459–1517, Theorem 6.1, cited by Cassese with F. Lust-Piquard,
*Inégalités de Khintchine dans `C_p` (`1 < p < ∞`)*, C. R. Acad. Sci. Paris Sér. I Math. 303 (1986),
289–292, and F. Lust-Piquard, G. Pisier, *Non commutative Khintchine and Paley inequalities*, Ark.
Mat. 29 (1991), 241–260 (LPP). The Handbook chapter (read, p. 1486) states the theorem, for semifinite
von Neumann algebras and `1 ≤ p < ∞`, and gives no proof: it refers to Lust-Piquard 1986, where the
result was first proved for the Schatten classes and `1 < p < ∞`, and to LPP for the general statement;
for `p ≥ 2` its upper constant `B'_p` depends only on `p`, and is "of order `√p` (the best possible)"
(Remark (i)), with a reference to G. Pisier, Astérisque 247 (1998), p. 106. LPP and Astérisque 247,
pp. 101–108, were read and are followed; Lust-Piquard 1986 was not obtained.

**Statement used by Cassese.** Proposition 6.3 (TeX lines 2300–2311): for `q ∈ [2, ∞)`, normal
`d × d` matrices `x_1, …, x_n` and independent Rademacher signs `ε_i`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≲ √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`. With
Proposition 6.4 it gives (31) (TeX lines 2322–2328). (The remark at TeX lines 2416–2421, on
noncommutative square function inequalities, is context and not formalized.)

**Lean.** [`Khintchine.lean`](Khintchine.lean), for real square matrices, with
`‖(Σ y_i)^{1/2}‖_{S_q}` written `‖Σ y_i‖_{S_{q/2}}^{1/2}` (`Σ y_i` positive semidefinite):

- `External.PisierXu.theorem6_1_general`: (6.4) for all real square matrices and `q ≥ 2`: the larger of
  the row and the column square function is at most `(E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q}`, which is at most
  `C √q` times it, `C` absolute;
- `External.PisierXu.theorem6_1`: the form Cassese quotes, for normal `x_i`, with the one square
  function.

**Proof.** `HarmonicAnalysis.ncKhintchine` and `HarmonicAnalysis.ncKhintchine_of_normal` in the
package `HarmonicAnalysis` ([lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis)),
by LPP and Astérisque 247, p. 106:

- the lower bound with constant `1` by (I.5)–(I.7) of LPP;
- Paley's inequality in the Schatten classes, uniformly in `1 ≤ p ≤ 2` (LPP, Theorem III.1 (i) for the
  Paley projection): the factorization of matrix-valued `H¹` functions ((α), (β) of LPP, p. 252) is
  Sarason's Theorem 4 (Trans. Amer. Math. Soc. 127 (1967), 179–203), with Helson–Lowdenslager (Acta Math.
  99 (1958) and 106 (1961)); (III.3), for every choice of signs, is McConnell's Littlewood–Paley inequality
  for UMD spaces (Trans. Amer. Math. Soc. 285 (1984), 739–757, Theorem 1.3, from his multiplier
  theorem, Theorem 1.1, `n = 1`, and from the boundedness of the Hilbert transform on UMD spaces, by
  Burkholder 1983, Lemmas 1–4, pp. 277–283, with M. Riesz (1928), §18, to which his Lemma 4 refers),
  transferred to the circle by HNVW I, Proposition 5.7.1,
  with the dilation of the proof of its Theorem 5.7.10;
- Corollary III.4 with signs, by averaging (LPP, p. 243);
- the upper bound by duality (LPP, pp. 254–255), with the Rademacher projection on `L^q (S_q)` bounded
  by a multiple of `√q` (Astérisque 247, p. 106): type 2 of `S_q` by Tomczak-Jaegermann (Studia Math. 50
  (1974), 163–182), and type 2 ⇒ K-convexity (Maurey–Pisier, Studia Math. 58 (1976), Remark 2.10, which
  has no proof; Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach Spaces II*, Proposition 7.4.22).

**Constants.** Lower constant `1`, as in (6.4); upper constant `C √q`, `C` absolute and not made explicit
(the source: `B'_p`, "of order `√p`").

**Departures.** None from the argument of LPP. For (III.3) LPP give two references, Bourgain 1986 (not
obtained) and McConnell 1984, Theorem 1.3; McConnell's proof is followed, for `n = 1`. Facts that
these sources take from works that were not read, or only recall, or state without proof, have named
substitutes: Sarason's Lemma 10.3, from Helson's book (not read), by Helson–Lowdenslager 1961, §§9–10;
Szegő's theorem and the quotient by an outer function, from Hoffman's book (pp. 53, 75; not read), by
Helson–Lowdenslager 1958, Theorem 9, and the density argument at the end of Sarason's proof; the
Schatten inequalities of Simon's and of Gohberg–Krein's books (not read), by Hytönen–van
Neerven–Veraar–Weis (HNVW), *Analysis in Banach Spaces I*, Appendix D, and by Sutter, Berta and
Tomamichel (Comm. Math. Phys. 352 (2017)); the multiplier `−i sgn` as the limit of the truncated
Hilbert transforms (Burkholder 1983, Theorem 2, stated without proof), by HNVW I, Lemma 5.2.1 and
Proposition 5.2.2; Theorem 1 of Burkholder 1983 for `ℝ` (its proof is in Burkholder 1981, read and not
followed), by Burkholder's inequality with the constant `p* − 1` (Cassese's Theorem 2.3 (1)): Burkholder
asserts on p. 275, without proof, that with Khintchine's inequality it gives the square-function
inequality for real martingales, which is proved here by the argument of his Lemma 1 (pp. 277–278); a
comparison of multinomial coefficients that Tomczak-Jaegermann quotes
(p. 177), by an elementary inequality; Maurey–Pisier, Remark 2.10 (read, no proof), by HNVW II,
Proposition 7.4.22. LPP recall that `C_{2p}` is UMD, with Cotlar's trick as a known argument; here it
is Randrianantoanina's theorem ([`External/Randrianantoanina`](../Randrianantoanina)), which Cassese
cites for it.

**Shorter proof.** The upper bound with the explicit constant `√(2 (q − 1)) ≤ √2 √q`, by the method of
exchangeable pairs of Mackey, Jordan, Chen, Farrell and Tropp (Ann. Probab. 42 (2014), §§7–8), is
`BanachProbability.ncKhintchine_upper` in
[lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability). It is not used here.

**Who uses it.** Cassese's `PisierXuKhintchine`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)) is derived from
`theorem6_1` by `Cassese.pisierXuKhintchine_holds` there. It is used by (31)
(`Cassese.equation31`) and by its versions with tracked constants (`square_eq31_two`,
`square_eq31_q` in `Morrey/Cassese/Square.lean`), hence by Proposition 6.2, Remark 6.3,
Proposition 6.5, Theorem 1.4 and Corollary 6.1; none of them takes it as a hypothesis.
`theorem6_1_general` is used by no proof.
