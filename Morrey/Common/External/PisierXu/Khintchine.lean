module

public import BanachProbability.NoncommutativeKhintchine.Basic

/-!
# The non-commutative Khintchine inequality (Pisier–Xu 2003, Theorem 6.1)

G. Pisier, Q. Xu, *Non-commutative `L^p`-spaces*, Handbook of the Geometry of Banach Spaces,
Vol. 2 (2003), 1459–1517, Theorem 6.1 (with F. Lust-Piquard, *Inégalités de Khintchine dans
`C_p` (`1 < p < ∞`)*, C. R. Acad. Sci. Paris 303 (1986), and F. Lust-Piquard, G. Pisier, *Non
commutative Khintchine and Paley inequalities*, Ark. Mat. 29 (1991)), which Cassese
(arXiv:2608.03488v3) cites as Proposition 6.3 (TeX lines 2297–2311): for `q ∈ [2, ∞)` and normal
matrices `x_1, …, x_k`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≲ √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`.
The Handbook chapter was not accessible; the statement is the one Cassese quotes. For general
`x_i` the package also proves the lower bounds by the row and by the column square function, and
the upper bound by the larger of the two; for normal `x_i` the two agree.

Stated for real square matrices, with `‖(Σ y_i)^{1/2}‖_{S_q} = ‖Σ y_i‖_{S_{q/2}}^{1/2}` for the
positive semidefinite `Σ y_i`:

* `External.PisierXu.theorem6_1_lower`: the lower bounds, with constant `1`, by the row and by
  the column square function;
* `External.PisierXu.theorem6_1_upper`: the upper bound with constant `√(2 (q − 1))`;
* `External.PisierXu.theorem6_1`: the form Cassese quotes, for normal `x_i`: there is an absolute
  `C` with lower constant `1` and upper constant `C √q` (here `C = √2`).

Proof: in the package `BanachProbability` (`lean4-banach-probability`, required by path while it
is developed), `BanachProbability.ncKhintchine_lower_row`, `ncKhintchine_lower_col`,
`ncKhintchine_upper` and `pisierXu_khintchine`. The source being inaccessible, the upper bound is
proved by the method of exchangeable pairs of L. Mackey, M. I. Jordan, R. Y. Chen, B. Farrell,
J. A. Tropp, *Matrix concentration inequalities via the method of exchangeable pairs*, Ann.
Probab. 42 (2014) (arXiv:1201.6002), §7 (the matrix Khintchine inequality, Corollary 7.3 and
Remark 7.2, for symmetric matrices; the variant of the mean value trace inequality that Remark 7.2
needs, which the source does not prove, is proved in the package) and §8 (the Hermitian dilation
for general square matrices); the lower bound by the standard convexity argument
(`E [Yᵀ Y] = Σ x_iᵀ x_i` and the convexity of `‖·‖_{S_{q/2}}`).
-/

@[expose] public section

open scoped Matrix

namespace External.PisierXu

open BanachProbability BanachProbability.SignCube

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Pisier–Xu (2003), Theorem 6.1**, lower bounds: for `q ≥ 2` and real square matrices
`x_1, …, x_k`, `‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q}` and
`‖(Σ x_iᵀ x_i)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q}`. -/
theorem theorem6_1_lower {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ) :
    √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ∧
      √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i)) ≤
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) :=
  ⟨ncKhintchine_lower_row hq x, ncKhintchine_lower_col hq x⟩

/-- **Pisier–Xu (2003), Theorem 6.1**, upper bound, with the constant `√(2 (q − 1)) ≤ √2 √q`
(Mackey–Jordan–Chen–Farrell–Tropp 2014): for `q ≥ 2` and real square matrices `x_1, …, x_k`,
`(E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≤ √(2 (q − 1))
  max (‖Σ x_i x_iᵀ‖_{S_{q/2}}, ‖Σ x_iᵀ x_i‖_{S_{q/2}})^{1/2}`. -/
theorem theorem6_1_upper {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (x : Fin k → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
      √(2 * (q - 1)) * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))) :=
  ncKhintchine_upper hq x

/-- **Pisier–Xu (2003), Theorem 6.1**, the form Cassese quotes (Proposition 6.3): there is an
absolute `C > 0` such that for `q ∈ [2, ∞)` and normal real square matrices `x_1, …, x_k`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≤ C √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`
(the proof gives `C = √2`). -/
theorem theorem6_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℝ), 2 ≤ q → ∀ (n : Type) [Fintype n] [DecidableEq n] (k : ℕ)
      (x : Fin k → Matrix n n ℝ), (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
      √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
          SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ∧
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
          C * √q * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) :=
  pisierXu_khintchine

end External.PisierXu
