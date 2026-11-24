module

public import HarmonicAnalysis.NoncommutativeKhintchine

/-!
# The non-commutative Khintchine inequality (Pisier–Xu 2003, Theorem 6.1)

G. Pisier, Q. Xu, *Non-commutative `L^p`-spaces*, Handbook of the Geometry of Banach Spaces, Vol. 2
(2003), 1459–1517, Theorem 6.1 (with F. Lust-Piquard, *Inégalités de Khintchine dans `C_p`
(`1 < p < ∞`)*, C. R. Acad. Sci. Paris 303 (1986), and F. Lust-Piquard, G. Pisier, *Non commutative
Khintchine and Paley inequalities*, Ark. Mat. 29 (1991)), which Cassese (arXiv:2608.03488v3) cites
as Proposition 6.3 (TeX lines 2297–2311): for `q ∈ [2, ∞)` and normal matrices `x_1, …, x_k`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≲ √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`. The
Handbook chapter (read, p. 1486) states the theorem for semifinite von Neumann algebras and
`1 ≤ p < ∞`: for `p ≥ 2`, (6.4), the lower bound with constant `1` and the upper bound with a
constant `B'_p` that depends only on `p`, for the larger of the row and the column square function;
by its Remark (i), `B'_p` "is of order `√p` … (cf. [G. Pisier, Astérisque 247 (1998), p. 106])". For
normal `x_i` the two square functions agree.

Stated for real square matrices, with `‖(Σ y_i)^{1/2}‖_{S_q} = ‖Σ y_i‖_{S_{q/2}}^{1/2}` for the
positive semidefinite `Σ y_i`:

* `External.PisierXu.theorem6_1_general`: (6.4), for all real square matrices: the lower bound with
  constant `1` and the upper bound with the constant `C √q`, `C` absolute, for the larger of the row
  and the column square function;
* `External.PisierXu.theorem6_1`: the form Cassese quotes, for normal `x_i`, with the one square
  function.

Proof: in the package `HarmonicAnalysis` (`lean4-harmonic-analysis`),
`HarmonicAnalysis.ncKhintchine` and `ncKhintchine_of_normal`. The Handbook chapter gives no proof
(p. 1486): it refers to Lust-Piquard 1986 (not obtained) and to Lust-Piquard–Pisier 1991, and to
Astérisque 247 for the order of `B'_p`. The proof is that of Lust-Piquard–Pisier 1991 and of
Astérisque 247, p. 106: the lower bound by (I.5)–(I.7); the Paley inequality of Theorem III.1 (i)
for the Paley projection, by the factorization of matrix-valued `H¹` functions (Sarason 1967,
Theorem 4, with Helson–Lowdenslager 1958 and 1961); the inequality (III.3), for every choice of
signs, by McConnell 1984, Theorem 1.3, which Lust-Piquard and Pisier cite for it with Bourgain
1986 (not obtained); Corollary III.4 with signs; and the upper bound by duality, with the
Rademacher projection on `L^q (S_q)` bounded by a multiple of `√q` (type 2 of `S_q`,
Tomczak-Jaegermann 1974, and K-convexity). Facts that these sources take from works that were not
read, or state without proof, have named substitutes, listed in the README of this directory.

A shorter proof of the upper bound, with the explicit constant `√(2 (q − 1))`, by the exchangeable
pairs of Mackey, Jordan, Chen, Farrell and Tropp (2014), is
`BanachProbability.ncKhintchine_upper` in the package `BanachProbability`; it is not used here.
-/

@[expose] public section

open scoped Matrix

namespace External.PisierXu

open BanachProbability BanachProbability.SignCube

/-- **Pisier–Xu (2003), Theorem 6.1, (6.4)**: there is an absolute `C > 0` such that for
`q ∈ [2, ∞)` and real square matrices `x_1, …, x_k`, with
`m = max (‖Σ x_iᵀ x_i‖_{S_{q/2}}, ‖Σ x_i x_iᵀ‖_{S_{q/2}})^{1/2}`,
`m ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≤ C √q m`. -/
theorem theorem6_1_general : ∃ C : ℝ, 0 < C ∧
    ∀ (n : Type) [Fintype n] [DecidableEq n] (q : ℝ), 2 ≤ q → ∀ (k : ℕ) (x : Fin k → Matrix n n ℝ),
      √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))
          (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))) ≤
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ∧
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
          (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
        C * √q * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, (x i)ᵀ * x i))
          (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))) :=
  HarmonicAnalysis.ncKhintchine

/-- **Pisier–Xu (2003), Theorem 6.1**, the form Cassese quotes (Proposition 6.3): there is an
absolute `C > 0` such that for `q ∈ [2, ∞)` and normal real square matrices `x_1, …, x_k`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≤ C √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`. -/
theorem theorem6_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℝ), 2 ≤ q → ∀ (n : Type) [Fintype n] [DecidableEq n] (k : ℕ)
      (x : Fin k → Matrix n n ℝ), (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
      √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
          SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ∧
        SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin k → Bool => ∑ i, coin (ε i) • x i) ≤
          C * √q * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) := by
  obtain ⟨C, hC, h⟩ := HarmonicAnalysis.ncKhintchine_of_normal
  exact ⟨C, hC, fun q hq n _ _ k x hx => h n q hq k x hx⟩

end External.PisierXu
