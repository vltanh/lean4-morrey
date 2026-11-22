module

public import BanachProbability.KahaneKhintchine.Basic

/-!
# The Kahane–Khintchine inequality (HNVW II, Theorem 6.2.4)

T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume II:
Probabilistic Methods and Operator Theory* (2017), Theorem 6.2.4 (J.-P. Kahane, *Sur les sommes
vectorielles `Σ ±u_n`*, C. R. Acad. Sci. Paris 259 (1964)), which Cassese (arXiv:2608.03488v3)
cites as Proposition 6.4 (TeX lines 2312–2321): for `p, q ∈ (1, ∞)` there is a constant
`κ_{p,q}` such that for every Banach space `X`, `x_1, …, x_n ∈ X` and independent Rademacher
signs `ε_i`, `‖Σ ε_i x_i‖_{L^p} ≤ κ_{p,q} ‖Σ ε_i x_i‖_{L^q}`. The book was not accessible; the
statement is the one Cassese quotes, for `p, q ∈ (1, ∞)`.

* `External.HNVW.theorem6_2_4`: the statement for a real normed space `X`, with the explicit
  constant `κ_{p,q} = max (1, √((p − 1) / (q − 1)))` (`BanachProbability.kahaneKhintchineConst`);
* `External.HNVW.theorem6_2_4_seminorm`: the same for every seminorm on a real vector space, in
  which form Cassese's Proposition 6.4 is stated here (no completeness is needed).

Proof: `BanachProbability.kahaneKhintchine` in the package `BanachProbability`
(`lean4-banach-probability`, required by path while it is developed). The source being
inaccessible, the argument is hypercontractivity (Bonami's two-point inequality as in
R. O'Donnell, *Analysis of Boolean Functions* (2014), §10.1, carried to seminormed spaces by the
triangle inequality and tensorised, C. Borell 1979; `External.Borell`): for `p ≤ q`,
`‖·‖_{L^p} ≤ ‖·‖_{L^q}` (monotonicity of `L^p` norms); for `p > q`,
`‖·‖_{L^p} ≤ √((p − 1) / (q − 1)) ‖·‖_{L^q}` (hypercontractivity). Not Kahane's original argument
through Lévy's inequality, which gives no growth rate of the constants.
-/

@[expose] public section

namespace External.HNVW

open BanachProbability BanachProbability.SignCube

/-- **HNVW II, Theorem 6.2.4** (Kahane–Khintchine), for seminorms: for every seminorm `S` on a real
vector space, `p, q ∈ (1, ∞)` and `x_1, …, x_n`,
`‖Σ ε_i x_i‖_{L^p} ≤ κ_{p,q} ‖Σ ε_i x_i‖_{L^q}`, `κ_{p,q} = max (1, √((p − 1) / (q − 1)))`. -/
theorem theorem6_2_4_seminorm {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Seminorm ℝ E)
    {p q : ℝ} (hp : 1 < p) (hq : 1 < q) {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      kahaneKhintchineConst p q *
        SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) :=
  kahaneKhintchine S hp hq x

/-- **HNVW II, Theorem 6.2.4** (Kahane–Khintchine): for a real normed space `X`, `p, q ∈ (1, ∞)`
and `x_1, …, x_n ∈ X`, `‖Σ ε_i x_i‖_{L^p} ≤ κ_{p,q} ‖Σ ε_i x_i‖_{L^q}`,
`κ_{p,q} = max (1, √((p − 1) / (q − 1)))`. -/
theorem theorem6_2_4 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {p q : ℝ} (hp : 1 < p)
    (hq : 1 < q) {n : ℕ} (x : Fin n → X) :
    SignCube.lpNorm (fun y : X => ‖y‖) p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      kahaneKhintchineConst p q *
        SignCube.lpNorm (fun y : X => ‖y‖) q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) :=
  kahaneKhintchine (normSeminorm ℝ X) hp hq x

end External.HNVW
