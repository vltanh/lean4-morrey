module

public import BanachProbability.KahaneKhintchine.Basic

/-!
# The Kahane–Khintchine inequality (HNVW II, Theorem 6.2.4)

T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume II: Probabilistic
Methods and Operator Theory* (2017; read), Theorem 6.2.4 (pp. 21–22), which Cassese
(arXiv:2608.03488v3) cites as Proposition 6.4 (TeX lines 2312–2321): for `p, q ∈ (1, ∞)` there is a
constant `κ_{p,q}` such that for every Banach space `X`, `x_1, …, x_n ∈ X` and independent
Rademacher signs `ε_i`, `‖Σ ε_i x_i‖_{L^p} ≤ κ_{p,q} ‖Σ ε_i x_i‖_{L^q}`.

The theorem of the book says more: for `0 < p < q < ∞` there is a constant `κ_{q,p}` with
`‖Σ ε_i x_i‖_{L^q} ≤ κ_{q,p} ‖Σ ε_i x_i‖_{L^p}`, and, for real signs and `1 < p < q < ∞`,
`κ_{q,p} ≤ √((q − 1) / (p − 1))`. The paper's Proposition 6.4 leaves out this bound, but Remark 6.3
(TeX lines 2425–2438) and the case `q = ∞` of Proposition 6.5 (TeX lines 2477–2479) need constants
that grow at most polynomially in `q` (inventory E27): the theorem it cites gives them.

* `External.HNVW.theorem6_2_4_hypercontractive`: `‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1))
  ‖Σ ε_i x_i‖_{L^p}`, `1 < p ≤ q < ∞`, for every seminorm on a real vector space;
* `External.HNVW.theorem6_2_4_seminorm`: for `p, q ∈ (1, ∞)` and every seminorm, with the explicit
  constant `κ_{p,q} = max (1, √((p − 1) / (q − 1)))` (`BanachProbability.kahaneKhintchineConst`),
  the form in which Cassese's Proposition 6.4 is stated here (no completeness is needed);
* `External.HNVW.theorem6_2_4`: the same for a real normed space `X`.

Only the real signs, and exponents greater than `1`, are stated, which is what Cassese uses. (The
package also has the exponents in `(0, 1]`, `BanachProbability.exists_kahaneKhintchine`.)

Proof: `BanachProbability.kahaneKhintchine_hypercontractive` and
`BanachProbability.kahaneKhintchine` in the package `BanachProbability`
(`lean4-banach-probability`), by the book's argument. For `1 < p ≤ q` it is the hypercontractivity
of the discrete heat semigroup `T (t)` (Theorem 6.2.2), since `T (t) f = e^{−t} f` for
`f = Σ ε_i x_i` and one takes `e^{−t} = √((p − 1) / (q − 1))`; the theorem is tensorised from
Bonami's two-point lemma (Lemma 6.2.3) in the space `L^q ({±1}^{n−1}; X)`. For `p ≥ q` the norms are
monotone.
-/

@[expose] public section

namespace External.HNVW

open BanachProbability BanachProbability.SignCube

/-- **HNVW II, Theorem 6.2.4** (Kahane–Khintchine, `κ_{q,p} ≤ √((q − 1) / (p − 1))` for real signs),
for seminorms: for every seminorm `S` on a real vector space, `1 < p ≤ q` and `x_1, …, x_n`,
`‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1)) ‖Σ ε_i x_i‖_{L^p}`. -/
theorem theorem6_2_4_hypercontractive {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Seminorm ℝ E)
    {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      √((q - 1) / (p - 1)) *
        SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) :=
  kahaneKhintchine_hypercontractive S hp hpq x

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
