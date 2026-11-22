module

public import BanachProbability.KahaneKhintchine.Basic

/-!
# Vector-valued hypercontractivity of Rademacher sums (Borell 1979)

C. Borell, *On the integrability of Banach space valued Walsh polynomials*, Séminaire de
Probabilités XIII, Lecture Notes in Math. 721 (1979), 1–3: the hypercontractivity of the
Rademacher semigroup for Banach-valued Walsh polynomials. For Rademacher sums it gives the
hypercontractive Kahane–Khintchine bound
`‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1)) ‖Σ ε_i x_i‖_{L^p}`, `1 < p ≤ q < ∞`, that is,
`k_{q,p} ≤ √((q − 1) / (p − 1))` in Cassese's Proposition 6.4. Cassese (arXiv:2608.03488v3) uses
constants that grow at most polynomially in `q` in Remark 6.3 (TeX lines 2425–2437) and in the
case `q = ∞` of Proposition 6.5 (TeX lines 2477–2479), without naming a source for that growth
(inventory E27); this is the standard bound, Borell's Theorem 1.1 for `d = 1` (the paper was read,
on Numdam).

* `External.Borell.hypercontractive_affine`: for a seminorm `S` on a real vector space,
  `1 < p ≤ q`, `ρ = √((p − 1) / (q − 1))`, `c` and `x_1, …, x_n`,
  `‖c + ρ Σ ε_i x_i‖_{L^q} ≤ ‖c + Σ ε_i x_i‖_{L^p}` (the noise operator `T_ρ` on Walsh polynomials
  of degree at most `1`);
* `External.Borell.kahaneKhintchine_hypercontractive`: its case `c = 0`, the bound above.

Proof: `BanachProbability.hypercontractive_affine` and
`BanachProbability.kahaneKhintchine_hypercontractive` in the package `BanachProbability`
(`lean4-banach-probability`, required by path while it is developed), by the argument of Borell's
§2: the elementary two-point inequality for Borell's operator `K̄` (from the nonnegative case,
A. Bonami (*Étude des coefficients de Fourier des fonctions de `L^p (G)`*, Ann. Inst. Fourier 20
(1970)) in the proof of R. O'Donnell, *Analysis of Boolean Functions* (2014), §10.1, after
S. Janson, and O'Donnell's Exercise 9.7), its tensorisation to `⊗ⁿ K̄` (the Segal lemma that
Borell cites, by the induction of O'Donnell's Exercise 10.3 with Minkowski's inequality, Exercise
10.1), the positivity of the kernel for the passage to seminormed spaces, and
`(⊗ⁿ K̄) (c + Σ ε_i x_i) = c + ρ Σ ε_i x_i`.
-/

@[expose] public section

namespace External.Borell

open BanachProbability BanachProbability.SignCube

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Borell (1979)**, hypercontractivity on Walsh polynomials of degree at most `1`: for a
seminorm `S` on a real vector space, `1 < p ≤ q`, `c` and `x_1, …, x_n`,
`‖c + √((p − 1) / (q − 1)) Σ ε_i x_i‖_{L^q} ≤ ‖c + Σ ε_i x_i‖_{L^p}`. -/
theorem hypercontractive_affine (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (c : E)
    {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S q
        (fun ε : Fin n → Bool => c + √((p - 1) / (q - 1)) • ∑ i, coin (ε i) • x i) ≤
      SignCube.lpNorm S p (fun ε : Fin n → Bool => c + ∑ i, coin (ε i) • x i) :=
  BanachProbability.hypercontractive_affine S hp hpq c x

/-- **The hypercontractive Kahane–Khintchine bound** (Borell 1979): for a seminorm `S` on a real
vector space, `1 < p ≤ q` and `x_1, …, x_n`,
`‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1)) ‖Σ ε_i x_i‖_{L^p}`. -/
theorem kahaneKhintchine_hypercontractive (S : Seminorm ℝ E) {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q)
    {n : ℕ} (x : Fin n → E) :
    SignCube.lpNorm S q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
      √((q - 1) / (p - 1)) *
        SignCube.lpNorm S p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) :=
  BanachProbability.kahaneKhintchine_hypercontractive S hp hpq x

end External.Borell
