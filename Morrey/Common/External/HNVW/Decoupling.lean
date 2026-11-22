module

public import BanachProbability.UMD.Decoupling

/-!
# Decoupling of Paley–Walsh martingales (HNVW I, Proposition 4.2.3)

T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I* (2016),
Proposition 4.2.3, which Cassese (arXiv:2608.03488v3) cites, with Cox–Veraar (2007), for
Proposition 2.8 (decoupling, TeX lines 875–896, (6)): for a real Banach space `X`, `p ∈ (1, ∞)`,
a Paley–Walsh martingale `Y_n = Σ_{k<n} ε_k ξ_k` with predictable `ξ_k` (`ξ_k` depends on
`ε_0, …, ε_{k−1}` only), and its decoupled version `Ỹ_n = Σ_{k<n} ε̃_k ξ_k` with an independent
copy `ε̃` of the signs,
`UMD_p (X)⁻¹ ‖Ỹ_n‖_{L^p} ≤ ‖Y_n‖_{L^p} ≤ UMD_p (X) ‖Ỹ_n‖_{L^p}`. The book was not accessible; the
statement is the one Cassese quotes.

* `External.HNVW.proposition4_2_3`: the statement, on the canonical spaces `{±1}^N` and
  `{±1}^N × {±1}^N` (`BanachProbability.SignCube.paleyWalsh`,
  `BanachProbability.decoupledLpNorm`).

Proof: `BanachProbability.decoupling` in the package `BanachProbability`, the standard argument
from the definition (credited by Cox–Veraar to S. Montgomery-Smith): with `η_k = ε_k ε̃_k`,
`(ε, ε̃) ↦ (ε, η)` preserves the uniform measure, and in the interleaved order
`η_0, ε_0, η_1, ε_1, …` of the doubled cube `Σ ε̃_k ξ_k` is the transform of `Σ ε_k ξ_k` by the
predictable signs `η_k`, and conversely; then Maurey's theorem (`UMD^Δ_p = UMD_p`).
-/

@[expose] public section

open scoped ENNReal

namespace External.HNVW

open BanachProbability BanachProbability.SignCube

/-- **HNVW I, Proposition 4.2.3** (decoupling): for a Paley–Walsh martingale `Σ_{k<n} ε_k ξ_k`
with predictable `ξ_k` in a real Banach space `X`, `p ∈ (1, ∞)`, and its decoupled version
`Σ_{k<n} ε̃_k ξ_k`, `‖Ỹ_n‖_{L^p} ≤ UMD_p (X) ‖Y_n‖_{L^p}` and
`‖Y_n‖_{L^p} ≤ UMD_p (X) ‖Ỹ_n‖_{L^p}`. -/
theorem proposition4_2_3 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {p : ℝ} (hp : 1 < p) {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (hξ : IsPredictable ξ)
    (n : ℕ) :
    ENNReal.ofReal (decoupledLpNorm p ξ n) ≤
        umdConst X p * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ≤
        umdConst X p * ENNReal.ofReal (decoupledLpNorm p ξ n) :=
  decoupling hp ξ hξ n

end External.HNVW
