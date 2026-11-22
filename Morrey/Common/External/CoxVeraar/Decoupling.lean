module

public import BanachProbability.UMD.Decoupling

/-!
# Decoupling with the constant `β_{p,X}` (Cox–Veraar 2007)

S. Cox, M. Veraar, *Some remarks on tangent martingale difference sequences in `L¹`-spaces*,
Electron. Commun. Probab. 12 (2007) (arXiv:0801.0695), introduction, which Cassese
(arXiv:2608.03488v3) cites, with HNVW I, Proposition 4.2.3, for Proposition 2.8 (decoupling, TeX
lines 875–896, (6)). Cox–Veraar recall that in a UMD space `X` a martingale difference sequence
and a decoupled tangent sequence of it have comparable `L^p` norms, `p ∈ (1, ∞)`, and that one may
take the constant `β_{p,X} = UMD_p (X)`; they credit the result to T. R. McConnell (1989) and,
independently, P. Hitczenko, and the proof from the definition to S. Montgomery-Smith.

Cassese uses the case of Paley–Walsh martingales: `dY_k = ε_k ξ_k` with predictable `ξ_k`, whose
decoupled tangent sequence is `ε̃_k ξ_k` with an independent copy `ε̃` of the signs. Only this
case is stated:

* `External.CoxVeraar.decoupling`: `‖Ỹ_n‖_{L^p} ≤ UMD_p (X) ‖Y_n‖_{L^p}` and
  `‖Y_n‖_{L^p} ≤ UMD_p (X) ‖Ỹ_n‖_{L^p}` for a real Banach space `X`, on the canonical spaces
  `{±1}^N` and `{±1}^N × {±1}^N`.

Proof: `BanachProbability.decoupling` in the package `BanachProbability`
(`lean4-banach-probability`, required by path while it is developed), the proof from the definition
that Cox–Veraar attribute to Montgomery-Smith: with `η_k = ε_k ε̃_k`, `Σ ε̃_k ξ_k` is the transform
of `Σ ε_k ξ_k` by the predictable signs `η_k` in the interleaved order `η_0, ε_0, η_1, ε_1, …` of
the doubled cube, and conversely; then Maurey's theorem (`UMD^Δ_p = UMD_p`). The same statement is
HNVW I, Proposition 4.2.3, which Cassese cites with it; it is not stated separately.
-/

@[expose] public section

open scoped ENNReal

namespace External.CoxVeraar

open BanachProbability BanachProbability.SignCube

/-- **Cox–Veraar (2007)**, decoupling with the constant `β_{p,X} = UMD_p (X)`, for Paley–Walsh
martingales: for predictable `ξ_k` in a real Banach space `X` and `p ∈ (1, ∞)`,
`‖Σ_{k<n} ε̃_k ξ_k‖_{L^p} ≤ UMD_p (X) ‖Σ_{k<n} ε_k ξ_k‖_{L^p}` and
`‖Σ_{k<n} ε_k ξ_k‖_{L^p} ≤ UMD_p (X) ‖Σ_{k<n} ε̃_k ξ_k‖_{L^p}`. -/
theorem decoupling {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {p : ℝ} (hp : 1 < p) {N : ℕ} (ξ : Fin N → (Fin N → Bool) → X) (hξ : IsPredictable ξ)
    (n : ℕ) :
    ENNReal.ofReal (decoupledLpNorm p ξ n) ≤
        umdConst X p * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ∧
      ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (paleyWalsh ξ n)) ≤
        umdConst X p * ENNReal.ofReal (decoupledLpNorm p ξ n) :=
  BanachProbability.decoupling hp ξ hξ n

end External.CoxVeraar
