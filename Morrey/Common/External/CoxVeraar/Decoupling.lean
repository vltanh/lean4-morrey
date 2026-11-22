module

public import BanachProbability.UMD.Decoupling

/-!
# Decoupling with the constant `β_{p,X}` (Cox–Veraar 2007)

S. Cox, M. Veraar, *Some remarks on tangent martingale difference sequences in `L¹`-spaces*,
Electron. Commun. Probab. 12 (2007) (arXiv:0801.0695), introduction, which Cassese
(arXiv:2608.03488v3) cites, with T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach
Spaces. Volume I* (HNVW I, 2016; read), Proposition 4.2.3 (p. 282), for Proposition 2.8 (decoupling,
TeX lines 875–896, (6)). Cox–Veraar recall that in a UMD space `X` a martingale difference sequence
and a decoupled tangent sequence of it have comparable `L^p` norms, `p ∈ (1, ∞)`, and that one may
take the constant `β_{p,X} = UMD_p (X)`; they credit the result to T. R. McConnell (1989) and,
independently, P. Hitczenko, and the proof from the definition to S. Montgomery-Smith.

Cassese uses the case of Paley–Walsh martingales: `dY_k = ε_k ξ_k` with predictable `ξ_k`, whose
decoupled tangent sequence is `ε̃_k ξ_k` with an independent copy `ε̃` of the signs. Only this
case is stated:

* `External.CoxVeraar.decoupling`: `‖Ỹ_n‖_{L^p} ≤ UMD_p (X) ‖Y_n‖_{L^p}` and
  `‖Y_n‖_{L^p} ≤ UMD_p (X) ‖Ỹ_n‖_{L^p}` for a real Banach space `X`, on the canonical spaces
  `{±1}^N` and `{±1}^N × {±1}^N`.

HNVW I, Proposition 4.2.3 (the randomised UMD property) is, for `X`-valued martingales `f` and
Rademacher signs `r_n` on a further probability space, the comparison of `Σ r_n df_n` with `Σ df_n`
in both directions, with constants at most `β_{p,X}`. The inequalities above are its case of
Paley–Walsh martingales: `df_k = ε_k ξ_k`, and for fixed `ε` the signs `r_k ε_k` have the law of
`ε̃_k`.

Proof: `BanachProbability.decoupling` in the package `BanachProbability`
(`lean4-banach-probability`), by the argument of HNVW I (the proof of Proposition 4.1.16, pp.
279–280, of which Proposition 4.2.3 is a corollary): for fixed values of the signs `r_k`,
`Σ r_k ε_k ξ_k` is the transform of `Σ ε_k ξ_k` by constant signs, and conversely; raise to the
power `p` and average over the signs. Cox–Veraar give no proof in their introduction, and attribute
one from the definition to S. Montgomery-Smith.
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
