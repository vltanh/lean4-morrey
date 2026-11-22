module

public import BanachProbability.Martingale.Osekowski.Sharpness

/-!
# The constant `p* − 1` is the best possible, also for dyadic martingales (Osękowski, Theorem 3.5)

A. Osękowski, *Sharp Martingale and Semimartingale Inequalities*, Monografie Matematyczne 72,
Birkhäuser 2012 (read): Theorem 3.5 (ii), "the constant is the best possible" (p. 53), and for
dyadic martingales Remark 3.8 (p. 137) with p. 138, "the best constant in Paley's inequality (3.212)
is equal to `p* − 1`, both in the real and the Hilbert-space-valued case". Cassese
(arXiv:2608.03488v3) uses the dyadic form in the proof of the lower bound of Corollary 6.3 (TeX
lines 2624–2633), where the only source he names is "see also" his own paper *Martingales, laminates
and minimal Korn inequalities* (arXiv:2512.02784; J. Math. Pures Appl. 213 (2026)), whose Theorem
2.3 quotes Burkholder (Ann. Probab. 12 (1984)) for the inequality, "see [Osękowski 2012] for an
exposition", and says that it is sharp: "no smaller constant works among martingales defined on
dyadic trees such that `‖dX_i‖ = ‖dY_i‖`".

## Main results

On the sign cube, `1 < p < ∞`, `p* = max (p, p / (p − 1))`:

* `dyadicUMDConst_real`: `UMD_p^Δ (ℝ) = p* − 1`, and `dyadicUMDConst_of_innerProductSpace`: the same
  for every real Hilbert space `H ≠ 0` (Remark 3.8, p. 138); `umdConst_of_innerProductSpace`:
  `UMD_p (H) = p* − 1` (Theorem 3.5 for `±1`-transforms; p. 121);
* `exists_lt_lpNorm_transform`: for `K < p* − 1` there are a real Paley–Walsh martingale
  `f = Σ ε_k φ_k` and a transform `g = Σ σ_k ε_k φ_k` of `f` by predictable signs with
  `K ‖f‖_p < ‖g‖_p`, the form that Corollary 6.3 uses.

The signs are predictable, as in Cassese's Definition 2.5. The book's `±1`-transforms are by a
deterministic sequence of signs, and in the dyadic case (Haar series) by one sign for each Haar
function; on the sign cube, a coefficient and a sign for each Haar function are a predictable `φ_k`
and a predictable `σ_k`.

## The proof

In the package `BanachProbability` (`lean4-banach-probability`,
`BanachProbability.Osekowski.exists_lt_lpNorm_transform` and the three statements on constants), by
the book's argument: for `1 < p ≤ 2` the second approach (pp. 56–57), for `p > 2` duality (p. 59).
The second approach is run on the function `W⁰` of the proof of Theorem 3.34 (p. 137), the supremum
of `E |g|^p − β^p E |f|^p` over the *dyadic* pairs started at `(x, y)`, instead of the supremum `U⁰`
over all simple pairs. The book passes from `U⁰` to the dyadic pairs by showing that `W⁰` has the
same properties 1°, 2°, 3° (Theorem 3.34 itself is not formalized).
-/

@[expose] public section

namespace External.Osekowski

open BanachProbability BanachProbability.SignCube

/-- **Osękowski (2012), Theorem 3.5 and Remark 3.8**: the dyadic `UMD_p` constant of `ℝ` is
`p* − 1`, `1 < p < ∞`. -/
theorem dyadicUMDConst_real {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst ℝ p = ENNReal.ofReal (pStar p - 1) :=
  BanachProbability.Osekowski.dyadicUMDConst_real hp

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [Nontrivial H]

/-- **Osękowski (2012), p. 138**: the dyadic `UMD_p` constant of a real Hilbert space `H ≠ 0` is
`p* − 1`, `1 < p < ∞`. -/
theorem dyadicUMDConst_of_innerProductSpace {p : ℝ} (hp : 1 < p) :
    dyadicUMDConst H p = ENNReal.ofReal (pStar p - 1) :=
  BanachProbability.Osekowski.dyadicUMDConst_of_innerProductSpace hp

/-- **Osękowski (2012), Theorem 3.5** (for `±1`-transforms; p. 121): the `UMD_p` constant of a real
Hilbert space `H ≠ 0` is `p* − 1`, `1 < p < ∞`. -/
theorem umdConst_of_innerProductSpace {p : ℝ} (hp : 1 < p) :
    umdConst H p = ENNReal.ofReal (pStar p - 1) :=
  BanachProbability.Osekowski.umdConst_of_innerProductSpace hp

end Hilbert

/-- **No constant below `p* − 1`** holds for the transforms of dyadic martingales by signs
(Osękowski 2012, Theorem 3.5, Remark 3.8): for `1 < p < ∞` and `K < p* − 1` there are a real
Paley–Walsh martingale `f = Σ ε_k φ_k` and a transform `g = Σ σ_k ε_k φ_k` of `f` by predictable
signs with `K ‖f‖_p < ‖g‖_p`. -/
theorem exists_lt_lpNorm_transform {p K : ℝ} (hp : 1 < p) (hK : K < pStar p - 1) :
    ∃ (N : ℕ) (φ σ : Fin N → (Fin N → Bool) → ℝ), IsPredictable φ ∧ IsPredictable σ ∧
      (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) ∧
        K * SignCube.lpNorm (fun x => |x|) p (paleyWalsh φ N) <
          SignCube.lpNorm (fun x => |x|) p (paleyWalsh (fun k ε => σ k ε * φ k ε) N) :=
  BanachProbability.Osekowski.exists_lt_lpNorm_transform hp hK

end External.Osekowski
