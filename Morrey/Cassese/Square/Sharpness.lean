module

public import Morrey.Cassese.Defs
public import Morrey.Common.External.Osekowski.Sharpness

/-!
# The sharpness of Burkholder's constant for dyadic martingale transforms

`burkholderSharpness_holds`: for `p ∈ (1, ∞)` and `K < p* − 1` there are a dyadic (Paley–Walsh)
martingale `f_N = Σ_{k<N} ε_k φ_k` and predictable signs `σ_k` with
`‖Σ_{k<N} σ_k ε_k φ_k‖_{L^p} > K ‖f_N‖_{L^p}` (`BurkholderSharpness`, used for the lower bound of
Corollary 6.3). It is `External.Osekowski.exists_lt_lpNorm_transform`, in the paper's notation.
-/

@[expose] public section

namespace Cassese

/-- The sharpness of Burkholder's constant for dyadic martingale transforms, as used for the
lower bound of Corollary 6.3: for `p ∈ (1, ∞)` and `K < p* − 1` there are a real dyadic martingale
`f_N = Σ_{k<N} ε_k φ_k` (predictable `φ_k`) and predictable signs `σ_k` with
`‖Σ_{k<N} σ_k ε_k φ_k‖_{L^p} > K ‖f_N‖_{L^p}`.

How the paper cites it: the proof of Corollary 6.3 (TeX lines 2624–2633) takes "a dyadic martingale
`f_n` and `g_n` a `±1` transform of it" and says "by choosing the martingale-transform pair suitably
(see also [Cassese 2025, *Martingales, laminates and minimal Korn inequalities*, J. Math. Pures
Appl. 213]), this construction shows `C^{rc} (d) ≥ 4* − 1 = 3`"; it names no other source for the
sharpness (inventory E30). Theorem 2.3 of that paper (arXiv:2512.02784) is Burkholder's inequality,
quoted from Burkholder (Ann. Probab. 12 (1984)), "see [A. Osękowski, *Sharp Martingale and
Semimartingale Inequalities*, 2012] for an exposition", and says in a footnote that "no smaller
constant works among martingales defined on dyadic trees"; its dyadic trees may split with any
weights, while Corollary 6.3 needs the weights `1/2` of a Rademacher martingale. In this form the
sharpness is Osękowski 2012, Theorem 3.5 with Remark 3.8 and p. 138 (the best constants of
`±1`-transforms are already the best possible for dyadic martingales).

Proved by `burkholderSharpness_holds`, from `External.Osekowski.exists_lt_lpNorm_transform`, by
Osękowski's proof (the second approach, pp. 56–57, and the duality of p. 59). -/
def BurkholderSharpness : Prop :=
  ∀ p : ℝ, 1 < p → ∀ K : ℝ, K < pStar p - 1 →
    ∃ (N : ℕ) (φ σ : Fin N → (Fin N → Bool) → ℝ), IsPredictable φ ∧ IsPredictable σ ∧
      (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) ∧
      K * lpNormWith (fun x => |x|) p (mart φ N) <
        lpNormWith (fun x => |x|) p (mart (fun k ε => σ k ε * φ k ε) N)

/-- **The sharpness of Burkholder's constant** `p* − 1` for dyadic martingale transforms, the source
of the lower bound of Corollary 6.3. From `External.Osekowski.exists_lt_lpNorm_transform`: the
definitions of `Morrey/Cassese/Defs.lean` are those of the package, definitionally. -/
theorem burkholderSharpness_holds : BurkholderSharpness :=
  fun _ hp _ hK => External.Osekowski.exists_lt_lpNorm_transform hp hK

end Cassese
