module

public import Morrey.Common.Basic.CalculusOfVariations.LegendreHadamard
public import Morrey.Pedregal.Bridges

/-!
# Acceptance of a planar negative certificate

The hypotheses require a global Legendre–Hadamard certificate and a strict integral violation
for an actual periodic Lipschitz map. No degree, grid, moment, or finite-support condition is
substituted for these hypotheses. This theorem is an acceptance interface; it supplies no
candidate satisfying its hypotheses.
-/

@[expose] public section

open MeasureTheory

namespace Pedregal

/-- A global Hessian certificate and a genuine periodic gradient gap contradict the universal
planar Morrey implication in the shared calculus-of-variations definitions. -/
theorem not_cov_morrey_of_lh_periodic_gap
    {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hLH : ∀ A H : Matrix (Fin 2) (Fin 2) ℝ, H.rank = 1 →
      0 ≤ iteratedFDeriv ℝ 2 f A (fun _ => H))
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (K : NNReal) (hφ : LipschitzWith K φ)
    (hper : ∀ (x : Fin 2 → ℝ) (z : Fin 2 → ℤ),
      φ (x + fun i => (z i : ℝ)) = φ x)
    (hgap : (∫ x in CalculusOfVariations.unitCube 2,
      f (A + CalculusOfVariations.grad φ x)) < f A) :
    ¬ (∀ g : Matrix (Fin 2) (Fin 2) ℝ → ℝ,
      CalculusOfVariations.RankOneConvex g → CalculusOfVariations.Quasiconvex g) := by
  intro h
  have hrc : CalculusOfVariations.RankOneConvex f :=
    CalculusOfVariations.rankOneConvex_of_iteratedFDeriv_nonneg hf hLH
  exact (not_quasiconvex_of_periodic_gap hf.continuous A φ K hφ hper hgap)
    (quasiconvex_of_cov_quasiconvex hf.continuous (h f hrc))

end Pedregal
