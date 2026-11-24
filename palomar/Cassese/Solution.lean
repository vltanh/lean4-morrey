module

public import Morrey.Cassese.Introduction

/-!
# Solution

The statements of `palomar/Cassese/Challenge.lean`, word for word, proved from the library.
`theorem1_2` is proved by `Cassese.theorem1_2`, the paper's proof (Section 4.4); `theorem1_4` by
`Cassese.theorem1_4`, the paper's proof (Section 6); `theorem1_4_four` by the paper's proof for
`p = 4` in Section 6.3 (`Cassese.theorem1_4_four`).
-/

@[expose] public section

namespace CasseseChallenge

open Cassese

theorem theorem1_2 {p : ℝ} (hp : 1 < p) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ f : Matrix (Fin 2) (Fin m) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f :=
  Cassese.theorem1_2 hp

theorem theorem1_3_a :
    ∃ P : Matrix (Fin 2) (Fin 3) ℝ → ℝ,
      IsHomogeneousPolynomial 4 P ∧ RankOneConvex P ∧ NowhereQuasiconvex P :=
  Cassese.theorem1_3_a

theorem theorem1_3_b :
    ∃ ε > 0, ∀ p : ℝ, |p - 4| < ε → ∃ f : Matrix (Fin 2) (Fin 3) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f :=
  Cassese.theorem1_3_b

theorem theorem1_4 {p : ℝ} (hp : 1 < p) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ f : Matrix (Fin d) (Fin d) ℝ → ℝ,
      IsIntegrand f ∧ IsConjugationInvariant f ∧ IsTranspositionInvariant f ∧
        IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f :=
  Cassese.theorem1_4 hp

theorem theorem1_4_four : ∀ d ≥ 588, ∃ f : Matrix (Fin d) (Fin d) ℝ → ℝ,
    IsIntegrand f ∧ IsConjugationInvariant f ∧ IsTranspositionInvariant f ∧
      IsPHomogeneous 4 f ∧ RankOneConvex f ∧ NowhereQuasiconvex f :=
  Cassese.theorem1_4_four

theorem theorem1_5 {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) :
    ∃ f : Matrix (Fin 4) (Fin 2) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f :=
  Cassese.theorem1_5 hp hp2

theorem corollary1_6 :
    ∃ f : Matrix (Fin 4) (Fin 4) ℝ → ℝ, IsIntegrand f ∧ (∀ A, 0 ≤ f A) ∧ IsPHomogeneous 1 f ∧
      RankOneConvex f ∧ ∃ A : Matrix (Fin 4) (Fin 4) ℝ, A.rank = 2 ∧ ¬ QuasiconvexAt f A :=
  Cassese.corollary1_6

theorem corollary5_3 :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      IsHomogeneousPolynomial 4 (qHat δ (K / δ)) ∧ RankOneConvex (qHat δ (K / δ)) ∧
        NowhereQuasiconvex (qHat δ (K / δ)) :=
  Cassese.corollary5_3

theorem morrey_landscape {d m : ℕ} (hd : 2 ≤ d)
    (hm : 2 ≤ m) (h22 : ¬ (d = 2 ∧ m = 2)) :
    ∃ f : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand f ∧ RankOneConvex f ∧ ¬ Quasiconvex f :=
  Cassese.morrey_landscape hd hm h22

theorem homMorrey_landscape {d m : ℕ}
    (hd : 2 ≤ d) (hm : 2 ≤ m) (h22 : ¬ (d = 2 ∧ m = 2)) :
    ∃ f : Matrix (Fin d) (Fin m) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous 4 f ∧ RankOneConvex f ∧ ¬ QuasiconvexAt f 0 :=
  Cassese.homMorrey_landscape hd hm h22

theorem projL3_mem (A : Matrix (Fin 2) (Fin 3) ℝ) : projL3 A ∈ L3 :=
  Cassese.projL3_mem A

end CasseseChallenge
