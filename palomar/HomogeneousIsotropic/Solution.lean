module

public import Morrey.HomogeneousIsotropic.Signed.Main
public import Morrey.HomogeneousIsotropic.Bridges

/-!
# Solution

The statements of `palomar/HomogeneousIsotropic/Challenge.lean`, word for word, proved from the
library. The library's proofs use the rank-one convexity and the quasiconvexity of the package
`CalculusOfVariations`; `Morrey/HomogeneousIsotropic/Bridges.lean` identifies them with the
Challenge's. The quasiconvexity of the truncated determinant, on which Theorem A, Proposition 6.8
and Corollary 1.6 (a) rest, comes from the package lean4-iwaniec.
-/

@[expose] public section

namespace HomogeneousIsotropicChallenge

open HomogeneousIsotropic

theorem det_eq_norm_sq_sub (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = ‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2 :=
  HomogeneousIsotropic.det_eq_norm_sq_sub A

theorem opNorm_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    opNorm A = ‖conformalPart A‖ + ‖anticonformalPart A‖ :=
  HomogeneousIsotropic.opNorm_eq A

theorem theorem1_1 {p : ℝ} (hp : 2 ≤ p) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (h0 : ∀ A, 0 ≤ F A)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : IsRankOneConvex F) :
    (∀ A₀, HasPolyaffineSupportAt F A₀) ∧ Polyconvex F :=
  ⟨fun A₀ => hasPolyaffineSupportAt_of_rankOneConvex hp h0 hiso hhom
      ((isRankOneConvex_iff F).1 hrc) A₀,
    polyconvex_of_rankOneConvex hp h0 hiso hhom ((isRankOneConvex_iff F).1 hrc)⟩

theorem theorem1_2 {p : ℝ} (hp : 2 ≤ p) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (h0 : ∀ A, 0 ≤ F A)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : IsRankOneConvex F) {t m H : ℝ}
    (ht : |t| < 1) (hH : F !![1, 0; 0, t] = H) (hHpos : 0 < H)
    (hm : ∀ s : ℝ, -1 ≤ s → s ≤ 1 → H + m * (s - t) ≤ F !![1, 0; 0, s]) :
    (∀ A, polyaffine (multiplier p H m t * t - (p - 1) * H)
        !![p * H - t * m - multiplier p H m t * t, 0; 0, m - multiplier p H m t]
        (multiplier p H m t) A ≤ F A) ∧
      polyaffine (multiplier p H m t * t - (p - 1) * H)
        !![p * H - t * m - multiplier p H m t * t, 0; 0, m - multiplier p H m t]
        (multiplier p H m t) !![1, 0; 0, t] = H :=
  polyaffine_multiplier_le hp h0 hiso hhom ((isRankOneConvex_iff F).1 hrc) ht hH hHpos hm

theorem theorem1_3_a {p : ℝ} (hp : 2 < p) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) :
    Polyconvex F ↔ IsRankOneConvex F ∧ ∀ A, 0 ≤ F A :=
  (polyconvex_iff_of_two_lt hp hiso hhom).trans
    (and_congr (isRankOneConvex_iff F).symm Iff.rfl)

theorem theorem1_3_b {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous 2 F) : Polyconvex F ↔ IsRankOneConvex F :=
  (polyconvex_iff_two hiso hhom).trans (isRankOneConvex_iff F).symm

theorem corollary1_4 {p : ℝ} (hp : 2 ≤ p) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hm : Measurable F)
    (hb : ∀ A, ∃ U ∈ nhds A, ∃ C : ℝ, ∀ B ∈ U, |F B| ≤ C) :
    List.TFAE [IsRankOneConvex F, IsQuasiconvex F, Polyconvex F] := by
  rw [isRankOneConvex_iff F, isQuasiconvex_iff F]
  exact tfae_of_two_le hp h0 hiso hhom hm hb

theorem theorem1_5 {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : IsRankOneConvex F) (A₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ c₀ m : ℝ, (2 - p) * |m| ≤ p * c₀ ∧ (∀ A, burkholderType p c₀ m A ≤ F A) ∧
      burkholderType p c₀ m A₀ = F A₀ :=
  exists_burkholderType_le hp1 hp2 h0 hiso hhom ((isRankOneConvex_iff F).1 hrc) A₀

theorem theorem1_5_identity {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) (c₀ m : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderType p c₀ m A =
      (p * c₀ + (2 - p) * m) / (2 * (2 - p)) * burkholder p A +
        (p * c₀ - (2 - p) * m) / (2 * (2 - p)) * burkholder p (reflection * A) :=
  burkholderType_eq hp0 hp2 c₀ m A

theorem corollary1_6_a {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : IsRankOneConvex F) : IsQuasiconvex F :=
  (isQuasiconvex_iff F).2 (quasiconvex_of_rankOneConvex_of_lt_two hp1 hp2 h0 hiso hhom
    ((isRankOneConvex_iff F).1 hrc))

theorem corollary1_6_b {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous 1 F) (hrc : IsRankOneConvex F) :
    (∀ A, 0 ≤ F A) ∧ ConvexOn ℝ Set.univ F :=
  ⟨nonneg_of_rankOneConvex_one hiso hhom ((isRankOneConvex_iff F).1 hrc),
    convexOn_of_rankOneConvex_one hiso hhom ((isRankOneConvex_iff F).1 hrc)⟩

theorem proposition1_7 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hhom : IsPosHomogeneous p F) (hrc : IsRankOneConvex F) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    F A = 0 :=
  eq_zero_of_rankOneConvex_of_lt_one hp0 hp1 hhom ((isRankOneConvex_iff F).1 hrc) A

theorem theoremA {p : ℝ} (hp : 0 < p) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous p F) (hrc : IsRankOneConvex F) : IsQuasiconvex F :=
  (isQuasiconvex_iff F).2 (quasiconvex_of_rankOneConvex_of_isotropic hp hiso hhom
    ((isRankOneConvex_iff F).1 hrc))

theorem proposition6_8 {e : ℝ} (he : e = 1 ∨ e = -1) {N : ℝ → ℝ} (hN : ConvexOn ℝ (Set.Ici 0) N)
    (hNc : Continuous N) (hN0 : N 0 ≤ 0) : IsQuasiconvex (radial e N) :=
  (isQuasiconvex_iff _).2 (quasiconvex_radial he hN hNc hN0)

end HomogeneousIsotropicChallenge
