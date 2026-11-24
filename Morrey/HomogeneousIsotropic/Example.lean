module

public import Morrey.HomogeneousIsotropic.Main

/-!
# An example: `F (A) = (det A)²`

The hypotheses of Theorem 1.1 are satisfied by integrands that are neither zero nor convex:
`detSq A = (det A)²` is nonnegative, isotropic, positively `4`-homogeneous and rank-one convex
(the determinant is affine along rank-one lines), and it is not convex. So
`polyconvex_of_rankOneConvex` applies to it (`polyconvex_detSq`); the support of Theorem 1.2 at
`diag (1, 1/2)` is `det A − 1/4` (`polyaffine_detSq_le`).
-/

@[expose] public section

open CalculusOfVariations

namespace HomogeneousIsotropic

/-- The integrand `A ↦ (det A)²` on `ℝ^{2×2}`. -/
noncomputable def detSq (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := A.det ^ 2

/-- `(det A)²` is nonnegative. -/
theorem detSq_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ detSq A := sq_nonneg _

/-- `(det A)²` is isotropic. -/
theorem isIsotropic_detSq : IsIsotropic detSq := by
  intro Q hQ R hR A
  have hQd : Q.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.1 hQ).2
  have hRd : R.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.1 hR).2
  simp [detSq, Matrix.det_mul, hQd, hRd]

/-- `(det A)²` is positively `4`-homogeneous. -/
theorem isPosHomogeneous_detSq : IsPosHomogeneous 4 detSq := by
  intro c hc A
  have h : (c • A).det = c ^ 2 * A.det := by
    rw [Matrix.det_smul]
    simp
  simp only [detSq, h]
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

/-- `(det A)²` is rank-one convex: the determinant is affine along rank-one lines. -/
theorem rankOneConvex_detSq : RankOneConvex detSq := by
  intro A B hB
  have hdet : B.det = 0 := (Matrix.rank_le_one_iff_det_eq_zero_of_fin_two B).1 (by omega)
  have key : ∀ t : ℝ, (A + t • B).det =
      A.det + t * (A 0 0 * B 1 1 + B 0 0 * A 1 1 - A 0 1 * B 1 0 - B 0 1 * A 1 0) := by
    intro t
    rw [Matrix.det_fin_two] at hdet
    simp [Matrix.det_fin_two]
    linear_combination t ^ 2 * hdet
  simp only [detSq, key]
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  obtain rfl : b = 1 - a := by linarith
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg ((x - y) *
    (A 0 0 * B 1 1 + B 0 0 * A 1 1 - A 0 1 * B 1 0 - B 0 1 * A 1 0)))]

/-- `(det A)²` is not convex: it vanishes at `diag (1, 0)` and `diag (0, 1)`, and not at their
midpoint. -/
theorem not_convexOn_detSq : ¬ ConvexOn ℝ Set.univ detSq := by
  intro h
  have h2 := h.2 (Set.mem_univ (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ))
    (Set.mem_univ (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp [detSq, Matrix.det_fin_two] at h2

/-- Theorem 1.1 applies to `(det A)²`, with `p = 4`. -/
theorem polyconvex_detSq : Polyconvex detSq :=
  polyconvex_of_rankOneConvex (p := 4) (by norm_num) detSq_nonneg isIsotropic_detSq
    isPosHomogeneous_detSq rankOneConvex_detSq

/-- Theorem 1.2 for `(det A)²` at `t = 1/2`, where `H = 1/4` and the slope is `m = 1`: the
polyaffine function with the multiplier `multiplier 4 (1/4) 1 (1/2)` lies below `(det A)²` and
touches it at `diag (1, 1/2)`. Here the multiplier is `1`, and the function is `det A − 1/4`. -/
theorem polyaffine_detSq_le :
    (∀ A, polyaffine (multiplier 4 (1 / 4) 1 (1 / 2) * (1 / 2) - (4 - 1) * (1 / 4))
        !![4 * (1 / 4) - 1 / 2 * 1 - multiplier 4 (1 / 4) 1 (1 / 2) * (1 / 2), 0;
          0, 1 - multiplier 4 (1 / 4) 1 (1 / 2)]
        (multiplier 4 (1 / 4) 1 (1 / 2)) A ≤ detSq A) ∧
      polyaffine (multiplier 4 (1 / 4) 1 (1 / 2) * (1 / 2) - (4 - 1) * (1 / 4))
        !![4 * (1 / 4) - 1 / 2 * 1 - multiplier 4 (1 / 4) 1 (1 / 2) * (1 / 2), 0;
          0, 1 - multiplier 4 (1 / 4) 1 (1 / 2)]
        (multiplier 4 (1 / 4) 1 (1 / 2)) !![1, 0; 0, 1 / 2] = 1 / 4 :=
  polyaffine_multiplier_le (p := 4) (F := detSq) (t := 1 / 2) (m := 1) (H := 1 / 4)
    (by norm_num) detSq_nonneg isIsotropic_detSq isPosHomogeneous_detSq rankOneConvex_detSq
    (by rw [abs_of_pos] <;> norm_num) (by simp [detSq, Matrix.det_fin_two]; norm_num)
    (by norm_num)
    (fun s _ _ => by simp [detSq, Matrix.det_fin_two]; nlinarith [sq_nonneg (s - 1 / 2)])

/-- The multiplier of the example is `1`. -/
theorem multiplier_detSq : multiplier 4 (1 / 4) 1 (1 / 2) = 1 := by
  norm_num [multiplier]

end HomogeneousIsotropic
