module

public import Sverak.Lemma1
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Šverák 1992, Section 2: the subspace `L`, the function `f` and the map `w`

* `ofRST r s t = (r 0; 0 s; t t)`, `L` the subspace of these matrices, `sverakP` (in
  `Sverak.Defs`) the orthogonal projection onto `L` (`sverakP_mem`, `sverakP_of_mem`,
  `sverakP_orth`).
* (3): `sverakf (ofRST r s t) = −(r s t)` (`sverakf_ofRST`); `sverakf X` (in `Sverak.Defs`) is
  `f (P X)`, so `sverakf` is the paper's `f` on `L`, where `P` is the identity.
* `rank_ofRST_eq_one`, `sverakf_affine_of_rankOne` (`sv-L`): "the only rank-one directions in `L`
  are" the three coordinate directions, "therefore the function `f` is convex (in fact linear) on
  each rank-one line contained in `L`".
* `w (x) = (2π)⁻¹ (sin 2πx₁, sin 2πx₂, sin 2π(x₁ + x₂))`, smooth and periodic, with
  `D w (x) ∈ L` (`jac_w`).
* `equation4` (`sv-eq4`): `∫_{[0,1]²} f (D w) = −∫ (cos 2πx₁)² (cos 2πx₂)² < 0 = f (0)`.
-/

@[expose] public section

open MeasureTheory Real

namespace Sverak

/-- The matrix `(r 0; 0 s; t t)`. -/
def ofRST (r s t : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![r, 0; 0, s; t, t]

/-- Šverák's subspace `L = {(r 0; 0 s; t t) : r, s, t ∈ ℝ}` of `M^{3×2}`. -/
def L : Set (Matrix (Fin 3) (Fin 2) ℝ) :=
  Set.range fun p : ℝ × ℝ × ℝ => ofRST p.1 p.2.1 p.2.2

theorem sverakP_mem (X : Matrix (Fin 3) (Fin 2) ℝ) : sverakP X ∈ L := by
  refine ⟨(X 0 0, X 1 1, (X 2 0 + X 2 1) / 2), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofRST, sverakP]

theorem sverakP_of_mem {X : Matrix (Fin 3) (Fin 2) ℝ} (hX : X ∈ L) : sverakP X = X := by
  obtain ⟨⟨r, s, t⟩, rfl⟩ := hX
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofRST, sverakP]

/-- `X − P X` is orthogonal to `L` for the Frobenius inner product: `P` is the orthogonal
projection onto `L`. -/
theorem sverakP_orth (X : Matrix (Fin 3) (Fin 2) ℝ) {Y : Matrix (Fin 3) (Fin 2) ℝ} (hY : Y ∈ L) :
    ∑ i, ∑ j, (X - sverakP X) i j * Y i j = 0 := by
  obtain ⟨⟨r, s, t⟩, rfl⟩ := hY
  simp [sverakP, ofRST, Fin.sum_univ_succ]
  ring

theorem sverakf_ofRST (r s t : ℝ) : sverakf (ofRST r s t) = -(r * s * t) := by
  simp [sverakf, sverakP, ofRST]

/-- A nonzero entry gives rank at least one (a nonzero `1 × 1` minor). -/
private theorem con_one_le_rank {A : Matrix (Fin 3) (Fin 2) ℝ} (i : Fin 3) (j : Fin 2)
    (h : A i j ≠ 0) : 1 ≤ A.rank := by
  have := A.rank_submatrix_le (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)
  rwa [Matrix.rank_of_det_ne_zero (by simpa [Matrix.det_unique] using h), Fintype.card_fin]
    at this

/-- A nonzero `2 × 2` minor gives rank at least two. -/
private theorem con_two_le_rank {A : Matrix (Fin 3) (Fin 2) ℝ} (i₀ i₁ : Fin 3)
    (h : A i₀ 0 * A i₁ 1 - A i₀ 1 * A i₁ 0 ≠ 0) : 2 ≤ A.rank := by
  have := A.rank_submatrix_le ![i₀, i₁] id
  rwa [Matrix.rank_of_det_ne_zero (by rw [Matrix.det_fin_two]; simpa using h), Fintype.card_fin]
    at this

/-- (`sv-L`) The rank-one matrices of `L` are the nonzero multiples of the three directions
`(1 0; 0 0; 0 0)`, `(0 0; 0 1; 0 0)`, `(0 0; 0 0; 1 1)`. -/
theorem rank_ofRST_eq_one (r s t : ℝ) :
    (ofRST r s t).rank = 1 ↔
      (r ≠ 0 ∧ s = 0 ∧ t = 0) ∨ (r = 0 ∧ s ≠ 0 ∧ t = 0) ∨ (r = 0 ∧ s = 0 ∧ t ≠ 0) := by
  constructor
  · -- the `2 × 2` minors are `r s`, `r t` and `−s t`, and the matrix is nonzero
    intro h
    have h2 : ∀ i₀ i₁ : Fin 3, ofRST r s t i₀ 0 * ofRST r s t i₁ 1 -
        ofRST r s t i₀ 1 * ofRST r s t i₁ 0 = 0 := fun i₀ i₁ => by
      by_contra hne
      have := con_two_le_rank i₀ i₁ hne
      omega
    have hrs := h2 0 1
    have hrt := h2 0 2
    have hst := h2 1 2
    simp [ofRST] at hrs hrt hst
    by_cases hr : r = 0 <;> by_cases hs : s = 0 <;> by_cases ht : t = 0 <;> simp_all
    subst hr hs ht
    have h0 : ofRST 0 0 0 = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [h0, Matrix.rank_zero] at h
    exact absurd h (by norm_num)
  · -- each of the three directions is an outer product `u vᵀ`
    rintro (⟨hr, rfl, rfl⟩ | ⟨rfl, hs, rfl⟩ | ⟨rfl, rfl, ht⟩)
    · have he : ofRST r 0 0 = Matrix.vecMulVec ![r, 0, 0] ![1, 0] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [ofRST, Matrix.vecMulVec]
      exact le_antisymm (he ▸ Matrix.rank_vecMulVec_le _ _)
        (con_one_le_rank 0 0 (by simpa [ofRST] using hr))
    · have he : ofRST 0 s 0 = Matrix.vecMulVec ![0, s, 0] ![0, 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [ofRST, Matrix.vecMulVec]
      exact le_antisymm (he ▸ Matrix.rank_vecMulVec_le _ _)
        (con_one_le_rank 1 1 (by simpa [ofRST] using hs))
    · have he : ofRST 0 0 t = Matrix.vecMulVec ![0, 0, t] ![1, 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [ofRST, Matrix.vecMulVec]
      exact le_antisymm (he ▸ Matrix.rank_vecMulVec_le _ _)
        (con_one_le_rank 2 0 (by simpa [ofRST] using ht))

/-- (`sv-L`) The function `f` is affine on each rank-one line contained in `L`. -/
theorem sverakf_affine_of_rankOne {A B : Matrix (Fin 3) (Fin 2) ℝ} (hA : A ∈ L) (hB : B ∈ L)
    (hB1 : B.rank = 1) : ∃ a b : ℝ, ∀ τ : ℝ, sverakf (A + τ • B) = a + b * τ := by
  obtain ⟨⟨r, s, t⟩, rfl⟩ := hA
  obtain ⟨⟨r', s', t'⟩, rfl⟩ := hB
  have hsum : ∀ τ : ℝ, ofRST r s t + τ • ofRST r' s' t' =
      ofRST (r + τ * r') (s + τ * s') (t + τ * t') := fun τ => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ofRST]
  simp only [hsum, sverakf_ofRST]
  rcases (rank_ofRST_eq_one r' s' t').1 hB1 with
    ⟨-, rfl, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, rfl, -⟩
  · exact ⟨-(r * s * t), -(r' * s * t), fun τ => by ring⟩
  · exact ⟨-(r * s * t), -(r * s' * t), fun τ => by ring⟩
  · exact ⟨-(r * s * t), -(r * s * t'), fun τ => by ring⟩

/-- Šverák's map `w : ℝ² → ℝ³`, `w (x) = (2π)⁻¹ (sin 2πx₁, sin 2πx₂, sin 2π(x₁ + x₂))`. -/
noncomputable def w (x : Fin 2 → ℝ) : Fin 3 → ℝ :=
  (2 * π)⁻¹ • ![sin (2 * π * x 0), sin (2 * π * x 1), sin (2 * π * (x 0 + x 1))]

theorem w_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [w] <;> fun_prop

theorem w_periodic : IsPeriodic w := by
  intro x z
  have h0 : 2 * π * (x 0 + z 0) = 2 * π * x 0 + (z 0 : ℤ) * (2 * π) := by ring
  have h1 : 2 * π * (x 1 + z 1) = 2 * π * x 1 + (z 1 : ℤ) * (2 * π) := by ring
  have h2 : 2 * π * (x 0 + z 0 + (x 1 + z 1)) =
      2 * π * (x 0 + x 1) + ((z 0 + z 1 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
  simp only [w, Pi.add_apply, h0, h1, h2, sin_add_int_mul_two_pi]

/-- `D w (x) = (cos 2πx₁ 0; 0 cos 2πx₂; cos 2π(x₁+x₂) cos 2π(x₁+x₂)) ∈ L`. -/
theorem jac_w (x : Fin 2 → ℝ) :
    jac w x = ofRST (cos (2 * π * x 0)) (cos (2 * π * x 1)) (cos (2 * π * (x 0 + x 1))) := by
  have key : ∀ (ℓ : (Fin 2 → ℝ) →L[ℝ] ℝ) (v : Fin 2 → ℝ),
      fderiv ℝ (fun y => (2 * π)⁻¹ * sin (2 * π * ℓ y)) x v = cos (2 * π * ℓ x) * ℓ v := by
    intro ℓ v
    have hh : HasDerivAt (fun t : ℝ => (2 * π)⁻¹ * sin (2 * π * t)) (cos (2 * π * ℓ x)) (ℓ x) := by
      have := (((hasDerivAt_id' (ℓ x)).const_mul (2 * π)).sin).const_mul (2 * π)⁻¹
      convert this using 1
      field_simp
    have h3 : HasFDerivAt (fun y => (2 * π)⁻¹ * sin (2 * π * ℓ y)) (cos (2 * π * ℓ x) • ℓ) x :=
      hh.comp_hasFDerivAt x ℓ.hasFDerivAt
    rw [h3.fderiv]
    simp
  have e0 : (fun y => w y 0) = fun y => (2 * π)⁻¹ * sin (2 * π * ContinuousLinearMap.proj
      (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 y) := by
    funext y; simp [w]
  have e1 : (fun y => w y 1) = fun y => (2 * π)⁻¹ * sin (2 * π * ContinuousLinearMap.proj
      (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 y) := by
    funext y; simp [w]
  have e2 : (fun y => w y 2) = fun y => (2 * π)⁻¹ * sin (2 * π *
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) y) := by
    funext y; simp [w]
  have k0 : ∀ v, fderiv ℝ (fun y => w y 0) x v = cos (2 * π * x 0) * v 0 := fun v => by
    rw [e0, key]; rfl
  have k1 : ∀ v, fderiv ℝ (fun y => w y 1) x v = cos (2 * π * x 1) * v 1 := fun v => by
    rw [e1, key]; rfl
  have k2 : ∀ v, fderiv ℝ (fun y => w y 2) x v = cos (2 * π * (x 0 + x 1)) * (v 0 + v 1) :=
    fun v => by rw [e2, key]; rfl
  ext i k
  fin_cases i <;> fin_cases k <;> simp [jac, ofRST, k0, k1, k2]

/-- **Equation (4)** (`sv-eq4`). `∫_{[0,1]²} f (D w (x)) dx = −∫_{[0,1]²} (cos 2πx₁)² (cos 2πx₂)² dx
< 0 = f (0)`. -/
theorem equation4 :
    ∫ x in unitCube 2, sverakf (jac w x) =
        -∫ x in unitCube 2, cos (2 * π * x 0) ^ 2 * cos (2 * π * x 1) ^ 2 ∧
      ∫ x in unitCube 2, sverakf (jac w x) < sverakf 0 := by
  -- the integral of a product `g (x₀) g (x₁)` over the unit square (Fubini)
  have hprod : ∀ g : ℝ → ℝ,
      ∫ x in unitCube 2, g (x 0) * g (x 1) = (∫ t in (0 : ℝ)..1, g t) ^ 2 := by
    intro g
    have h := integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun _ : Fin 2 => g)
      (μ := fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Ioo 0 1))
    rw [← Measure.restrict_pi_pi] at h
    simp only [Fin.prod_univ_two] at h
    rw [unitCube, volume_pi, h, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, sq]
  have h2π : (2 * π) ≠ 0 := by positivity
  have hcos : ∫ t in (0 : ℝ)..1, cos (2 * π * t) ^ 2 = 1 / 2 := by
    rw [intervalIntegral.integral_comp_mul_left (fun t => cos t ^ 2) h2π, integral_cos_sq]
    simp
    field_simp
  have hsc : ∫ t in (0 : ℝ)..1, sin (2 * π * t) * cos (2 * π * t) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left (fun t => sin t * cos t) h2π,
      integral_sin_mul_cos₁]
    simp
  have hA : ∫ x in unitCube 2, cos (2 * π * x 0) ^ 2 * cos (2 * π * x 1) ^ 2 = 1 / 4 := by
    rw [hprod (fun t => cos (2 * π * t) ^ 2), hcos]
    norm_num
  have hB : ∫ x in unitCube 2, sin (2 * π * x 0) * cos (2 * π * x 0) *
      (sin (2 * π * x 1) * cos (2 * π * x 1)) = 0 := by
    rw [hprod (fun t => sin (2 * π * t) * cos (2 * π * t)), hsc]
    norm_num
  -- `f (D w) = −(cos a)² (cos b)² + (sin a cos a)(sin b cos b)`, by
  -- `cos (a + b) = cos a cos b − sin a sin b`
  have hpt : (fun x => sverakf (jac w x)) = fun x =>
      -(cos (2 * π * x 0) ^ 2 * cos (2 * π * x 1) ^ 2) +
        sin (2 * π * x 0) * cos (2 * π * x 0) * (sin (2 * π * x 1) * cos (2 * π * x 1)) := by
    funext x
    rw [jac_w, sverakf_ofRST, mul_add, cos_add]
    ring
  have hint : ∫ x in unitCube 2, sverakf (jac w x) = -(1 / 4) := by
    rw [hpt, integral_add, integral_neg, hA, hB]
    · norm_num
    · exact (gen_integrableOn_unitCube (by fun_prop)).neg
    · exact gen_integrableOn_unitCube (by fun_prop)
  have hf0 : sverakf 0 = 0 := by simp [sverakf, sverakP]
  refine ⟨by rw [hint, hA], ?_⟩
  rw [hint, hf0]
  norm_num

end Sverak
