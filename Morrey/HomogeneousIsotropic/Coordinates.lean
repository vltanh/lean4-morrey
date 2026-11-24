module

public import Morrey.HomogeneousIsotropic.Defs
public import CalculusOfVariations.Basic
public import Morrey.Common.Basic.LinearAlgebra.Matrix.RankTwo
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Conformal coordinates on `2 × 2` matrices

With `ℝ² = ℂ`, a real `2 × 2` matrix `A` acts as `ζ ↦ z ζ + w ζ̄`, where `z = conformalPart A` and
`w = anticonformalPart A`. This file proves the calculus of these coordinates.

* `ofComplex_conformalPart`, `conformalPart_ofComplex`, `anticonformalPart_ofComplex`:
  `A ↦ (z, w)` and `ofComplex` are inverse to each other; the coordinates are `ℝ`-linear
  (`conformalPart_add`, `conformalPart_smul`, `ofComplex_add_mul`, `ofComplex_real_mul`).
* `det_ofComplex`, `det_eq_norm_sq_sub`: `det A = |z|² − |w|²`; `rank_ofComplex_eq_one`: the
  matrix with coordinates `(α, β)`, `|α| = |β|`, `α ≠ 0`, has rank one.
* `ofComplex_mem_specialOrthogonalGroup`, `ofComplex_mul_mul`: the rotation by a unit complex
  number `u` is `ofComplex u 0`, and `(rotation u) A (rotation v)` has the coordinates
  `(u v z, u v̄ w)`.
* `IsIsotropic.apply_ofComplex`, `IsIsotropic.eq_profile`: an isotropic `F` is the function
  `profile F (|z|, |w|)`; `isProfile_profile`: the profile of an isotropic, positively
  `p`-homogeneous, rank-one convex `F` satisfies `IsProfile p`.
* `conformalPart_reflection_mul`, `anticonformalPart_reflection_mul`: the reflection `J` swaps
  the two coordinates, up to conjugation.
* `sum_ofComplex_mul`: the pairing `⟨K, A⟩` in conformal coordinates;
  `hasPolyaffineSupportAt_of_profile`: a support `k + b x + g y + c (x² − y²)` of the profile,
  `b, g ≥ 0`, gives a polyaffine support of `F`.
-/

@[expose] public section

namespace HomogeneousIsotropic

open CalculusOfVariations

/-! ### The coordinates -/

/-- The matrix with the conformal and the anticonformal part of `A` is `A`. -/
theorem ofComplex_conformalPart (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ofComplex (conformalPart A) (anticonformalPart A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofComplex, conformalPart, anticonformalPart] <;> ring

/-- The conformal part of `ofComplex z w` is `z`. -/
theorem conformalPart_ofComplex (z w : ℂ) : conformalPart (ofComplex z w) = z := by
  apply Complex.ext
  · simp [ofComplex, conformalPart]
  · simp [ofComplex, conformalPart]
    ring

/-- The anticonformal part of `ofComplex z w` is `w`. -/
theorem anticonformalPart_ofComplex (z w : ℂ) : anticonformalPart (ofComplex z w) = w := by
  apply Complex.ext
  · simp [ofComplex, anticonformalPart]
  · simp [ofComplex, anticonformalPart]
    ring

/-- The conformal part of the zero matrix is `0`. -/
theorem conformalPart_zero : conformalPart 0 = 0 := by
  apply Complex.ext <;> simp [conformalPart]

/-- The anticonformal part of the zero matrix is `0`. -/
theorem anticonformalPart_zero : anticonformalPart 0 = 0 := by
  apply Complex.ext <;> simp [anticonformalPart]

/-- The matrix with coordinates `(0, 0)` is the zero matrix. -/
theorem ofComplex_zero : ofComplex 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofComplex]

/-- The conformal part is additive. -/
theorem conformalPart_add (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    conformalPart (A + B) = conformalPart A + conformalPart B := by
  apply Complex.ext <;> simp [conformalPart] <;> ring

/-- The anticonformal part is additive. -/
theorem anticonformalPart_add (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    anticonformalPart (A + B) = anticonformalPart A + anticonformalPart B := by
  apply Complex.ext <;> simp [anticonformalPart] <;> ring

/-- The conformal part is homogeneous over `ℝ`. -/
theorem conformalPart_smul (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    conformalPart (c • A) = (c : ℂ) * conformalPart A := by
  apply Complex.ext <;> simp [conformalPart] <;> ring

/-- The anticonformal part is homogeneous over `ℝ`. -/
theorem anticonformalPart_smul (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    anticonformalPart (c • A) = (c : ℂ) * anticonformalPart A := by
  apply Complex.ext <;> simp [anticonformalPart] <;> ring

/-- The determinant in conformal coordinates: `det (ofComplex z w) = |z|² − |w|²`. -/
theorem det_ofComplex (z w : ℂ) : (ofComplex z w).det = ‖z‖ ^ 2 - ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, ofComplex,
    Matrix.det_fin_two_of]
  ring

/-- The determinant of `A` is `|z|² − |w|²`, for the conformal part `z` and the anticonformal
part `w` of `A`. -/
theorem det_eq_norm_sq_sub (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = ‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2 := by
  rw [← det_ofComplex, ofComplex_conformalPart]

/-- The line `τ ↦ (z + τ α, w + τ β)` in conformal coordinates is the line
`τ ↦ ofComplex z w + τ • ofComplex α β` of matrices. -/
theorem ofComplex_add_mul (z w α β : ℂ) (τ : ℝ) :
    ofComplex (z + τ * α) (w + τ * β) = ofComplex z w + τ • ofComplex α β := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofComplex] <;> ring

/-- Multiplying both coordinates by a real `c` multiplies the matrix by `c`. -/
theorem ofComplex_real_mul (c : ℝ) (z w : ℂ) :
    ofComplex ((c : ℂ) * z) ((c : ℂ) * w) = c • ofComplex z w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofComplex] <;> ring

/-- For real coordinates `x`, `y` the matrix is `diag (x + y, x − y)`. -/
theorem ofComplex_ofReal (x y : ℝ) : ofComplex (x : ℂ) (y : ℂ) = !![x + y, 0; 0, x - y] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofComplex]

/-- A matrix with coordinates `(α, β)`, `|α| = |β|` and `α ≠ 0`, has rank one. -/
theorem rank_ofComplex_eq_one {α β : ℂ} (h : ‖α‖ = ‖β‖) (hα : α ≠ 0) :
    (ofComplex α β).rank = 1 := by
  have hdet : (ofComplex α β).det = 0 := by rw [det_ofComplex, h, sub_self]
  have hle := (Matrix.rank_le_one_iff_det_eq_zero_of_fin_two _).2 hdet
  have hne : (ofComplex α β).rank ≠ 0 := by
    intro h0
    rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
    have hzero : ofComplex α β = 0 := by
      ext i j
      have := congrArg (fun L => L (Pi.single j 1) i) h0
      simpa [Matrix.mulVecLin_apply] using this
    apply hα
    rw [← conformalPart_ofComplex α β, hzero, conformalPart_zero]
  omega

/-! ### Rotations -/

/-- The rotation by a unit complex number `u`, the matrix `ofComplex u 0`, is in `SO(2)`. -/
theorem ofComplex_mem_specialOrthogonalGroup {u : ℂ} (hu : ‖u‖ = 1) :
    ofComplex u 0 ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  have h : u.re * u.re + u.im * u.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hu, one_pow]
  rw [ofComplex, Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
  refine ⟨by simp, by simp, ?_⟩
  simp only [Complex.zero_re, Complex.zero_im, add_zero, zero_sub]
  linear_combination h

/-- Rotating on both sides: `(rotation u) (ofComplex z w) (rotation v)` has the coordinates
`(u v z, u v̄ w)`. -/
theorem ofComplex_mul_mul (u v z w : ℂ) :
    ofComplex u 0 * ofComplex z w * ofComplex v 0 =
      ofComplex (u * v * z) (u * (starRingEnd ℂ) v * w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ofComplex, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The unit complex number `exp (−i arg z)` rotates `z` to `|z|`. -/
theorem exp_neg_arg_mul_I_mul (z : ℂ) :
    Complex.exp (-(Complex.arg z : ℂ) * Complex.I) * z = (‖z‖ : ℂ) := by
  calc Complex.exp (-(Complex.arg z : ℂ) * Complex.I) * z
      = Complex.exp (-(Complex.arg z : ℂ) * Complex.I) *
          ((‖z‖ : ℂ) * Complex.exp (Complex.arg z * Complex.I)) := by
        rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (‖z‖ : ℂ) * (Complex.exp (-(Complex.arg z : ℂ) * Complex.I) *
          Complex.exp (Complex.arg z * Complex.I)) := by ring
    _ = (‖z‖ : ℂ) := by rw [← Complex.exp_add]; simp

/-- Every complex number `z` is rotated to `|z|` by a unit complex number. -/
theorem exists_norm_eq_one_mul_eq_norm (z : ℂ) : ∃ u : ℂ, ‖u‖ = 1 ∧ u * z = (‖z‖ : ℂ) := by
  refine ⟨Complex.exp (-(Complex.arg z : ℂ) * Complex.I), ?_, exp_neg_arg_mul_I_mul z⟩
  rw [← Complex.ofReal_neg]
  exact Complex.norm_exp_ofReal_mul_I _

/-! ### Isotropic functions and their profiles -/

/-- An isotropic function depends only on `(|z|, |w|)`: `F (ofComplex z w)` is the profile of `F`
at `(|z|, |w|)`. -/
theorem IsIsotropic.apply_ofComplex {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : IsIsotropic F)
    (z w : ℂ) : F (ofComplex z w) = profile F ‖z‖ ‖w‖ := by
  have hu := Complex.norm_exp_ofReal_mul_I (-(Complex.arg z + Complex.arg w) / 2)
  have hv := Complex.norm_exp_ofReal_mul_I (-(Complex.arg z - Complex.arg w) / 2)
  have h := hF _ (ofComplex_mem_specialOrthogonalGroup hu) _
    (ofComplex_mem_specialOrthogonalGroup hv) (ofComplex z w)
  rw [ofComplex_mul_mul, ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add] at h
  have h1 : (((-(Complex.arg z + Complex.arg w) / 2 : ℝ) : ℂ) * Complex.I +
      ((-(Complex.arg z - Complex.arg w) / 2 : ℝ) : ℂ) * Complex.I) =
        -(Complex.arg z : ℂ) * Complex.I := by
    push_cast; ring
  have h2 : (((-(Complex.arg z + Complex.arg w) / 2 : ℝ) : ℂ) * Complex.I +
      (starRingEnd ℂ) (((-(Complex.arg z - Complex.arg w) / 2 : ℝ) : ℂ) * Complex.I)) =
        -(Complex.arg w : ℂ) * Complex.I := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  rw [h1, h2, exp_neg_arg_mul_I_mul, exp_neg_arg_mul_I_mul] at h
  rw [← h, profile]

/-- An isotropic function is its profile at `(|z|, |w|)`, for the conformal part `z` and the
anticonformal part `w` of the matrix. -/
theorem IsIsotropic.eq_profile {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : IsIsotropic F)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    F A = profile F ‖conformalPart A‖ ‖anticonformalPart A‖ := by
  rw [← hF.apply_ofComplex, ofComplex_conformalPart]

/-- The profile of an isotropic, positively `p`-homogeneous, rank-one convex `F` is a profile:
it is `p`-homogeneous and convex along the images of the rank-one lines. -/
theorem isProfile_profile {p : ℝ} {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F) : IsProfile p (profile F) where
  homog c x y hc _ _ := by
    simp only [profile, Complex.ofReal_mul, ofComplex_real_mul]
    exact hhom c hc _
  convex z w α β h := by
    have heq : (fun τ : ℝ => profile F ‖z + τ * α‖ ‖w + τ * β‖) =
        fun τ : ℝ => F (ofComplex z w + τ • ofComplex α β) := by
      funext τ
      rw [← hiso.apply_ofComplex, ofComplex_add_mul]
    rw [heq]
    by_cases hα : α = 0
    · have hβ : β = 0 := by rw [← norm_eq_zero, ← h, hα, norm_zero]
      simp only [hα, hβ, ofComplex_zero, smul_zero, add_zero]
      exact convexOn_const _ convex_univ
    · exact hrc _ _ (rank_ofComplex_eq_one h hα)

/-! ### The reflection -/

/-- The conformal part of `J A` is the conjugate of the anticonformal part of `A`. -/
theorem conformalPart_reflection_mul (A : Matrix (Fin 2) (Fin 2) ℝ) :
    conformalPart (reflection * A) = (starRingEnd ℂ) (anticonformalPart A) := by
  apply Complex.ext <;>
    simp [reflection, conformalPart, anticonformalPart, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- The anticonformal part of `J A` is the conjugate of the conformal part of `A`. -/
theorem anticonformalPart_reflection_mul (A : Matrix (Fin 2) (Fin 2) ℝ) :
    anticonformalPart (reflection * A) = (starRingEnd ℂ) (conformalPart A) := by
  apply Complex.ext
  · simp [reflection, conformalPart, anticonformalPart, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [reflection, conformalPart, anticonformalPart, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-! ### Polyaffine supports -/

/-- The pairing `⟨K, A⟩ = ∑ K i j * A i j` in conformal coordinates: for `K = ofComplex ζ ω` it
is `2 Re (ζ̄ z + ω̄ w)`, with `z`, `w` the conformal and the anticonformal part of `A`. -/
theorem sum_ofComplex_mul (ζ ω : ℂ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∑ i, ∑ j, ofComplex ζ ω i j * A i j =
      2 * (((starRingEnd ℂ) ζ * conformalPart A).re +
        ((starRingEnd ℂ) ω * anticonformalPart A).re) := by
  simp [Fin.sum_univ_two, ofComplex, conformalPart, anticonformalPart]
  ring

/-- A support of the profile of the form `k + b x + g y + c (x² − y²)`, with `b, g ≥ 0`, that
touches at `(|z₀|, |w₀|)` gives a polyaffine support of `F` at `A₀`. -/
theorem hasPolyaffineSupportAt_of_profile {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hiso : IsIsotropic F) (A₀ : Matrix (Fin 2) (Fin 2) ℝ) {k b g c : ℝ} (hb : 0 ≤ b)
    (hg : 0 ≤ g)
    (hle : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → k + b * x + g * y + c * (x ^ 2 - y ^ 2) ≤ profile F x y)
    (heq : k + b * ‖conformalPart A₀‖ + g * ‖anticonformalPart A₀‖ +
        c * (‖conformalPart A₀‖ ^ 2 - ‖anticonformalPart A₀‖ ^ 2) =
      profile F ‖conformalPart A₀‖ ‖anticonformalPart A₀‖) :
    HasPolyaffineSupportAt F A₀ := by
  obtain ⟨u, hu, hu0⟩ := exists_norm_eq_one_mul_eq_norm (conformalPart A₀)
  obtain ⟨v, hv, hv0⟩ := exists_norm_eq_one_mul_eq_norm (anticonformalPart A₀)
  have hP : ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      polyaffine k (ofComplex (((b / 2 : ℝ) : ℂ) * (starRingEnd ℂ) u)
        (((g / 2 : ℝ) : ℂ) * (starRingEnd ℂ) v)) c A =
      k + b * (u * conformalPart A).re + g * (v * anticonformalPart A).re +
        c * (‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2) := by
    intro A
    rw [polyaffine, sum_ofComplex_mul, det_eq_norm_sq_sub A, map_mul, map_mul,
      Complex.conj_conj, Complex.conj_conj, Complex.conj_ofReal, Complex.conj_ofReal, mul_assoc,
      mul_assoc, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    ring
  refine ⟨k, ofComplex (((b / 2 : ℝ) : ℂ) * (starRingEnd ℂ) u)
    (((g / 2 : ℝ) : ℂ) * (starRingEnd ℂ) v), c, fun A => ?_, ?_⟩
  · rw [hP, hiso.eq_profile A]
    have h1 : (u * conformalPart A).re ≤ ‖conformalPart A‖ :=
      (Complex.re_le_norm _).trans_eq (by rw [norm_mul, hu, one_mul])
    have h2 : (v * anticonformalPart A).re ≤ ‖anticonformalPart A‖ :=
      (Complex.re_le_norm _).trans_eq (by rw [norm_mul, hv, one_mul])
    have h3 := hle _ _ (norm_nonneg (conformalPart A)) (norm_nonneg (anticonformalPart A))
    have h4 := mul_le_mul_of_nonneg_left h1 hb
    have h5 := mul_le_mul_of_nonneg_left h2 hg
    linarith
  · rw [hP, hiso.eq_profile A₀, hu0, hv0, Complex.ofReal_re, Complex.ofReal_re]
    exact heq

/-- **Lemma 2.1 (b).** A nonzero matrix has rank one if and only if its conformal and its
anticonformal part have the same modulus. -/
theorem rank_eq_one_iff_norm_eq {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : B ≠ 0) :
    B.rank = 1 ↔ ‖conformalPart B‖ = ‖anticonformalPart B‖ := by
  constructor
  · intro h
    have hdet : B.det = 0 := (Matrix.rank_le_one_iff_det_eq_zero_of_fin_two B).1 h.le
    rw [det_eq_norm_sq_sub] at hdet
    have hmul : (‖conformalPart B‖ - ‖anticonformalPart B‖) *
        (‖conformalPart B‖ + ‖anticonformalPart B‖) = 0 := by
      rw [← hdet]
      ring
    rcases mul_eq_zero.1 hmul with h1 | h1
    · linarith
    · linarith [norm_nonneg (conformalPart B), norm_nonneg (anticonformalPart B)]
  · intro h
    have hα : conformalPart B ≠ 0 := by
      intro h0
      apply hB
      have hw : anticonformalPart B = 0 := norm_eq_zero.1 (by rw [← h, h0, norm_zero])
      rw [← ofComplex_conformalPart B, h0, hw, ofComplex_zero]
    have := rank_ofComplex_eq_one h hα
    rwa [ofComplex_conformalPart] at this

/-- A matrix of `SO(2)` is a rotation: it is `ofComplex u 0` with `|u| = 1`. -/
theorem exists_ofComplex_eq_of_mem_specialOrthogonalGroup {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ofComplex u 0 = Q := by
  rw [Matrix.mem_specialOrthogonalGroup_fin_two_iff] at hQ
  obtain ⟨h1, h2, h3⟩ := hQ
  refine ⟨⟨Q 0 0, Q 1 0⟩, ?_, ?_⟩
  · have hsq : ‖(⟨Q 0 0, Q 1 0⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      rw [h2] at h3
      linarith
    have hn := norm_nonneg (⟨Q 0 0, Q 1 0⟩ : ℂ)
    nlinarith
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ofComplex] <;> linarith

/-- **Lemma 2.1 (c), for the moduli.** Rotations on both sides do not change the moduli of the
conformal and of the anticonformal part. -/
theorem norm_conformalPart_mul_mul {Q R : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖conformalPart (Q * A * R)‖ = ‖conformalPart A‖ ∧
      ‖anticonformalPart (Q * A * R)‖ = ‖anticonformalPart A‖ := by
  obtain ⟨u, hu, rfl⟩ := exists_ofComplex_eq_of_mem_specialOrthogonalGroup hQ
  obtain ⟨v, hv, rfl⟩ := exists_ofComplex_eq_of_mem_specialOrthogonalGroup hR
  obtain ⟨z, w, rfl⟩ : ∃ z w, A = ofComplex z w := ⟨_, _, (ofComplex_conformalPart A).symm⟩
  rw [ofComplex_mul_mul]
  simp [conformalPart_ofComplex, anticonformalPart_ofComplex, hu, hv]

/-- A function of the moduli of the conformal and of the anticonformal part is isotropic. -/
theorem isIsotropic_of_eq {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    (h : ∀ A, F A = Φ ‖conformalPart A‖ ‖anticonformalPart A‖) : IsIsotropic F := by
  intro Q hQ R hR A
  obtain ⟨h1, h2⟩ := norm_conformalPart_mul_mul hQ hR A
  rw [h, h A, h1, h2]

/-- `F` is isotropic if and only if `F (A) = Φ (|z|, |w|)`, where `Φ (x, y) =
F (diag (x + y, x − y))` is the profile of `F`. -/
theorem isIsotropic_iff_eq_profile {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} :
    IsIsotropic F ↔ ∀ A, F A = profile F ‖conformalPart A‖ ‖anticonformalPart A‖ :=
  ⟨fun h => h.eq_profile, isIsotropic_of_eq⟩

end HomogeneousIsotropic
