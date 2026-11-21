module

public import Morrey.Common.Basic.CalculusOfVariations.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Hom.Basic
public import Morrey.Common.External.Dacorogna.Plancherel

/-!
# Dacorogna: rank-one affine functions and quadratic forms

B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer 2008,
Theorems 5.20 and 5.25 (i). Cassese uses both in the proof of Proposition 5.1 only. Both are
proved here:

* Theorem 5.20 is the proposition `RankOneAffineMinors`, which Cassese's Proposition 5.1 takes as
  a hypothesis; `rankOneAffineMinors_holds` proves it (rank-one affine ⇒ affine combination of
  minors, by induction on the number of rows; the minors are rank-one affine by the matrix
  determinant lemma);
* Theorem 5.25 (i) is `quadraticForm_quasiconvex`, by Dacorogna's Fourier–Plancherel argument
  (the analytic part is in `Morrey.Common.External.Dacorogna.Plancherel`).
-/

@[expose] public section

namespace External.Dacorogna

open CalculusOfVariations MeasureTheory

variable {d m : ℕ}

/-- The `k × k` minor of `A` with the rows `r` and the columns `c` (strictly increasing). -/
noncomputable def minor (A : Matrix (Fin d) (Fin m) ℝ) {k : ℕ} (r : Fin k ↪o Fin d)
    (c : Fin k ↪o Fin m) : ℝ :=
  (A.submatrix r c).det

/-- Dacorogna, Theorem 5.20 (used in the proof of Cassese's Proposition 5.1): a
continuous rank-one affine `f : ℝ^{d×m} → ℝ` is an affine combination of the minors of its
argument (the `0 × 0` minor is the constant `1`). -/
def RankOneAffineMinors : Prop :=
  ∀ (d m : ℕ) (f : Matrix (Fin d) (Fin m) ℝ → ℝ), Continuous f → RankOneAffine f →
    ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
      ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c

private lemma minors_rank_eq_zero_imp {A : Matrix (Fin d) (Fin m) ℝ} (h : A.rank = 0) :
    A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun F => F (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply] using this

/-- A bilinear form on matrices in coordinates: `Q (X, Y) = ∑ Q (E_{ik}, E_{jl}) X_{ik} Y_{jl}`. -/
private lemma minors_bilin_expand (Q : LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ))
    (X Y : Matrix (Fin d) (Fin m) ℝ) :
    Q X Y = ∑ i, ∑ k, ∑ j, ∑ l,
      Q (Matrix.single i k 1) (Matrix.single j l 1) * (X i k * Y j l) := by
  have hX : X = ∑ i, ∑ k, X i k • Matrix.single i k (1 : ℝ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp
  have hY : Y = ∑ j, ∑ l, Y j l • Matrix.single j l (1 : ℝ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp
  have h1 : ∀ Z, Q Z Y = ∑ j, ∑ l, Y j l * Q Z (Matrix.single j l 1) := by
    intro Z
    conv_lhs => rw [hY]
    simp only [map_sum, map_smul, smul_eq_mul]
  have h2 : Q X Y = ∑ i, ∑ k, X i k * Q (Matrix.single i k 1) Y := by
    conv_lhs => rw [hX]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [h2]
  simp only [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The Legendre–Hadamard condition `Q (a ⊗ ξ, a ⊗ ξ) ≥ 0` of a rank-one convex quadratic form. -/
private lemma minors_legendreHadamard (Q : LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ))
    (hQ : RankOneConvex fun A => Q A A) (a : Fin d → ℝ) (ξ : Fin m → ℝ) :
    0 ≤ Q (Matrix.vecMulVec a ξ) (Matrix.vecMulVec a ξ) := by
  set B := Matrix.vecMulVec a ξ
  by_cases hB : B = 0
  · simp [hB]
  have hrank : B.rank = 1 := by
    refine le_antisymm (Matrix.rank_vecMulVec_le _ _) ?_
    rw [Nat.one_le_iff_ne_zero]
    exact fun h => hB (minors_rank_eq_zero_imp h)
  have hc := (hQ 0 B hrank).2 (Set.mem_univ (-1 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [zero_add, smul_eq_mul, map_smul, LinearMap.smul_apply] at hc
  norm_num at hc
  linarith

/-- Dacorogna, Theorem 5.25 (i) (used in the proof of Cassese's Proposition 5.1): a rank-one
convex quadratic form is quasiconvex.

Proof (Dacorogna's): since `Q` is quadratic, `Q (A + ∇φ) = Q (A) + [Q (A, ∇φ) + Q (∇φ, A)] +
Q (∇φ)`; the linear term integrates to `0` (`plancherel_integral_fderiv_eq_zero`), and
`∫ Q (∇φ) ≥ 0` by Plancherel, since rank-one convexity is the Legendre–Hadamard condition
`Q (a ⊗ ξ) ≥ 0` (`plancherel_lipschitz_nonneg`). The test map, extended by `0` outside the cube,
is a compactly supported Lipschitz map on `ℝ^m`, and its gradient vanishes off the closed cube,
whose boundary is null.

Departure from the source: Dacorogna applies Plancherel's formula in `L²` directly to the
`W^{1,∞}_0` map. Mathlib has Plancherel for Schwartz functions (and an abstract `L²` Fourier
transform), but not the rule `𝓕 (∂_k φ) = 2πi ξ_k 𝓕 φ` for Sobolev maps; so the Fourier inequality
is proved for smooth compactly supported maps, on `EuclideanSpace ℝ (Fin m)` (Mathlib's Fourier
transform needs an inner product space), and extended to Lipschitz maps by mollification (the
density step implicit in the `L²` argument). Reason 2 (mathematics missing from Mathlib). -/
theorem quadraticForm_quasiconvex
    (Q : LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ))
    (hQ : RankOneConvex fun A => Q A A) : Quasiconvex fun A => Q A A := by
  intro A φ K hφ hφ0 hint
  set c : Fin d → Fin m → Fin d → Fin m → ℝ :=
    fun i k j l => Q (Matrix.single i k 1) (Matrix.single j l 1) with hcdef
  have hc : ∀ (a : Fin d → ℝ) (ξ : Fin m → ℝ),
      0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, c i k j l * (a i * ξ k) * (a j * ξ l) := by
    intro a ξ
    have h := minors_legendreHadamard Q hQ a ξ
    rw [minors_bilin_expand] at h
    simpa [Matrix.vecMulVec_apply, mul_assoc, hcdef] using h
  -- the components of `φ` and the closed cube
  set φc : Fin d → (Fin m → ℝ) → ℝ := fun i y => φ y i with hφcdef
  set S : Set (Fin m → ℝ) := Set.Icc 0 1 with hS
  have hScpt : IsCompact S := isCompact_Icc
  have hcubeS : unitCube m ⊆ S := fun x hx => ⟨fun k => (hx k (Set.mem_univ _)).1.le,
    fun k => (hx k (Set.mem_univ _)).2.le⟩
  have hφi : ∀ i, LipschitzWith K (φc i) := fun i => by
    have := (LipschitzWith.eval (α := fun _ : Fin d => ℝ) i).comp hφ
    rw [one_mul] at this
    exact this
  have hφS : ∀ i, ∀ x ∉ S, φc i x = 0 := fun i x hx => by
    simp [hφcdef, hφ0 x (fun h => hx (hcubeS h))]
  have hφc : ∀ i, HasCompactSupport (φc i) := fun i =>
    HasCompactSupport.intro hScpt (hφS i)
  have hG : ∀ x i k, grad φ x i k = fderiv ℝ (φc i) x (Pi.single k 1) := fun _ _ _ => rfl
  have hG0 : ∀ i k, ∀ x ∉ S, grad φ x i k = 0 := by
    intro i k x hx
    rw [hG, fderiv_of_notMem_tsupport]
    · rfl
    · exact fun h => hx ((closure_minimal (fun y hy => by
        by_contra h'; exact hy (hφS i y h')) hScpt.isClosed) h)
  have hGb : ∀ x i k, |grad φ x i k| ≤ K := by
    intro x i k
    rw [hG]
    calc |fderiv ℝ (φc i) x (Pi.single k 1)| ≤ ‖fderiv ℝ (φc i) x‖ * ‖(Pi.single k 1 : Fin m → ℝ)‖ :=
          (fderiv ℝ (φc i) x).le_opNorm _
      _ ≤ K * 1 := by
          gcongr
          · exact norm_fderiv_le_of_lipschitz ℝ (hφi i)
          · simp [Pi.norm_single]
      _ = K := mul_one _
  have hGm : ∀ i k, Measurable fun x => grad φ x i k := fun i k =>
    measurable_fderiv_apply_const ℝ (φc i) (Pi.single k 1)
  -- integrability on `ℝ^m`
  have hbint : ∀ C : ℝ, Integrable (S.indicator fun _ => C) :=
    fun C => (integrable_indicator_iff hScpt.measurableSet).2
      (integrableOn_const hScpt.measure_lt_top.ne)
  have hi1 : ∀ i k, Integrable fun x => grad φ x i k := by
    intro i k
    refine (hbint K).mono' (hGm i k).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]; exact hGb x i k
    · rw [Set.indicator_of_notMem hx, hG0 i k x hx, norm_zero]
  have hi2 : ∀ i k j l, Integrable fun x => grad φ x i k * grad φ x j l := by
    intro i k j l
    refine (hbint (K * K)).mono' ((hGm i k).mul (hGm j l)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hGb x i k) (hGb x j l) (abs_nonneg _) K.2
    · rw [Set.indicator_of_notMem hx, hG0 i k x hx, zero_mul, norm_zero]
  -- the decomposition
  set L : Fin d → Fin m → ℝ := fun i k => Q A (Matrix.single i k 1) + Q (Matrix.single i k 1) A
  set h : (Fin m → ℝ) → ℝ := fun x => (∑ i, ∑ k, L i k * grad φ x i k) +
    ∑ i, ∑ k, ∑ j, ∑ l, c i k j l * (grad φ x i k * grad φ x j l) with hh
  have hpt : ∀ x, Q (A + grad φ x) (A + grad φ x) = Q A A + h x := by
    intro x
    have e1 : Q A (grad φ x) + Q (grad φ x) A = ∑ i, ∑ k, L i k * grad φ x i k := by
      have hX : grad φ x = ∑ i, ∑ k, grad φ x i k • Matrix.single i k (1 : ℝ) := by
        conv_lhs => rw [Matrix.matrix_eq_sum_single (grad φ x)]
        simp
      conv_lhs => rw [hX]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have e2 := minors_bilin_expand Q (grad φ x) (grad φ x)
    simp only [map_add, LinearMap.add_apply, hh]
    rw [← e1, e2]
    ring
  have hhint : Integrable h := by
    refine (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      (hi1 i k).const_mul (L i k)).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
          (hi2 i k j l).const_mul (c i k j l))
  have hh0 : ∀ x ∉ S, h x = 0 := by
    intro x hx
    simp [hh, hG0 _ _ x hx]
  have hvol : volume (unitCube m) ≠ ⊤ := (measure_mono hcubeS).trans_lt hScpt.measure_lt_top |>.ne
  -- the integral over the cube
  have hcube : ∫ x in unitCube m, Q (A + grad φ x) (A + grad φ x) =
      (volume (unitCube m)).toReal * Q A A + ∫ x, h x := by
    simp only [hpt]
    rw [integral_add (integrableOn_const hvol) hhint.integrableOn, setIntegral_const,
      smul_eq_mul, Measure.real]
    congr 1
    have hae : unitCube m =ᵐ[volume] S := by
      rw [hS, ← Set.pi_univ_Icc]
      exact Measure.pi_Ioo_ae_eq_pi_Icc
    rw [setIntegral_congr_set hae, setIntegral_eq_integral_of_forall_compl_eq_zero hh0]
  have hlin : ∫ x, h x = (∑ i, ∑ k, L i k * ∫ x, grad φ x i k) +
      ∑ i, ∑ k, ∑ j, ∑ l, c i k j l * ∫ x, grad φ x i k * grad φ x j l := by
    rw [hh, integral_add (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      (hi1 i k).const_mul (L i k))
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
          (hi2 i k j l).const_mul (c i k j l))]
    congr 1
    · rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        (hi1 i k).const_mul (L i k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun k _ => (hi1 i k).const_mul (L i k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul]
    · rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
          (hi2 i k j l).const_mul (c i k j l)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun l _ => (hi2 i k j l).const_mul (c i k j l)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
        (hi2 i k j l).const_mul (c i k j l)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum _ fun l _ => (hi2 i k j l).const_mul (c i k j l)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_const_mul]
  have hzero : ∀ i k, ∫ x, grad φ x i k = 0 := fun i k => by
    simp only [hG]
    exact plancherel_integral_fderiv_eq_zero (hφi i) (hφc i) _
  have hpos : 0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, c i k j l * ∫ x, grad φ x i k * grad φ x j l := by
    simp only [hG]
    exact plancherel_lipschitz_nonneg φc (fun _ => K) hφi hφc c hc
  simp only at hcube ⊢
  rw [hcube, hlin]
  simp only [hzero, mul_zero, Finset.sum_const_zero, zero_add]
  linarith

/-! ### Theorem 5.20: rank-one affine functions are affine combinations of minors -/

section RankOneAffine

open Matrix

/-- `det (X + t u ⊗ v)` is affine in `t` (the matrix determinant lemma), by multilinearity of the
determinant in the rows: two rows proportional to `v` give a vanishing determinant. -/
private lemma minors_det_add_smul_vecMulVec {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) (u v : n → ℝ) (t : ℝ) :
    (X + t • vecMulVec u v).det = X.det + t * ∑ i, u i * (X.updateRow i v).det := by
  suffices h : ∀ (s : Finset n) (X : Matrix n n ℝ),
      (X + t • vecMulVec (fun i => if i ∈ s then u i else 0) v).det =
        X.det + t * ∑ i ∈ s, u i * (X.updateRow i v).det by
    simpa using h Finset.univ X
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro X
    have : vecMulVec (fun _ : n => (0 : ℝ)) v = 0 := by ext; simp [vecMulVec_apply]
    simp [this]
  | insert p s hp ih =>
    intro X
    set w : n → ℝ := fun i => if i ∈ s then u i else 0 with hw
    set N := X + t • vecMulVec w v with hN
    have hrow : X + t • vecMulVec (fun i => if i ∈ insert p s then u i else 0) v =
        N.updateRow p (X p + (t * u p) • v) := by
      ext i j
      by_cases hi : i = p
      · subst hi
        simp [updateRow_self, vecMulVec_apply, mul_comm, mul_left_comm]
      · simp [hN, hw, vecMulVec_apply, Finset.mem_insert, hi]
    have h1 : N.updateRow p (X p) = N := by
      ext i j
      by_cases hi : i = p
      · subst hi; simp [updateRow_self, hN, hw, vecMulVec_apply, hp]
      · simp [updateRow_ne hi]
    have h2 : N.updateRow p v = X.updateRow p v + t • vecMulVec w v := by
      ext i j
      by_cases hi : i = p
      · subst hi; simp [updateRow_self, hw, vecMulVec_apply, hp]
      · simp [updateRow_ne hi, hN]
    have h3 : ∀ i ∈ s, ((X.updateRow p v).updateRow i v).det = 0 := by
      intro i hi
      have hip : i ≠ p := fun h => hp (h ▸ hi)
      refine det_zero_of_row_eq hip ?_
      rw [updateRow_self, updateRow_ne hip.symm, updateRow_self]
    have h4 : ∑ x ∈ s, u x * ((X.updateRow p v).updateRow x v).det = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [h3 i hi, mul_zero]
    have h5 : ((X.updateRow p v).updateRow p v) = X.updateRow p v := by
      ext i j; by_cases hi : i = p
      · subst hi; simp [updateRow_self]
      · simp [updateRow_ne hi]
    rw [hrow, det_updateRow_add, det_updateRow_smul, h1, h2, ih X, ih (X.updateRow p v), h4,
      Finset.sum_insert hp]
    ring

/-- Affinity along the rank-one lines `t ↦ A + t (u ⊗ v)`. -/
private def MinorsRA {d m : ℕ} (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A (u : Fin d → ℝ) (v : Fin m → ℝ) (t : ℝ),
    f (A + t • vecMulVec u v) = f A + t * (f (A + vecMulVec u v) - f A)

/-- Independence of the columns in `J`. -/
private def MinorsIndep {d m : ℕ} (J : Set (Fin m)) (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A (u : Fin d → ℝ) (j : Fin m), j ∈ J → f (A + vecMulVec u (Pi.single j 1)) = f A

/-- A function on `ℝ` that is convex and concave is affine. -/
private lemma minors_affine_of_convex_concave {g : ℝ → ℝ} (h1 : ConvexOn ℝ Set.univ g)
    (h2 : ConvexOn ℝ Set.univ (-g)) (t : ℝ) : g t = g 0 + t * (g 1 - g 0) := by
  have key : ∀ x y a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → g (a * x + b * y) = a * g x + b * g y := by
    intro x y a b ha hb hab
    have e1 := h1.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have e2 := h2.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul, Pi.neg_apply] at e1 e2
    linarith
  rcases le_or_gt t 1 with ht1 | ht1
  · rcases le_or_gt 0 t with ht0 | ht0
    · have := key 0 1 (1 - t) t (by linarith) ht0 (by ring)
      simp only [mul_zero, zero_add, mul_one] at this
      rw [this]; ring
    · -- `0` is a convex combination of `t` and `1`
      have hpos : 0 < 1 - t := by linarith
      have := key t 1 (1 / (1 - t)) (-t / (1 - t)) (by positivity)
        (div_nonneg (by linarith) hpos.le) (by field_simp; ring)
      have e : 1 / (1 - t) * t + -t / (1 - t) * 1 = 0 := by field_simp; ring
      rw [e] at this
      field_simp at this
      linarith
  · have hpos : 0 < t := by linarith
    have := key 0 t (1 - 1 / t) (1 / t) (by rw [sub_nonneg, div_le_one hpos]; linarith)
      (by positivity) (by ring)
    have e : (1 - 1 / t) * 0 + 1 / t * t = 1 := by
      rw [mul_zero, zero_add, one_div, inv_mul_cancel₀ hpos.ne']
    rw [e] at this
    field_simp at this
    linarith

private lemma minors_rank_vecMulVec {u : Fin d → ℝ} {v : Fin m → ℝ} (h : vecMulVec u v ≠ 0) :
    (vecMulVec u v).rank = 1 :=
  le_antisymm (rank_vecMulVec_le _ _) (Nat.one_le_iff_ne_zero.2 fun h' =>
    h (minors_rank_eq_zero_imp h'))

private lemma minors_RA_of_rankOneAffine {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : RankOneAffine f) : MinorsRA f := by
  intro A u v t
  by_cases h : vecMulVec u v = 0
  · simp [h]
  have hr := minors_rank_vecMulVec h
  have := minors_affine_of_convex_concave (hf.1 A _ hr) (hf.2 A _ hr) t
  simpa using this

private lemma minors_minor_RA {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m) :
    MinorsRA fun A : Matrix (Fin d) (Fin m) ℝ => minor A r c := by
  intro A u v t
  have hs : ∀ s : ℝ, (A + s • vecMulVec u v).submatrix r c =
      A.submatrix r c + s • vecMulVec (u ∘ r) (v ∘ c) := by
    intro s; ext i j; simp [vecMulVec_apply]
  rw [show A + vecMulVec u v = A + (1 : ℝ) • vecMulVec u v by rw [one_smul]]
  simp only [minor, hs, minors_det_add_smul_vecMulVec]
  ring

private lemma minors_minor_indep {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m)
    {J : Set (Fin m)} (hc : ∀ i, c i ∉ J) :
    MinorsIndep J fun A : Matrix (Fin d) (Fin m) ℝ => minor A r c := by
  intro A u j hj
  have : (A + vecMulVec u (Pi.single j 1)).submatrix r c = A.submatrix r c := by
    ext a b
    have hb : c b ≠ j := fun h => hc b (h ▸ hj)
    simp [vecMulVec_apply, hb]
  simp only [minor, this]

/-- The span of the minors whose columns avoid `J`. -/
private def minorsSpan (d m : ℕ) (J : Set (Fin m)) :
    Submodule ℝ (Matrix (Fin d) (Fin m) ℝ → ℝ) :=
  Submodule.span ℝ {g | ∃ (k : ℕ) (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m),
    (∀ i, c i ∉ J) ∧ g = fun A => minor A r c}

private lemma minors_span_RA_indep {J : Set (Fin m)} {g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hg : g ∈ minorsSpan d m J) : MinorsRA g ∧ MinorsIndep J g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, r, c, hc, rfl⟩ := hx
    exact ⟨minors_minor_RA r c, minors_minor_indep r c hc⟩
  | zero => exact ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    exact ⟨fun A u v t => by simp only [Pi.add_apply, hx.1 A u v t, hy.1 A u v t]; ring,
      fun A u j hj => by simp only [Pi.add_apply, hx.2 A u j hj, hy.2 A u j hj]⟩
  | smul a x _ hx =>
    exact ⟨fun A u v t => by simp only [Pi.smul_apply, smul_eq_mul, hx.1 A u v t]; ring,
      fun A u j hj => by simp only [Pi.smul_apply, hx.2 A u j hj]⟩

/-- The matrix with first row `a` and the rows of `A'` below it. -/
private def minorsRowCons (a : Fin m → ℝ) (A' : Matrix (Fin d) (Fin m) ℝ) :
    Matrix (Fin (d + 1)) (Fin m) ℝ :=
  Matrix.of (Fin.cons a fun i => A' i)

@[simp] private lemma minorsRowCons_zero (a : Fin m → ℝ) (A' : Matrix (Fin d) (Fin m) ℝ)
    (j : Fin m) : minorsRowCons a A' 0 j = a j := rfl

@[simp] private lemma minorsRowCons_succ (a : Fin m → ℝ) (A' : Matrix (Fin d) (Fin m) ℝ)
    (i : Fin d) (j : Fin m) : minorsRowCons a A' i.succ j = A' i j := rfl

private lemma minorsRowCons_eta (A : Matrix (Fin (d + 1)) (Fin m) ℝ) :
    minorsRowCons (A 0) (Matrix.of fun i => A i.succ) = A := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

private lemma minorsRowCons_add_smul (a w : Fin m → ℝ) (A' B : Matrix (Fin d) (Fin m) ℝ) (t : ℝ) :
    minorsRowCons a A' + t • minorsRowCons w B = minorsRowCons (a + t • w) (A' + t • B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

private lemma minors_vecMulVec_cons (x : ℝ) (u : Fin d → ℝ) (v : Fin m → ℝ) :
    vecMulVec (Fin.cons x u : Fin (d + 1) → ℝ) v = minorsRowCons (x • v) (vecMulVec u v) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [vecMulVec_apply]

/-- A function on `ℝ^m` that is affine along every line is affine. -/
private lemma minors_affine_of_lines {g : (Fin m → ℝ) → ℝ}
    (hg : ∀ a v (t : ℝ), g (a + t • v) = g a + t * (g (a + v) - g a)) (a : Fin m → ℝ) :
    g a = g 0 + ∑ k, a k * (g (Pi.single k 1) - g 0) := by
  have hsmul : ∀ (t : ℝ) x, g (t • x) - g 0 = t * (g x - g 0) := by
    intro t x
    have := hg 0 x t
    simp only [zero_add] at this
    rw [this]; ring
  have hadd : ∀ x y, g (x + y) - g 0 = (g x - g 0) + (g y - g 0) := by
    intro x y
    have e1 := hg x (y - x) (1 / 2)
    have e2 := hg 0 (x + y) (1 / 2)
    have e : x + (1 / 2 : ℝ) • (y - x) = 0 + (1 / 2 : ℝ) • (x + y) := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
      ring
    rw [e, e2, add_sub_cancel] at e1
    simp only [zero_add] at e1
    linarith
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => g x - g 0
      map_add' := hadd
      map_smul' := fun t x => by simp only [hsmul, smul_eq_mul, RingHom.id_apply] }
  have h := LinearMap.pi_apply_eq_sum_univ L a
  have hs : ∀ i : Fin m, (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    intro i; ext j; simp [Pi.single_apply, eq_comm]
  simp only [hs, smul_eq_mul] at h
  change g a - g 0 = ∑ i, a i * (g (Pi.single i 1) - g 0) at h
  linarith

/-- The coefficient of `a_k` in `f (a; A')`, for `f` affine in the first row `a`. -/
private def minorsH (f : Matrix (Fin (d + 1)) (Fin m) ℝ → ℝ) (k : Fin m)
    (A' : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  f (minorsRowCons (Pi.single k 1) A') - f (minorsRowCons 0 A')

private lemma minors_rowAffine {f : Matrix (Fin (d + 1)) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    (a : Fin m → ℝ) (A' : Matrix (Fin d) (Fin m) ℝ) :
    f (minorsRowCons a A') = f (minorsRowCons 0 A') + ∑ k, a k * minorsH f k A' := by
  have := minors_affine_of_lines (g := fun a => f (minorsRowCons a A')) (fun a v t => by
    have h := hf (minorsRowCons a A') (Pi.single 0 1) v t
    have e : ∀ s : ℝ, minorsRowCons a A' + s • vecMulVec (Pi.single 0 1) v =
        minorsRowCons (a + s • v) A' := by
      intro s
      have : (Pi.single 0 1 : Fin (d + 1) → ℝ) = Fin.cons 1 0 := by
        ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [Fin.succ_ne_zero]
      rw [this, minors_vecMulVec_cons, minorsRowCons_add_smul, one_smul]
      congr 1
      ext i j; simp
    have e1 := e 1
    rw [one_smul, one_smul] at e1
    rw [e t, e1] at h
    exact h) a
  simpa [minorsH] using this

private lemma minors_rowCons_RA {f : Matrix (Fin (d + 1)) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    (w : Fin m → ℝ) : MinorsRA fun A' => f (minorsRowCons w A') := by
  intro A' u v t
  have h := hf (minorsRowCons w A') (Fin.cons 0 u) v t
  have e : ∀ s : ℝ, minorsRowCons w A' + s • vecMulVec (Fin.cons 0 u : Fin (d + 1) → ℝ) v =
      minorsRowCons w (A' + s • vecMulVec u v) := by
    intro s
    rw [minors_vecMulVec_cons, minorsRowCons_add_smul, zero_smul, smul_zero, add_zero]
  have e1 := e 1
  rw [one_smul, one_smul] at e1
  rw [e t, e1] at h
  exact h

private lemma minors_H_RA {f : Matrix (Fin (d + 1)) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    (k : Fin m) : MinorsRA (minorsH f k) := by
  intro A' u v t
  have h1 := minors_rowCons_RA hf (Pi.single k 1) A' u v t
  have h2 := minors_rowCons_RA hf 0 A' u v t
  simp only [minorsH] at h1 h2 ⊢
  rw [h1, h2]
  ring

/-- The constraint linking the coefficients `h_k` of the first row: adding `u' ⊗ v` to the other
rows does not change `∑ v_k h_k` (the `t²` coefficient of `f` along the rank-one line
`(1; u') ⊗ v` vanishes). -/
private lemma minors_invariance {f : Matrix (Fin (d + 1)) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    (v : Fin m → ℝ) (u' : Fin d → ℝ) (A' : Matrix (Fin d) (Fin m) ℝ) :
    ∑ k, v k * minorsH f k (A' + vecMulVec u' v) = ∑ k, v k * minorsH f k A' := by
  have hB : ∀ t : ℝ, minorsRowCons 0 A' + t • vecMulVec (Fin.cons 1 u' : Fin (d + 1) → ℝ) v =
      minorsRowCons (t • v) (A' + t • vecMulVec u' v) := by
    intro t
    rw [minors_vecMulVec_cons, minorsRowCons_add_smul, one_smul, zero_add]
  have hF0 : ∀ t : ℝ, f (minorsRowCons 0 (A' + t • vecMulVec u' v)) =
      f (minorsRowCons 0 A') + t * (f (minorsRowCons 0 (A' + vecMulVec u' v)) -
        f (minorsRowCons 0 A')) :=
    fun t => minors_rowCons_RA hf 0 A' u' v t
  have expand : ∀ t : ℝ,
      f (minorsRowCons 0 A' + t • vecMulVec (Fin.cons 1 u' : Fin (d + 1) → ℝ) v) =
      f (minorsRowCons 0 A') + t * (f (minorsRowCons 0 (A' + vecMulVec u' v)) -
        f (minorsRowCons 0 A')) + t * ∑ k, v k * minorsH f k A' +
        t ^ 2 * ∑ k, v k * (minorsH f k (A' + vecMulVec u' v) - minorsH f k A') := by
    intro t
    rw [hB, minors_rowAffine hf, hF0 t]
    have hk : ∀ k, minorsH f k (A' + t • vecMulVec u' v) =
        minorsH f k A' + t * (minorsH f k (A' + vecMulVec u' v) - minorsH f k A') :=
      fun k => minors_H_RA hf k A' u' v t
    simp only [hk, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [add_assoc, add_assoc, ← Finset.sum_add_distrib, add_assoc]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hRA := hf (minorsRowCons 0 A') (Fin.cons 1 u') v (-1)
  have e0 := expand 0
  have e1 := expand 1
  have em := expand (-1)
  simp only [zero_smul, add_zero, one_smul] at e0 e1
  rw [em, e1, e0] at hRA
  have : ∑ k, v k * (minorsH f k (A' + vecMulVec u' v) - minorsH f k A') = 0 := by nlinarith
  simp only [mul_sub, Finset.sum_sub_distrib] at this
  linarith

private lemma minorsRowCons_add_vecMulVec (w : Fin m → ℝ) (A' : Matrix (Fin d) (Fin m) ℝ)
    (u : Fin d → ℝ) (v : Fin m → ℝ) :
    minorsRowCons w (A' + vecMulVec u v) =
      minorsRowCons w A' + vecMulVec (Fin.cons 0 u : Fin (d + 1) → ℝ) v := by
  rw [minors_vecMulVec_cons, ← one_smul ℝ (minorsRowCons (0 • v) (vecMulVec u v)),
    minorsRowCons_add_smul, zero_smul, smul_zero, add_zero, one_smul]

private lemma minors_RA_sub {f g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    (hg : MinorsRA g) : MinorsRA (f - g) := by
  intro A u v t
  simp only [Pi.sub_apply, hf A u v t, hg A u v t]
  ring

private lemma minors_indep_sub {J : Set (Fin m)} {f g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : MinorsIndep J f) (hg : MinorsIndep J g) : MinorsIndep J (f - g) := by
  intro A u j hj
  simp only [Pi.sub_apply, hf A u j hj, hg A u j hj]

/-- Minors of the rows below the first are minors of the whole matrix. -/
private lemma minors_tail_mem {J : Set (Fin m)} {g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hg : g ∈ minorsSpan d m J) :
    (fun A : Matrix (Fin (d + 1)) (Fin m) ℝ => g (Matrix.of fun i => A i.succ)) ∈
      minorsSpan (d + 1) m J := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, r, c, hc, rfl⟩ := hx
    exact Submodule.subset_span ⟨k, r.trans (Fin.succOrderEmb d), c, hc, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

/-- The minor of `(a; A')` with rows `{0} ∪ (1 + r')` and columns `{n} ∪ c'` (all of `c'` beyond
`n`): its coefficient of `a_n` is the minor of `A'` with rows `r'` and columns `c'`, and it has no
coefficient of `a_j`, `j < n` (Laplace expansion along the first row). -/
private lemma minors_lift_gen {J : Set (Fin m)} (n : Fin m) (hn : n ∉ J) {p : ℕ}
    (r' : Fin p ↪o Fin d) (c' : Fin p ↪o Fin m) (hc' : ∀ i, c' i ∉ J ∪ Set.Iic n) :
    ∃ G ∈ minorsSpan (d + 1) m J,
      (∀ j : Fin m, j < n → ∀ A',
        G (minorsRowCons (Pi.single j 1) A') = G (minorsRowCons 0 A')) ∧
      ∀ A', G (minorsRowCons (Pi.single n 1) A') - G (minorsRowCons 0 A') = minor A' r' c' := by
  have hgt : ∀ i, n < c' i := fun i => lt_of_not_ge fun h => hc' i (Or.inr h)
  have hJ : ∀ i, c' i ∉ J := fun i h => hc' i (Or.inl h)
  let R : Fin (p + 1) ↪o Fin (d + 1) :=
    OrderEmbedding.ofStrictMono (Fin.cons 0 (Fin.succ ∘ r'))
      (Fin.strictMono_cons.2 ⟨fun j => Fin.succ_pos _, Fin.strictMono_succ.comp r'.strictMono⟩)
  let C : Fin (p + 1) ↪o Fin m :=
    OrderEmbedding.ofStrictMono (Fin.cons n c') (Fin.strictMono_cons.2 ⟨hgt, c'.strictMono⟩)
  have hR0 : R 0 = 0 := rfl
  have hRs : ∀ i, R i.succ = (r' i).succ := fun _ => rfl
  have hC0 : C 0 = n := rfl
  have hCs : ∀ i, C i.succ = c' i := fun _ => rfl
  have hz : ∀ w : Fin m → ℝ, (∀ i, w (C i) = 0) → ∀ A', minor (minorsRowCons w A') R C = 0 := by
    intro w hw A'
    refine det_eq_zero_of_row_eq_zero 0 fun i => ?_
    simp only [submatrix_apply, hR0, minorsRowCons_zero, hw]
  have hCge : ∀ i, n ≤ C i := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact le_of_eq hC0.symm
    · rw [hCs]; exact (hgt i).le
  refine ⟨fun A => minor A R C, Submodule.subset_span ⟨p + 1, R, C, ?_, rfl⟩, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hC0]; exact hn
    · rw [hCs]; exact hJ i
  · intro j hj A'
    beta_reduce
    rw [hz _ (fun i => ?_) A', hz 0 (fun i => rfl) A']
    have : C i ≠ j := fun h => absurd (h ▸ hCge i) (not_le.2 hj)
    simp [this]
  · intro A'
    beta_reduce
    rw [hz 0 (fun i => rfl) A', sub_zero]
    unfold minor
    rw [det_succ_row_zero, Fin.sum_univ_succ]
    have hrest : ∀ i : Fin p, ((minorsRowCons (Pi.single n 1) A').submatrix R C) 0 i.succ = 0 := by
      intro i
      simp only [submatrix_apply, hR0, hCs, minorsRowCons_zero]
      simp [(hgt i).ne']
    simp only [hrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [submatrix_apply, hR0, hC0, minorsRowCons_zero, Fin.val_zero, pow_zero,
      Pi.single_eq_same, one_mul, Fin.succAbove_zero]
    rfl

private lemma minors_lift_span {J : Set (Fin m)} (n : Fin m) (hn : n ∉ J)
    {g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hg : g ∈ minorsSpan d m (J ∪ Set.Iic n)) :
    ∃ G ∈ minorsSpan (d + 1) m J,
      (∀ j : Fin m, j < n → ∀ A',
        G (minorsRowCons (Pi.single j 1) A') = G (minorsRowCons 0 A')) ∧
      ∀ A', G (minorsRowCons (Pi.single n 1) A') - G (minorsRowCons 0 A') = g A' := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, r, c, hc, rfl⟩ := hx
    exact minors_lift_gen n hn r c hc
  | zero => exact ⟨0, Submodule.zero_mem _, fun _ _ _ => rfl, fun _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨G1, h1, a1, b1⟩ := hx
    obtain ⟨G2, h2, a2, b2⟩ := hy
    refine ⟨G1 + G2, Submodule.add_mem _ h1 h2, fun j hj A' => ?_, fun A' => ?_⟩
    · simp only [Pi.add_apply, a1 j hj, a2 j hj]
    · simp only [Pi.add_apply, ← b1, ← b2]; ring
  | smul a x _ hx =>
    obtain ⟨G, h, a1, b1⟩ := hx
    refine ⟨a • G, Submodule.smul_mem _ a h, fun j hj A' => ?_, fun A' => ?_⟩
    · simp only [Pi.smul_apply, a1 j hj]
    · simp only [Pi.smul_apply, smul_eq_mul, ← b1]; ring

/-- The coefficient `h_n` of a column `n ∈ J` vanishes. -/
private lemma minors_H_eq_zero_of_mem {J : Set (Fin m)} {f : Matrix (Fin (d + 1)) (Fin m) ℝ → ℝ}
    (hJ : MinorsIndep J f) {n : Fin m} (hn : n ∈ J) (A' : Matrix (Fin d) (Fin m) ℝ) :
    minorsH f n A' = 0 := by
  have h := hJ (minorsRowCons 0 A') (Pi.single 0 1) n hn
  have e : minorsRowCons 0 A' + vecMulVec (Pi.single 0 1) (Pi.single n 1) =
      minorsRowCons (Pi.single n 1) A' := by
    have : (Pi.single 0 1 : Fin (d + 1) → ℝ) = Fin.cons 1 0 := by
      ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [Fin.succ_ne_zero]
    rw [this, minors_vecMulVec_cons, ← one_smul ℝ (minorsRowCons (1 • Pi.single n 1) _),
      minorsRowCons_add_smul, one_smul, one_smul, zero_add]
    congr 1
    ext i j; simp
  rw [e] at h
  simp [minorsH, h]

/-- **The induction of Theorem 5.20.** A function on `ℝ^{d×m}` that is affine along the rank-one
lines and independent of the columns in `J` is a linear combination of the minors avoiding the
columns `J`. Induction on the number of rows: write `f (a; A') = f (0; A') + ∑_k a_k h_k (A')`;
`f (0; ·)` is covered by the induction hypothesis, and the coefficients `h_n` are removed one at a
time, in increasing order of `n`: the rank-one lines `(1; u') ⊗ v` show that once `h_j = 0` for
`j < n`, `h_n` is independent of the columns `j ≤ n` (and of `J`), so by induction it is a
combination of minors of `A'` with columns beyond `n`, which is the coefficient of `a_n` of the
corresponding minors of `(a; A')` with row `0` and column `n` added (Laplace expansion). -/
private lemma minors_main : ∀ (d : ℕ) (J : Set (Fin m)) (f : Matrix (Fin d) (Fin m) ℝ → ℝ),
    MinorsRA f → MinorsIndep J f → f ∈ minorsSpan d m J := by
  intro d
  induction d with
  | zero =>
    intro J f _ _
    let r0 : Fin 0 ↪o Fin 0 := OrderEmbedding.ofIsEmpty
    let c0 : Fin 0 ↪o Fin m := OrderEmbedding.ofIsEmpty
    have hf : f = f 0 • fun A : Matrix (Fin 0) (Fin m) ℝ => minor A r0 c0 := by
      ext A
      have hA : A = 0 := by ext i; exact i.elim0
      simp [minor, hA, det_isEmpty]
    rw [hf]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, r0, c0, fun i => i.elim0, rfl⟩)
  | succ d ih =>
    intro J f hf hJ
    have claim : ∀ k n, n + k = m → ∀ f : Matrix (Fin (d + 1)) (Fin m) ℝ → ℝ, MinorsRA f →
        MinorsIndep J f → (∀ j : Fin m, j.val < n → ∀ A', minorsH f j A' = 0) →
        f ∈ minorsSpan (d + 1) m J := by
      intro k
      induction k with
      | zero =>
        intro n hn f hf hJ hH
        have hF0 : (fun A' => f (minorsRowCons 0 A')) ∈ minorsSpan d m J := by
          refine ih J _ (minors_rowCons_RA hf 0) (fun A' u j hj => ?_)
          simp only [minorsRowCons_add_vecMulVec]
          exact hJ _ _ j hj
        convert minors_tail_mem hF0 using 1
        ext A
        conv_lhs => rw [← minorsRowCons_eta A]
        rw [minors_rowAffine hf, Finset.sum_eq_zero fun k _ => by rw [hH k (by omega), mul_zero],
          add_zero]
      | succ k ih2 =>
        intro n hn f hf hJ hH
        have hnm : n < m := by omega
        by_cases hnJ : (⟨n, hnm⟩ : Fin m) ∈ J
        · refine ih2 (n + 1) (by omega) f hf hJ fun j hj A' => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
          · exact hH j h A'
          · have : j = ⟨n, hnm⟩ := Fin.ext h
            subst this
            exact minors_H_eq_zero_of_mem hJ hnJ A'
        · set nn : Fin m := ⟨n, hnm⟩ with hnn
          -- `h_n` is independent of the column `n`
          have hself : ∀ A' (u : Fin d → ℝ),
              minorsH f nn (A' + vecMulVec u (Pi.single nn 1)) = minorsH f nn A' := by
            intro A' u
            have := minors_invariance hf (Pi.single nn 1) u A'
            simpa [Pi.single_apply] using this
          have hind : MinorsIndep (J ∪ Set.Iic nn) (minorsH f nn) := by
            intro A' u j hj
            rcases hj with hjJ | hjle
            · simp only [minorsH, minorsRowCons_add_vecMulVec]
              rw [hJ _ _ j hjJ, hJ _ _ j hjJ]
            · rcases lt_or_eq_of_le (Set.mem_Iic.1 hjle) with hlt | heq
              · have hj0 : ∀ A'', minorsH f j A'' = 0 := hH j hlt
                have hjn : j ≠ nn := hlt.ne
                have := minors_invariance hf (Pi.single j 1 + Pi.single nn 1) u A'
                simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Pi.single_apply,
                  ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
                  hj0, zero_add] at this
                rw [vecMulVec_add, ← add_assoc, hself] at this
                exact this
              · subst heq
                exact hself A' u
          have hmem := ih (J ∪ Set.Iic nn) _ (minors_H_RA hf nn) hind
          obtain ⟨G, hG, hG1, hG2⟩ := minors_lift_span nn hnJ hmem
          have hGp := minors_span_RA_indep hG
          have hfG : f - G ∈ minorsSpan (d + 1) m J := by
            refine ih2 (n + 1) (by omega) (f - G) (minors_RA_sub hf hGp.1)
              (minors_indep_sub hJ hGp.2) fun j hj A' => ?_
            have e : minorsH (f - G) j A' = minorsH f j A' -
                (G (minorsRowCons (Pi.single j 1) A') - G (minorsRowCons 0 A')) := by
              simp only [minorsH, Pi.sub_apply]; ring
            rw [e]
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
            · rw [hH j h A', hG1 j h A', sub_self, sub_self]
            · have : j = nn := Fin.ext h
              subst this
              rw [hG2, sub_self]
          have : f = (f - G) + G := by abel
          rw [this]
          exact Submodule.add_mem _ hfG hG
    exact claim m 0 (by omega) f hf hJ fun j hj => absurd hj (Nat.not_lt_zero _)

end RankOneAffine

/-- **Dacorogna, Theorem 5.20** ((iii) ⇒ (iv)): a rank-one affine `f : ℝ^{d×m} → ℝ` is an affine
combination of the minors of its argument.

Proof (continuity is not needed): `f` is affine along each rank-one line `A + t (u ⊗ v)`; such a
function is affine in each row, and an induction on the number of rows (`minors_main`) writes it
as a combination of minors, the coefficients of the first row being identified through the
rank-one lines `(1; u') ⊗ v` and the Laplace expansion of the determinant along its first row. The
minors are themselves rank-one affine by the matrix determinant lemma
(`minors_det_add_smul_vecMulVec`).

Departure from the source (to be checked): Dacorogna's own proof of (iii) ⇒ (iv) was not available
to this formalization (no access to the book); the argument above is a direct induction on the
number of rows, using only the definition of rank-one affinity and the Laplace expansion, in the
spirit of the classical characterisation of null Lagrangians (Ball–Currie–Olver 1981). -/
theorem rankOneAffineMinors_holds : RankOneAffineMinors := by
  intro d m f _ hf
  have hmem := minors_main d (∅ : Set (Fin m)) f (minors_RA_of_rankOneAffine hf)
    (fun _ _ _ h => absurd h (Set.notMem_empty _))
  let ι := Σ k : Fin (min d m + 1), (Fin k ↪o Fin d) × (Fin k ↪o Fin m)
  let v : ι → Matrix (Fin d) (Fin m) ℝ → ℝ := fun i A => minor A i.2.1 i.2.2
  have hle : minorsSpan d m ∅ ≤ Submodule.span ℝ (Set.range v) := by
    refine Submodule.span_le.2 ?_
    rintro g ⟨k, r, c, -, rfl⟩
    have hk : k < min d m + 1 := by
      have h1 := Fintype.card_le_of_embedding r.toEmbedding
      have h2 := Fintype.card_le_of_embedding c.toEmbedding
      simp only [Fintype.card_fin] at h1 h2
      omega
    exact Submodule.subset_span ⟨⟨⟨k, hk⟩, (r, c)⟩, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hle hmem)
  refine ⟨fun k r c => if hk : k < min d m + 1 then a ⟨⟨k, hk⟩, (r, c)⟩ else 0, fun A => ?_⟩
  rw [← ha, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [k.isLt, ↓reduceDIte, Pi.smul_apply, smul_eq_mul, v]

end External.Dacorogna
