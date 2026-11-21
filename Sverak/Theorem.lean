module

public import Sverak.Lemma2
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Šverák 1992: the Theorem, the Corollary and the Remark

* `theorem_main` (`sv-theorem`): there exist `ε > 0` and `k > 0` such that `F = sverakF ε k`
  is rank-one convex but not quasiconvex.
* `corollary` (`sv-corollary`): for `n ≥ 2` and `m ≥ 3`, `F̃ (X) = F (T X)`, with `T X` the upper
  left `3 × 2` block of `X ∈ M^{m×n}`, is rank-one convex but not quasiconvex.
* `remark_polynomial` (`sv-remark`): `F` is a polynomial of degree four.
* `equation11` (`sv-eq11`): the choice of `ε` by (10), of `k` by Lemma 2, and (11).
-/

@[expose] public section

namespace Sverak

/-! ### The polynomial of the Remark -/

section Poly

open MvPolynomial

/-- `f (P X) = −X₀₀ X₁₁ (X₂₀ + X₂₁)/2` as a polynomial. -/
private noncomputable def thm_pf : MvPolynomial (Fin 3 × Fin 2) ℝ :=
  -(X (0, 0) * X (1, 1) * (C (1 / 2) * (X (2, 0) + X (2, 1))))

/-- `|X|²` as a polynomial. -/
private noncomputable def thm_pS : MvPolynomial (Fin 3 × Fin 2) ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 2, X (i, j) ^ 2

/-- `|X − P X|² = X₀₁² + X₁₀² + (X₂₀ − X₂₁)²/2` as a polynomial. -/
private noncomputable def thm_pQ : MvPolynomial (Fin 3 × Fin 2) ℝ :=
  X (0, 1) ^ 2 + X (1, 0) ^ 2 + C (1 / 2) * (X (2, 0) - X (2, 1)) ^ 2

/-- Šverák's `F` as a polynomial. -/
private noncomputable def thm_poly (ε k : ℝ) : MvPolynomial (Fin 3 × Fin 2) ℝ :=
  thm_pf + C ε * thm_pS + C ε * thm_pS ^ 2 + C k * thm_pQ

private theorem thm_eval_poly (ε k : ℝ) (A : Matrix (Fin 3) (Fin 2) ℝ) :
    sverakF ε k A = eval (fun ij => A ij.1 ij.2) (thm_poly ε k) := by
  simp [thm_poly, thm_pf, thm_pS, thm_pQ, sverakF, sverakf, sverakP, frobSq, Fin.sum_univ_succ,
    Matrix.sub_apply]
  ring

private theorem thm_pf_hom : thm_pf.IsHomogeneous 3 :=
  (((isHomogeneous_X ℝ _).mul (isHomogeneous_X ℝ _)).mul
    ((isHomogeneous_C _ _).mul ((isHomogeneous_X ℝ _).add (isHomogeneous_X ℝ _)))).neg

private theorem thm_pS_hom : thm_pS.IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun _ _ => IsHomogeneous.sum _ _ _ fun _ _ =>
    (isHomogeneous_X ℝ _).pow 2

private theorem thm_pQ_hom : thm_pQ.IsHomogeneous 2 :=
  (((isHomogeneous_X ℝ _).pow 2).add ((isHomogeneous_X ℝ _).pow 2)).add
    ((isHomogeneous_C _ _).mul (((isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)).pow 2))

end Poly

/-- `F` is continuous: it is a polynomial in the entries. -/
theorem thm_sverakF_continuous (ε k : ℝ) : Continuous (sverakF ε k) := by
  have : sverakF ε k = fun A => MvPolynomial.eval (fun ij => A ij.1 ij.2) (thm_poly ε k) :=
    funext (thm_eval_poly ε k)
  rw [this]
  exact (MvPolynomial.continuous_eval _).comp (by fun_prop)

/-! ### The estimates (10) and (11) -/

section Key

open MeasureTheory Real

/-- On `L` the term `k |X − P X|²` vanishes: `F (r 0; 0 s; t t) = −r s t + ε |·|² + ε |·|⁴` with
`|·|² = r² + s² + 2t²`. -/
private theorem thm_sverakF_ofRST (ε k r s t : ℝ) :
    sverakF ε k (ofRST r s t) =
      -(r * s * t) + ε * (r ^ 2 + s ^ 2 + 2 * t ^ 2) + ε * (r ^ 2 + s ^ 2 + 2 * t ^ 2) ^ 2 := by
  simp [sverakF, sverakf, sverakP, ofRST, frobSq, Fin.sum_univ_succ, Matrix.sub_apply]
  ring

/-- A continuous function is integrable on the unit cube. -/
private theorem thm_integrableOn_unitCube {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    IntegrableOn g (unitCube n) := by
  refine (hg.continuousOn.integrableOn_compact
    (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1))).mono_set ?_
  intro x hx i _
  exact ⟨(hx i (Set.mem_univ i)).1.le, (hx i (Set.mem_univ i)).2.le⟩

/-- `F (D w (x))`, explicitly. -/
private theorem thm_sverakF_jac_w (ε k : ℝ) :
    (fun x : Fin 2 → ℝ => sverakF ε k (jac w x)) = fun x =>
      -(cos (2 * π * x 0) * cos (2 * π * x 1) * cos (2 * π * (x 0 + x 1))) +
        ε * (cos (2 * π * x 0) ^ 2 + cos (2 * π * x 1) ^ 2 + 2 * cos (2 * π * (x 0 + x 1)) ^ 2) +
        ε * (cos (2 * π * x 0) ^ 2 + cos (2 * π * x 1) ^ 2 +
          2 * cos (2 * π * (x 0 + x 1)) ^ 2) ^ 2 := by
  funext x; rw [jac_w, thm_sverakF_ofRST]

private theorem thm_continuous_sverakF_jac_w (ε k : ℝ) :
    Continuous fun x : Fin 2 → ℝ => sverakF ε k (jac w x) := by
  rw [thm_sverakF_jac_w]; fun_prop

/-- **(10) and (11)** (`sv-eq11`), the heart of the proof of the Theorem: `ε` with (10), `k` from
Lemma 2, and `∫_{[0,1]²} F (Dw) < 0 = F (0)`. -/
theorem equation11 : ∃ ε > 0, ∃ k > 0, RankOneConvex (sverakF ε k) ∧
    ∫ x in unitCube 2, sverakF ε k (jac w x) < sverakF ε k 0 := by
  set I := ∫ x in unitCube 2, sverakf (jac w x) with hI
  have hI0 : I < 0 := by
    have h := equation4.2
    have hf0 : sverakf 0 = 0 := by simp [sverakf, sverakP]
    rwa [hf0] at h
  set ε := -I / 40 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨k, hk, hR⟩ := lemma2 hεpos
  refine ⟨ε, hεpos, k, hk, hR, ?_⟩
  have hF0 : sverakF ε k 0 = 0 := by
    simp [sverakF, sverakf, sverakP, frobSq, Fin.sum_univ_succ, Matrix.sub_apply]
  rw [hF0]
  have hf : (fun x : Fin 2 → ℝ => sverakf (jac w x)) = fun x =>
      -(cos (2 * π * x 0) * cos (2 * π * x 1) * cos (2 * π * (x 0 + x 1))) := by
    funext x; rw [jac_w, sverakf_ofRST]
  have hF := thm_sverakF_jac_w ε k
  have hcf : Continuous fun x : Fin 2 → ℝ => sverakf (jac w x) := by rw [hf]; fun_prop
  have hcF := thm_continuous_sverakF_jac_w ε k
  -- `|D w|² ≤ 4`, so the `ε`-terms are at most `20 ε`
  have hpt : ∀ x : Fin 2 → ℝ, sverakF ε k (jac w x) ≤ sverakf (jac w x) + 20 * ε := by
    intro x
    have h1 := congrFun hF x
    have h2 := congrFun hf x
    rw [h1, h2]
    have ha := cos_sq_le_one (2 * π * x 0)
    have hb := cos_sq_le_one (2 * π * x 1)
    have hc := cos_sq_le_one (2 * π * (x 0 + x 1))
    set S := cos (2 * π * x 0) ^ 2 + cos (2 * π * x 1) ^ 2 + 2 * cos (2 * π * (x 0 + x 1)) ^ 2
      with hS
    have hS0 : 0 ≤ S := by positivity
    have hS4 : S ≤ 4 := by rw [hS]; linarith
    have hS16 : S ^ 2 ≤ 16 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hS4 hεpos.le, mul_le_mul_of_nonneg_left hS16 hεpos.le]
  calc ∫ x in unitCube 2, sverakF ε k (jac w x)
      ≤ ∫ x in unitCube 2, (sverakf (jac w x) + 20 * ε) :=
        setIntegral_mono (thm_integrableOn_unitCube hcF)
          (thm_integrableOn_unitCube (hcf.add continuous_const)) hpt
    _ = I + 20 * ε := by
        rw [integral_add (thm_integrableOn_unitCube hcf)
          (thm_integrableOn_unitCube continuous_const), setIntegral_const]
        simp [Measure.real, volume_unitCube, hI]
    _ < 0 := by rw [hε]; linarith

end Key

/-- **Theorem** (`sv-theorem`). There exist `ε > 0` and `k > 0` such that the function `F` given
by (5) is rank-one convex but is not quasiconvex. -/
theorem theorem_main :
    ∃ ε > 0, ∃ k > 0, RankOneConvex (sverakF ε k) ∧ ¬ QuasiconvexOn (unitCube 2) (sverakF ε k) := by
  obtain ⟨ε, hε, k, hk, hR, hlt⟩ := equation11
  refine ⟨ε, hε, k, hk, hR, fun hQ => ?_⟩
  have h := (lemma1 (thm_sverakF_continuous ε k)).1 hQ 0 w w_contDiff w_periodic
  simp only [zero_add] at h
  linarith

/-! ### The Corollary -/

section Cor

open MeasureTheory

variable {m n : ℕ}

private theorem thm_topLeft_add_smul (hm : 3 ≤ m) (hn : 2 ≤ n) (A B : Matrix (Fin m) (Fin n) ℝ)
    (t : ℝ) : topLeft hm hn (A + t • B) = topLeft hm hn A + t • topLeft hm hn B := by
  ext i j; simp [topLeft]

private theorem thm_topLeft_zero (hm : 3 ≤ m) (hn : 2 ≤ n) :
    topLeft hm hn (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  ext i j; simp [topLeft]

private theorem thm_topLeft_continuous (hm : 3 ≤ m) (hn : 2 ≤ n) :
    Continuous (topLeft hm hn) :=
  continuous_id.matrix_submatrix (Fin.castLE hm) (Fin.castLE hn)

private theorem thm_eq_zero_of_rank_eq_zero {p q : ℕ} {A : Matrix (Fin p) (Fin q) ℝ}
    (h : A.rank = 0) : A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply] using this

/-- `T` maps rank-one lines to rank-one lines or to points, so `F ∘ T` is rank-one convex. -/
private theorem thm_rankOneConvex_topLeft (hm : 3 ≤ m) (hn : 2 ≤ n)
    {F : Matrix (Fin 3) (Fin 2) ℝ → ℝ} (hF : RankOneConvex F) :
    RankOneConvex fun X : Matrix (Fin m) (Fin n) ℝ => F (topLeft hm hn X) := by
  intro A B hB
  have hle : (topLeft hm hn B).rank ≤ 1 :=
    hB ▸ Matrix.rank_submatrix_le B (Fin.castLE hm) (Fin.castLE hn)
  simp_rw [thm_topLeft_add_smul]
  by_cases h1 : (topLeft hm hn B).rank = 1
  · exact hF _ _ h1
  · have h0 : topLeft hm hn B = 0 := thm_eq_zero_of_rank_eq_zero (by omega)
    simp only [h0, smul_zero, add_zero]
    exact convexOn_const _ convex_univ

/-- The projection `(x₁, …, x_n) ↦ (x₁, x₂)`. -/
private noncomputable def thm_proj (hn : 2 ≤ n) : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.castLE hn j)

private theorem thm_proj_apply (hn : 2 ≤ n) (x : Fin n → ℝ) (j : Fin 2) :
    thm_proj hn x j = x (Fin.castLE hn j) := rfl

/-- Šverák's `w̃ (x₁, …, x_n) = (w₁ (x₁, x₂), w₂ (x₁, x₂), w₃ (x₁, x₂), 0, …, 0)`. -/
private noncomputable def thm_wt (_hm : 3 ≤ m) (hn : 2 ≤ n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => if h : (i : ℕ) < 3 then w (thm_proj hn x) ⟨i, h⟩ else 0

private theorem thm_wt_contDiff (hm : 3 ≤ m) (hn : 2 ≤ n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (thm_wt hm hn) := by
  rw [contDiff_pi]
  intro i
  by_cases h : (i : ℕ) < 3
  · simp only [thm_wt, h, ↓reduceDIte]
    exact (contDiff_pi.1 w_contDiff ⟨i, h⟩).comp (thm_proj hn).contDiff
  · simp only [thm_wt, h, ↓reduceDIte]
    exact contDiff_const

private theorem thm_wt_periodic (hm : 3 ≤ m) (hn : 2 ≤ n) : IsPeriodic (thm_wt hm hn) := by
  intro x z
  have h : thm_proj hn (x + fun i => (z i : ℝ)) =
      thm_proj hn x + fun j => ((z (Fin.castLE hn j) : ℤ) : ℝ) := by
    rw [map_add]; rfl
  have h2 : w (thm_proj hn (x + fun i => (z i : ℝ))) = w (thm_proj hn x) := by
    rw [h]; exact w_periodic _ fun j => z (Fin.castLE hn j)
  funext i
  simp only [thm_wt, h2]

/-- `T (D w̃ (x)) = D w (x₁, x₂)`. -/
private theorem thm_topLeft_jac_wt (hm : 3 ≤ m) (hn : 2 ≤ n) (x : Fin n → ℝ) :
    topLeft hm hn (jac (thm_wt hm hn) x) = jac w (thm_proj hn x) := by
  ext i j
  have hfun : (fun y => thm_wt hm hn y (Fin.castLE hm i)) = (fun z => w z i) ∘ thm_proj hn := by
    funext y
    simp [thm_wt, i.2]
  have hd : DifferentiableAt ℝ (fun z => w z i) (thm_proj hn x) :=
    ((contDiff_pi.1 w_contDiff i).differentiable (by simp)).differentiableAt
  have hsingle : thm_proj hn (Pi.single (Fin.castLE hn j) 1) = Pi.single j 1 := by
    funext j'
    simp only [thm_proj_apply, Pi.single_apply, (Fin.castLE_injective hn).eq_iff]
  simp only [topLeft, jac, Matrix.of_apply]
  rw [hfun, (hd.hasFDerivAt.comp x (thm_proj hn).hasFDerivAt).fderiv]
  simp [hsingle]

/-- The image of the uniform measure on `(0, 1)^n` under `(x₁, …, x_n) ↦ (x₁, x₂)` is the uniform
measure on `(0, 1)²` (Fubini: the other factor has volume `1`). -/
private theorem thm_map_proj (hn : 2 ≤ n) :
    (volume.restrict (unitCube n)).map (thm_proj hn) = volume.restrict (unitCube 2) := by
  have h2 : volume.restrict (unitCube 2) =
      Measure.pi fun _ : Fin 2 => volume.restrict (Set.Ioo (0 : ℝ) 1) := by
    rw [unitCube, volume_pi, Measure.restrict_pi_pi]
  rw [h2]
  refine (Measure.pi_eq (μ := fun _ : Fin 2 => volume.restrict (Set.Ioo (0 : ℝ) 1))
    fun s hs => ?_).symm
  have hmeas := MeasurableSet.univ_pi hs
  rw [Measure.map_apply (thm_proj hn).continuous.measurable hmeas,
    Measure.restrict_apply ((thm_proj hn).continuous.measurable hmeas)]
  simp_rw [Measure.restrict_apply (hs _)]
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hset : (thm_proj hn ⁻¹' Set.univ.pi s) ∩ unitCube (2 + l) =
      Set.univ.pi fun i : Fin (2 + l) =>
        if h : (i : ℕ) < 2 then s ⟨i, h⟩ ∩ Set.Ioo 0 1 else Set.Ioo 0 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      thm_proj_apply, unitCube]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases hi : (i : ℕ) < 2
      · simp only [hi, ↓reduceDIte]
        refine ⟨?_, h2 i⟩
        have := h1 ⟨i, hi⟩
        have hc : Fin.castLE hn ⟨i, hi⟩ = i := Fin.ext rfl
        rwa [hc] at this
      · simp only [hi, ↓reduceDIte]; exact h2 i
    · intro h
      refine ⟨fun j => ?_, fun i => ?_⟩
      · have := h (Fin.castLE hn j)
        simp only [Fin.val_castLE, j.2, ↓reduceDIte] at this
        exact this.1
      · have := h i
        by_cases hi : (i : ℕ) < 2
        · simp only [hi, ↓reduceDIte] at this; exact this.2
        · simp only [hi, ↓reduceDIte] at this; exact this
  rw [hset, volume_pi_pi, Fin.prod_univ_add]
  have hnot : ∀ x : ℕ, ¬ (2 + x ≤ 1) := fun x => by omega
  simp [hnot]

private theorem thm_integral_proj (hn : 2 ≤ n) {G : (Fin 2 → ℝ) → ℝ} (hG : Continuous G) :
    ∫ x in unitCube n, G (thm_proj hn x) = ∫ y in unitCube 2, G y := by
  rw [← thm_map_proj hn, integral_map (thm_proj hn).continuous.measurable.aemeasurable
    hG.aestronglyMeasurable]

end Cor

/-- **Corollary** (`sv-corollary`). Let `n ≥ 2` and `m ≥ 3`, and `F̃ (X) = F (T X)` with `F` the
function of the Theorem and `T X` the upper left `3 × 2` block of `X`. Then `F̃` is rank-one convex
but is not quasiconvex. -/
theorem corollary :
    ∃ ε > 0, ∃ k > 0, ∀ {m n : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n),
      RankOneConvex (fun X : Matrix (Fin m) (Fin n) ℝ => sverakF ε k (topLeft hm hn X)) ∧
        ¬ QuasiconvexOn (unitCube n)
          (fun X : Matrix (Fin m) (Fin n) ℝ => sverakF ε k (topLeft hm hn X)) := by
  obtain ⟨ε, hε, k, hk, hR, hlt⟩ := equation11
  refine ⟨ε, hε, k, hk, fun {m n} hm hn => ⟨thm_rankOneConvex_topLeft hm hn hR, fun hQ => ?_⟩⟩
  have hcont : Continuous fun X : Matrix (Fin m) (Fin n) ℝ => sverakF ε k (topLeft hm hn X) :=
    (thm_sverakF_continuous ε k).comp (thm_topLeft_continuous hm hn)
  have h := (lemma1 hcont).1 hQ 0 (thm_wt hm hn) (thm_wt_contDiff hm hn) (thm_wt_periodic hm hn)
  have heq : ∫ x in unitCube n, sverakF ε k (topLeft hm hn (0 + jac (thm_wt hm hn) x)) =
      ∫ x in unitCube 2, sverakF ε k (jac w x) := by
    simp_rw [zero_add, thm_topLeft_jac_wt]
    exact thm_integral_proj hn (thm_continuous_sverakF_jac_w ε k)
  rw [heq, thm_topLeft_zero] at h
  linarith

/-- **Remark** (`sv-remark`). `F` is a polynomial of degree four in the entries of the matrix
(for `ε ≠ 0`). -/
theorem remark_polynomial {ε : ℝ} (hε : ε ≠ 0) (k : ℝ) :
    ∃ P : MvPolynomial (Fin 3 × Fin 2) ℝ, P.totalDegree = 4 ∧
      ∀ X, sverakF ε k X = MvPolynomial.eval (fun ij => X ij.1 ij.2) P := by
  open MvPolynomial in
  refine ⟨thm_poly ε k, le_antisymm ?_ ?_, thm_eval_poly ε k⟩
  · -- the four parts are homogeneous of degrees `3, 2, 4, 2`
    unfold thm_poly
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
      (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)) ?_)
    · exact thm_pf_hom.totalDegree_le.trans (by norm_num)
    · exact ((isHomogeneous_C _ ε).mul thm_pS_hom).totalDegree_le.trans (by norm_num)
    · exact ((isHomogeneous_C _ ε).mul (thm_pS_hom.pow 2)).totalDegree_le
    · exact ((isHomogeneous_C _ k).mul thm_pQ_hom).totalDegree_le.trans (by norm_num)
  · -- the homogeneous component of degree `4` is `ε |X|⁴ ≠ 0`
    by_contra h
    have h0 := homogeneousComponent_eq_zero 4 _ (not_le.mp h)
    have hc : homogeneousComponent 4 (thm_poly ε k) = C ε * thm_pS ^ 2 := by
      simp only [thm_poly, map_add, homogeneousComponent_C_mul,
        homogeneousComponent_of_mem thm_pf_hom, homogeneousComponent_of_mem thm_pS_hom,
        homogeneousComponent_of_mem (thm_pS_hom.pow 2), homogeneousComponent_of_mem thm_pQ_hom]
      norm_num
    have := congrArg (eval fun ij => if ij = ((0 : Fin 3), (0 : Fin 2)) then (1 : ℝ) else 0)
      (hc.symm.trans h0)
    simp [thm_pS, Fin.sum_univ_succ] at this
    exact hε this

end Sverak
