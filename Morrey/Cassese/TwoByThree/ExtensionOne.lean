module

public import Morrey.Cassese.TwoByThree.Basic
public import Morrey.Cassese.Toolkit
public import Morrey.Cassese.TwoByThree.Rademacher

/-!
# Section 5.3: Lemma 5.1 (1), extension from a subspace at the origin

Lemma 5.1 is stated for a subspace `L` and a map `π` with the defining property of the orthogonal
projection onto `L` (`IsFrobProj`); functions "on `L`" are functions on `ℝ^{d×m}` of which only the
values on `L` matter. An `L`-valued rank-one Rademacher martingale is one whose increments lie in
`L`.

The proof uses Proposition 2.5 (`proposition2_5`, Toolkit) and Burkholder's inequality on the
canonical space of signs (`Morrey/Cassese/TwoByThree/Rademacher.lean`). Helpers are prefixed
`tbt1_`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-! ### The orthogonal projection and the Frobenius norm -/

theorem tbt1_frobInner_sub_left (A B C : Matrix (Fin d) (Fin m) ℝ) :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  simp only [frobInner, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem tbt1_frobInner_add_left (A B C : Matrix (Fin d) (Fin m) ℝ) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  simp only [frobInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem tbt1_frobInner_smul_left (c : ℝ) (A C : Matrix (Fin d) (Fin m) ℝ) :
    frobInner (c • A) C = c * frobInner A C := by
  simp only [frobInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem tbt1_frobInner_self (A : Matrix (Fin d) (Fin m) ℝ) : frobInner A A = frobSq A := by
  simp only [frobInner, frobSq, pow_two]

/-- The defining property determines `π A`. -/
theorem tbt1_proj_unique {L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ)}
    {π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ} (hπ : IsFrobProj L π)
    (A P : Matrix (Fin d) (Fin m) ℝ) (hP : P ∈ L) (h : ∀ B ∈ L, frobInner (A - P) B = 0) :
    π A = P := by
  have hD : π A - P ∈ L := L.sub_mem (hπ A).1 hP
  have : frobSq (π A - P) = 0 := by
    rw [← tbt1_frobInner_self, show π A - P = (A - P) - (A - π A) by abel,
      tbt1_frobInner_sub_left, ← show π A - P = (A - P) - (A - π A) by abel, h _ hD,
      (hπ A).2 _ hD, sub_zero]
  exact sub_eq_zero.mp (tbt_eq_zero_of_frobSq_eq_zero this)

/-- `π` as a linear map. -/
noncomputable def tbt1ProjLin {L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ)}
    {π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ} (hπ : IsFrobProj L π) :
    Matrix (Fin d) (Fin m) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin m) ℝ where
  toFun := π
  map_add' A B := tbt1_proj_unique hπ _ _ (L.add_mem (hπ A).1 (hπ B).1) fun C hC => by
    rw [show A + B - (π A + π B) = (A - π A) + (B - π B) by abel, tbt1_frobInner_add_left,
      (hπ A).2 C hC, (hπ B).2 C hC, add_zero]
  map_smul' c A := tbt1_proj_unique hπ _ _ (L.smul_mem c (hπ A).1) fun C hC => by
    rw [RingHom.id_apply, show c • A - c • π A = c • (A - π A) by rw [smul_sub],
      tbt1_frobInner_smul_left, (hπ A).2 C hC, mul_zero]

theorem tbt1_continuous_entry (i : Fin d) (j : Fin m) :
    Continuous fun A : Matrix (Fin d) (Fin m) ℝ => A i j :=
  (continuous_apply j).comp (continuous_apply i)

theorem tbt1_continuous_proj {L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ)}
    {π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ} (hπ : IsFrobProj L π) :
    Continuous π := by
  have h : π = fun A => ∑ i, ∑ j, A i j • π (Matrix.single i j 1) := by
    funext A
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    change tbt1ProjLin hπ _ = _
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
    rfl
  rw [h]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (tbt1_continuous_entry i j).smul continuous_const

/-- The isometry `ℝ^{d×m} → ℓ₂ (d × m)` of the Frobenius norm. -/
noncomputable def tbt1Iota : Matrix (Fin d) (Fin m) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin d × Fin m) where
  toFun A := WithLp.toLp 2 fun ij => A ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tbt1_norm_iota (A : Matrix (Fin d) (Fin m) ℝ) : ‖tbt1Iota A‖ = frobNorm A := by
  rw [EuclideanSpace.norm_eq, frobNorm, frobSq]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.norm_eq_abs, sq_abs]; rfl

/-- The inverse of `tbt1Iota`. -/
noncomputable def tbt1Psi : EuclideanSpace ℝ (Fin d × Fin m) →ₗ[ℝ] Matrix (Fin d) (Fin m) ℝ where
  toFun v := Matrix.of fun i j => v (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tbt1_psi_iota (A : Matrix (Fin d) (Fin m) ℝ) : tbt1Psi (tbt1Iota A) = A := rfl

theorem tbt1_continuous_psi : Continuous (tbt1Psi : EuclideanSpace ℝ (Fin d × Fin m) → _) :=
  LinearMap.continuous_of_finiteDimensional _

theorem tbt1_frobNorm_nonneg (A : Matrix (Fin d) (Fin m) ℝ) : 0 ≤ frobNorm A :=
  Real.sqrt_nonneg _

theorem tbt1_frobNorm_smul (c : ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    frobNorm (c • A) = |c| * frobNorm A := by
  rw [← tbt1_norm_iota, map_smul, norm_smul, tbt1_norm_iota, Real.norm_eq_abs]

theorem tbt1_frobNorm_add_le (A B : Matrix (Fin d) (Fin m) ℝ) :
    frobNorm (A + B) ≤ frobNorm A + frobNorm B := by
  rw [← tbt1_norm_iota, ← tbt1_norm_iota, ← tbt1_norm_iota, map_add]; exact norm_add_le _ _

theorem tbt1_continuous_frobNorm : Continuous fun A : Matrix (Fin d) (Fin m) ℝ => frobNorm A := by
  unfold frobNorm frobSq
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (tbt1_continuous_entry i j).pow 2)


theorem tbt1_eq_zero_of_frobNorm_eq_zero {A : Matrix (Fin d) (Fin m) ℝ} (h : frobNorm A = 0) :
    A = 0 := by
  rw [← tbt1_norm_iota, norm_eq_zero] at h
  rw [← tbt1_psi_iota A, h, map_zero]

/-- A positively `p`-homogeneous `g` (`p > 0`) vanishes at `0`. -/
theorem tbt1_g_zero {L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ)} {g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    {p : ℝ} (hp : 0 < p) (hgh : ∀ t : ℝ, 0 < t → ∀ X ∈ L, g (t • X) = t ^ p * g X) : g 0 = 0 := by
  have h := hgh 2 two_pos 0 L.zero_mem
  rw [smul_zero] at h
  have h2 : (1 : ℝ) < 2 ^ p := Real.one_lt_rpow (by norm_num) hp
  have : (2 ^ p - 1) * g 0 = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h'
  · linarith
  · exact h'

/-- "By homogeneity and Young's inequality" (proof of Lemma 5.1 (1)): for every `η' > 0` there is
`C` with `|g (X + Y) − g (X)| ≤ η' |X|^p + C |Y|^p` on `L`. From the uniform continuity of `g` on
the compact set `{Z ∈ L : |Z| ≤ 2}` (the case `|Y| < δ |X|`, after scaling `X` to the unit sphere)
and the bound `|g (Z)| ≤ M |Z|^p` (the case `|Y| ≥ δ |X|`). -/
theorem tbt1_young {L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ)} {g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hgc : ContinuousOn g L) {p : ℝ} (hp : 0 < p)
    (hgh : ∀ t : ℝ, 0 < t → ∀ X ∈ L, g (t • X) = t ^ p * g X) {η' : ℝ} (hη' : 0 < η') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X ∈ L, ∀ Y ∈ L,
      |g (X + Y) - g X| ≤ η' * frobNorm X ^ p + C * frobNorm Y ^ p := by
  set L' : Submodule ℝ (EuclideanSpace ℝ (Fin d × Fin m)) := L.comap tbt1Psi
  set K : Set (EuclideanSpace ℝ (Fin d × Fin m)) := (L' : Set _) ∩ Metric.closedBall 0 2
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).inter_left (Submodule.closed_of_finiteDimensional L')
  have hg' : ContinuousOn (fun v => g (tbt1Psi v)) K :=
    hgc.comp tbt1_continuous_psi.continuousOn fun v hv => hv.1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg'
  obtain ⟨δ, hδ, hδu⟩ :=
    Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hg') η' hη'
  have hmemK : ∀ Z ∈ L, frobNorm Z ≤ 2 → tbt1Iota Z ∈ K := fun Z hZ hZ2 =>
    ⟨by simpa [L', tbt1_psi_iota] using hZ, by
      rw [Metric.mem_closedBall, dist_zero_right, tbt1_norm_iota]; exact hZ2⟩
  set M0 := max M 0
  have hg0 := tbt1_g_zero hp hgh
  -- `|g (Z)| ≤ M₀ |Z|^p` on `L`
  have hgb : ∀ Z ∈ L, |g Z| ≤ M0 * frobNorm Z ^ p := by
    intro Z hZ
    by_cases hz : Z = 0
    · subst hz; rw [hg0, abs_zero]
      exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (tbt1_frobNorm_nonneg _) _)
    have hs : 0 < frobNorm Z :=
      lt_of_le_of_ne (tbt1_frobNorm_nonneg _) fun h => hz (tbt1_eq_zero_of_frobNorm_eq_zero h.symm)
    set Zh := (frobNorm Z)⁻¹ • Z
    have hZh : Zh ∈ L := L.smul_mem _ hZ
    have hn : frobNorm Zh = 1 := by
      rw [tbt1_frobNorm_smul, abs_inv, abs_of_pos hs, inv_mul_cancel₀ hs.ne']
    have hZe : Z = frobNorm Z • Zh := by rw [smul_inv_smul₀ hs.ne']
    have hb := hM _ (hmemK Zh hZh (by rw [hn]; norm_num))
    rw [Real.norm_eq_abs, tbt1_psi_iota] at hb
    rw [hZe, hgh _ hs _ hZh, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs _), ← hZe, mul_comm]
    exact mul_le_mul_of_nonneg_right (hb.trans (le_max_left _ _))
      (Real.rpow_nonneg (tbt1_frobNorm_nonneg _) _)
  set δ' := min δ 1
  have hδ' : 0 < δ' := lt_min hδ one_pos
  set C := M0 * ((1 / δ' + 1) ^ p + (1 / δ') ^ p) + M0
  have hM0 : 0 ≤ M0 := le_max_right _ _
  refine ⟨C, by positivity, fun X hX Y hY => ?_⟩
  have hXY : X + Y ∈ L := L.add_mem hX hY
  have hy := tbt1_frobNorm_nonneg Y
  by_cases hx0 : X = 0
  · subst hx0
    rw [zero_add, hg0, sub_zero, show frobNorm (0 : Matrix (Fin d) (Fin m) ℝ) = 0 by
      simp [frobNorm, frobSq], Real.zero_rpow hp.ne', mul_zero, zero_add]
    refine (hgb Y hY).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy _))
    have : 0 ≤ M0 * ((1 / δ' + 1) ^ p + (1 / δ') ^ p) := by positivity
    linarith
  have hs : 0 < frobNorm X :=
    lt_of_le_of_ne (tbt1_frobNorm_nonneg _) fun h => hx0 (tbt1_eq_zero_of_frobNorm_eq_zero h.symm)
  set s := frobNorm X
  by_cases hcase : frobNorm Y < δ' * s
  · -- `|Y| < δ |X|`: uniform continuity on the unit sphere, after scaling
    set Xh := s⁻¹ • X
    set Yh := s⁻¹ • Y
    have hXh : Xh ∈ L := L.smul_mem _ hX
    have hXYh : Xh + Yh ∈ L := L.add_mem hXh (L.smul_mem _ hY)
    have hnX : frobNorm Xh = 1 := by
      rw [tbt1_frobNorm_smul, abs_inv, abs_of_pos hs, inv_mul_cancel₀ hs.ne']
    have hnY : frobNorm Yh < δ' := by
      rw [tbt1_frobNorm_smul, abs_inv, abs_of_pos hs, inv_mul_lt_iff₀ hs, mul_comm]
      exact hcase
    have hnXY : frobNorm (Xh + Yh) ≤ 2 := by
      have := tbt1_frobNorm_add_le Xh Yh
      have : δ' ≤ 1 := min_le_right _ _
      linarith
    have hd := hδu _ (hmemK _ hXYh hnXY) _ (hmemK _ hXh (by rw [hnX]; norm_num)) (by
      rw [dist_eq_norm, ← map_sub, add_sub_cancel_left, tbt1_norm_iota]
      exact lt_of_lt_of_le hnY (min_le_left _ _))
    rw [tbt1_psi_iota, tbt1_psi_iota, Real.dist_eq] at hd
    have hX' : X = s • Xh := by rw [smul_inv_smul₀ hs.ne']
    have hXY' : X + Y = s • (Xh + Yh) := by rw [smul_add, smul_inv_smul₀ hs.ne',
      smul_inv_smul₀ hs.ne']
    rw [hXY', hgh _ hs _ hXYh, hX', hgh _ hs _ hXh, ← mul_sub, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hs _)]
    have : 0 ≤ C * frobNorm Y ^ p := mul_nonneg (by positivity) (Real.rpow_nonneg hy _)
    have := mul_le_mul_of_nonneg_left hd.le (Real.rpow_nonneg hs.le p)
    nlinarith
  · -- `|Y| ≥ δ |X|`: the bound `|g (Z)| ≤ M₀ |Z|^p`
    push Not at hcase
    have hsY : s ≤ frobNorm Y / δ' := by rw [le_div_iff₀ hδ']; linarith
    have h1 : frobNorm (X + Y) ≤ (1 / δ' + 1) * frobNorm Y := by
      have := tbt1_frobNorm_add_le X Y
      have : frobNorm Y / δ' = 1 / δ' * frobNorm Y := by ring
      linarith
    have h2 : s ≤ 1 / δ' * frobNorm Y := by rw [one_div_mul_eq_div]; exact hsY
    have e1 : frobNorm (X + Y) ^ p ≤ (1 / δ' + 1) ^ p * frobNorm Y ^ p := by
      rw [← Real.mul_rpow (by positivity) hy]
      exact Real.rpow_le_rpow (tbt1_frobNorm_nonneg _) h1 hp.le
    have e2 : s ^ p ≤ (1 / δ') ^ p * frobNorm Y ^ p := by
      rw [← Real.mul_rpow (by positivity) hy]
      exact Real.rpow_le_rpow hs.le h2 hp.le
    have hb1 := hgb _ hXY
    have hb2 := hgb _ hX
    have : |g (X + Y) - g X| ≤ |g (X + Y)| + |g X| := abs_sub _ _
    have hsp : 0 ≤ s ^ p := Real.rpow_nonneg hs.le _
    have hyp : 0 ≤ frobNorm Y ^ p := Real.rpow_nonneg hy _
    have : 0 ≤ η' * s ^ p := mul_nonneg hη'.le hsp
    have : M0 * frobNorm (X + Y) ^ p ≤ M0 * ((1 / δ' + 1) ^ p * frobNorm Y ^ p) :=
      mul_le_mul_of_nonneg_left e1 hM0
    have : M0 * s ^ p ≤ M0 * ((1 / δ') ^ p * frobNorm Y ^ p) := mul_le_mul_of_nonneg_left e2 hM0
    have : C * frobNorm Y ^ p = M0 * ((1 / δ' + 1) ^ p * frobNorm Y ^ p) +
        M0 * ((1 / δ') ^ p * frobNorm Y ^ p) + M0 * frobNorm Y ^ p := by ring
    nlinarith [mul_nonneg hM0 hyp]

/-! ### Averages and Rademacher sums -/

theorem tbt1_avg_add {N : ℕ} (f h : (Fin N → Bool) → ℝ) :
    avg (fun ε => f ε + h ε) = avg f + avg h := by
  simp only [avg, Finset.sum_add_distrib, add_div]

theorem tbt1_avg_sub {N : ℕ} (f h : (Fin N → Bool) → ℝ) :
    avg (fun ε => f ε - h ε) = avg f - avg h := by
  simp only [avg, Finset.sum_sub_distrib, sub_div]

theorem tbt1_avg_const_mul {N : ℕ} (c : ℝ) (f : (Fin N → Bool) → ℝ) :
    avg (fun ε => c * f ε) = c * avg f := by
  simp only [avg, ← Finset.mul_sum, mul_div_assoc]

theorem tbt1_avg_mono {N : ℕ} {f h : (Fin N → Bool) → ℝ} (hfh : ∀ ε, f ε ≤ h ε) :
    avg f ≤ avg h :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun ε _ => hfh ε) (by positivity)

theorem tbt1_avg_nonneg {N : ℕ} {f : (Fin N → Bool) → ℝ} (hf : ∀ ε, 0 ≤ f ε) : 0 ≤ avg f :=
  div_nonneg (Finset.sum_nonneg fun ε _ => hf ε) (by positivity)

theorem tbt1_mart_map {N : ℕ} {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (T : E →ₗ[ℝ] F) (ξ : Fin N → (Fin N → Bool) → E) (n : ℕ) (ε : Fin N → Bool) :
    T (mart ξ n ε) = mart (fun k ε => T (ξ k ε)) n ε := by
  simp only [mart, map_sum, map_smul]

theorem tbt1_mart_sub {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ ζ : Fin N → (Fin N → Bool) → E) (n : ℕ) (ε : Fin N → Bool) :
    mart (fun k ε => ξ k ε - ζ k ε) n ε = mart ξ n ε - mart ζ n ε := by
  simp only [mart, smul_sub, Finset.sum_sub_distrib]

theorem tbt1_mart_mem {N : ℕ} (L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ))
    {ξ : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ} (h : ∀ k ε, ξ k ε ∈ L) (n : ℕ)
    (ε : Fin N → Bool) : mart ξ n ε ∈ L :=
  L.sum_mem fun k _ => L.smul_mem _ (h k ε)

/-- **Lemma 5.1 (1), quantitative form** (`lem:extension-from-subspace`): under the hypotheses of
`lemma5_1_part1`, if `C ≥ 0` is a constant of the homogeneity and Young estimate
`|g (X + Y) − g (X)| ≤ (η/2) |X|^p + C |Y|^p` on `L`, then the penalty
`Λ₀ = (C (p* − 1)^p (max κ 0)^p)^{1/p}` suffices: for every `Λ ≥ Λ₀`,
`A ↦ g (π A) + Λ^p |π^⊥ A|^p` is rank-one convex at `0`. This is the proof of Lemma 5.1 (1) with
its constants kept explicit; the proof of Theorem 1.3 (b) needs them to choose `Λ` uniformly in `p`
(inventory E4). Burkholder's inequality (Theorem 2.3) gives (27). -/
theorem lemma5_1_part1_quant
    (L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ))
    (π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ) (hπ : IsFrobProj L π) (κ : ℝ)
    (hκ : HasRankOneCorrection L π κ) {p : ℝ} (hp : 1 < p) (g : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (hgc : ContinuousOn g L) (hgh : ∀ t : ℝ, 0 < t → ∀ X ∈ L, g (t • X) = t ^ p * g X)
    {η : ℝ} (hη : 0 < η)
    (hcoer : ∀ (N : ℕ) (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ),
      IsRankOneIncrements A → (∀ k ε, A k ε ∈ L) →
        η * avg (fun ε => frobNorm (radMart 0 A N ε) ^ p) ≤
          avg fun ε => g (radMart 0 A N ε))
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ X ∈ L, ∀ Y ∈ L, |g (X + Y) - g X| ≤ η / 2 * frobNorm X ^ p + C * frobNorm Y ^ p) :
    ∀ Λ ≥ (C * ((pStar p - 1) ^ p * max κ 0 ^ p)) ^ (1 / p),
      RankOneConvexAt (fun A => g (π A) + Λ ^ p * frobNorm (A - π A) ^ p) 0 := by
  have hp0 : 0 < p := by linarith
  have hπc := tbt1_continuous_proj hπ
  have hπ0 : π 0 = 0 := map_zero (tbt1ProjLin hπ)
  set κ' := max κ 0 with hκ'_def
  have hκ' : 0 ≤ κ' := le_max_right _ _
  -- the predictable correction: a rank-one `R_L ∈ L` for each increment (`0` for `R = 0`)
  have hcorr : ∀ R : Matrix (Fin d) (Fin m) ℝ, ∃ RL ∈ L, RL.rank ≤ 1 ∧
      (R.rank ≤ 1 → frobNorm (π R - RL) ≤ κ' * frobNorm (R - π R)) := by
    intro R
    by_cases h1 : R.rank = 1
    · obtain ⟨RL, hRL, hr, hle⟩ := hκ R h1
      exact ⟨RL, hRL, hr.le, fun _ => hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (tbt1_frobNorm_nonneg _))⟩
    · refine ⟨0, L.zero_mem, by rw [Matrix.rank_zero]; exact zero_le_one, fun hR => ?_⟩
      have h0 : R = 0 := tbt_eq_zero_of_rank_eq_zero R (by omega)
      subst h0
      rw [hπ0, sub_zero, show frobNorm (0 : Matrix (Fin d) (Fin m) ℝ) = 0 by
        simp [frobNorm, frobSq], mul_zero]
  choose corr hcorrL hcorrr hcorrle using hcorr
  set K := C * ((pStar p - 1) ^ p * κ' ^ p) with hK_def
  have hpstar : 0 ≤ pStar p - 1 := by
    have : p ≤ pStar p := le_max_left _ _
    linarith
  have hK0 : 0 ≤ K := by positivity
  intro Λ hΛ
  have hΛ0 : 0 ≤ Λ := (Real.rpow_nonneg hK0 _).trans hΛ
  have hΛp : K ≤ Λ ^ p := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hΛ hp0.le
    rwa [← Real.rpow_mul hK0, one_div_mul_cancel hp0.ne', Real.rpow_one] at this
  have hFc : Continuous fun A => g (π A) + Λ ^ p * frobNorm (A - π A) ^ p :=
    (hgc.comp_continuous hπc fun A => (hπ A).1).add (continuous_const.mul
      ((tbt1_continuous_frobNorm.comp (continuous_id.sub hπc)).rpow_const
        fun _ => Or.inr hp0.le))
  rw [proposition2_5 hFc]
  intro N A hA
  have hF0 : g (π 0) + Λ ^ p * frobNorm (0 - π 0) ^ p = 0 := by
    rw [hπ0, sub_zero, tbt1_g_zero hp0 hgh, show frobNorm (0 : Matrix (Fin d) (Fin m) ℝ) = 0 by
      simp [frobNorm, frobSq], Real.zero_rpow hp0.ne', mul_zero, add_zero]
  rw [hF0]
  -- `M̃`: the `L`-valued rank-one martingale with the corrected increments
  set B : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ := fun k ε => corr (A k ε)
  have hBpred : IsPredictable B := fun k ε ε' h => by simp only [B, hA.1 k ε ε' h]
  have hco := hcoer N B ⟨hBpred, fun k ε => hcorrr _⟩ fun k ε => hcorrL _
  -- `𝓔 = π M − M̃` and `N = π^⊥ M`
  set E : (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ :=
    fun ε => mart (fun k ε => π (A k ε) - B k ε) N ε
  set Nn : (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ :=
    fun ε => mart (fun k ε => A k ε - π (A k ε)) N ε
  have hMtL : ∀ ε, radMart 0 B N ε ∈ L := fun ε => by
    rw [radMart, zero_add]; exact tbt1_mart_mem L (fun k ε => hcorrL _) N ε
  have hEL : ∀ ε, E ε ∈ L := fun ε =>
    tbt1_mart_mem L (fun k ε => L.sub_mem (hπ _).1 (hcorrL _)) N ε
  have hπM : ∀ ε, π (radMart 0 A N ε) = radMart 0 B N ε + E ε := fun ε => by
    simp only [radMart, zero_add, E]
    rw [tbt1_mart_sub, add_sub_cancel]
    exact tbt1_mart_map (tbt1ProjLin hπ) A N ε
  have hperp : ∀ ε, radMart 0 A N ε - π (radMart 0 A N ε) = Nn ε := fun ε => by
    simp only [Nn, tbt1_mart_sub]
    rw [show π (radMart 0 A N ε) = mart (fun k ε => π (A k ε)) N ε by
      rw [radMart, zero_add]; exact tbt1_mart_map (tbt1ProjLin hπ) A N ε, radMart, zero_add]
  -- Young pointwise
  have hy : ∀ ε, g (radMart 0 B N ε) - (η / 2) * frobNorm (radMart 0 B N ε) ^ p -
      C * frobNorm (E ε) ^ p ≤ g (π (radMart 0 A N ε)) := fun ε => by
    rw [hπM]
    have := hC _ (hMtL ε) _ (hEL ε)
    have := neg_abs_le (g (radMart 0 B N ε + E ε) - g (radMart 0 B N ε))
    linarith
  -- (27), from Burkholder's inequality: `‖𝓔_N‖_p ≤ κ (p* − 1) ‖N_N‖_p`
  have hbk : avg (fun ε => frobNorm (E ε) ^ p) ≤
      (pStar p - 1) ^ p * κ' ^ p * avg (fun ε => frobNorm (Nn ε) ^ p) := by
    have hξ : IsPredictable fun k ε => tbt1Iota (π (A k ε) - B k ε) := fun k ε ε' h => by
      simp only [B, hA.1 k ε ε' h]
    have hζ : IsPredictable fun k ε => tbt1Iota (κ' • (A k ε - π (A k ε))) := fun k ε ε' h => by
      simp only [hA.1 k ε ε' h]
    have := tbt1_burkholder_avg hξ hζ (fun k ε => by
      rw [tbt1_norm_iota, tbt1_norm_iota, tbt1_frobNorm_smul, abs_of_nonneg hκ']
      exact hcorrle _ (hA.2 k ε)) hp
    have e1 : ∀ ε, ‖mart (fun k ε => tbt1Iota (π (A k ε) - B k ε)) N ε‖ = frobNorm (E ε) :=
      fun ε => by rw [← tbt1_mart_map, tbt1_norm_iota]
    have e2 : ∀ ε, ‖mart (fun k ε => tbt1Iota (κ' • (A k ε - π (A k ε)))) N ε‖ ^ p =
        κ' ^ p * frobNorm (Nn ε) ^ p := fun ε => by
      have : mart (fun k ε => tbt1Iota (κ' • (A k ε - π (A k ε)))) N ε =
          (tbt1Iota.comp (κ' • LinearMap.id)) (Nn ε) := by
        rw [tbt1_mart_map]; rfl
      rw [this, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, tbt1_norm_iota,
        tbt1_frobNorm_smul, abs_of_nonneg hκ', Real.mul_rpow hκ' (tbt1_frobNorm_nonneg _)]
    simp only [e1, e2, tbt1_avg_const_mul] at this
    rw [mul_assoc]; exact this
  -- `E F (M_N) ≥ (Λ^p − C κ^p (p* − 1)^p) E |N_N|^p ≥ 0`
  have hNn : 0 ≤ avg (fun ε => frobNorm (Nn ε) ^ p) :=
    tbt1_avg_nonneg fun ε => Real.rpow_nonneg (tbt1_frobNorm_nonneg _) _
  have hMt : 0 ≤ avg (fun ε => frobNorm (radMart 0 B N ε) ^ p) :=
    tbt1_avg_nonneg fun ε => Real.rpow_nonneg (tbt1_frobNorm_nonneg _) _
  have hlow : ∀ ε, (g (radMart 0 B N ε) - (η / 2) * frobNorm (radMart 0 B N ε) ^ p -
      C * frobNorm (E ε) ^ p) + Λ ^ p * frobNorm (Nn ε) ^ p ≤
      g (π (radMart 0 A N ε)) + Λ ^ p * frobNorm (radMart 0 A N ε - π (radMart 0 A N ε)) ^ p :=
    fun ε => by rw [hperp]; linarith [hy ε]
  refine le_trans ?_ (tbt1_avg_mono hlow)
  rw [tbt1_avg_add, tbt1_avg_sub, tbt1_avg_sub, tbt1_avg_const_mul, tbt1_avg_const_mul,
    tbt1_avg_const_mul]
  have h1 : C * avg (fun ε => frobNorm (E ε) ^ p) ≤ K * avg (fun ε => frobNorm (Nn ε) ^ p) := by
    rw [hK_def, mul_assoc]; exact mul_le_mul_of_nonneg_left hbk hC0
  have h2 : K * avg (fun ε => frobNorm (Nn ε) ^ p) ≤ Λ ^ p * avg (fun ε => frobNorm (Nn ε) ^ p) :=
    mul_le_mul_of_nonneg_right hΛp hNn
  nlinarith

/-- **Lemma 5.1 (1)** (`lem:extension-from-subspace`, extension from a subspace): let `π` be the
orthogonal projection onto a subspace `L ⊆ ℝ^{d×m}` satisfying (25) for some `κ`. Let `p > 1` and
let `g` be continuous and positively `p`-homogeneous on `L`, with `E g (M_n) ≥ η E |M_n|^p` for
some `η > 0` and every `L`-valued rank-one Rademacher martingale started at `0`. Then for `Λ`
large enough, `A ↦ g (π A) + Λ^p |π^⊥ A|^p` is rank-one convex at `0`. Burkholder's inequality
(Theorem 2.3) gives (27).

Proof, as in the paper (TeX lines 1870–1903). By Proposition 2.5 it suffices that
`E F (M_N) ≥ 0 = F (0)` for every rank-one Rademacher martingale `M` started at `0`. Applying (25)
to each increment gives the predictable correction `M̃` (increments `(dM_k)_L ∈ L` of rank at most
one; `0` for a zero increment, inventory E16), an `L`-valued rank-one martingale, so
`E g (M̃_N) ≥ η E |M̃_N|^p`. The error `𝓔 = π M − M̃` is differentially subordinate to `κ N`,
`N = π^⊥ M`, so Burkholder's inequality on the canonical space of signs gives (27),
`E |𝓔_N|^p ≤ (κ (p* − 1))^p E |N_N|^p` (`tbt1_burkholder_avg`; `κ` is replaced by `max κ 0`, which
(25) also satisfies). "By homogeneity and Young's inequality",
`|g (X + Y) − g (X)| ≤ (η/2) |X|^p + C |Y|^p` on `L` (`tbt1_young`, from the uniform continuity of
`g` on a compact ball of `L`), so `E g (π M_N) ≥ (η/2) E |M̃_N|^p − C E |𝓔_N|^p`, and
`Λ^p ≥ C (κ (p* − 1))^p` makes `E F (M_N) ≥ 0`. -/
theorem lemma5_1_part1
    (L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ))
    (π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ) (hπ : IsFrobProj L π) (κ : ℝ)
    (hκ : HasRankOneCorrection L π κ) {p : ℝ} (hp : 1 < p) (g : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (hgc : ContinuousOn g L) (hgh : ∀ t : ℝ, 0 < t → ∀ X ∈ L, g (t • X) = t ^ p * g X)
    {η : ℝ} (hη : 0 < η)
    (hcoer : ∀ (N : ℕ) (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ),
      IsRankOneIncrements A → (∀ k ε, A k ε ∈ L) →
        η * avg (fun ε => frobNorm (radMart 0 A N ε) ^ p) ≤
          avg fun ε => g (radMart 0 A N ε)) :
    ∃ Λ₀ : ℝ, ∀ Λ ≥ Λ₀, RankOneConvexAt (fun A => g (π A) + Λ ^ p * frobNorm (A - π A) ^ p) 0 := by
  -- "by homogeneity and Young's inequality"
  obtain ⟨C, hC0, hC⟩ := tbt1_young hgc (by linarith) hgh (η' := η / 2) (by linarith)
  exact ⟨_, lemma5_1_part1_quant L π hπ κ hκ hp g hgc hgh hη hcoer C hC0 hC⟩

end Cassese
