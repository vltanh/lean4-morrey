module

public import Morrey.Common.External.KinderlehrerPedregal.Basic
public import Morrey.Common.External.KinderlehrerPedregal.SepConvex
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Data.EReal.Operations

/-!
# The infimum formula on the unit cube

For a continuous `f : ℝ^{d×m} → ℝ`, `kpQ f A = inf_φ ∫_{(0,1)^m} f (A + ∇φ)` over the Lipschitz
`φ` vanishing outside the unit cube (values in `EReal`). This file proves the properties of `kpQ f`
that the standard proof of Dacorogna's formula needs (Dacorogna 2008, Theorem 6.9;
Kinderlehrer–Pedregal 1991, Proposition 8.1):

* `kpQ_le`: `kpQ f ≤ f`; `kpQ_usc`: `kpQ f` is upper semicontinuous;
* `kpQ_quasiconvex_robust`: `kpQ f (A) ≤ ∫ max (kpQ f (A + ∇φ), -N)` for every test map `φ` and
  every `N`: near almost every point `x`, `φ` is close to its tangent map and `x` is a Lebesgue
  point of the integrand; finitely many disjoint small cubes around such points cover the cube up
  to `ε` (Besicovitch); in each cube the tangent map is glued to `φ` by a cut-off, and a rescaled
  almost minimiser for `kpQ f (A + ∇φ (x))` is inserted;
* separate convexity (by laminates), the dichotomy `kpQ f ≡ -∞` or finite, continuity, and
  quasiconvexity of `kpQ f`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace External.KinderlehrerPedregal

open CalculusOfVariations

variable {d m : ℕ}

/-- The test maps on the unit cube: Lipschitz, vanishing outside `(0, 1)^m`. -/
def KpAdm (φ : (Fin m → ℝ) → Fin d → ℝ) : Prop :=
  (∃ K, LipschitzWith K φ) ∧ ∀ x ∉ unitCube m, φ x = 0

/-- The infimum formula on the unit cube. -/
noncomputable def kpQ (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    EReal :=
  ⨅ (φ : (Fin m → ℝ) → Fin d → ℝ) (_ : KpAdm φ),
    ((∫ x in unitCube m, f (A + grad φ x) : ℝ) : EReal)

/-! ### The unit cube -/

theorem kp_unitCube_eq_ball : unitCube m = ball (fun _ => (1 / 2 : ℝ)) (1 / 2) := by
  ext x
  simp only [unitCube, Set.mem_pi, mem_univ, true_implies, mem_Ioo, mem_ball, dist_pi_lt_iff
    (by norm_num : (0 : ℝ) < 1 / 2), Real.dist_eq, abs_sub_lt_iff]
  refine forall_congr' fun i => ?_
  constructor
  · intro h; constructor <;> linarith [h.1, h.2]
  · intro h; constructor <;> linarith [h.1, h.2]

theorem kp_isOpen_unitCube : IsOpen (unitCube m) := by
  rw [kp_unitCube_eq_ball]; exact isOpen_ball

theorem kp_measurableSet_unitCube : MeasurableSet (unitCube m) :=
  kp_isOpen_unitCube.measurableSet

theorem kp_volume_unitCube : volume (unitCube m) = 1 := by
  rw [unitCube, Real.volume_pi_Ioo]
  simp

theorem kp_unitCube_subset_closedBall :
    unitCube m ⊆ closedBall (fun _ => (1 / 2 : ℝ)) (1 / 2) := by
  rw [kp_unitCube_eq_ball]; exact ball_subset_closedBall

/-! ### Bounds and integrability -/

/-- A continuous `f` is bounded near `A`. -/
theorem kp_bdd {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ X : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |X i k| ≤ R) → |f (A + X)| ≤ M := by
  have hc : Continuous fun X : Fin d → Fin m → ℝ => f (A + Matrix.of X) :=
    hf.comp (continuous_const.add continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin d → Fin m → ℝ) (max R 0)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun X hX => ?_⟩
  have hmem : (fun i k => X i k : Fin d → Fin m → ℝ) ∈ closedBall (0 : Fin d → Fin m → ℝ)
      (max R 0) := by
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    intro k
    rw [Real.norm_eq_abs]
    exact (hX i k).trans (le_max_left _ _)
  have := hC _ hmem
  rw [Real.norm_eq_abs] at this
  exact (le_of_eq (by rfl)).trans (this.trans (le_max_left _ _))

/-- `f (A + ∇φ)` is integrable on sets of finite measure for a Lipschitz `φ`. -/
theorem kp_integrableOn {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) {s : Set (Fin m → ℝ)} (hs : volume s ≠ ⊤) :
    IntegrableOn (fun x => f (A + grad φ x)) s := by
  obtain ⟨M, -, hM⟩ := kp_bdd hf A K
  refine Measure.integrableOn_of_bounded (M := M) hs ?_ ?_
  · exact (kp_measurable_comp_grad (kp_continuous_of hf).measurable A φ).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hM _ (kp_grad_abs_le hφ x)

/-- `kpQ f ≤ f`, with the test map `0`. -/
theorem kpQ_le {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (A : Matrix (Fin d) (Fin m) ℝ) :
    kpQ f A ≤ f A := by
  have h0 : KpAdm (fun _ : Fin m → ℝ => (0 : Fin d → ℝ)) :=
    ⟨⟨0, LipschitzWith.const _⟩, fun _ _ => rfl⟩
  refine (iInf₂_le _ h0).trans ?_
  have hg : ∀ x, grad (fun _ : Fin m → ℝ => (0 : Fin d → ℝ)) x = 0 := fun x =>
    kp_grad_eq_zero (Filter.Eventually.of_forall fun _ => rfl)
  simp only [hg, add_zero, setIntegral_const, smul_eq_mul, Measure.real, kp_volume_unitCube,
    ENNReal.toReal_one, one_mul, le_refl]

/-- For a fixed test map, `A ↦ ∫_Q f (A + ∇φ)` is continuous. -/
theorem kp_continuous_integral {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) :
    Continuous fun A : Matrix (Fin d) (Fin m) ℝ => ∫ x in unitCube m, f (A + grad φ x) := by
  -- continuity on `Fin d → Fin m → ℝ`, a first-countable space
  have hg : Continuous fun X : Fin d → Fin m → ℝ =>
      ∫ x in unitCube m, f (Matrix.of X + grad φ x) := by
    rw [continuous_iff_continuousAt]
    intro X₀
    obtain ⟨M, -, hM⟩ := kp_bdd hf (Matrix.of X₀) (K + 1)
    have hnhds : ∀ᶠ X in 𝓝 X₀, ∀ i k, |X i k - X₀ i k| ≤ 1 := by
      filter_upwards [closedBall_mem_nhds X₀ one_pos] with X hX i k
      rw [← Real.dist_eq]
      exact (dist_le_pi_dist (X i) (X₀ i) k).trans ((dist_le_pi_dist X X₀ i).trans hX)
    refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun X =>
        (kp_measurable_comp_grad (kp_continuous_of hf).measurable (Matrix.of X) φ).aestronglyMeasurable
    · filter_upwards [hnhds] with X hX
      filter_upwards with x
      rw [Real.norm_eq_abs]
      have : Matrix.of X + grad φ x = Matrix.of X₀ + (Matrix.of X - Matrix.of X₀ + grad φ x) := by
        abel
      rw [this]
      refine hM _ fun i k => ?_
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply]
      calc |X i k - X₀ i k + grad φ x i k| ≤ |X i k - X₀ i k| + |grad φ x i k| := abs_add_le _ _
        _ ≤ 1 + K := add_le_add (hX i k) (kp_grad_abs_le hφ x i k)
        _ = K + 1 := add_comm _ _
    · exact integrableOn_const (by rw [kp_volume_unitCube]; exact ENNReal.one_ne_top)
    · exact Filter.Eventually.of_forall fun x =>
        (hf.comp ((continuous_matrixOf.2 continuous_id).add continuous_const)).continuousAt
  have hc : Continuous fun A : Matrix (Fin d) (Fin m) ℝ => (fun i k => A i k : Fin d → Fin m → ℝ) :=
    continuous_pi fun i => continuous_pi fun k => continuous_id.matrix_elem i k
  exact hg.comp hc

/-- `kpQ f` is upper semicontinuous, as an infimum of continuous functions. -/
theorem kpQ_usc {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) :
    UpperSemicontinuous (kpQ f) := by
  refine upperSemicontinuous_iInf fun φ => upperSemicontinuous_iInf fun hφ => ?_
  obtain ⟨⟨K, hK⟩, -⟩ := hφ
  exact (continuous_coe_real_ereal.comp (kp_continuous_integral hf hK)).upperSemicontinuous

/-! ### Cut-offs -/

/-- The cut-off equal to `1` on `closedBall x ((1 - δ) r)`, `0` outside `ball x r`, and
`1/(δ r)`-Lipschitz. -/
noncomputable def kpCut (x : Fin m → ℝ) (r δ : ℝ) (y : Fin m → ℝ) : ℝ :=
  max 0 (min 1 ((r - ‖y - x‖) / (δ * r)))

theorem kpCut_nonneg (x : Fin m → ℝ) (r δ : ℝ) (y : Fin m → ℝ) : 0 ≤ kpCut x r δ y :=
  le_max_left _ _

theorem kpCut_le_one (x : Fin m → ℝ) (r δ : ℝ) (y : Fin m → ℝ) : kpCut x r δ y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem kpCut_eq_one {x : Fin m → ℝ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) {y : Fin m → ℝ}
    (hy : ‖y - x‖ ≤ (1 - δ) * r) : kpCut x r δ y = 1 := by
  have h : 1 ≤ (r - ‖y - x‖) / (δ * r) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  simp [kpCut, min_eq_left h]

theorem kpCut_eq_zero {x : Fin m → ℝ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) {y : Fin m → ℝ}
    (hy : r ≤ ‖y - x‖) : kpCut x r δ y = 0 := by
  have h : (r - ‖y - x‖) / (δ * r) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  simp [kpCut, (min_le_right _ _).trans h]

theorem kpCut_lipschitz (x : Fin m → ℝ) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    LipschitzWith (1 / (δ * r)).toNNReal (kpCut x r δ) := by
  have hu : LipschitzWith (1 / (δ * r)).toNNReal fun y : Fin m → ℝ => (r - ‖y - x‖) / (δ * r) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity), ← sub_div, abs_div,
      abs_of_pos (by positivity : 0 < δ * r), div_le_iff₀ (by positivity : 0 < δ * r)]
    have : |r - ‖y - x‖ - (r - ‖z - x‖)| ≤ dist y z := by
      rw [show r - ‖y - x‖ - (r - ‖z - x‖) = ‖z - x‖ - ‖y - x‖ by ring, dist_comm,
        dist_eq_norm]
      calc |‖z - x‖ - ‖y - x‖| ≤ ‖(z - x) - (y - x)‖ := abs_norm_sub_norm_le _ _
        _ = ‖z - y‖ := by rw [sub_sub_sub_cancel_right]
    calc |r - ‖y - x‖ - (r - ‖z - x‖)| ≤ dist y z := this
      _ = 1 / (δ * r) * dist y z * (δ * r) := by field_simp
  have := (hu.min_const 1).const_max 0
  convert this using 2 with y
  simp only [kpCut, min_comm]

/-- A product `θ g` with `θ ∈ [0, 1]` vanishing outside `S` and `|g| ≤ B` on `S` is
`(L_g + L_θ B)`-Lipschitz. -/
theorem kp_lipschitz_smul {E F : Type*} [PseudoMetricSpace E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ F] {θ : E → ℝ} {g : E → F} {Lθ Lg : NNReal} {B : ℝ} {S : Set E}
    (hθ : LipschitzWith Lθ θ) (hθ0 : ∀ y, 0 ≤ θ y) (hθ1 : ∀ y, θ y ≤ 1)
    (hθS : ∀ y ∉ S, θ y = 0) (hg : LipschitzWith Lg g) (hgS : ∀ y ∈ S, ‖g y‖ ≤ B) (hB : 0 ≤ B) :
    LipschitzWith (Lg + Lθ * B.toNNReal) fun y => θ y • g y := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [dist_eq_norm]
  push_cast
  rw [Real.coe_toNNReal _ hB]
  have hθd : |θ y - θ z| ≤ Lθ * dist y z := by
    rw [← Real.dist_eq]; exact hθ.dist_le_mul y z
  have hgd : ‖g y - g z‖ ≤ Lg * dist y z := by
    rw [← dist_eq_norm]; exact hg.dist_le_mul y z
  by_cases hz : z ∈ S
  · -- θ y g y - θ z g z = θ y (g y - g z) + (θ y - θ z) g z
    have e : θ y • g y - θ z • g z = θ y • (g y - g z) + (θ y - θ z) • g z := by
      rw [smul_sub, sub_smul]; abel
    rw [e]
    calc ‖θ y • (g y - g z) + (θ y - θ z) • g z‖
        ≤ ‖θ y • (g y - g z)‖ + ‖(θ y - θ z) • g z‖ := norm_add_le _ _
      _ = |θ y| * ‖g y - g z‖ + |θ y - θ z| * ‖g z‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * (Lg * dist y z) + (Lθ * dist y z) * B := by
          gcongr
          · rw [abs_of_nonneg (hθ0 y)]; exact hθ1 y
          · exact hgS z hz
      _ = (Lg + Lθ * B) * dist y z := by ring
  · by_cases hy : y ∈ S
    · have e : θ y • g y - θ z • g z = (θ y - θ z) • g y := by
        rw [hθS z hz, zero_smul, sub_zero, sub_zero]
      rw [e, norm_smul, Real.norm_eq_abs]
      calc |θ y - θ z| * ‖g y‖ ≤ (Lθ * dist y z) * B :=
            mul_le_mul hθd (hgS y hy) (norm_nonneg _) (by positivity)
        _ ≤ (Lg + Lθ * B) * dist y z := by
            have h1 : (0 : ℝ) ≤ Lg * dist y z := mul_nonneg Lg.2 dist_nonneg
            nlinarith
    · rw [hθS y hy, hθS z hz, zero_smul, zero_smul, sub_zero, norm_zero]
      exact mul_nonneg (by positivity) dist_nonneg

/-! ### The local modification near a point of differentiability -/

/-- The tangent map of `φ` at `x`. -/
noncomputable def kpTan (φ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) :
    (Fin m → ℝ) → Fin d → ℝ :=
  fun z => φ x + fderiv ℝ φ x (z - x)

/-- The corner of the cube `ball x ρ` (sup norm): `ball x ρ = c + 2ρ (0,1)^m`. -/
def kpCorner (x : Fin m → ℝ) (ρ : ℝ) : Fin m → ℝ := x - fun _ => ρ

/-- The modification of `φ` in `ball x r`: the tangent map glued to `φ` by the cut-off, plus a
rescaled copy of `ψ` in `ball x ((1 - δ) r)`. -/
noncomputable def kpPiece (φ ψ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) (r δ : ℝ) :
    (Fin m → ℝ) → Fin d → ℝ :=
  fun z => kpCut x r δ z • (kpTan φ x z - φ z) +
    kpScale ψ (kpCorner x ((1 - δ) * r)) (2 * ((1 - δ) * r)) z

theorem kp_ball_eq_preimage (x : Fin m → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ball x ρ = {y | (2 * ρ)⁻¹ • (y - kpCorner x ρ) ∈ unitCube m} := by
  ext y
  simp only [mem_ball, dist_pi_lt_iff hρ, Real.dist_eq, abs_sub_lt_iff, mem_ofPred_eq, unitCube,
    Set.mem_pi, mem_univ, true_implies, mem_Ioo, kpCorner, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  refine forall_congr' fun i => ?_
  have h2 : 0 < 2 * ρ := by positivity
  constructor
  · rintro ⟨h1, h1'⟩
    constructor
    · exact mul_pos (inv_pos.2 h2) (by linarith)
    · rw [inv_mul_lt_iff₀ h2]; linarith
  · rintro ⟨h1, h1'⟩
    have h1 := (mul_pos_iff_of_pos_left (inv_pos.2 h2)).1 h1
    rw [inv_mul_lt_iff₀ h2] at h1'
    constructor <;> linarith

theorem kpTan_lipschitz {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (x : Fin m → ℝ) : LipschitzWith K (kpTan φ x) := by
  have hD : ‖fderiv ℝ φ x‖ ≤ K := norm_fderiv_le_of_lipschitz ℝ hφ (x₀ := x)
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [dist_eq_norm, dist_eq_norm, kpTan, kpTan, add_sub_add_left_eq_sub, ← map_sub,
    sub_sub_sub_cancel_right]
  exact ((fderiv ℝ φ x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))

theorem kpTan_grad {φ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ} (hφ : DifferentiableAt ℝ φ x)
    (y : Fin m → ℝ) : grad (kpTan φ x) y = grad φ x := by
  ext i k
  change fderiv ℝ (fun z => (φ x + fderiv ℝ φ x (z - x)) i) y (Pi.single k 1) =
    fderiv ℝ (fun z => φ z i) x (Pi.single k 1)
  have h1 : HasFDerivAt (fun z => (φ x + fderiv ℝ φ x (z - x)) i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ φ x)) y := by
    have : HasFDerivAt (fun z => φ x + fderiv ℝ φ x (z - x)) (fderiv ℝ φ x) y := by
      have := ((fderiv ℝ φ x).hasFDerivAt (x := y - x)).comp y ((hasFDerivAt_id y).sub_const x)
      simpa using this.const_add (φ x)
    exact (hasFDerivAt_apply i _).comp y this
  have h2 : HasFDerivAt (fun z => φ z i) ((ContinuousLinearMap.proj i).comp (fderiv ℝ φ x)) x :=
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin d => ℝ) i (φ x)).comp x hφ.hasFDerivAt
  rw [h1.fderiv, h2.fderiv]

section Piece

variable {φ ψ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ} {r δ : ℝ}

theorem kpScale_eq_zero_of_notMem_ball (hψ : ∀ y ∉ unitCube m, ψ y = 0) {ρ : ℝ} (hρ : 0 < ρ)
    {z : Fin m → ℝ} (hz : z ∉ ball x ρ) : kpScale ψ (kpCorner x ρ) (2 * ρ) z = 0 := by
  refine kpScale_eq_zero hψ _ _ ?_
  rw [kp_ball_eq_preimage x hρ] at hz
  exact hz

theorem kpPiece_eq_zero (hr : 0 < r) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hψ : ∀ y ∉ unitCube m, ψ y = 0) {z : Fin m → ℝ} (hz : z ∉ ball x r) :
    kpPiece φ ψ x r δ z = 0 := by
  have hz' : r ≤ ‖z - x‖ := by rw [mem_ball, dist_eq_norm, not_lt] at hz; exact hz
  have hρ : 0 < (1 - δ) * r := mul_pos (by linarith) hr
  have hzρ : z ∉ ball x ((1 - δ) * r) := fun h =>
    hz (ball_subset_ball (by nlinarith) h)
  simp only [kpPiece, kpCut_eq_zero hr hδ0 hz', zero_smul, zero_add,
    kpScale_eq_zero_of_notMem_ball hψ hρ hzρ]

/-- The glued map near `x`, without the inserted copy of `ψ`, is `(3K+1)`-Lipschitz. -/
theorem kp_cut_lipschitz {K : NNReal} (hφ : LipschitzWith K φ) (hr : 0 < r) (hδ0 : 0 < δ)
    (happrox : ∀ z ∈ closedBall x r, ‖φ z - kpTan φ x z‖ ≤ δ * r) :
    LipschitzWith (K + (K + K + (1 / (δ * r)).toNNReal * (δ * r).toNNReal))
      fun z => φ z + kpCut x r δ z • (kpTan φ x z - φ z) := by
  refine hφ.add (kp_lipschitz_smul (S := closedBall x r) (kpCut_lipschitz x hr hδ0)
    (kpCut_nonneg x r δ) (kpCut_le_one x r δ) (fun y hy => ?_) ((kpTan_lipschitz hφ x).sub hφ)
    (fun y hy => ?_) (by positivity))
  · refine kpCut_eq_zero hr hδ0 ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hy
    exact hy.le
  · rw [norm_sub_rev]; exact happrox y hy

theorem kp_cut_lipschitz_const {K : NNReal} (hr : 0 < r) (hδ0 : 0 < δ) :
    ((K + (K + K + (1 / (δ * r)).toNNReal * (δ * r).toNNReal) : NNReal) : ℝ) = 3 * K + 1 := by
  push_cast
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  field_simp
  ring

theorem kpPiece_lipschitz {K K' : NNReal} (hφ : LipschitzWith K φ) (hψ : LipschitzWith K' ψ)
    (hr : 0 < r) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (happrox : ∀ z ∈ closedBall x r, ‖φ z - kpTan φ x z‖ ≤ δ * r) :
    ∃ C, LipschitzWith C (kpPiece φ ψ x r δ) := by
  have hρ : 0 < 2 * ((1 - δ) * r) := by have := mul_pos (by linarith : (0 : ℝ) < 1 - δ) hr; linarith
  refine ⟨_, (kp_lipschitz_smul (S := closedBall x r) (B := δ * r) (kpCut_lipschitz x hr hδ0)
    (kpCut_nonneg x r δ) (kpCut_le_one x r δ) (fun y hy => ?_) ((kpTan_lipschitz hφ x).sub hφ)
    (fun y hy => ?_) (by positivity)).add (kpScale_lipschitz hψ _ hρ)⟩
  · refine kpCut_eq_zero hr hδ0 ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hy
    exact hy.le
  · rw [norm_sub_rev]; exact happrox y hy

/-- In the inner cube, the glued map is the tangent map plus the copy of `ψ`. -/
theorem kpPiece_eventually_inner (hr : 0 < r) (hδ0 : 0 < δ) {z : Fin m → ℝ}
    (hz : z ∈ ball x ((1 - δ) * r)) :
    (fun y => φ y + kpPiece φ ψ x r δ y) =ᶠ[𝓝 z]
      fun y => kpTan φ x y + kpScale ψ (kpCorner x ((1 - δ) * r)) (2 * ((1 - δ) * r)) y := by
  filter_upwards [isOpen_ball.mem_nhds hz] with y hy
  have : kpCut x r δ y = 1 := by
    refine kpCut_eq_one hr hδ0 ?_
    rw [mem_ball, dist_eq_norm] at hy
    exact hy.le
  simp only [kpPiece, this, one_smul]
  abel

/-- Outside the inner cube, the glued map does not see the copy of `ψ`. -/
theorem kpPiece_eventually_outer (hψ : ∀ y ∉ unitCube m, ψ y = 0) (hr : 0 < r) (hδ1 : δ < 1)
    {z : Fin m → ℝ} (hz : z ∉ closedBall x ((1 - δ) * r)) :
    (fun y => φ y + kpPiece φ ψ x r δ y) =ᶠ[𝓝 z]
      fun y => φ y + kpCut x r δ y • (kpTan φ x y - φ y) := by
  have hρ : 0 < (1 - δ) * r := mul_pos (by linarith) hr
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz] with y hy
  have : y ∉ ball x ((1 - δ) * r) := fun h => hy (ball_subset_closedBall h)
  simp only [kpPiece, kpScale_eq_zero_of_notMem_ball hψ hρ this, add_zero]

end Piece

theorem kp_finsum_lipschitz {ι : Type*} (t : Finset ι) (g : ι → (Fin m → ℝ) → Fin d → ℝ)
    (hg : ∀ p ∈ t, ∃ C, LipschitzWith C (g p)) :
    ∃ C, LipschitzWith C fun z => ∑ p ∈ t, g p z := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨C1, h1⟩ := hg a (Finset.mem_insert_self _ _)
    obtain ⟨C2, h2⟩ := ih fun p hp => hg p (Finset.mem_insert_of_mem hp)
    refine ⟨C1 + C2, ?_⟩
    simpa [Finset.sum_insert ha] using h1.add h2

theorem kp_volume_sphere (x : Fin m → ℝ) {ρ : ℝ} (hρ : 0 < ρ) : volume (sphere x ρ) = 0 := by
  rw [← frontier_ball x hρ.ne']
  exact Convex.addHaar_frontier volume (convex_ball x ρ)

/-- **Gluing.** Finitely many disjoint cubes `closedBall x_p r_p` in the unit cube, around points
where `φ` is differentiable and `δ r_p`-close to its tangent map: replacing `φ` in each cube by the
tangent map glued to `φ` by a cut-off, plus a rescaled copy of a test map `ψ_p` in the inner cube
`ball x_p ((1 - δ) r_p)`, gives a test map whose energy is at most the sum of the energies of the
copies plus `M` times the measure of the rest. -/
theorem kp_glue_on {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) {Ω : Set (Fin m → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (hφQ : ∀ x ∉ Ω, φ x = 0) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (t : Finset ((Fin m → ℝ) × ℝ))
    (ht : ∀ p ∈ t, 0 < p.2 ∧ closedBall p.1 p.2 ⊆ Ω ∧ DifferentiableAt ℝ φ p.1 ∧
      ∀ z ∈ closedBall p.1 p.2, ‖φ z - kpTan φ p.1 z‖ ≤ δ * p.2)
    (hdisj : (t : Set ((Fin m → ℝ) × ℝ)).PairwiseDisjoint fun p => closedBall p.1 p.2)
    (ψ : (Fin m → ℝ) × ℝ → (Fin m → ℝ) → Fin d → ℝ) (hψ : ∀ p ∈ t, KpAdm (ψ p)) {M : ℝ}
    (hM : ∀ X : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |X i k| ≤ 3 * K + 1) → |f (A + X)| ≤ M) :
    ∃ Φ, ((∃ C, LipschitzWith C Φ) ∧ ∀ x ∉ Ω, Φ x = 0) ∧ ∫ x in Ω, f (A + grad Φ x) ≤
      (∑ p ∈ t, (2 * ((1 - δ) * p.2)) ^ m *
        ∫ y in unitCube m, f (A + grad φ p.1 + grad (ψ p) y)) +
      M * volume.real (Ω \ ⋃ p ∈ t, ball p.1 ((1 - δ) * p.2)) := by
  classical
  set Φ : (Fin m → ℝ) → Fin d → ℝ := fun z => φ z + ∑ p ∈ t, kpPiece φ (ψ p) p.1 p.2 δ z
    with hΦ
  have hpiece0 : ∀ q ∈ t, ∀ z, z ∉ closedBall q.1 q.2 →
      ∀ᶠ y in 𝓝 z, kpPiece φ (ψ q) q.1 q.2 δ y = 0 := by
    intro q hq z hz
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz] with y hy
    exact kpPiece_eq_zero (ht q hq).1 hδ0 hδ1 (hψ q hq).2 (fun h => hy (ball_subset_closedBall h))
  have hloc : ∀ p ∈ t, ∀ z ∈ closedBall p.1 p.2,
      Φ =ᶠ[𝓝 z] fun y => φ y + kpPiece φ (ψ p) p.1 p.2 δ y := by
    intro p hp z hz
    have h : ∀ q ∈ t.erase p, ∀ᶠ y in 𝓝 z, kpPiece φ (ψ q) q.1 q.2 δ y = 0 := by
      intro q hq
      have hq' := Finset.mem_of_mem_erase hq
      refine hpiece0 q hq' z fun h => ?_
      exact Set.disjoint_left.1 (hdisj hq' hp (Finset.ne_of_mem_erase hq)) h hz
    filter_upwards [(Filter.eventually_all_finset _).2 h] with y hy
    simp only [hΦ]
    rw [← Finset.add_sum_erase t _ hp, Finset.sum_eq_zero hy, add_zero]
  have hout : ∀ z, (∀ p ∈ t, z ∉ closedBall p.1 p.2) → Φ =ᶠ[𝓝 z] φ := by
    intro z hz
    filter_upwards [(Filter.eventually_all_finset t).2 fun q hq => hpiece0 q hq z (hz q hq)]
      with y hy
    simp only [hΦ, Finset.sum_eq_zero hy, add_zero]
  -- `Φ` is a test map
  have hΦlip : ∃ C, LipschitzWith C Φ := by
    obtain ⟨C, hC⟩ := kp_finsum_lipschitz t (fun p => kpPiece φ (ψ p) p.1 p.2 δ) fun p hp => by
      obtain ⟨⟨K', hK'⟩, -⟩ := hψ p hp
      exact kpPiece_lipschitz hφ hK' (ht p hp).1 hδ0 hδ1 (ht p hp).2.2.2
    exact ⟨K + C, hφ.add hC⟩
  have hΦQ : ∀ x ∉ Ω, Φ x = 0 := by
    intro x hx
    simp only [hΦ, hφQ x hx, zero_add]
    refine Finset.sum_eq_zero fun p hp => ?_
    exact kpPiece_eq_zero (ht p hp).1 hδ0 hδ1 (hψ p hp).2
      (fun h => hx ((ht p hp).2.1 (ball_subset_closedBall h)))
  refine ⟨Φ, ⟨hΦlip, hΦQ⟩, ?_⟩
  obtain ⟨CΦ, hCΦ⟩ := hΦlip
  set U := ⋃ p ∈ t, ball p.1 ((1 - δ) * p.2) with hU
  have hUQ : U ⊆ Ω := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    have h1 : (1 - δ) * p.2 ≤ p.2 := by nlinarith [(ht p hp).1]
    exact (ht p hp).2.1 (ball_subset_closedBall (ball_subset_ball h1 hzp))
  have hint : IntegrableOn (fun x => f (A + grad Φ x)) Ω := kp_integrableOn hf A hCΦ hΩ
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion _ fun _ _ => measurableSet_ball
  rw [← integral_inter_add_sdiff hUm hint, inter_eq_right.2 hUQ,
    integral_biUnion_finset t (fun p _ => measurableSet_ball) (fun p hp q hq hpq => by
      have h1 : (1 - δ) * p.2 ≤ p.2 := by nlinarith [(ht p hp).1]
      have h2 : (1 - δ) * q.2 ≤ q.2 := by nlinarith [(ht q hq).1]
      exact (hdisj hp hq hpq).mono (ball_subset_closedBall.trans (closedBall_subset_closedBall h1))
        (ball_subset_closedBall.trans (closedBall_subset_closedBall h2)))
    (fun p hp => hint.mono_set (hUQ.trans' (subset_biUnion_of_mem (u := fun p =>
      ball p.1 ((1 - δ) * p.2)) hp)))]
  apply add_le_add
  · -- the inner cubes
    refine le_of_eq (Finset.sum_congr rfl fun p hp => ?_)
    obtain ⟨hr, -, hdiff, happrox⟩ := ht p hp
    obtain ⟨⟨Kψ, hKψ⟩, hψQ⟩ := hψ p hp
    have hρ : 0 < (1 - δ) * p.2 := mul_pos (by linarith) hr
    have h2ρ : 0 < 2 * ((1 - δ) * p.2) := by linarith
    set c := kpCorner p.1 ((1 - δ) * p.2)
    set Ψ := kpScale (ψ p) c (2 * ((1 - δ) * p.2))
    have hΨlip : LipschitzWith Kψ Ψ := kpScale_lipschitz hKψ c h2ρ
    have hae : ∀ᵐ z, z ∈ ball p.1 ((1 - δ) * p.2) → f (A + grad Φ z) =
        (fun y => f (A + grad φ p.1 + grad (ψ p) y)) ((2 * ((1 - δ) * p.2))⁻¹ • (z - c)) := by
      filter_upwards [hΨlip.ae_differentiableAt (μ := volume)] with z hzd hz
      have e1 := (hloc p hp z (ball_subset_closedBall (ball_subset_ball (by nlinarith) hz))).trans
        (kpPiece_eventually_inner (ψ := ψ p) hr hδ0 hz)
      rw [kp_grad_congr e1]
      have hTd : DifferentiableAt ℝ (kpTan φ p.1) z := by
        have : DifferentiableAt ℝ (fun y => φ p.1 + fderiv ℝ φ p.1 (y - p.1)) z :=
          ((fderiv ℝ φ p.1).differentiableAt.comp z (differentiableAt_id.sub_const _)).const_add _
        exact this
      rw [show (fun y => kpTan φ p.1 y + Ψ y) = kpTan φ p.1 + Ψ from rfl,
        kp_grad_add hTd hzd, kpTan_grad hdiff, kpScale_grad _ _ h2ρ.ne', add_assoc]
    rw [setIntegral_congr_ae measurableSet_ball hae, ← integral_indicator measurableSet_ball,
      ← integral_indicator kp_measurableSet_unitCube]
    have hind : (ball p.1 ((1 - δ) * p.2)).indicator (fun z =>
        (fun y => f (A + grad φ p.1 + grad (ψ p) y)) ((2 * ((1 - δ) * p.2))⁻¹ • (z - c))) =
        fun z => (unitCube m).indicator (fun y => f (A + grad φ p.1 + grad (ψ p) y))
          ((2 * ((1 - δ) * p.2))⁻¹ • (z - c)) := by
      ext z
      simp only [Set.indicator, kp_ball_eq_preimage p.1 hρ, mem_ofPred_eq]
      rfl
    rw [hind, kp_integral_comp_affine _ c h2ρ]
  · -- the rest: the gradient is bounded there
    have hfin : volume (Ω \ U) < ⊤ := (measure_mono sdiff_subset).trans_lt hΩ.lt_top
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const_ae' hfin ?_
    have hnull : ∀ᵐ z : Fin m → ℝ, ∀ p ∈ t,
        z ∉ sphere p.1 ((1 - δ) * p.2) ∧ z ∉ sphere p.1 p.2 := by
      refine (Filter.eventually_all_finset t).2 fun p hp => ?_
      have hr := (ht p hp).1
      have hρ : 0 < (1 - δ) * p.2 := mul_pos (by linarith) hr
      exact (measure_eq_zero_iff_ae_notMem.1 (kp_volume_sphere p.1 hρ)).and
        (measure_eq_zero_iff_ae_notMem.1 (kp_volume_sphere p.1 hr))
    filter_upwards [hnull] with z hz hzQU
    rw [Real.norm_eq_abs]
    refine hM _ fun i k => ?_
    have hzU : z ∉ U := hzQU.2
    by_cases hzin : ∃ p ∈ t, z ∈ ball p.1 p.2
    · obtain ⟨p, hp, hzp⟩ := hzin
      obtain ⟨hr, -, -, happrox⟩ := ht p hp
      have hzρ : z ∉ closedBall p.1 ((1 - δ) * p.2) := by
        rw [← ball_union_sphere]
        rintro (h | h)
        · exact hzU (mem_iUnion₂.2 ⟨p, hp, h⟩)
        · exact (hz p hp).1 h
      have e := (hloc p hp z (ball_subset_closedBall hzp)).trans
        (kpPiece_eventually_outer (hψ p hp).2 hr hδ1 hzρ)
      rw [kp_grad_congr e]
      have := kp_grad_abs_le (kp_cut_lipschitz hφ hr hδ0 happrox) z i k
      rwa [kp_cut_lipschitz_const hr hδ0] at this
    · push Not at hzin
      have hcl : ∀ p ∈ t, z ∉ closedBall p.1 p.2 := by
        intro p hp h
        rw [← ball_union_sphere] at h
        rcases h with h | h
        · exact hzin p hp h
        · exact (hz p hp).2 h
      rw [kp_grad_congr (hout z hcl)]
      have := kp_grad_abs_le hφ z i k
      have hK : (0 : ℝ) ≤ K := K.2
      linarith

/-- `kp_glue_on` in the unit cube. -/
theorem kp_glue {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (hφQ : ∀ x ∉ unitCube m, φ x = 0) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (t : Finset ((Fin m → ℝ) × ℝ))
    (ht : ∀ p ∈ t, 0 < p.2 ∧ closedBall p.1 p.2 ⊆ unitCube m ∧ DifferentiableAt ℝ φ p.1 ∧
      ∀ z ∈ closedBall p.1 p.2, ‖φ z - kpTan φ p.1 z‖ ≤ δ * p.2)
    (hdisj : (t : Set ((Fin m → ℝ) × ℝ)).PairwiseDisjoint fun p => closedBall p.1 p.2)
    (ψ : (Fin m → ℝ) × ℝ → (Fin m → ℝ) → Fin d → ℝ) (hψ : ∀ p ∈ t, KpAdm (ψ p)) {M : ℝ}
    (hM : ∀ X : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |X i k| ≤ 3 * K + 1) → |f (A + X)| ≤ M) :
    ∃ Φ, KpAdm Φ ∧ ∫ x in unitCube m, f (A + grad Φ x) ≤
      (∑ p ∈ t, (2 * ((1 - δ) * p.2)) ^ m *
        ∫ y in unitCube m, f (A + grad φ p.1 + grad (ψ p) y)) +
      M * volume.real (unitCube m \ ⋃ p ∈ t, ball p.1 ((1 - δ) * p.2)) :=
  kp_glue_on hf A hφ (by rw [kp_volume_unitCube]; exact ENNReal.one_ne_top) hφQ hδ0 hδ1 t ht
    hdisj ψ hψ hM

/-! ### Quasiconvexity of the infimum formula, robust form -/

/-- The truncation `max (kpQ f B) N` is a real number between `N` and `max (f B) N`. -/
theorem kp_trunc (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (B : Matrix (Fin d) (Fin m) ℝ) (N : ℝ) :
    (((max (kpQ f B) (N : EReal)).toReal : ℝ) : EReal) = max (kpQ f B) (N : EReal) ∧
      N ≤ (max (kpQ f B) (N : EReal)).toReal ∧
      (max (kpQ f B) (N : EReal)).toReal ≤ max (f B) N := by
  have h1 : (N : EReal) ≤ max (kpQ f B) (N : EReal) := le_max_right _ _
  have h2 : max (kpQ f B) (N : EReal) ≤ ((max (f B) N : ℝ) : EReal) := by
    exact max_le ((kpQ_le B).trans (EReal.coe_le_coe_iff.2 (le_max_left _ _)))
      (EReal.coe_le_coe_iff.2 (le_max_right _ _))
  have hne1 : max (kpQ f B) (N : EReal) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
  have hne2 : max (kpQ f B) (N : EReal) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1
  have e := EReal.coe_toReal hne1 hne2
  refine ⟨e, ?_, ?_⟩
  · rw [← EReal.coe_le_coe_iff, e]; exact h1
  · rw [← EReal.coe_le_coe_iff, e]; exact h2

theorem kp_measurable_trunc {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) (φ : (Fin m → ℝ) → Fin d → ℝ) (N : ℝ) :
    Measurable fun x => (max (kpQ f (A + grad φ x)) (N : EReal)).toReal := by
  have hU : UpperSemicontinuous fun X : Fin d → Fin m → ℝ => kpQ f (Matrix.of X) := kpQ_usc hf
  have hG : Measurable fun X : Fin d → Fin m → ℝ => kpQ f (Matrix.of X) := hU.measurable
  have hin : Measurable fun x => (fun i k => A i k + grad φ x i k : Fin d → Fin m → ℝ) :=
    Measurable.of_eval fun i => Measurable.of_eval fun k =>
      measurable_const.add ((measurable_pi_iff.1 ((measurable_pi_iff.1 (kp_measurable_grad φ)) i)) k)
  exact measurable_ereal_toReal.comp ((hG.comp hin).max measurable_const)

/-- An `EReal` bounded by `b + C ε` for all small `ε > 0` is bounded by `b`. -/
theorem kp_ereal_le_of_eps {a : EReal} {b C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → a ≤ ((b + C * ε : ℝ) : EReal)) : a ≤ (b : EReal) := by
  induction a using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd (h (1 / 4) (by norm_num) (by norm_num)) (not_le.2 (EReal.coe_lt_top _))
  | coe a =>
    rw [EReal.coe_le_coe_iff]
    by_contra hab
    push Not at hab
    set ε := min (1 / 4) ((a - b) / (2 * (C + 1))) with hε
    have hε0 : 0 < ε := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
    have hε1 : ε < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
    have h1 := h ε hε0 hε1
    rw [EReal.coe_le_coe_iff] at h1
    have h2 : ε ≤ (a - b) / (2 * (C + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith

theorem kp_measureReal_closedBall (x : Fin m → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) = (2 * r) ^ m := by
  rw [measureReal_def, Real.volume_pi_closedBall x hr, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

theorem kp_measureReal_ball (x : Fin m → ℝ) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) = (2 * r) ^ m := by
  rw [measureReal_def, Real.volume_pi_ball x hr, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

/-- The arithmetic at the end of the gluing argument. -/
theorem kp_final_estimate {m : ℕ} {ε H M G S T R I V : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (_hH0 : 0 ≤ H) (hM0 : 0 ≤ M) (hG : G ≤ (1 - ε) ^ m * (S + 2 * ε * T)) (hI : I = S + R)
    (hR : |R| ≤ H * ε) (hS : |S| ≤ H) (hT1 : 1 - ε ≤ T) (hT2 : T ≤ 1)
    (hV : V = 1 - (1 - ε) ^ m * T) :
    G + M * V ≤ I + (H + 3 + m * (H + 2) + M * (m + 1)) * ε := by
  have hpow0 : 0 ≤ (1 - ε) ^ m := pow_nonneg (by linarith) m
  have hpow1 : (1 - ε) ^ m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hbern : 1 + (m : ℝ) * (-ε) ≤ (1 + -ε) ^ m :=
    one_add_le_pow_of_two_add_nonneg (by linarith) m
  rw [← sub_eq_add_neg] at hbern
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- the measure of the rest
  have hV' : V ≤ m * ε + ε := by
    rw [hV]
    have h1 : (1 - ε) ^ m * (1 - ε) ≤ (1 - ε) ^ m * T := mul_le_mul_of_nonneg_left hT1 hpow0
    have h2 : (1 - m * ε) * (1 - ε) ≤ (1 - ε) ^ m * (1 - ε) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h3 : 0 ≤ (m : ℝ) * ε * ε := by positivity
    have e : (1 - m * ε) * (1 - ε) = 1 - m * ε - ε + m * ε * ε := by ring
    linarith
  set Y := S + 2 * ε * T with hY
  have hT0 : 0 ≤ T := by linarith
  have hYabs : |Y| ≤ H + 1 := by
    have h0 : 0 ≤ 2 * ε * T := by positivity
    have h1 : 2 * ε * T ≤ 1 := by nlinarith
    calc |S + 2 * ε * T| ≤ |S| + |2 * ε * T| := abs_add_le _ _
      _ ≤ H + 1 := by rw [abs_of_nonneg h0]; linarith
  have hYle : Y ≤ I + H * ε + 2 * ε := by
    have := neg_abs_le R
    have h1 : 2 * ε * T ≤ 2 * ε := by nlinarith
    rw [hY, hI]; linarith
  have hpowY : (1 - ε) ^ m * Y ≤ Y + m * ε * (H + 1) := by
    have h0 : 0 ≤ 1 - (1 - ε) ^ m := by linarith
    have h1 : ((1 - ε) ^ m - 1) * Y ≤ (1 - (1 - ε) ^ m) * |Y| := by
      have e : ((1 - ε) ^ m - 1) * Y = (1 - (1 - ε) ^ m) * (-Y) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (neg_le_abs Y) h0
    have h2 : (1 - (1 - ε) ^ m) * |Y| ≤ m * ε * (H + 1) :=
      mul_le_mul (by linarith) hYabs (abs_nonneg _) (by positivity)
    have e : (1 - ε) ^ m * Y = Y + ((1 - ε) ^ m - 1) * Y := by ring
    linarith
  have hMV : M * V ≤ M * (m * ε + ε) := mul_le_mul_of_nonneg_left hV' hM0
  have hfin : I + H * ε + 2 * ε + m * ε * (H + 1) + M * (m * ε + ε) ≤
      I + (H + 3 + m * (H + 2) + M * (m + 1)) * ε := by
    have e : I + (H + 3 + m * (H + 2) + M * (m + 1)) * ε =
        I + H * ε + 2 * ε + m * ε * (H + 1) + M * (m * ε + ε) + (ε + m * ε) := by ring
    have : 0 ≤ ε + m * ε := by positivity
    linarith
  linarith

/-- The fine cover of the gluing argument: almost every point of the cube is a point of
differentiability of `φ` and a Lebesgue point of `h`, so that all small cubes around it are
admissible. -/
theorem kp_fine_cover {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hK : LipschitzWith K φ)
    {h : (Fin m → ℝ) → ℝ} (hhint : IntegrableOn h (unitCube m)) {ε : ℝ} (hε0 : 0 < ε) :
    ∀ᵐ x, x ∈ unitCube m → ∀ δ' > 0, ∃ r ∈ Ioo 0 δ', closedBall x r ⊆ unitCube m ∧
      DifferentiableAt ℝ φ x ∧ (∀ z ∈ closedBall x r, ‖φ z - kpTan φ x z‖ ≤ ε * r) ∧
      volume.real (closedBall x r) * h x ≤
        (∫ y in closedBall x r, h y) + ε * volume.real (closedBall x r) := by
  have hloc : LocallyIntegrable ((unitCube m).indicator h) volume :=
    (hhint.integrable_indicator kp_measurableSet_unitCube).locallyIntegrable
  have hleb := (Besicovitch.vitaliFamily (volume : Measure (Fin m → ℝ))).ae_tendsto_average hloc
  filter_upwards [hK.ae_differentiableAt (μ := volume), hleb] with x hxd hxl hxQ δ' hδ'
  have e1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall x r ⊆ unitCube m := by
    obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.1 kp_isOpen_unitCube x hxQ
    filter_upwards [Ioo_mem_nhdsGT (half_pos hε')] with r hr
    exact (closedBall_subset_ball (by linarith [hr.2])).trans hball
  have e2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ closedBall x r, ‖φ z - kpTan φ x z‖ ≤ ε * r := by
    have hlo := hxd.hasFDerivAt.isLittleO
    obtain ⟨ρ0, hρ0, hball⟩ := Metric.eventually_nhds_iff.1 (Asymptotics.isLittleO_iff.1 hlo hε0)
    filter_upwards [Ioo_mem_nhdsGT hρ0] with r hr z hz
    have hzx : dist z x < ρ0 := lt_of_le_of_lt (mem_closedBall.1 hz) hr.2
    have := hball hzx
    calc ‖φ z - kpTan φ x z‖ = ‖φ z - φ x - fderiv ℝ φ x (z - x)‖ := by
          simp only [kpTan, sub_sub]
      _ ≤ ε * ‖z - x‖ := this
      _ ≤ ε * r := mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hz) hε0.le
  have e3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), volume.real (closedBall x r) * h x ≤
      (∫ y in closedBall x r, h y) + ε * volume.real (closedBall x r) := by
    have ht := hxl.comp (Besicovitch.tendsto_filterAt volume x)
    have hx' : (unitCube m).indicator h x = h x := indicator_of_mem hxQ h
    rw [hx'] at ht
    filter_upwards [ht (Ioi_mem_nhds (show h x - ε < h x by linarith)), e1,
      self_mem_nhdsWithin] with r hr hrQ hr0
    simp only [Function.comp_apply, mem_preimage, mem_Ioi] at hr
    rw [setAverage_eq, smul_eq_mul] at hr
    have hind : ∫ y in closedBall x r, (unitCube m).indicator h y =
        ∫ y in closedBall x r, h y :=
      setIntegral_congr_fun measurableSet_closedBall fun y hy => indicator_of_mem (hrQ hy) h
    rw [hind] at hr
    have hvpos : 0 < volume.real (closedBall x r) := by
      rw [kp_measureReal_closedBall x (le_of_lt hr0)]
      exact pow_pos (by linarith [mem_Ioi.1 hr0]) m
    rw [lt_inv_mul_iff₀ hvpos] at hr
    nlinarith
  obtain ⟨r, hr⟩ := (e1.and (e2.and (e3.and (Ioo_mem_nhdsGT hδ')))).exists
  exact ⟨r, hr.2.2.2, hr.1, hxd, hr.2.1, hr.2.2.1⟩

/-- **The infimum formula is quasiconvex** (robust form: no integrability is needed): for a test
map `φ` and a truncation level `N`, `kpQ f (A) ≤ ∫_Q max (kpQ f (A + ∇φ), N)`.

The standard gluing argument (Dacorogna 2008, proof of Theorem 6.9; Kinderlehrer–Pedregal 1991,
Proposition 8.1): almost every point of the cube is a point of differentiability of `φ` and a
Lebesgue point of the truncated integrand `h`; finitely many disjoint small cubes centred at such
points cover the unit cube up to `ε` (`kp_exists_finite_cover`); in each, `φ` is replaced by its
tangent map glued to `φ` by a cut-off, with a rescaled almost minimiser for `kpQ f (A + ∇φ (x))`
in the inner cube (`kp_glue`); the energy of the new test map is at most `∫_Q h + C ε`. -/
theorem kpQ_quasiconvex_robust {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} (hφ : KpAdm φ) (N : ℝ) :
    kpQ f A ≤
      ((∫ x in unitCube m, (max (kpQ f (A + grad φ x)) (N : EReal)).toReal : ℝ) : EReal) := by
  classical
  obtain ⟨⟨K, hK⟩, hφQ⟩ := hφ
  set h : (Fin m → ℝ) → ℝ := fun x => (max (kpQ f (A + grad φ x)) (N : EReal)).toReal with hh
  obtain ⟨Mf, -, hMf⟩ := kp_bdd hf A K
  obtain ⟨M, hM0, hM⟩ := kp_bdd hf A (3 * K + 1)
  set H := max |N| Mf with hH
  have hH0 : 0 ≤ H := (abs_nonneg N).trans (le_max_left _ _)
  have hhb : ∀ x, |h x| ≤ H := by
    intro x
    obtain ⟨-, h1, h2⟩ := kp_trunc f (A + grad φ x) N
    have h3 : f (A + grad φ x) ≤ Mf := (le_abs_self _).trans (hMf _ (kp_grad_abs_le hK x))
    rw [abs_le]; constructor
    · have := neg_abs_le N; have := le_max_left |N| Mf; linarith
    · calc h x ≤ max (f (A + grad φ x)) N := h2
        _ ≤ max Mf |N| := max_le_max h3 (le_abs_self N)
        _ = H := max_comm _ _
  have hhm : Measurable h := kp_measurable_trunc hf A φ N
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [kp_volume_unitCube]; exact ENNReal.one_ne_top
  have hhint : IntegrableOn h (unitCube m) :=
    Measure.integrableOn_of_bounded (M := H) hQfin hhm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hhb x)
  -- almost minimisers
  have hchoice : ∀ ε > 0, ∀ B : Matrix (Fin d) (Fin m) ℝ, ∃ ψ, KpAdm ψ ∧
      ∫ y in unitCube m, f (A + B + grad ψ y) ≤ (max (kpQ f (A + B)) (N : EReal)).toReal + ε := by
    intro ε hε B
    obtain ⟨e, -, -⟩ := kp_trunc f (A + B) N
    have hlt : kpQ f (A + B) <
        (((max (kpQ f (A + B)) (N : EReal)).toReal + ε : ℝ) : EReal) := by
      calc kpQ f (A + B) ≤ max (kpQ f (A + B)) (N : EReal) := le_max_left _ _
        _ = ((max (kpQ f (A + B)) (N : EReal)).toReal : EReal) := e.symm
        _ < _ := EReal.coe_lt_coe_iff.2 (by linarith)
    unfold kpQ at hlt
    obtain ⟨ψ, hψ⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hadm, hψ'⟩ := iInf_lt_iff.1 hψ
    exact ⟨ψ, hadm, (EReal.coe_lt_coe_iff.1 hψ').le⟩
  refine kp_ereal_le_of_eps (C := H + 3 + m * (H + 2) + M * (m + 1)) (by positivity)
    fun ε hε0 hε1 => ?_
  choose ψ hψadm hψle using hchoice ε hε0
  -- the fine cover
  set P : (Fin m → ℝ) → ℝ → Prop := fun x r => closedBall x r ⊆ unitCube m ∧
    DifferentiableAt ℝ φ x ∧ (∀ z ∈ closedBall x r, ‖φ z - kpTan φ x z‖ ≤ ε * r) ∧
    volume.real (closedBall x r) * h x ≤
      (∫ y in closedBall x r, h y) + ε * volume.real (closedBall x r) with hPdef
  have hP : ∀ᵐ x, x ∈ unitCube m → ∀ δ' > 0, ∃ r ∈ Ioo 0 δ', P x r :=
    kp_fine_cover hK hhint hε0
  obtain ⟨t, htP, htdisj, htvol⟩ := kp_exists_finite_cover hQfin kp_measurableSet_unitCube P hP
    (ENNReal.ofReal_pos.2 hε0)
  obtain ⟨Φ, hΦadm, hΦle⟩ := kp_glue hf A hK hφQ hε0 (by linarith : ε < 1) t
    (fun p hp => ⟨(htP p hp).1, (htP p hp).2.1, (htP p hp).2.2.1, (htP p hp).2.2.2.1⟩) htdisj
    (fun p => ψ (grad φ p.1)) (fun p _ => hψadm _) hM
  have hQ : kpQ f A ≤ ((∫ x in unitCube m, f (A + grad Φ x) : ℝ) : EReal) := iInf₂_le Φ hΦadm
  refine hQ.trans (EReal.coe_le_coe_iff.2 (hΦle.trans ?_))
  -- the estimates
  have hQ1 : volume.real (unitCube m) = 1 := by
    rw [measureReal_def, kp_volume_unitCube, ENNReal.toReal_one]
  have hV : ∀ p ∈ t, volume.real (closedBall p.1 p.2) = (2 * p.2) ^ m := fun p hp =>
    kp_measureReal_closedBall _ (htP p hp).1.le
  have hpow0 : 0 ≤ (1 - ε) ^ m := pow_nonneg (by linarith) m
  have hA : ∀ p ∈ t, (2 * ((1 - ε) * p.2)) ^ m *
      ∫ y in unitCube m, f (A + grad φ p.1 + grad (ψ (grad φ p.1)) y) ≤
      (1 - ε) ^ m * ((∫ y in closedBall p.1 p.2, h y) +
        2 * ε * volume.real (closedBall p.1 p.2)) := by
    intro p hp
    have hr := (htP p hp).1
    have hlebp := (htP p hp).2.2.2.2
    have hI := hψle (grad φ p.1)
    rw [hV p hp] at hlebp ⊢
    have e : (2 * ((1 - ε) * p.2)) ^ m = (1 - ε) ^ m * (2 * p.2) ^ m := by
      rw [← mul_pow]; ring_nf
    rw [e, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hpow0
    have h2 : 0 ≤ (2 * p.2) ^ m := pow_nonneg (by linarith) m
    change (2 * p.2) ^ m * ∫ y in unitCube m, f (A + grad φ p.1 + grad (ψ (grad φ p.1)) y) ≤ _
    have : (2 * p.2) ^ m * ∫ y in unitCube m, f (A + grad φ p.1 + grad (ψ (grad φ p.1)) y) ≤
        (2 * p.2) ^ m * (h p.1 + ε) := mul_le_mul_of_nonneg_left hI h2
    nlinarith
  have hsumA := Finset.sum_le_sum hA
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hsumA
  set S := ∑ p ∈ t, ∫ y in closedBall p.1 p.2, h y with hSdef
  set T := ∑ p ∈ t, volume.real (closedBall p.1 p.2) with hTdef
  have hUC : (⋃ p ∈ t, closedBall p.1 p.2) ⊆ unitCube m := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    exact (htP p hp).2.1 hzp
  have hUCm : MeasurableSet (⋃ p ∈ t, closedBall p.1 p.2) :=
    Finset.measurableSet_biUnion _ fun _ _ => measurableSet_closedBall
  have hS : S = ∫ y in ⋃ p ∈ t, closedBall p.1 p.2, h y :=
    (integral_biUnion_finset t (fun _ _ => measurableSet_closedBall) htdisj
      (fun p hp => hhint.mono_set (htP p hp).2.1)).symm
  have hT : T = volume.real (⋃ p ∈ t, closedBall p.1 p.2) :=
    (measureReal_biUnion_finset htdisj (fun _ _ => measurableSet_closedBall)
      (fun _ _ => measure_closedBall_lt_top.ne)).symm
  have hrest : volume.real (unitCube m \ ⋃ p ∈ t, closedBall p.1 p.2) ≤ ε :=
    (ENNReal.toReal_lt_of_lt_ofReal htvol).le
  have hTeq : T = 1 - volume.real (unitCube m \ ⋃ p ∈ t, closedBall p.1 p.2) := by
    rw [measureReal_sdiff hUC hUCm hQfin, hQ1, hT]; ring
  have hrest0 : 0 ≤ volume.real (unitCube m \ ⋃ p ∈ t, closedBall p.1 p.2) := measureReal_nonneg
  have hSeq : (∫ x in unitCube m, h x) =
      S + ∫ x in unitCube m \ ⋃ p ∈ t, closedBall p.1 p.2, h x := by
    rw [hS, ← integral_inter_add_sdiff hUCm hhint, inter_eq_right.2 hUC]
  have hfinC : volume (⋃ p ∈ t, closedBall p.1 p.2) < ⊤ :=
    (measure_mono hUC).trans_lt (by rw [kp_volume_unitCube]; exact ENNReal.one_lt_top)
  have hfinR : volume (unitCube m \ ⋃ p ∈ t, closedBall p.1 p.2) < ⊤ :=
    (measure_mono sdiff_subset).trans_lt (by rw [kp_volume_unitCube]; exact ENNReal.one_lt_top)
  have hSrest : |∫ x in unitCube m \ ⋃ p ∈ t, closedBall p.1 p.2, h x| ≤ H * ε := by
    rw [← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const hfinR fun x _ => ?_).trans
      (mul_le_mul_of_nonneg_left hrest hH0)
    rw [Real.norm_eq_abs]; exact hhb x
  have hSabs : |S| ≤ H := by
    rw [hS, ← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const (C := H) hfinC fun x _ => ?_).trans ?_
    · rw [Real.norm_eq_abs]; exact hhb x
    · rw [← hT]
      have : T ≤ 1 := by linarith
      nlinarith
  -- the inner cubes
  set U := ⋃ p ∈ t, ball p.1 ((1 - ε) * p.2) with hUdef
  have hUQ : U ⊆ unitCube m := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    have h1 : (1 - ε) * p.2 ≤ p.2 := by nlinarith [(htP p hp).1]
    exact (htP p hp).2.1 (ball_subset_closedBall (ball_subset_ball h1 hzp))
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion _ fun _ _ => measurableSet_ball
  have hUvol : volume.real U = (1 - ε) ^ m * T := by
    rw [hUdef, measureReal_biUnion_finset (fun p hp q hq hpq => by
      have h1 : (1 - ε) * p.2 ≤ p.2 := by nlinarith [(htP p hp).1]
      have h2 : (1 - ε) * q.2 ≤ q.2 := by nlinarith [(htP q hq).1]
      exact (htdisj hp hq hpq).mono (ball_subset_closedBall.trans (closedBall_subset_closedBall h1))
        (ball_subset_closedBall.trans (closedBall_subset_closedBall h2)))
      (fun _ _ => measurableSet_ball) (fun _ _ => measure_ball_lt_top.ne), hTdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hr := (htP p hp).1
    rw [kp_measureReal_ball _ (mul_pos (by linarith) hr), hV p hp, ← mul_pow]
    ring_nf
  have hQU : volume.real (unitCube m \ U) = 1 - (1 - ε) ^ m * T := by
    rw [measureReal_sdiff hUQ hUm hQfin, hQ1, hUvol]
  have hT1 : 1 - ε ≤ T := by linarith
  have hTle : T ≤ 1 := by linarith
  exact kp_final_estimate hε0 hε1 hH0 hM0 hsumA hSeq hSrest hSabs hT1 hTle hQU

/-! ### Laminates -/

/-- The asymmetric absolute value `max ((1 - λ) τ, -λ τ)`. -/
noncomputable def kpRho (l τ : ℝ) : ℝ := max ((1 - l) * τ) (-l * τ)

/-- The sawtooth with `n` teeth on `[0, 1]`: slope `1 - λ` on `(k/n, (k+λ)/n)`, slope `-λ` on
`((k+λ)/n, (k+1)/n)`, vanishing at the nodes `k/n`. -/
noncomputable def kpSaw (l : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (Finset.range (n + 1)).inf' (by simp) fun k => kpRho l (t - k / n)

theorem kpRho_nonneg {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (τ : ℝ) : 0 ≤ kpRho l τ := by
  rcases le_total 0 τ with h | h
  · exact (mul_nonneg (by linarith) h).trans (le_max_left _ _)
  · exact (mul_nonneg_of_nonpos_of_nonpos (by linarith) h).trans (le_max_right _ _)

theorem kpRho_lipschitz {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) : LipschitzWith 1 (kpRho l) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  unfold kpRho
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [← mul_sub, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - l)]; nlinarith [abs_nonneg (a - b)]
  · rw [← mul_sub, abs_mul, abs_neg, abs_of_pos hl0]; nlinarith [abs_nonneg (a - b)]

theorem kpSaw_nonneg {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (n : ℕ) (t : ℝ) : 0 ≤ kpSaw l n t :=
  Finset.le_inf' _ _ fun _ _ => kpRho_nonneg hl0 hl1 _

theorem kpSaw_lipschitz {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (n : ℕ) :
    LipschitzWith 1 (kpSaw l n) := by
  refine LipschitzWith.of_le_add_mul 1 fun a b => ?_
  obtain ⟨k, hk, hkb⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (n + 1)) (by simp)
    (fun k' => kpRho l (b - k' / n))
  calc kpSaw l n a ≤ kpRho l (a - k / n) := Finset.inf'_le _ hk
    _ ≤ kpRho l (b - k / n) + 1 * dist (a - k / n) (b - k / n) := by
        have := (kpRho_lipschitz hl0 hl1).dist_le_mul (a - k / n) (b - k / n)
        rw [Real.dist_eq (kpRho l _)] at this
        have h2 := le_abs_self (kpRho l (a - k / n) - kpRho l (b - k / n))
        push_cast at this ⊢
        linarith
    _ = kpSaw l n b + 1 * dist a b := by
        rw [kpSaw, ← hkb, Real.dist_eq, Real.dist_eq, sub_sub_sub_cancel_right]

theorem kpSaw_le {l : ℝ} (hl0 : 0 < l) (_hl1 : l < 1) {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : kpSaw l n t ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set k := ⌊(n : ℝ) * t⌋₊ with hk
  have hk1 : (k : ℝ) ≤ n * t := Nat.floor_le (by positivity)
  have hk2 : (n : ℝ) * t < k + 1 := Nat.lt_floor_add_one _
  have hkn : k ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_of_le (by nlinarith)
  refine (Finset.inf'_le _ hkn).trans ?_
  have h0 : 0 ≤ t - k / n := by rw [sub_nonneg, div_le_iff₀ hn']; linarith
  have h1 : t - k / n < 1 / n := by
    rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hn']; linarith
  unfold kpRho
  refine max_le ?_ ?_
  · nlinarith
  · nlinarith

/-- On the rising part of a tooth, the sawtooth is `(1 - λ) (t - k/n)`. -/
theorem kpSaw_eq_rise {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {n k : ℕ} (hn : 0 < n) (hk : k < n)
    {t : ℝ} (ht0 : k / n ≤ t) (ht1 : t ≤ (k + l) / n) :
    kpSaw l n t = (1 - l) * (t - k / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hkm : k ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hval : kpRho l (t - k / n) = (1 - l) * (t - k / n) := by
    unfold kpRho
    have : 0 ≤ t - k / n := by linarith
    exact max_eq_left (by nlinarith)
  refine le_antisymm (hval ▸ Finset.inf'_le _ hkm) (Finset.le_inf' _ _ fun k' hk' => ?_)
  unfold kpRho
  rcases le_or_gt k' k with h | h
  · have : (k' : ℝ) ≤ k := Nat.cast_le.2 h
    have : (k' : ℝ) / n ≤ k / n := div_le_div_of_nonneg_right this hn'.le
    exact le_max_of_le_left (by nlinarith)
  · have h' : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
    have e1 : ((k : ℝ) + 1) / n ≤ k' / n := div_le_div_of_nonneg_right h' hn'.le
    have e2 : t ≤ (k + l) / n := ht1
    refine le_max_of_le_right ?_
    have e3 : (1 - l) * (t - k / n) ≤ l * ((k + 1) / n - t) := by
      have : (k + l) / n = (1 - l) * (k / n) + l * ((k + 1) / n) := by field_simp; ring
      nlinarith
    nlinarith

/-- On the falling part of a tooth, the sawtooth is `λ ((k+1)/n - t)`. -/
theorem kpSaw_eq_fall {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {n k : ℕ} (hn : 0 < n) (hk : k < n)
    {t : ℝ} (ht0 : (k + l) / n ≤ t) (ht1 : t ≤ (k + 1) / n) :
    kpSaw l n t = l * ((k + 1) / n - t) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hkm : k + 1 ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hval : kpRho l (t - ((k + 1 : ℕ) : ℝ) / n) = l * ((k + 1) / n - t) := by
    unfold kpRho
    push_cast
    have : t - (k + 1) / n ≤ 0 := by linarith
    rw [max_eq_right (by nlinarith)]; ring
  refine le_antisymm (hval ▸ Finset.inf'_le _ hkm) (Finset.le_inf' _ _ fun k' hk' => ?_)
  unfold kpRho
  rcases le_or_gt k' k with h | h
  · have : (k' : ℝ) ≤ k := Nat.cast_le.2 h
    have : (k' : ℝ) / n ≤ k / n := div_le_div_of_nonneg_right this hn'.le
    refine le_max_of_le_left ?_
    have e3 : l * ((k + 1) / n - t) ≤ (1 - l) * (t - k / n) := by
      have : (k + l) / n = (1 - l) * (k / n) + l * ((k + 1) / n) := by field_simp; ring
      nlinarith
    nlinarith
  · have h' : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
    have e1 : ((k : ℝ) + 1) / n ≤ k' / n := div_le_div_of_nonneg_right h' hn'.le
    exact le_max_of_le_right (by nlinarith)

/-- The laminate: the sawtooth in the direction `e_j`, in the entry `i`, cut off near the
boundary of the cube by `min` with the distance to the complement. -/
noncomputable def kpLam (i : Fin d) (j : Fin m) (l : ℝ) (n : ℕ) (s : ℝ) :
    (Fin m → ℝ) → Fin d → ℝ :=
  fun x => Pi.single i (min (s * kpSaw l n (x j)) (infDist x (unitCube m)ᶜ))

theorem kpLam_lipschitz (i : Fin d) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (n : ℕ)
    {s : ℝ} (hs : 0 < s) : LipschitzWith (max s.toNNReal 1) (kpLam i j l n s) := by
  have h1 : LipschitzWith s.toNNReal fun x : Fin m → ℝ => s * kpSaw l n (x j) := by
    have := ((kpSaw_lipschitz hl0 hl1 n).comp (LipschitzWith.eval (α := fun _ : Fin m => ℝ) j))
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := this.dist_le_mul x y
    simp only [Function.comp_apply, mul_one, NNReal.coe_one, one_mul] at h
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hs, Real.coe_toNNReal _ hs.le]
    rw [Real.dist_eq] at h
    exact mul_le_mul_of_nonneg_left h hs.le
  have h2 := h1.min (lipschitz_infDist_pt (s := (unitCube m)ᶜ))
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [kpLam, dist_eq_norm, ← Pi.single_sub, Pi.norm_single]
  have := h2.dist_le_mul x y
  rw [Real.dist_eq] at this
  rw [← Real.norm_eq_abs] at this
  exact this.trans (le_of_eq (by rw [dist_eq_norm]))

theorem kpLam_eq_zero (i : Fin d) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (n : ℕ)
    {s : ℝ} (hs : 0 < s) {x : Fin m → ℝ} (hx : x ∉ unitCube m) : kpLam i j l n s x = 0 := by
  simp only [kpLam, infDist_zero_of_mem (show x ∈ (unitCube m)ᶜ from hx),
    min_eq_right (mul_nonneg hs.le (kpSaw_nonneg hl0 hl1 n _)), Pi.single_zero]

/-- The gradient of the affine map `x ↦ a (x_j - b) e_i`. -/
theorem kp_grad_single (i : Fin d) (j : Fin m) (a b : ℝ) (x : Fin m → ℝ) :
    grad (fun y : Fin m → ℝ => (Pi.single i (a * (y j - b)) : Fin d → ℝ)) x =
      Matrix.single i j a := by
  ext i' k
  change fderiv ℝ (fun y : Fin m → ℝ => (Pi.single i (a * (y j - b)) : Fin d → ℝ) i') x
    (Pi.single k 1) = _
  by_cases hi : i' = i
  · subst hi
    have e : (fun y : Fin m → ℝ => (Pi.single i' (a * (y j - b)) : Fin d → ℝ) i') =
        fun y => a * (y j - b) := by ext y; simp
    rw [e]
    have hd : HasFDerivAt (fun y : Fin m → ℝ => a * (y j - b))
        (a • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) x := by
      have := ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin m => ℝ) j x).sub_const b).const_mul a
      simpa using this
    rw [hd.fderiv]
    simp [Matrix.single_apply, Pi.single_apply]
  · have e : (fun y : Fin m → ℝ => (Pi.single i (a * (y j - b)) : Fin d → ℝ) i') = fun _ => 0 := by
      ext y; simp [hi]
    rw [e, fderiv_const_apply]
    simp [Ne.symm hi]

/-- The box `{x : a < x_j < b, 0 < x_l < 1 (l ≠ j)}`. -/
def kpBox (j : Fin m) (a b : ℝ) : Set (Fin m → ℝ) :=
  Set.pi univ fun l => Ioo (if l = j then a else 0) (if l = j then b else 1)

theorem kpBox_subset {j : Fin m} {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    kpBox j a b ⊆ unitCube m := by
  intro x hx l _
  have := hx l (mem_univ l)
  simp only at this
  show x l ∈ Ioo 0 1
  split_ifs at this with h
  · exact ⟨ha.trans_lt this.1, this.2.trans_le hb⟩
  · exact this

theorem kpBox_measureReal (j : Fin m) {a b : ℝ} (hab : a ≤ b) :
    volume.real (kpBox j a b) = b - a := by
  rw [measureReal_def, kpBox, Real.volume_pi_Ioo]
  have : (fun l : Fin m => ENNReal.ofReal ((if l = j then b else 1) - (if l = j then a else 0))) =
      fun l => if l = j then ENNReal.ofReal (b - a) else 1 := by
    ext l; split_ifs <;> simp
  rw [this, Finset.prod_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  rw [ENNReal.toReal_ofReal (by linarith)]

theorem kpBox_disjoint {j : Fin m} {a b a' b' : ℝ} (h : b ≤ a') :
    Disjoint (kpBox j a b) (kpBox j a' b') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := hx j (mem_univ j)
  have h2 := hx' j (mem_univ j)
  simp only [ite_true, mem_Ioo] at h1 h2
  linarith [h1.2, h2.1]

theorem kpBox_mem {j : Fin m} {a b : ℝ} {x : Fin m → ℝ} (hx : x ∈ kpBox j a b) :
    a < x j ∧ x j < b := by
  have := hx j (mem_univ j)
  simpa using this

theorem kpBox_ne_top (j : Fin m) (a b : ℝ) : volume (kpBox j a b) ≠ ⊤ := by
  rw [kpBox, Real.volume_pi_Ioo]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

/-- The rising strips of the laminate, and their total measure. -/
noncomputable def kpStrip1 (j : Fin m) (l : ℝ) (n : ℕ) : Set (Fin m → ℝ) :=
  ⋃ k ∈ Finset.range n, kpBox j (k / n) ((k + l) / n)

/-- The falling strips of the laminate. -/
noncomputable def kpStrip2 (j : Fin m) (l : ℝ) (n : ℕ) : Set (Fin m → ℝ) :=
  ⋃ k ∈ Finset.range n, kpBox j ((k + l) / n) ((k + 1) / n)

theorem kp_strip_facts (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {n : ℕ} (hn : 0 < n) :
    kpStrip1 j l n ⊆ unitCube m ∧ kpStrip2 j l n ⊆ unitCube m ∧
    MeasurableSet (kpStrip1 j l n) ∧ MeasurableSet (kpStrip2 j l n) ∧
    Disjoint (kpStrip1 j l n) (kpStrip2 j l n) ∧
    volume.real (kpStrip1 j l n) = l ∧ volume.real (kpStrip2 j l n) = 1 - l := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hmb : ∀ a b, MeasurableSet (kpBox j a b) := fun a b =>
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hk : ∀ k ∈ Finset.range n, (k : ℝ) + 1 ≤ n := fun k hk => by
    have := Finset.mem_range.1 hk; exact_mod_cast this
  have hdiv : ∀ a b : ℝ, a ≤ b → a / n ≤ b / n := fun a b h => div_le_div_of_nonneg_right h hn'.le
  -- the boxes are ordered along `e_j`
  have hd1 : (Finset.range n : Set ℕ).PairwiseDisjoint fun k => kpBox j (k / n) ((k + l) / n) := by
    intro k _ k' _ hkk'
    rcases lt_or_gt_of_ne hkk' with h | h
    · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
      exact kpBox_disjoint (hdiv _ _ (by linarith))
    · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast h
      exact (kpBox_disjoint (hdiv _ _ (by linarith))).symm
  have hd2 : (Finset.range n : Set ℕ).PairwiseDisjoint fun k =>
      kpBox j ((k + l) / n) ((k + 1) / n) := by
    intro k _ k' _ hkk'
    rcases lt_or_gt_of_ne hkk' with h | h
    · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
      exact kpBox_disjoint (hdiv _ _ (by linarith))
    · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast h
      exact (kpBox_disjoint (hdiv _ _ (by linarith))).symm
  refine ⟨?_, ?_, Finset.measurableSet_biUnion _ fun _ _ => hmb _ _,
    Finset.measurableSet_biUnion _ fun _ _ => hmb _ _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk', hx⟩ := mem_iUnion₂.1 hx
    exact kpBox_subset (div_nonneg (Nat.cast_nonneg k) hn'.le)
      (by rw [div_le_one hn']; linarith [hk k hk']) hx
  · intro x hx
    obtain ⟨k, hk', hx⟩ := mem_iUnion₂.1 hx
    exact kpBox_subset (div_nonneg (by positivity) hn'.le)
      (by rw [div_le_one hn']; linarith [hk k hk']) hx
  · rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨k, -, hx⟩ := mem_iUnion₂.1 hx
    obtain ⟨k', -, hx'⟩ := mem_iUnion₂.1 hx'
    have h1 := kpBox_mem hx
    have h2 := kpBox_mem hx'
    -- `k/n < x_j < (k+l)/n` and `(k'+l)/n < x_j < (k'+1)/n` are incompatible
    rcases le_or_gt k k' with h | h
    · have : (k : ℝ) ≤ k' := by exact_mod_cast h
      have : ((k : ℝ) + l) / n ≤ (k' + l) / n := hdiv _ _ (by linarith)
      linarith [h1.2, h2.1]
    · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast h
      have : ((k' : ℝ) + 1) / n ≤ k / n := hdiv _ _ this
      linarith [h1.1, h2.2]
  · rw [kpStrip1, measureReal_biUnion_finset hd1 (fun _ _ => hmb _ _)
      (fun _ _ => kpBox_ne_top _ _ _)]
    rw [Finset.sum_congr rfl fun k _ => kpBox_measureReal j (hdiv _ _ (by linarith))]
    simp only [add_div, add_sub_cancel_left, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  · rw [kpStrip2, measureReal_biUnion_finset hd2 (fun _ _ => hmb _ _)
      (fun _ _ => kpBox_ne_top _ _ _)]
    rw [Finset.sum_congr rfl fun k _ => kpBox_measureReal j (hdiv _ _ (by linarith))]
    simp only [add_div, add_sub_add_left_eq_sub, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    field_simp

theorem kpBox_isOpen (j : Fin m) (a b : ℝ) : IsOpen (kpBox j a b) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

/-- On a rising strip, away from the boundary layer, the laminate is affine. -/
theorem kpLam_grad_rise (i : Fin d) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {n k : ℕ}
    (hn : 0 < n) (hk : k < n) {s : ℝ} (hs : 0 < s) {x : Fin m → ℝ}
    (hx : x ∈ kpBox j (k / n) ((k + l) / n)) (hxd : s / n < infDist x (unitCube m)ᶜ) :
    grad (kpLam i j l n s) x = Matrix.single i j ((1 - l) * s) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hsub : kpBox j (k / n) ((k + l) / n) ⊆ unitCube m := kpBox_subset
    (div_nonneg (Nat.cast_nonneg k) hn'.le)
    (by rw [div_le_one hn']; have : (k : ℝ) + 1 ≤ n := (by exact_mod_cast hk); linarith)
  have hV : kpBox j (k / n) ((k + l) / n) ∩ {y | s / n < infDist y (unitCube m)ᶜ} ∈ 𝓝 x :=
    ((kpBox_isOpen j _ _).inter (isOpen_lt continuous_const
      (continuous_infDist_pt (unitCube m)ᶜ))).mem_nhds
      ⟨hx, hxd⟩
  have e : kpLam i j l n s =ᶠ[𝓝 x]
      fun y => (Pi.single i (((1 - l) * s) * (y j - k / n)) : Fin d → ℝ) := by
    filter_upwards [hV] with y hy
    have hyQ := hsub hy.1
    have hyj := kpBox_mem hy.1
    have hy01 : 0 ≤ y j ∧ y j ≤ 1 := ⟨(hyQ j (mem_univ j)).1.le, (hyQ j (mem_univ j)).2.le⟩
    have hsaw := kpSaw_eq_rise hl0 hl1 hn hk hyj.1.le hyj.2.le
    have hle := kpSaw_le hl0 hl1 hn hy01.1 hy01.2
    have hmin : min (s * kpSaw l n (y j)) (infDist y (unitCube m)ᶜ) = s * kpSaw l n (y j) := by
      refine min_eq_left (le_of_lt (lt_of_le_of_lt ?_ hy.2))
      calc s * kpSaw l n (y j) ≤ s * (1 / n) := mul_le_mul_of_nonneg_left hle hs.le
        _ = s / n := by ring
    simp only [kpLam]
    rw [hmin, hsaw]
    congr 1
    ring
  rw [kp_grad_congr e, kp_grad_single]

/-- On a falling strip, away from the boundary layer, the laminate is affine. -/
theorem kpLam_grad_fall (i : Fin d) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {n k : ℕ}
    (hn : 0 < n) (hk : k < n) {s : ℝ} (hs : 0 < s) {x : Fin m → ℝ}
    (hx : x ∈ kpBox j ((k + l) / n) ((k + 1) / n)) (hxd : s / n < infDist x (unitCube m)ᶜ) :
    grad (kpLam i j l n s) x = Matrix.single i j (-l * s) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hsub : kpBox j ((k + l) / n) ((k + 1) / n) ⊆ unitCube m := kpBox_subset
    (div_nonneg (by positivity) hn'.le)
    (by rw [div_le_one hn']; have : (k : ℝ) + 1 ≤ n := (by exact_mod_cast hk); linarith)
  have hV : kpBox j ((k + l) / n) ((k + 1) / n) ∩ {y | s / n < infDist y (unitCube m)ᶜ} ∈ 𝓝 x :=
    ((kpBox_isOpen j _ _).inter (isOpen_lt continuous_const
      (continuous_infDist_pt (unitCube m)ᶜ))).mem_nhds
      ⟨hx, hxd⟩
  have e : kpLam i j l n s =ᶠ[𝓝 x]
      fun y => (Pi.single i ((-l * s) * (y j - (k + 1) / n)) : Fin d → ℝ) := by
    filter_upwards [hV] with y hy
    have hyQ := hsub hy.1
    have hyj := kpBox_mem hy.1
    have hy01 : 0 ≤ y j ∧ y j ≤ 1 := ⟨(hyQ j (mem_univ j)).1.le, (hyQ j (mem_univ j)).2.le⟩
    have hsaw := kpSaw_eq_fall hl0 hl1 hn hk hyj.1.le hyj.2.le
    have hle := kpSaw_le hl0 hl1 hn hy01.1 hy01.2
    have hmin : min (s * kpSaw l n (y j)) (infDist y (unitCube m)ᶜ) = s * kpSaw l n (y j) := by
      refine min_eq_left (le_of_lt (lt_of_le_of_lt ?_ hy.2))
      calc s * kpSaw l n (y j) ≤ s * (1 / n) := mul_le_mul_of_nonneg_left hle hs.le
        _ = s / n := by ring
    simp only [kpLam]
    rw [hmin, hsaw]
    congr 1
    ring
  rw [kp_grad_congr e, kp_grad_single]

/-- The boundary layer `{x ∈ Q : dist (x, Qᶜ) ≤ η}` has measure at most `2 m η`. -/
theorem kp_layer_measure (hm : 0 < m) {η : ℝ} (hη : 0 ≤ η) :
    volume.real {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η} ≤ 2 * m * η := by
  have hQ1 : volume.real (unitCube m) = 1 := by
    rw [measureReal_def, kp_volume_unitCube, ENNReal.toReal_one]
  have hsub : {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η} ⊆ unitCube m := fun x hx => hx.1
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [kp_volume_unitCube]; exact ENNReal.one_ne_top
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rcases le_or_gt (1 / 2) η with hη2 | hη2
  · calc volume.real {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η}
        ≤ volume.real (unitCube m) := measureReal_mono hsub hQfin
      _ = 1 := hQ1
      _ ≤ 2 * m * η := by nlinarith
  · set c : Fin m → ℝ := fun _ => 1 / 2
    have hne : ((unitCube m)ᶜ).Nonempty := by
      refine ⟨fun _ => 2, fun h => ?_⟩
      have := (h ⟨0, hm⟩ (mem_univ _)).2
      norm_num at this
    have hsub2 : {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η} ⊆
        unitCube m \ ball c (1 / 2 - η) := by
      intro x hx
      refine ⟨hx.1, fun hxb => ?_⟩
      have hlt : η < 1 / 2 - dist x c := by rw [mem_ball] at hxb; linarith
      have : infDist x (unitCube m)ᶜ < 1 / 2 - dist x c := lt_of_le_of_lt hx.2 hlt
      obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hne).1 this
      apply hy
      rw [kp_unitCube_eq_ball, mem_ball]
      calc dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
        _ < 1 / 2 := by rw [dist_comm]; linarith
    have hballQ : ball c (1 / 2 - η) ⊆ unitCube m := by
      rw [kp_unitCube_eq_ball]; exact ball_subset_ball (by linarith)
    calc volume.real {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η}
        ≤ volume.real (unitCube m \ ball c (1 / 2 - η)) :=
          measureReal_mono hsub2 (ne_top_of_le_ne_top hQfin (measure_mono sdiff_subset))
      _ = 1 - (1 - 2 * η) ^ m := by
          rw [measureReal_sdiff hballQ measurableSet_ball hQfin, hQ1,
            kp_measureReal_ball c (by linarith)]
          ring_nf
      _ ≤ 2 * m * η := by
          have := one_add_le_pow_of_two_add_nonneg (a := -2 * η) (by linarith) m
          have e : (1 : ℝ) + -2 * η = 1 - 2 * η := by ring
          rw [e] at this
          nlinarith

/-- The integral of a function that equals `c₁` on `S₁` and `c₂` on `S₂` away from a set `B`. -/
theorem kp_laminate_integral {h : (Fin m → ℝ) → ℝ} {H c₁ c₂ l : ℝ}
    (hint : IntegrableOn h (unitCube m)) (hb : ∀ x, |h x| ≤ H)
    {S₁ S₂ B : Set (Fin m → ℝ)} (h1 : S₁ ⊆ unitCube m) (h2 : S₂ ⊆ unitCube m)
    (hm1 : MeasurableSet S₁) (hm2 : MeasurableSet S₂) (hmB : MeasurableSet B)
    (hBQ : B ⊆ unitCube m) (hd : Disjoint S₁ S₂) (hv1 : volume.real S₁ = l) (hv2 : volume.real S₂ = 1 - l)
    (he1 : ∀ x ∈ S₁, x ∉ B → h x = c₁) (he2 : ∀ x ∈ S₂, x ∉ B → h x = c₂) :
    ∫ x in unitCube m, h x ≤ l * c₁ + (1 - l) * c₂ + (2 * H + |c₁| + |c₂|) * volume.real B := by
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [kp_volume_unitCube]; exact ENNReal.one_ne_top
  have hQ1 : volume.real (unitCube m) = 1 := by
    rw [measureReal_def, kp_volume_unitCube, ENNReal.toReal_one]
  have hfin1 : volume S₁ ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono h1)
  have hfin2 : volume S₂ ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono h2)
  have h12 : S₁ ∪ S₂ ⊆ unitCube m := union_subset h1 h2
  have hnull : volume (unitCube m \ (S₁ ∪ S₂)) = 0 := by
    have hr : volume.real (unitCube m \ (S₁ ∪ S₂)) = 0 := by
      rw [measureReal_sdiff h12 (hm1.union hm2) hQfin, measureReal_union hd hm2 hfin1 hfin2, hQ1,
        hv1, hv2]
      ring
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hr
    exact hr.resolve_right (ne_top_of_le_ne_top hQfin (measure_mono sdiff_subset))
  have hH : 0 ≤ H := (abs_nonneg _).trans (hb 0)
  rw [← integral_inter_add_sdiff (hm1.union hm2) hint, inter_eq_right.2 h12,
    setIntegral_measure_zero _ hnull, add_zero,
    setIntegral_union hd hm2 (hint.mono_set h1) (hint.mono_set h2)]
  have hB : ∀ (S : Set (Fin m → ℝ)) (c : ℝ), S ⊆ unitCube m → MeasurableSet S →
      (∀ x ∈ S, x ∉ B → h x = c) →
      ∫ x in S, h x ≤ c * volume.real S + (H + |c|) * volume.real B := by
    intro S c hS hmS he
    have hfinS : volume S ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono hS)
    have hg : IntegrableOn (fun x => c + B.indicator (fun _ => H + |c|) x) S :=
      (integrableOn_const hfinS).add ((integrableOn_const (C := H + |c|) hfinS).indicator hmB)
    calc ∫ x in S, h x ≤ ∫ x in S, (c + B.indicator (fun _ => H + |c|) x) := by
          refine setIntegral_mono_on (hint.mono_set hS) hg hmS fun x hx => ?_
          by_cases hxB : x ∈ B
          · rw [indicator_of_mem hxB]
            have := (le_abs_self (h x)).trans (hb x)
            have := neg_abs_le c
            linarith
          · rw [indicator_of_notMem hxB, he x hx hxB, add_zero]
      _ = c * volume.real S + (H + |c|) * volume.real (S ∩ B) := by
          rw [integral_add (integrableOn_const hfinS)
            ((integrableOn_const (C := H + |c|) hfinS).indicator hmB),
            setIntegral_const, setIntegral_indicator hmB, setIntegral_const, smul_eq_mul,
            smul_eq_mul, mul_comm (volume.real S), mul_comm (volume.real (S ∩ B))]
      _ ≤ c * volume.real S + (H + |c|) * volume.real B := by
          have := measureReal_mono (μ := volume) (inter_subset_right (s := S) (t := B))
            (ne_top_of_le_ne_top hQfin (measure_mono hBQ))
          have h0 : 0 ≤ H + |c| := add_nonneg hH (abs_nonneg _)
          nlinarith
  have b1 := hB S₁ c₁ h1 hm1 he1
  have b2 := hB S₂ c₂ h2 hm2 he2
  rw [hv1] at b1
  rw [hv2] at b2
  linarith

theorem kp_trunc_abs_le {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {A : Matrix (Fin d) (Fin m) ℝ}
    {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) {ML : ℝ}
    (hML : ∀ X : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |X i k| ≤ K) → |f (A + X)| ≤ ML) (N : ℝ)
    (x : Fin m → ℝ) : |(max (kpQ f (A + grad φ x)) (N : EReal)).toReal| ≤ max |N| ML := by
  obtain ⟨-, h1, h2⟩ := kp_trunc f (A + grad φ x) N
  have h3 : f (A + grad φ x) ≤ ML := (le_abs_self _).trans (hML _ (kp_grad_abs_le hφ x))
  rw [abs_le]; constructor
  · have := neg_abs_le N; have := le_max_left |N| ML; linarith
  · calc _ ≤ max (f (A + grad φ x)) N := h2
      _ ≤ max ML |N| := max_le_max h3 (le_abs_self N)
      _ = max |N| ML := max_comm _ _

/-- **Laminates.** The convexity inequality of `kpQ f` along a rank-one line `A + t E_{ij}`, with
truncated values: `kpQ f (A) ≤ λ max (kpQ f (A + (1-λ) s E), N) + (1-λ) max (kpQ f (A - λ s E), N)`.
The robust quasiconvexity applied to the laminates `kpLam` with `n` layers, whose gradient is
`(1-λ) s E` on the rising strips (measure `λ`) and `-λ s E` on the falling strips (measure `1-λ`)
off a boundary layer of measure `O(s/n)`. -/
theorem kpQ_laminate {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m) {l s : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    (hs : 0 < s) (N : ℝ) :
    kpQ f A ≤ ((l * (max (kpQ f (A + Matrix.single i j ((1 - l) * s))) (N : EReal)).toReal +
      (1 - l) * (max (kpQ f (A + Matrix.single i j (-l * s))) (N : EReal)).toReal : ℝ) : EReal) := by
  have hm : 0 < m := j.pos
  set c₁ := (max (kpQ f (A + Matrix.single i j ((1 - l) * s))) (N : EReal)).toReal with hc₁
  set c₂ := (max (kpQ f (A + Matrix.single i j (-l * s))) (N : EReal)).toReal with hc₂
  obtain ⟨ML, -, hML⟩ := kp_bdd hf A (max s.toNNReal 1)
  set H := max |N| ML with hH
  have hH0 : 0 ≤ H := (abs_nonneg N).trans (le_max_left _ _)
  refine kp_ereal_le_of_eps (C := (2 * H + |c₁| + |c₂|) * (2 * m * s)) (by positivity)
    fun ε hε0 hε1 => ?_
  set n := ⌈1 / ε⌉₊ + 1 with hndef
  have hn : 0 < n := Nat.succ_pos _
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hnε : 1 / (n : ℝ) ≤ ε := by
    rw [div_le_iff₀ hn']
    have h1 : 1 / ε ≤ ⌈1 / ε⌉₊ := Nat.le_ceil _
    have h2 : (⌈1 / ε⌉₊ : ℝ) + 1 = n := by rw [hndef]; push_cast; ring
    rw [div_le_iff₀ hε0] at h1
    nlinarith
  set φ := kpLam i j l n s with hφdef
  have hφL := kpLam_lipschitz i j hl0 hl1 n hs
  have hadm : KpAdm φ := ⟨⟨_, hφL⟩, fun x hx => kpLam_eq_zero i j hl0 hl1 n hs hx⟩
  have hq := kpQ_quasiconvex_robust hf A hadm N
  refine hq.trans (EReal.coe_le_coe_iff.2 ?_)
  have hb := kp_trunc_abs_le (f := f) (A := A) hφL (by simpa using hML) N
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [kp_volume_unitCube]; exact ENNReal.one_ne_top
  have hhint : IntegrableOn (fun x => (max (kpQ f (A + grad φ x)) (N : EReal)).toReal)
      (unitCube m) :=
    Measure.integrableOn_of_bounded (M := H) hQfin
      (kp_measurable_trunc hf A φ N).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  obtain ⟨hS1Q, hS2Q, hm1, hm2, hd, hv1, hv2⟩ := kp_strip_facts j hl0 hl1 hn
  set B := {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ s / n} with hBdef
  have hmB : MeasurableSet B := kp_measurableSet_unitCube.inter
    (measurableSet_le (continuous_infDist_pt (unitCube m)ᶜ).measurable measurable_const)
  have hBQ : B ⊆ unitCube m := fun x hx => hx.1
  have he1 : ∀ x ∈ kpStrip1 j l n, x ∉ B →
      (max (kpQ f (A + grad φ x)) (N : EReal)).toReal = c₁ := by
    intro x hx hxB
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx
    have hxd : s / n < infDist x (unitCube m)ᶜ := by
      by_contra h
      exact hxB ⟨hS1Q hx, not_lt.1 h⟩
    rw [hφdef, kpLam_grad_rise i j hl0 hl1 hn (Finset.mem_range.1 hk) hs hxk hxd]
  have he2 : ∀ x ∈ kpStrip2 j l n, x ∉ B →
      (max (kpQ f (A + grad φ x)) (N : EReal)).toReal = c₂ := by
    intro x hx hxB
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx
    have hxd : s / n < infDist x (unitCube m)ᶜ := by
      by_contra h
      exact hxB ⟨hS2Q hx, not_lt.1 h⟩
    rw [hφdef, kpLam_grad_fall i j hl0 hl1 hn (Finset.mem_range.1 hk) hs hxk hxd]
  have hint := kp_laminate_integral hhint hb hS1Q hS2Q hm1 hm2 hmB hBQ hd hv1 hv2 he1 he2
  have hBm := kp_layer_measure hm (η := s / n) (by positivity)
  have hC : 0 ≤ 2 * H + |c₁| + |c₂| := by positivity
  have h1 : 2 * (m : ℝ) * (s / n) ≤ 2 * m * s * ε := by
    have : s / n = s * (1 / n) := by ring
    rw [this]
    have hm0 : (0 : ℝ) ≤ 2 * m * s := by positivity
    nlinarith
  calc ∫ x in unitCube m, (max (kpQ f (A + grad φ x)) (N : EReal)).toReal
      ≤ l * c₁ + (1 - l) * c₂ + (2 * H + |c₁| + |c₂|) * volume.real B := hint
    _ ≤ l * c₁ + (1 - l) * c₂ + (2 * H + |c₁| + |c₂|) * (2 * m * s * ε) := by
        gcongr
        exact hBm.trans h1
    _ = l * c₁ + (1 - l) * c₂ + (2 * H + |c₁| + |c₂|) * (2 * m * s) * ε := by ring

/-! ### The dichotomy, convexity along rank-one lines, continuity -/

theorem kp_single_shift (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m) {t₁ t₂ t : ℝ}
    (h : t₁ + t₂ = t) :
    A + Matrix.single i j t₁ + Matrix.single i j t₂ = A + Matrix.single i j t := by
  rw [add_assoc, ← Matrix.single_add, h]

theorem kp_smul_single (i : Fin d) (j : Fin m) (t : ℝ) :
    t • Matrix.single i j (1 : ℝ) = Matrix.single i j t := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

/-- If the convexity bound holds with one endpoint at `-∞`, then `kpQ f (A) = -∞`. -/
theorem kp_bot_of_bound {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {A X Y : Matrix (Fin d) (Fin m) ℝ}
    (hY : kpQ f Y = ⊥)
    (h : ∀ N : ℝ, kpQ f A ≤ ((1 / 2 * (max (kpQ f X) (N : EReal)).toReal +
      (1 - 1 / 2) * (max (kpQ f Y) (N : EReal)).toReal : ℝ) : EReal)) : kpQ f A = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  set N := min (f X) (2 * y - f X - 2) with hN
  have hcX := (kp_trunc f X N).2.2
  have hY' : (max (kpQ f Y) (N : EReal)).toReal = N := by
    rw [hY, max_eq_right bot_le, EReal.toReal_coe]
  have hmax : max (f X) N = f X := max_eq_left (min_le_left _ _)
  have := h N
  rw [hY'] at this
  refine this.trans_lt (EReal.coe_lt_coe_iff.2 ?_)
  have h2 : N ≤ 2 * y - f X - 2 := min_le_right _ _
  rw [hmax] at hcX
  linarith

/-- `-∞` propagates along the lines `B + t E_{ij}`. -/
theorem kpQ_bot_line {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    {B : Matrix (Fin d) (Fin m) ℝ} (hB : kpQ f B = ⊥) (i : Fin d) (j : Fin m) (t : ℝ) :
    kpQ f (B + Matrix.single i j t) = ⊥ := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · refine kp_bot_of_bound (X := B + Matrix.single i j (2 * t)) (Y := B) hB fun N => ?_
    have := kpQ_laminate hf (B + Matrix.single i j t) i j (l := 1 / 2) (s := -2 * t)
      (by norm_num) (by norm_num) (by linarith) N
    rw [kp_single_shift _ _ _ (show t + (1 - 1 / 2) * (-2 * t) = 0 by ring), Matrix.single_zero,
      add_zero, kp_single_shift _ _ _ (show t + -(1 / 2) * (-2 * t) = 2 * t by ring)] at this
    refine this.trans_eq ?_
    congr 1
    ring
  · simpa using hB
  · refine kp_bot_of_bound (X := B + Matrix.single i j (2 * t)) (Y := B) hB fun N => ?_
    have := kpQ_laminate hf (B + Matrix.single i j t) i j (l := 1 / 2) (s := 2 * t)
      (by norm_num) (by norm_num) (by linarith) N
    rw [kp_single_shift _ _ _ (show t + (1 - 1 / 2) * (2 * t) = 2 * t by ring),
      kp_single_shift _ _ _ (show t + -(1 / 2) * (2 * t) = 0 by ring), Matrix.single_zero,
      add_zero] at this
    exact this

/-- **The dichotomy**: if `kpQ f` takes the value `-∞`, it is `-∞` everywhere (changing one entry
at a time along rank-one lines). -/
theorem kpQ_bot_all {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    {B : Matrix (Fin d) (Fin m) ℝ} (hB : kpQ f B = ⊥) (A : Matrix (Fin d) (Fin m) ℝ) :
    kpQ f A = ⊥ := by
  classical
  have key : ∀ S : Finset (Fin d × Fin m),
      kpQ f (B + ∑ p ∈ S, Matrix.single p.1 p.2 ((A - B) p.1 p.2)) = ⊥ := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using hB
    | insert p S hp ih =>
      rw [Finset.sum_insert hp, add_comm (Matrix.single p.1 p.2 _), ← add_assoc]
      exact kpQ_bot_line hf ih _ _ _
  have e : B + ∑ p : Fin d × Fin m, Matrix.single p.1 p.2 ((A - B) p.1 p.2) = A := by
    rw [Fintype.sum_prod_type, ← Matrix.matrix_eq_sum_single (A - B)]
    abel
  have := key Finset.univ
  rwa [e] at this

/-- The real-valued infimum formula, when it is finite. -/
noncomputable def kpG (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  (kpQ f A).toReal

theorem kpQ_eq_kpG {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {A : Matrix (Fin d) (Fin m) ℝ}
    (h : kpQ f A ≠ ⊥) : kpQ f A = (kpG f A : EReal) :=
  (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (kpQ_le A)) h).symm

theorem kp_trunc_eq {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {A : Matrix (Fin d) (Fin m) ℝ}
    (h : kpQ f A ≠ ⊥) {N : ℝ} (hN : N ≤ kpG f A) :
    (max (kpQ f A) (N : EReal)).toReal = kpG f A := by
  rw [kpQ_eq_kpG h, max_eq_left (EReal.coe_le_coe_iff.2 hN), EReal.toReal_coe]

/-- The key inequality of convexity along a rank-one line, in the finite case. -/
theorem kpG_convex_ineq {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, kpQ f A ≠ ⊥) (A₀ : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m)
    {x y a b : ℝ} (hxy : x < y) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    kpG f (A₀ + (a * x + b * y) • Matrix.single i j 1) ≤
      a * kpG f (A₀ + x • Matrix.single i j 1) + b * kpG f (A₀ + y • Matrix.single i j 1) := by
  set N := min (kpG f (A₀ + x • Matrix.single i j 1)) (kpG f (A₀ + y • Matrix.single i j 1))
  have hl := kpQ_laminate hf (A₀ + (a * x + b * y) • Matrix.single i j 1) i j (l := b)
    (s := y - x) hb (by linarith) (by linarith) N
  rw [kp_smul_single, kp_single_shift _ _ _
      (show a * x + b * y + (1 - b) * (y - x) = y by rw [show 1 - b = a by linarith]; linear_combination y * hab),
    kp_single_shift _ _ _ (show a * x + b * y + -b * (y - x) = x by linear_combination x * hab),
    ← kp_smul_single i j y, ← kp_smul_single i j x,
    kp_trunc_eq (hfin _) (min_le_right _ _), kp_trunc_eq (hfin _) (min_le_left _ _)] at hl
  rw [← kp_smul_single i j, kpQ_eq_kpG (hfin _), EReal.coe_le_coe_iff,
    show 1 - b = a by linarith] at hl
  linarith

theorem kpG_convexOn {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, kpQ f A ≠ ⊥) (A₀ : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m) :
    ConvexOn ℝ univ fun t : ℝ => kpG f (A₀ + t • Matrix.single i j 1) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · rcases lt_trichotomy x y with hxy | rfl | hxy
      · exact kpG_convex_ineq hf hfin A₀ i j hxy ha' hb' hab
      · rw [← add_mul, hab, one_mul, ← add_mul, hab, one_mul]
      · have := kpG_convex_ineq hf hfin A₀ i j hxy hb' ha' (by linarith)
        rw [add_comm (a * x), add_comm (a * kpG f _)]
        exact this
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

/-- In the finite case, `kpQ f` is continuous (a separately convex function is locally
Lipschitz). -/
theorem kpG_continuous {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, kpQ f A ≠ ⊥) : Continuous (kpG f) := by
  have hsep : ∀ (y : Fin d → Fin m → ℝ) (i : Fin d) (j : Fin m),
      ConvexOn ℝ univ fun t : ℝ => kpG f (Matrix.of (y + t • kpE i j)) := by
    intro y i j
    simp only [kp_of_add_smul_kpE]
    exact kpG_convexOn hf hfin (Matrix.of y) i j
  exact (kp_locallyLipschitz_of_sep hsep).continuous

/-- In the finite case, `kpQ f` is quasiconvex. -/
theorem kpG_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, kpQ f A ≠ ⊥) : Quasiconvex (kpG f) := by
  intro A φ K hφ hφQ _
  have hc := kpG_continuous hf hfin
  obtain ⟨M, -, hM⟩ := kp_bdd hc A K
  have hq := kpQ_quasiconvex_robust hf A ⟨⟨K, hφ⟩, hφQ⟩ (-M)
  have heq : ∀ x, (max (kpQ f (A + grad φ x)) ((-M : ℝ) : EReal)).toReal = kpG f (A + grad φ x) :=
    fun x => kp_trunc_eq (hfin _) (by
      have := hM _ (kp_grad_abs_le hφ x); have := neg_abs_le (kpG f (A + grad φ x)); linarith)
  simp only [heq] at hq
  rw [kpQ_eq_kpG (hfin A), EReal.coe_le_coe_iff] at hq
  rw [kp_volume_unitCube, ENNReal.toReal_one, one_mul]
  exact hq

/-- **`kpQ f` is below the quasiconvex envelope**: either `kpQ f ≡ -∞`, or it is a continuous
quasiconvex minorant of `f`. -/
theorem kpQ_le_qcEnvelope {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) : kpQ f A ≤ qcEnvelope f A := by
  by_cases hA : kpQ f A = ⊥
  · rw [hA]; exact bot_le
  have hfin : ∀ B, kpQ f B ≠ ⊥ := fun B hB => hA (kpQ_bot_all hf hB A)
  have hc := kpG_continuous hf hfin
  have hadm : LowerSemicontinuous (kpG f) ∧ IsLocallyBounded (kpG f) ∧ Quasiconvex (kpG f) ∧
      ∀ B, kpG f B ≤ f B := by
    refine ⟨hc.lowerSemicontinuous, fun B => ?_, kpG_quasiconvex hf hfin, fun B => ?_⟩
    · refine ⟨kpG f ⁻¹' Metric.ball (kpG f B) 1, hc.continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ one_pos), |kpG f B| + 1, fun C hC => ?_⟩
      rw [mem_preimage, Metric.mem_ball, Real.dist_eq] at hC
      have := abs_sub_abs_le_abs_sub (kpG f C) (kpG f B)
      linarith
    · have := kpQ_le (f := f) B
      rw [kpQ_eq_kpG (hfin B), EReal.coe_le_coe_iff] at this
      exact this
  rw [kpQ_eq_kpG hA]
  exact le_iSup₂ (f := fun g (_ : LowerSemicontinuous g ∧ IsLocallyBounded g ∧ Quasiconvex g ∧
    ∀ B, g B ≤ f B) => (g A : EReal)) (kpG f) hadm

end External.KinderlehrerPedregal
