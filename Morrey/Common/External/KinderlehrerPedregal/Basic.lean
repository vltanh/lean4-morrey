module

public import Morrey.Common.Basic.CalculusOfVariations.Basic
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Tools for Dacorogna's formula: test maps, rescaling, coverings

Elementary facts used in the proof of Dacorogna's formula (`Formula.lean`), on `ℝ^m = Fin m → ℝ`
with its sup norm (so that `Metric.closedBall x r` is the cube `x + [-r, r]^m`):

* `kp_grad_abs_le`, `kp_measurable_comp_grad`: the gradient of a Lipschitz map is bounded and
  measurable;
* `kpScale ψ c s = s ψ (s⁻¹ (x - c))`, a rescaled copy of a test map, with its gradient
  (`kpScale_grad`) and the change of variables (`kp_integral_comp_affine`);
* `kp_exists_finite_cover`: the Besicovitch covering theorem in the form used to glue test maps:
  finitely many disjoint admissible cubes cover a set of finite measure up to `ε`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace External.KinderlehrerPedregal

open CalculusOfVariations

variable {d m : ℕ}

/-- The entries of the gradient of a `K`-Lipschitz map are bounded by `K`. -/
theorem kp_grad_abs_le {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (x : Fin m → ℝ) (i : Fin d) (k : Fin m) : |grad φ x i k| ≤ K := by
  have hφi : LipschitzWith K (fun y => φ y i) := by
    have := (LipschitzWith.eval (α := fun _ : Fin d => ℝ) i).comp hφ
    rw [one_mul] at this
    exact this
  change |fderiv ℝ (fun y => φ y i) x (Pi.single k 1)| ≤ K
  calc |fderiv ℝ (fun y => φ y i) x (Pi.single k 1)|
      ≤ ‖fderiv ℝ (fun y => φ y i) x‖ * ‖(Pi.single k 1 : Fin m → ℝ)‖ :=
        (fderiv ℝ (fun y => φ y i) x).le_opNorm _
    _ ≤ K * 1 := by
        gcongr
        · exact norm_fderiv_le_of_lipschitz ℝ hφi
        · simp [Pi.norm_single]
    _ = K := mul_one _

/-- The gradient, as a map to `Fin d → Fin m → ℝ`, is measurable. -/
theorem kp_measurable_grad (φ : (Fin m → ℝ) → Fin d → ℝ) :
    Measurable (fun x i k => grad φ x i k : (Fin m → ℝ) → Fin d → Fin m → ℝ) :=
  Measurable.of_eval fun i => Measurable.of_eval fun k =>
    measurable_fderiv_apply_const ℝ (fun y => φ y i) (Pi.single k 1)

/-- `x ↦ F (A + ∇φ x)` is measurable for a measurable `F` on `Fin d → Fin m → ℝ`. -/
theorem kp_measurable_comp_grad {F : (Fin d → Fin m → ℝ) → ℝ} (hF : Measurable F)
    (A : Matrix (Fin d) (Fin m) ℝ) (φ : (Fin m → ℝ) → Fin d → ℝ) :
    Measurable fun x => F (fun i k => A i k + grad φ x i k) :=
  hF.comp (Measurable.of_eval fun i => Measurable.of_eval fun k =>
    measurable_const.add ((measurable_pi_iff.1 ((measurable_pi_iff.1 (kp_measurable_grad φ)) i)) k))

/-- A continuous function of a matrix is continuous on `Fin d → Fin m → ℝ`. -/
theorem kp_continuous_of {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) :
    Continuous fun X : Fin d → Fin m → ℝ => f (Matrix.of X) := hf

/-- The gradient at `x` only depends on the map near `x`. -/
theorem kp_grad_congr {φ ψ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ} (h : φ =ᶠ[𝓝 x] ψ) :
    grad φ x = grad ψ x := by
  ext i k
  change fderiv ℝ (fun y => φ y i) x (Pi.single k 1) = fderiv ℝ (fun y => ψ y i) x (Pi.single k 1)
  have := (h.fun_comp (fun v : Fin d → ℝ => v i)).fderiv_eq (𝕜 := ℝ)
  exact congrArg (fun L => L (Pi.single k 1)) this

/-- The gradient of a map vanishing near `x` vanishes at `x`. -/
theorem kp_grad_eq_zero {φ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ}
    (h : φ =ᶠ[𝓝 x] fun _ => 0) : grad φ x = 0 := by
  rw [kp_grad_congr h]
  ext i k
  change fderiv ℝ (fun _ => (0 : Fin d → ℝ) i) x (Pi.single k 1) = 0
  simp

/-- The gradient of the sum of two maps, at a point where both are differentiable. -/
theorem kp_grad_add {φ ψ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ}
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    grad (φ + ψ) x = grad φ x + grad ψ x := by
  ext i k
  change fderiv ℝ (fun y => φ y i + ψ y i) x (Pi.single k 1) =
    fderiv ℝ (fun y => φ y i) x (Pi.single k 1) + fderiv ℝ (fun y => ψ y i) x (Pi.single k 1)
  have h1 : DifferentiableAt ℝ (fun y => φ y i) x :=
    (differentiableAt_pi.1 hφ) i
  have h2 : DifferentiableAt ℝ (fun y => ψ y i) x :=
    (differentiableAt_pi.1 hψ) i
  rw [fderiv_fun_add h1 h2]
  rfl

/-! ### Rescaled test maps -/

/-- The rescaled copy `x ↦ s ψ (s⁻¹ (x - c))` of `ψ`, supported in `c + s · supp ψ`. -/
noncomputable def kpScale (ψ : (Fin m → ℝ) → Fin d → ℝ) (c : Fin m → ℝ) (s : ℝ) :
    (Fin m → ℝ) → Fin d → ℝ :=
  fun x => s • ψ (s⁻¹ • (x - c))

theorem kpScale_lipschitz {ψ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hψ : LipschitzWith K ψ)
    (c : Fin m → ℝ) {s : ℝ} (hs : 0 < s) : LipschitzWith K (kpScale ψ c s) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [kpScale, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hs.le]
  have := hψ.dist_le_mul (s⁻¹ • (x - c)) (s⁻¹ • (y - c))
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_pos.2 hs).le,
    sub_sub_sub_cancel_right] at this
  calc s * ‖ψ (s⁻¹ • (x - c)) - ψ (s⁻¹ • (y - c))‖ ≤ s * (K * (s⁻¹ * ‖x - y‖)) :=
        mul_le_mul_of_nonneg_left this hs.le
    _ = K * ‖x - y‖ := by field_simp

theorem kpScale_grad (ψ : (Fin m → ℝ) → Fin d → ℝ) (c : Fin m → ℝ) {s : ℝ} (hs : s ≠ 0)
    (x : Fin m → ℝ) : grad (kpScale ψ c s) x = grad ψ (s⁻¹ • (x - c)) := by
  ext i k
  change fderiv ℝ (fun y => (s • ψ (s⁻¹ • (y - c))) i) x (Pi.single k 1) =
    fderiv ℝ (fun y => ψ y i) (s⁻¹ • (x - c)) (Pi.single k 1)
  have e : fderiv ℝ (fun y => (s • ψ (s⁻¹ • (y - c))) i) x =
      s • (s⁻¹ • fderiv ℝ (fun w => ψ w i) (s⁻¹ • (x - c))) := by
    calc fderiv ℝ (fun y => (s • ψ (s⁻¹ • (y - c))) i) x
        = fderiv ℝ (s • fun y => ψ (s⁻¹ • (y + -c)) i) x := by
          congr 1
      _ = s • fderiv ℝ (fun z => ψ (s⁻¹ • z) i) (x + -c) := by
          rw [fderiv_const_smul_field, Pi.smul_apply,
            fderiv_comp_add_right (f := fun z => ψ (s⁻¹ • z) i)]
      _ = s • (s⁻¹ • fderiv ℝ (fun w => ψ w i) (s⁻¹ • (x - c))) := by
          rw [fderiv_comp_smul (f := fun w => ψ w i), sub_eq_add_neg]
  rw [e]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem kpScale_eq_zero {ψ : (Fin m → ℝ) → Fin d → ℝ} {S : Set (Fin m → ℝ)}
    (hψ : ∀ y ∉ S, ψ y = 0) (c : Fin m → ℝ) (s : ℝ) {x : Fin m → ℝ}
    (hx : s⁻¹ • (x - c) ∉ S) : kpScale ψ c s x = 0 := by
  simp [kpScale, hψ _ hx]

/-- The change of variables `y = s⁻¹ (x - c)`. -/
theorem kp_integral_comp_affine (G : (Fin m → ℝ) → ℝ) (c : Fin m → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x, G (s⁻¹ • (x - c)) = s ^ m * ∫ y, G y := by
  rw [integral_sub_right_eq_self (fun x => G (s⁻¹ • x)) c, Measure.integral_comp_smul,
    Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (pow_pos hs m), smul_eq_mul]

/-! ### Finite disjoint coverings by cubes -/

/-- The Besicovitch covering theorem, finite form: if every point of `s` (up to a null set) has
arbitrarily small admissible radii, then finitely many disjoint admissible closed cubes cover `s`
up to measure `ε`. -/
theorem kp_exists_finite_cover {s : Set (Fin m → ℝ)} (hs : volume s ≠ ⊤)
    (hsm : MeasurableSet s) (P : (Fin m → ℝ) → ℝ → Prop)
    (hP : ∀ᵐ x, x ∈ s → ∀ δ > 0, ∃ r ∈ Ioo 0 δ, P x r) {ε : ENNReal} (hε : 0 < ε) :
    ∃ t : Finset ((Fin m → ℝ) × ℝ), (∀ p ∈ t, 0 < p.2 ∧ P p.1 p.2) ∧
      (t : Set ((Fin m → ℝ) × ℝ)).PairwiseDisjoint (fun p => closedBall p.1 p.2) ∧
      volume (s \ ⋃ p ∈ t, closedBall p.1 p.2) < ε := by
  classical
  -- the good points
  set s' := {x ∈ s | ∀ δ > 0, ∃ r ∈ Ioo 0 δ, P x r} with hs'
  have hss' : volume (s \ s') = 0 := by
    rw [ae_iff] at hP
    refine measure_mono_null (fun x hx => ?_) hP
    intro h
    exact hx.2 ⟨hx.1, h hx.1⟩
  obtain ⟨t, r, htc, hts, htr, htμ, htd⟩ := Besicovitch.exists_disjoint_closedBall_covering_ae
    volume (fun x => {r | P x r}) s' (fun x hx δ hδ => by
      obtain ⟨r, hr, hPr⟩ := hx.2 δ hδ
      exact ⟨r, hPr, hr⟩) (fun _ => 1) (fun _ _ => one_pos)
  -- the whole countable family covers `s` up to a null set
  have hnull : volume (s \ ⋃ x ∈ t, closedBall x (r x)) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hss' htμ)
    by_cases h : x ∈ s'
    · exact Or.inr ⟨h, hx.2⟩
    · exact Or.inl ⟨hx.1, h⟩
  -- exhaust the countable family by finite subfamilies
  rcases t.eq_empty_or_nonempty with rfl | hne
  · refine ⟨∅, by simp, by simp, ?_⟩
    simpa using (show volume s = 0 by simpa using hnull) ▸ hε
  obtain ⟨e, he⟩ := htc.exists_eq_range hne
  let S : ℕ → Set (Fin m → ℝ) := fun n => s \ ⋃ k ∈ Finset.range n, closedBall (e k) (r (e k))
  have hanti : Antitone S := by
    intro a b hab x hx
    refine ⟨hx.1, fun h => hx.2 ?_⟩
    simp only [mem_iUnion, Finset.mem_range] at h ⊢
    obtain ⟨k, hk, hxk⟩ := h
    exact ⟨k, lt_of_lt_of_le hk hab, hxk⟩
  have hmeas : ∀ n, NullMeasurableSet (S n) volume := fun n =>
    (hsm.diff (Finset.measurableSet_biUnion _ fun k _ => isClosed_closedBall.measurableSet))
      |>.nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, by
    exact ne_top_of_le_ne_top hs (measure_mono sdiff_subset)⟩
  have hinter : (⋂ n, S n) = s \ ⋃ x ∈ t, closedBall x (r x) := by
    ext x
    simp only [S, mem_iInter]
    constructor
    · intro h
      refine ⟨(h 0).1, fun hx => ?_⟩
      simp only [mem_iUnion] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      rw [he] at hy
      obtain ⟨k, rfl⟩ := hy
      exact (h (k + 1)).2 (mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_self k), hxy⟩)
    · rintro ⟨hxs, h⟩ n
      refine ⟨hxs, fun hx => h ?_⟩
      obtain ⟨k, -, hxk⟩ := mem_iUnion₂.1 hx
      exact mem_iUnion₂.2 ⟨e k, he ▸ mem_range_self k, hxk⟩
  rw [hinter, hnull] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨(Finset.range n).image fun k => (e k, r (e k)), ?_, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨k, -, rfl⟩ := hp
    have hk : e k ∈ t := he ▸ mem_range_self k
    exact ⟨(htr _ hk).2.1, (htr _ hk).1⟩
  · intro p hp q hq hpq
    simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio] at hp hq
    obtain ⟨k, -, rfl⟩ := hp
    obtain ⟨l, -, rfl⟩ := hq
    have hk : e k ∈ t := he ▸ mem_range_self k
    have hl : e l ∈ t := he ▸ mem_range_self l
    have hne : e k ≠ e l := fun h => hpq (by simp [h])
    exact htd hk hl hne
  · have e : s \ ⋃ p ∈ (Finset.range n).image (fun k => (e k, r (e k))), closedBall p.1 p.2 =
        S n := by
      ext x
      simp [S]
    rw [e]
    exact hn

end External.KinderlehrerPedregal
