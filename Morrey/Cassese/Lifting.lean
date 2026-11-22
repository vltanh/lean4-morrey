module

public import Morrey.Cassese.Bridges

/-!
# Lifting integrands and test maps to larger matrices

The upper left `d' × m'` block of a `d × m` matrix (`lift_trunc`), and the lifting of an
integrand `f` on `ℝ^{d'×m'}` to `f ∘ lift_trunc` on `ℝ^{d×m}`: it stays rank-one convex
(`lift_rankOneConvex_comp`), an integrand (`lift_isIntegrand_comp`) and `p`-homogeneous
(`lift_isPHomogeneous_comp`), and a witness against quasiconvexity of `f` lifts to one for
`f ∘ lift_trunc` (`lift_quasiconvexAt_of_comp_trunc`). The witness lifts through the periodic form
of quasiconvexity (Lemma 2.2, `External.Rindler.quasiconvexAtOn_iff_periodic`): a periodic test map
`φ` of `ℝ^{m'}` lifts to the periodic test map `x ↦ (φ (x₁, …, x_{m'}), 0, …, 0)` of `ℝ^m`, whose
gradient has `∇φ` as upper left block (`lift_trunc_jac`), and the integrals over the unit cubes
agree by Fubini (`lift_measurePreserving_projX`).

The paper uses this step in the claims of the introduction (the monotonicity of Morrey's problem in
the dimensions, lines 105–107), in the proof of Theorem 1.2 (lines 1154–1156) and in Corollary 5.2;
`Introduction.lean`, `TwoByM.lean` and `NonLocality.lean` take it from here. Helpers are prefixed
`lift_`.
-/

@[expose] public section

open scoped Matrix

namespace Cassese

open MeasureTheory

section Lifting

variable {d m d' m' : ℕ}

/-- The upper left `d' × m'` block of a `d × m` matrix. -/
def lift_trunc (hd : d' ≤ d) (hm : m' ≤ m) (A : Matrix (Fin d) (Fin m) ℝ) :
    Matrix (Fin d') (Fin m') ℝ :=
  A.submatrix (Fin.castLE hd) (Fin.castLE hm)

/-- The `d × m` matrix with upper left block `A` and zeros elsewhere. -/
def lift_pad (_hd : d' ≤ d) (_hm : m' ≤ m) (A : Matrix (Fin d') (Fin m') ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  Matrix.of fun i j => if h : i.val < d' ∧ j.val < m' then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

theorem lift_trunc_pad (hd : d' ≤ d) (hm : m' ≤ m) (A : Matrix (Fin d') (Fin m') ℝ) :
    lift_trunc hd hm (lift_pad hd hm A) = A := by
  ext i j
  simp [lift_trunc, lift_pad, i.2, j.2]

theorem lift_trunc_add (hd : d' ≤ d) (hm : m' ≤ m) (A B : Matrix (Fin d) (Fin m) ℝ) :
    lift_trunc hd hm (A + B) = lift_trunc hd hm A + lift_trunc hd hm B := by
  ext i j
  simp [lift_trunc]

theorem lift_trunc_sub (hd : d' ≤ d) (hm : m' ≤ m) (A B : Matrix (Fin d) (Fin m) ℝ) :
    lift_trunc hd hm (A - B) = lift_trunc hd hm A - lift_trunc hd hm B := by
  ext i j
  simp [lift_trunc]

theorem lift_trunc_smul (hd : d' ≤ d) (hm : m' ≤ m) (t : ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    lift_trunc hd hm (t • A) = t • lift_trunc hd hm A := by
  ext i j
  simp [lift_trunc]

theorem lift_trunc_zero (hd : d' ≤ d) (hm : m' ≤ m) :
    lift_trunc hd hm (0 : Matrix (Fin d) (Fin m) ℝ) = 0 := by
  ext i j
  simp [lift_trunc]

theorem lift_continuous_trunc (hd : d' ≤ d) (hm : m' ≤ m) : Continuous (lift_trunc hd hm) :=
  continuous_id.matrix_submatrix (Fin.castLE hd) (Fin.castLE hm)

/-- The block map sends rank-one lines to rank-one lines or to points: `f ∘ lift_trunc` is
rank-one convex with `f`. -/
theorem lift_rankOneConvex_comp (hd : d' ≤ d) (hm : m' ≤ m) {f : Matrix (Fin d') (Fin m') ℝ → ℝ}
    (hf : RankOneConvex f) : RankOneConvex fun A => f (lift_trunc hd hm A) := by
  intro A B hAB
  simp_rw [lift_trunc_add, lift_trunc_smul]
  have hle : (lift_trunc hd hm A - lift_trunc hd hm B).rank ≤ 1 := by
    rw [← lift_trunc_sub, ← hAB]
    exact Matrix.rank_submatrix_le _ _ _
  by_cases h1 : (lift_trunc hd hm A - lift_trunc hd hm B).rank = 1
  · exact hf _ _ h1
  · have h0 := eq_zero_of_rank_eq_zero (show (lift_trunc hd hm A -
      lift_trunc hd hm B).rank = 0 by omega)
    rw [sub_eq_zero] at h0
    simp only [h0, ← add_smul, add_sub_cancel, one_smul]
    exact convexOn_const _ (convex_Icc 0 1)

theorem lift_isIntegrand_comp (hd : d' ≤ d) (hm : m' ≤ m) {f : Matrix (Fin d') (Fin m') ℝ → ℝ}
    (hf : IsIntegrand f) : IsIntegrand fun A => f (lift_trunc hd hm A) := by
  refine ⟨hf.1.comp (lift_continuous_trunc hd hm), fun A => ?_⟩
  obtain ⟨U, hU, C, hC⟩ := hf.2 (lift_trunc hd hm A)
  exact ⟨lift_trunc hd hm ⁻¹' U, (lift_continuous_trunc hd hm).continuousAt.preimage_mem_nhds hU,
    C, fun B hB => hC _ hB⟩

theorem lift_isPHomogeneous_comp (hd : d' ≤ d) (hm : m' ≤ m) {p : ℝ}
    {f : Matrix (Fin d') (Fin m') ℝ → ℝ} (hf : IsPHomogeneous p f) :
    IsPHomogeneous p fun A => f (lift_trunc hd hm A) := by
  intro t A
  show f (lift_trunc hd hm (t • A)) = |t| ^ p * f (lift_trunc hd hm A)
  rw [lift_trunc_smul]
  exact hf t _

/-- `(x₁, …, x_m) ↦ (x₁, …, x_{m'})`. -/
noncomputable def lift_projX (hm : m' ≤ m) : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.castLE hm j)

/-- Padding a vector of `ℝ^{d'}` with zeros to a vector of `ℝ^d`. -/
noncomputable def lift_padV (_hd : d' ≤ d) : (Fin d' → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    if h : i.val < d' then ContinuousLinearMap.proj ⟨i, h⟩ else 0

theorem lift_projX_apply (hm : m' ≤ m) (x : Fin m → ℝ) (j : Fin m') :
    lift_projX hm x j = x (Fin.castLE hm j) := rfl

theorem lift_padV_castLE (hd : d' ≤ d) (v : Fin d' → ℝ) (i : Fin d') :
    lift_padV hd v (Fin.castLE hd i) = v i := by
  simp [lift_padV, i.2]

theorem lift_projX_padV (hm : m' ≤ m) (z : Fin m' → ℝ) : lift_projX hm (lift_padV hm z) = z := by
  funext j
  rw [lift_projX_apply, lift_padV_castLE]

theorem lift_projX_single (hm : m' ≤ m) (k : Fin m') :
    lift_projX hm (Pi.single (Fin.castLE hm k) 1) = Pi.single k 1 := by
  funext j
  simp only [lift_projX_apply, Pi.single_apply, (Fin.castLE_injective hm).eq_iff]

/-- `g ∘ lift_projX` is differentiable at `x` exactly when `g` is differentiable at the
projection of `x` (the projection has an affine right inverse through `x`). -/
theorem lift_differentiableAt_comp_projX_iff (hm : m' ≤ m) {g : (Fin m' → ℝ) → ℝ}
    {x : Fin m → ℝ} :
    DifferentiableAt ℝ (g ∘ lift_projX hm) x ↔ DifferentiableAt ℝ g (lift_projX hm x) := by
  refine ⟨fun h => ?_, fun h => h.comp x (lift_projX hm).differentiableAt⟩
  set E : (Fin m' → ℝ) → (Fin m → ℝ) := fun z => x + lift_padV hm (z - lift_projX hm x)
  have hE : ∀ z, lift_projX hm (E z) = z := fun z => by
    simp only [E, map_add, lift_projX_padV, add_sub_cancel]
  have hEx : E (lift_projX hm x) = x := by simp [E]
  have hdE : DifferentiableAt ℝ E (lift_projX hm x) :=
    (differentiableAt_const x).add ((lift_padV hm).differentiableAt.comp _
      (differentiableAt_id.sub_const _))
  have h' : DifferentiableAt ℝ (g ∘ lift_projX hm) (E (lift_projX hm x)) := by rwa [hEx]
  have := h'.comp (lift_projX hm x) hdE
  convert this using 1
  funext z
  simp only [Function.comp, hE]

theorem lift_fderiv_comp_projX (hm : m' ≤ m) (g : (Fin m' → ℝ) → ℝ) (x v : Fin m → ℝ) :
    fderiv ℝ (g ∘ lift_projX hm) x v = fderiv ℝ g (lift_projX hm x) (lift_projX hm v) := by
  by_cases h : DifferentiableAt ℝ g (lift_projX hm x)
  · rw [fderiv_comp x h (lift_projX hm).differentiableAt, ContinuousLinearMap.fderiv]
    rfl
  · rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt
      (mt (lift_differentiableAt_comp_projX_iff hm).1 h)]
    rfl

/-- The upper left block of the gradient of the lifted map is the gradient of the map. -/
theorem lift_trunc_jac (hd : d' ≤ d) (hm : m' ≤ m) (φ : (Fin m' → ℝ) → Fin d' → ℝ)
    (x : Fin m → ℝ) :
    lift_trunc hd hm (jac (fun y => lift_padV hd (φ (lift_projX hm y))) x) =
      jac φ (lift_projX hm x) := by
  ext i k
  have hfun : (fun y => lift_padV hd (φ (lift_projX hm y)) (Fin.castLE hd i)) =
      (fun z => φ z i) ∘ lift_projX hm := by
    funext y
    simp [lift_padV_castLE]
  simp only [lift_trunc, jac, Matrix.submatrix_apply, Matrix.of_apply]
  rw [hfun, lift_fderiv_comp_projX, lift_projX_single]

/-- The image of the uniform measure on `(0, 1)^m` under `(x₁, …, x_m) ↦ (x₁, …, x_{m'})` is the
uniform measure on `(0, 1)^{m'}` (Fubini: the other factor has volume `1`). -/
theorem lift_map_projX (hm : m' ≤ m) :
    (volume.restrict (unitCube m)).map (lift_projX hm) = volume.restrict (unitCube m') := by
  have h2 : volume.restrict (unitCube m') =
      Measure.pi fun _ : Fin m' => volume.restrict (Set.Ioo (0 : ℝ) 1) := by
    rw [unitCube, volume_pi, Measure.restrict_pi_pi]
  rw [h2]
  refine (Measure.pi_eq (μ := fun _ : Fin m' => volume.restrict (Set.Ioo (0 : ℝ) 1))
    fun s hs => ?_).symm
  have hmeas := MeasurableSet.univ_pi hs
  rw [Measure.map_apply (lift_projX hm).continuous.measurable hmeas,
    Measure.restrict_apply ((lift_projX hm).continuous.measurable hmeas)]
  simp_rw [Measure.restrict_apply (hs _)]
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hset : (lift_projX hm ⁻¹' Set.univ.pi s) ∩ unitCube (m' + l) =
      Set.univ.pi fun i : Fin (m' + l) =>
        if h : (i : ℕ) < m' then s ⟨i, h⟩ ∩ Set.Ioo 0 1 else Set.Ioo 0 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      lift_projX_apply, unitCube]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases hi : (i : ℕ) < m'
      · simp only [hi, ↓reduceDIte]
        refine ⟨?_, h2 i⟩
        have := h1 ⟨i, hi⟩
        have hc : Fin.castLE hm ⟨i, hi⟩ = i := Fin.ext rfl
        rwa [hc] at this
      · simp only [hi, ↓reduceDIte]; exact h2 i
    · intro h
      refine ⟨fun j => ?_, fun i => ?_⟩
      · have := h (Fin.castLE hm j)
        simp only [Fin.val_castLE, j.2, ↓reduceDIte] at this
        exact this.1
      · have := h i
        by_cases hi : (i : ℕ) < m'
        · simp only [hi, ↓reduceDIte] at this; exact this.2
        · simp only [hi, ↓reduceDIte] at this; exact this
  rw [hset, volume_pi_pi, Fin.prod_univ_add]
  simp

theorem lift_measurePreserving_projX (hm : m' ≤ m) :
    MeasurePreserving (lift_projX hm) (volume.restrict (unitCube m))
      (volume.restrict (unitCube m')) :=
  ⟨(lift_projX hm).continuous.measurable, lift_map_projX hm⟩

/-- Lifting a witness (lines 105–107, 1154–1156): if `f ∘ lift_trunc` is quasiconvex at `A`,
then `f` is quasiconvex at the upper left block of `A`. Through the periodic form of
quasiconvexity (Lemma 2.2, `External.Rindler.quasiconvexAtOn_iff_periodic`, with the bridge
`cov_quasiconvexAtOn_unitCube_iff`): a periodic test map `φ` of `ℝ^{m'}` lifts to the periodic
test map `x ↦ (φ (x₁, …, x_{m'}), 0, …, 0)` of `ℝ^m`, and the integrals over the unit cubes agree
by Fubini. -/
theorem lift_quasiconvexAt_of_comp_trunc (hd : d' ≤ d) (hm : m' ≤ m)
    {f : Matrix (Fin d') (Fin m') ℝ → ℝ} (hf : IsIntegrand f) {A : Matrix (Fin d) (Fin m) ℝ}
    (h : QuasiconvexAt (fun B => f (lift_trunc hd hm B)) A) :
    QuasiconvexAt f (lift_trunc hd hm A) := by
  have hF := lift_isIntegrand_comp hd hm hf
  have hper := (External.Rindler.quasiconvexAtOn_iff_periodic hF.1 hF.2 A).1
    ((cov_quasiconvexAtOn_unitCube_iff _ A).2 h)
  refine (cov_quasiconvexAtOn_unitCube_iff f _).1
    ((External.Rindler.quasiconvexAtOn_iff_periodic hf.1 hf.2 _).2 ?_)
  intro φ K hK hφper hint
  set ψ : (Fin m → ℝ) → Fin d → ℝ := fun y => lift_padV hd (φ (lift_projX hm y)) with hψ
  have hψK : LipschitzWith (‖lift_padV hd‖₊ * K * ‖lift_projX hm‖₊) ψ :=
    ((lift_padV hd).lipschitzWith.comp hK).comp (lift_projX hm).lipschitzWith
  have hψper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), ψ (x + fun i => (z i : ℝ)) = ψ x := by
    intro x z
    have hz : lift_projX hm (fun i => (z i : ℝ)) = fun j => ((z (Fin.castLE hm j) : ℤ) : ℝ) := rfl
    simp only [hψ, map_add, hz, hφper]
  set G : (Fin m' → ℝ) → ℝ := fun y => f (lift_trunc hd hm A + CalculusOfVariations.grad φ y)
  have hG : (fun x => f (lift_trunc hd hm (A + CalculusOfVariations.grad ψ x))) =
      G ∘ lift_projX hm := by
    funext x
    simp only [G, Function.comp, lift_trunc_add, grad_eq, hψ, lift_trunc_jac]
  have hmp := lift_measurePreserving_projX hm
  have hGm : AEStronglyMeasurable G (volume.restrict (unitCube m')) := hint.aestronglyMeasurable
  have hint' : IntegrableOn (fun x => f (lift_trunc hd hm (A + CalculusOfVariations.grad ψ x)))
      (CalculusOfVariations.unitCube m) := by
    rw [hG]
    exact (hmp.integrable_comp hGm).2 hint
  have key := hper ψ _ hψK hψper hint'
  rw [hG] at key
  have heq : ∫ x in CalculusOfVariations.unitCube m, (G ∘ lift_projX hm) x =
      ∫ y in CalculusOfVariations.unitCube m', G y := by
    change ∫ x, G (lift_projX hm x) ∂(volume.restrict (unitCube m)) =
      ∫ y, G y ∂(volume.restrict (unitCube m'))
    rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hGm), hmp.map_eq]
  rw [heq] at key
  exact key

end Lifting

end Cassese
