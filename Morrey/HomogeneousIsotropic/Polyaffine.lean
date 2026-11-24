module

public import Morrey.HomogeneousIsotropic.Defs
public import CalculusOfVariations.Minors.Characterization
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Polyaffine supports: polyconvexity and quasiconvexity

A polyaffine function `P (A) = k + ⟨K, A⟩ + c det A` on `ℝ^{2×2}` is a null Lagrangian
(`setIntegral_polyaffine_add_grad`), since the entries and the determinant are minors. Hence:

* a polyaffine support of `F` at `A₀` gives quasiconvexity of `F` at `A₀`
  (`HasPolyaffineSupportAt.quasiconvexAtOn`), and polyaffine supports at every matrix give
  quasiconvexity (`quasiconvex_of_hasPolyaffineSupportAt`) and polyconvexity
  (`polyconvex_of_hasPolyaffineSupportAt`: `F (A) = g (A, det A)` with `g` the supremum of the
  affine functions `(X, d) ↦ k + ⟨K, X⟩ + c d` whose polyaffine function lies below `F`);
* conversely, a polyconvex function has a polyaffine support at every matrix
  (`Polyconvex.hasPolyaffineSupportAt`: a convex function on a finite-dimensional space has an
  affine support at every point, `exists_affine_support_of_convexOn`), so that polyconvex
  functions are quasiconvex (`Polyconvex.quasiconvex`), continuous and rank-one convex
  (`Polyconvex.rankOneConvex`);
* a continuous minorant that is quasiconvex at `A₀` and touches `F` there gives quasiconvexity of
  `F` at `A₀` (`quasiconvexAtOn_of_le_of_eq`);
* nonnegative combinations of continuous quasiconvex functions are quasiconvex
  (`quasiconvex_add_mul`), and quasiconvexity is invariant under `A ↦ J A`, `J = diag (1, −1)`
  (`quasiconvex_comp_reflection_mul`).
-/

@[expose] public section

namespace HomogeneousIsotropic

open CalculusOfVariations MeasureTheory

/-- The unit square is bounded. -/
theorem isBounded_unitCube_two : Bornology.IsBounded (unitCube 2) :=
  (nl_isCompact_Icc 2).isBounded.subset (nl_unitCube_subset 2)

/-- The unit square has finite measure. -/
theorem volume_unitCube_two_ne_top : volume (unitCube 2) ≠ ⊤ :=
  isBounded_unitCube_two.measure_lt_top.ne

/-- A polyaffine function is continuous. -/
theorem continuous_polyaffine (k : ℝ) (K : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) :
    Continuous (polyaffine k K c) := by
  unfold polyaffine
  exact (continuous_const.add (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (by fun_prop))).add (continuous_const.mul continuous_id.matrix_det)

/-- The entries are null Lagrangians: `∫_Ω (A + ∇φ)_{ij} = |Ω| A_{ij}`. -/
theorem setIntegral_entry_add_grad {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} {L : NNReal}
    (hφ : LipschitzWith L φ) (h0 : ∀ x ∉ unitCube 2, φ x = 0) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (i j : Fin 2) :
    ∫ x in unitCube 2, (A + grad φ x) i j = (volume (unitCube 2)).toReal * A i j := by
  have h := setIntegral_minor_add_grad isBounded_unitCube_two hφ h0 A
    (OrderEmbedding.ofStrictMono (fun _ : Fin 1 => i) (Subsingleton.strictMono _))
    (OrderEmbedding.ofStrictMono (fun _ : Fin 1 => j) (Subsingleton.strictMono _))
  simpa [minor] using h

/-- The determinant is a null Lagrangian: `∫_Ω det (A + ∇φ) = |Ω| det A`. -/
theorem setIntegral_det_add_grad {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} {L : NNReal}
    (hφ : LipschitzWith L φ) (h0 : ∀ x ∉ unitCube 2, φ x = 0) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∫ x in unitCube 2, (A + grad φ x).det = (volume (unitCube 2)).toReal * A.det :=
  setIntegral_minor_add_grad isBounded_unitCube_two hφ h0 A (RelEmbedding.refl _)
    (RelEmbedding.refl _)

/-- Polyaffine functions are null Lagrangians: `∫_Ω P (A + ∇φ) = |Ω| P (A)`. -/
theorem setIntegral_polyaffine_add_grad (k : ℝ) (K : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ)
    {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} {L : NNReal} (hφ : LipschitzWith L φ)
    (h0 : ∀ x ∉ unitCube 2, φ x = 0) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∫ x in unitCube 2, polyaffine k K c (A + grad φ x) =
      (volume (unitCube 2)).toReal * polyaffine k K c A := by
  have hfin := volume_unitCube_two_ne_top
  have hE : ∀ i j, IntegrableOn (fun x => K i j * (A + grad φ x) i j) (unitCube 2) := fun i j =>
    (nl_integrableOn_cube hφ (Φ := fun B => B i j) (by fun_prop) A _ hfin).const_mul _
  have hS : IntegrableOn (fun x => ∑ i, ∑ j, K i j * (A + grad φ x) i j) (unitCube 2) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hE i j
  have hD : IntegrableOn (fun x => c * (A + grad φ x).det) (unitCube 2) :=
    (nl_integrableOn_cube hφ (Φ := fun B => B.det) continuous_id.matrix_det A _ hfin).const_mul _
  have hk : IntegrableOn (fun _ : Fin 2 → ℝ => k) (unitCube 2) :=
    integrableOn_const hfin enorm_ne_top
  have hkS : IntegrableOn (fun x => k + ∑ i, ∑ j, K i j * (A + grad φ x) i j) (unitCube 2) :=
    hk.add hS
  have hsum : ∫ x in unitCube 2, ∑ i, ∑ j, K i j * (A + grad φ x) i j =
      (volume (unitCube 2)).toReal * ∑ i, ∑ j, K i j * A i j := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hE i j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hE i j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, setIntegral_entry_add_grad hφ h0]
    ring
  unfold polyaffine
  rw [integral_add hkS hD, integral_add hk hS, setIntegral_const, integral_const_mul,
    setIntegral_det_add_grad hφ h0, hsum, smul_eq_mul, Measure.real]
  ring

/-- A polyaffine support at `A₀` gives quasiconvexity at `A₀`. -/
theorem HasPolyaffineSupportAt.quasiconvexAtOn {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    {A₀ : Matrix (Fin 2) (Fin 2) ℝ} (h : HasPolyaffineSupportAt F A₀) :
    QuasiconvexAtOn (unitCube 2) F A₀ := by
  obtain ⟨k, K, c, hle, heq⟩ := h
  intro φ L hφ h0 hI
  rw [← heq, ← setIntegral_polyaffine_add_grad k K c hφ h0 A₀]
  exact setIntegral_mono (nl_integrableOn_cube hφ (continuous_polyaffine k K c) A₀ _
    volume_unitCube_two_ne_top) hI fun x => hle _

/-- Polyaffine supports at every matrix give quasiconvexity. -/
theorem quasiconvex_of_hasPolyaffineSupportAt {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (h : ∀ A, HasPolyaffineSupportAt F A) : Quasiconvex F :=
  fun A => (h A).quasiconvexAtOn

/-- The affine function `(X, d) ↦ k + ⟨K, X⟩ + c d` on `ℝ^{2×2} × ℝ`, for `p = (k, K, c)`: the
polyaffine function `polyaffine k K c` is `A ↦ polyaffineLift p (A, det A)`. -/
noncomputable def polyaffineLift (p : ℝ × Matrix (Fin 2) (Fin 2) ℝ × ℝ)
    (y : Matrix (Fin 2) (Fin 2) ℝ × ℝ) : ℝ :=
  p.1 + ∑ i, ∑ j, p.2.1 i j * y.1 i j + p.2.2 * y.2

/-- `polyaffineLift p` is affine. -/
theorem polyaffineLift_combo (p : ℝ × Matrix (Fin 2) (Fin 2) ℝ × ℝ)
    (x y : Matrix (Fin 2) (Fin 2) ℝ × ℝ) {a b : ℝ} (hab : a + b = 1) :
    polyaffineLift p (a • x + b • y) = a * polyaffineLift p x + b * polyaffineLift p y := by
  simp only [polyaffineLift, Fin.sum_univ_two, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (-p.1) * hab

/-- In `ℝ^{2×2} × ℝ`, the point `(X, d)` is the midpoint of two points `(B, det B)` of the graph
of the determinant: `B = X ± C` with `C = diag (d − det X, 1)`. -/
theorem polyaffineLift_eq_half (p : ℝ × Matrix (Fin 2) (Fin 2) ℝ × ℝ)
    (X : Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ) :
    polyaffineLift p (X, d) =
      (polyaffine p.1 p.2.1 p.2.2 (X + !![d - X.det, 0; 0, 1]) +
        polyaffine p.1 p.2.1 p.2.2 (X - !![d - X.det, 0; 0, 1])) / 2 := by
  simp [polyaffineLift, polyaffine, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- Polyaffine supports at every matrix give polyconvexity. -/
theorem polyconvex_of_hasPolyaffineSupportAt {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (h : ∀ A, HasPolyaffineSupportAt F A) : Polyconvex F := by
  -- the polyaffine minorants of `F`
  set S : Set (ℝ × Matrix (Fin 2) (Fin 2) ℝ × ℝ) :=
    {p | ∀ A, polyaffine p.1 p.2.1 p.2.2 A ≤ F A} with hS
  have : Nonempty S := by
    obtain ⟨k, K, c, hle, -⟩ := h 0
    exact ⟨⟨(k, K, c), hle⟩⟩
  have hbdd : ∀ y : Matrix (Fin 2) (Fin 2) ℝ × ℝ,
      BddAbove (Set.range fun p : S => polyaffineLift p.1 y) := by
    rintro ⟨X, d⟩
    refine ⟨(F (X + !![d - X.det, 0; 0, 1]) + F (X - !![d - X.det, 0; 0, 1])) / 2, ?_⟩
    rintro _ ⟨p, rfl⟩
    simp only
    rw [polyaffineLift_eq_half]
    linarith [p.2 (X + !![d - X.det, 0; 0, 1]), p.2 (X - !![d - X.det, 0; 0, 1])]
  refine ⟨fun y => ⨆ p : S, polyaffineLift p.1 y, ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩,
    fun A => le_antisymm ?_ (ciSup_le fun p => p.2 A)⟩
  · refine ciSup_le fun p => ?_
    rw [polyaffineLift_combo p.1 x y hab, smul_eq_mul, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_ciSup (hbdd x) p) ha)
      (mul_le_mul_of_nonneg_left (le_ciSup (hbdd y) p) hb)
  · obtain ⟨k, K, c, hle, heq⟩ := h A
    rw [← heq]
    exact le_ciSup (hbdd (A, A.det)) ⟨(k, K, c), hle⟩

/-- A finite convex function on a finite-dimensional space has an affine support at every point
(a subgradient): separate the point `(y₀, g (y₀))` from the open strict epigraph of `g`. -/
theorem exists_affine_support_of_convexOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → ℝ} (hg : ConvexOn ℝ Set.univ g) (y₀ : E) :
    ∃ l : E →L[ℝ] ℝ, ∀ y, g y₀ + l (y - y₀) ≤ g y := by
  have hc : Continuous g := continuousOn_univ.1 (hg.continuousOn isOpen_univ)
  have hopen : IsOpen {p : E × ℝ | g p.1 < p.2} :=
    isOpen_lt (hc.comp continuous_fst) continuous_snd
  have hconv : Convex ℝ {p : E × ℝ | g p.1 < p.2} := by
    simpa using hg.convex_strict_epigraph
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconv hopen (x := (y₀, g y₀)) (by simp)
  have hsplit : ∀ (y : E) (t : ℝ), f (y, t) = f (y, 0) + t * f (0, 1) := by
    intro y t
    have e : (y, t) = (y, (0 : ℝ)) + t • ((0 : E), (1 : ℝ)) := by simp
    conv_lhs => rw [e]
    rw [map_add, map_smul, smul_eq_mul]
  have hβ : 0 < -f (0, 1) := by
    have := hf (y₀, g y₀ + 1) (by simp)
    rw [hsplit y₀ (g y₀ + 1), hsplit y₀ (g y₀)] at this
    linarith
  refine ⟨(-f (0, 1))⁻¹ • f.comp (ContinuousLinearMap.inl ℝ E ℝ), fun y => ?_⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1 := hf (y, g y + ε) (by simpa using hε)
  rw [hsplit y (g y + ε), hsplit y₀ (g y₀)] at h1
  have h2 : (f.comp (ContinuousLinearMap.inl ℝ E ℝ)) (y - y₀) = f (y, 0) - f (y₀, 0) := by
    rw [map_sub]
    rfl
  have h3 : (-f (0, 1))⁻¹ * (f (y, 0) - f (y₀, 0)) < g y + ε - g y₀ := by
    rw [inv_mul_lt_iff₀ hβ]
    linarith
  rw [smul_apply, h2, smul_eq_mul]
  linarith

/-- A linear functional on `ℝ^{2×2} × ℝ` in coordinates. -/
theorem linearMap_matrix_prod_apply (l : Matrix (Fin 2) (Fin 2) ℝ × ℝ →ₗ[ℝ] ℝ)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ) :
    l (B, d) = ∑ i, ∑ j, l (Matrix.single i j 1, 0) * B i j + l (0, 1) * d := by
  have hB : (B, d) = ∑ i, ∑ j, B i j • (Matrix.single i j (1 : ℝ), (0 : ℝ)) +
      d • ((0 : Matrix (Fin 2) (Fin 2) ℝ), (1 : ℝ)) := by
    refine Prod.ext ?_ ?_
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two]
    · simp [Fin.sum_univ_two]
  conv_lhs => rw [hB]
  simp only [map_add, map_sum, map_smul, smul_eq_mul, mul_comm]

section Support

open scoped Matrix.Norms.Elementwise

/-- A polyconvex function has a polyaffine support at every matrix: an affine support of the
convex `g` at `(A, det A)`. -/
theorem Polyconvex.hasPolyaffineSupportAt {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (h : Polyconvex F)
    (A : Matrix (Fin 2) (Fin 2) ℝ) : HasPolyaffineSupportAt F A := by
  obtain ⟨g, hg, hFg⟩ := h
  obtain ⟨l, hl⟩ := exists_affine_support_of_convexOn hg (A, A.det)
  have key : ∀ B : Matrix (Fin 2) (Fin 2) ℝ, polyaffine (g (A, A.det) - l (A, A.det))
      (Matrix.of fun i j => l (Matrix.single i j 1, 0)) (l (0, 1)) B =
        g (A, A.det) + l ((B, B.det) - (A, A.det)) := by
    intro B
    have hB := linearMap_matrix_prod_apply (l : Matrix (Fin 2) (Fin 2) ℝ × ℝ →ₗ[ℝ] ℝ) B B.det
    simp only [ContinuousLinearMap.coe_coe] at hB
    rw [map_sub, hB, polyaffine]
    simp only [Matrix.of_apply]
    ring
  refine ⟨g (A, A.det) - l (A, A.det), Matrix.of fun i j => l (Matrix.single i j 1, 0), l (0, 1),
    fun B => ?_, ?_⟩
  · rw [key, hFg]
    exact hl _
  · rw [key, sub_self, map_zero, add_zero, hFg]

/-- A polyconvex function is continuous. -/
theorem Polyconvex.continuous {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (h : Polyconvex F) :
    Continuous F := by
  obtain ⟨g, hg, hFg⟩ := h
  have hc : Continuous g := continuousOn_univ.1 (hg.continuousOn isOpen_univ)
  rw [show F = fun A => g (A, A.det) from funext hFg]
  exact hc.comp (continuous_id.prodMk continuous_id.matrix_det)

end Support

/-- Polyconvex functions are quasiconvex. -/
theorem Polyconvex.quasiconvex {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (h : Polyconvex F) :
    Quasiconvex F :=
  quasiconvex_of_hasPolyaffineSupportAt h.hasPolyaffineSupportAt

/-- Polyconvex functions are rank-one convex. -/
theorem Polyconvex.rankOneConvex {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (h : Polyconvex F) :
    RankOneConvex F :=
  rankOneConvex_of_quasiconvex h.continuous.measurable
    (isLocallyBounded_of_continuous h.continuous) h.quasiconvex

/-- A quasiconvex minorant that touches at `A₀` gives quasiconvexity at `A₀`. -/
theorem quasiconvexAtOn_of_le_of_eq {F G : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    {A₀ : Matrix (Fin 2) (Fin 2) ℝ} (hG : QuasiconvexAtOn (unitCube 2) G A₀)
    (hGc : Continuous G) (hle : ∀ A, G A ≤ F A) (heq : G A₀ = F A₀) :
    QuasiconvexAtOn (unitCube 2) F A₀ := by
  intro φ L hφ h0 hI
  have hGI := nl_integrableOn_cube hφ hGc A₀ (unitCube 2) volume_unitCube_two_ne_top
  rw [← heq]
  exact (hG φ L hφ h0 hGI).trans (setIntegral_mono hGI hI fun x => hle _)

/-- Nonnegative combinations of continuous quasiconvex functions are quasiconvex. -/
theorem quasiconvex_add_mul {f g : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hf : Quasiconvex f) (hfc : Continuous f) (hg : Quasiconvex g)
    (hgc : Continuous g) : Quasiconvex fun A => a * f A + b * g A := by
  intro A φ L hφ h0 _
  have hfI := nl_integrableOn_cube hφ hfc A (unitCube 2) volume_unitCube_two_ne_top
  have hgI := nl_integrableOn_cube hφ hgc A (unitCube 2) volume_unitCube_two_ne_top
  have h1 := mul_le_mul_of_nonneg_left (hf A φ L hφ h0 hfI) ha
  have h2 := mul_le_mul_of_nonneg_left (hg A φ L hφ h0 hgI) hb
  rw [integral_add (hfI.const_mul a) (hgI.const_mul b), integral_const_mul, integral_const_mul]
  linarith

/-- The gradient of the reflected map `x ↦ (φ₁ (x), −φ₂ (x))` is `J ∇φ`. -/
theorem grad_reflection (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    grad (fun y => ![φ y 0, -φ y 1]) x = reflection * grad φ x := by
  ext i j
  fin_cases i
  · simp [grad, reflection, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [grad, reflection, Matrix.mul_apply, Fin.sum_univ_two, fderiv_fun_neg]

/-- Quasiconvexity is invariant under `A ↦ J A`, `J = diag (1, −1)`. -/
theorem quasiconvex_comp_reflection_mul {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hf : Quasiconvex f) : Quasiconvex fun A => f (reflection * A) := by
  intro A φ L hφ h0 hI
  have hψ : LipschitzWith L fun y => ![φ y 0, -φ y 1] := by
    refine LipschitzWith.of_dist_le_mul fun x y => le_trans ?_ (hφ.dist_le_mul x y)
    refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
    fin_cases i
    · exact dist_le_pi_dist (φ x) (φ y) 0
    · simpa using dist_le_pi_dist (φ x) (φ y) 1
  have h0ψ : ∀ x ∉ unitCube 2, (fun y => ![φ y 0, -φ y 1]) x = 0 := by
    intro x hx
    ext i
    fin_cases i <;> simp [h0 x hx]
  have e : ∀ x, f (reflection * A + grad (fun y => ![φ y 0, -φ y 1]) x) =
      f (reflection * (A + grad φ x)) := fun x => by rw [grad_reflection, mul_add]
  have := hf (reflection * A) _ L hψ h0ψ (by simpa only [e] using hI)
  simpa only [e] using this

end HomogeneousIsotropic
