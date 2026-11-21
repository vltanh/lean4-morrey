module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Fourier coefficients of Lipschitz periodic functions, and Fejér means

For a `ℤ^ι`-periodic function `g : (ι → ℝ) → ℂ`, its Fourier coefficients are integrals over the
open unit cube `(0, 1)^ι` (`UnitAddTorus.cubeFourierCoeff`):
`ĝ (n) = ∫_{(0,1)^ι} e^{−2πi ⟨n, x⟩} g (x) dx`. This file proves:

* Parseval's identity on the cube, for bounded measurable periodic `g`
  (`UnitAddTorus.hasSum_sq_cubeFourierCoeff`), from Mathlib's Parseval identity on the torus;
* the coefficients of the derivative of a Lipschitz periodic function `f : (ι → ℝ) → ℝ`:
  `(∂_v f)^ (n) = 2πi ⟨n, v⟩ f̂ (n)`, with `∂_v f (x) = fderiv ℝ f x v` (which is the derivative
  of `f` almost everywhere, by Rademacher's theorem) (`UnitAddTorus.cubeFourierCoeff_fderiv`);
* the Fejér means `σ_M g = Σ_n λ_M (n) ĝ (n) e_n` (`UnitAddTorus.fejerMean`), with the weights
  `λ_M (n) = #{(a, b) ∈ B_M² | a − b = n} / #B_M` of the box `B_M = {0, …, M − 1}^ι`: they are
  bounded by `sup ‖g‖` (`UnitAddTorus.norm_fejerMean_le`; the kernel `|Σ_{a ∈ B_M} e_a|² / #B_M` is
  nonnegative with mean one) and converge to `g` in `L²` of the cube
  (`UnitAddTorus.tendsto_integral_norm_fejerMean_sub_sq`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Complex
open scoped ComplexConjugate Real Finset

/-- As in `Mathlib.Analysis.Fourier.AddCircleMulti`, the measure on `ℝ / ℤ` is normalised to have
total mass one. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-! ### Periodic functions on `ℝ^ι` and functions on the torus -/

/-- The projection `ℝ^ι → 𝕋^ι = (ℝ / ℤ)^ι`. -/
def ofPi (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

omit [Fintype ι] in
theorem continuous_ofPi : Continuous (ofPi : (ι → ℝ) → UnitAddTorus ι) :=
  continuous_pi fun i => (AddCircle.continuous_mk' 1).comp (continuous_apply i)

theorem measurable_ofPi : Measurable (ofPi : (ι → ℝ) → UnitAddTorus ι) :=
  continuous_ofPi.measurable

omit [Fintype ι] in
theorem ofPi_add (x y : ι → ℝ) : ofPi (x + y) = ofPi x + ofPi y := by
  funext i; simp [ofPi]

omit [Fintype ι] in
theorem ofPi_add_int (x : ι → ℝ) (k : ι → ℤ) : ofPi (x + fun i => (k i : ℝ)) = ofPi x := by
  funext i
  simp only [ofPi, Pi.add_apply, AddCircle.coe_add, add_eq_left]
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k i, by simp⟩

/-- The representative of a point of the torus in `(0, 1]^ι`. -/
def toPi (z : UnitAddTorus ι) : ι → ℝ := ((measurableEquivPiIoc (0 : ι → ℝ) z : _) : ι → ℝ)

omit [Fintype ι] in
theorem measurable_toPi : Measurable (toPi : UnitAddTorus ι → ι → ℝ) :=
  measurable_subtype_coe.comp (measurableEquivPiIoc (0 : ι → ℝ)).measurable

omit [Fintype ι] in
theorem ofPi_toPi (z : UnitAddTorus ι) : ofPi (toPi z) = z := by
  funext i
  simp [ofPi, toPi]

omit [Fintype ι] in
theorem exists_toPi_ofPi (x : ι → ℝ) : ∃ k : ι → ℤ, toPi (ofPi x) = x + fun i => (k i : ℝ) := by
  have h : ∀ i, ∃ k : ℤ, toPi (ofPi x) i = x i + k := by
    intro i
    have h1 : ((toPi (ofPi x) i - x i : ℝ) : UnitAddCircle) = 0 := by
      have := congrFun (ofPi_toPi (ofPi x)) i
      simp only [ofPi] at this
      rw [AddCircle.coe_sub, this, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h1
    exact ⟨k, by simp at hk; linarith⟩
  choose k hk using h
  exact ⟨k, funext fun i => by simp [hk i]⟩

/-- `g` is `ℤ^ι`-periodic. -/
def IsPeriodic {E : Type*} (g : (ι → ℝ) → E) : Prop :=
  ∀ (x : ι → ℝ) (k : ι → ℤ), g (x + fun i => (k i : ℝ)) = g x

omit [Fintype ι] in
theorem IsPeriodic.comp_toPi_ofPi {E : Type*} {g : (ι → ℝ) → E} (hg : IsPeriodic g)
    (x : ι → ℝ) : g (toPi (ofPi x)) = g x := by
  obtain ⟨k, hk⟩ := exists_toPi_ofPi x
  rw [hk, hg]

/-- The open unit cube `(0, 1)^ι`. -/
abbrev cube (ι : Type*) : Set (ι → ℝ) := univ.pi fun _ => Ioo (0 : ℝ) 1

theorem measurableSet_cube : MeasurableSet (cube ι) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem volume_cube : volume (cube ι) = 1 := by
  rw [Real.volume_pi_Ioo]; simp

instance : IsFiniteMeasure (volume.restrict (cube ι)) :=
  ⟨by rw [Measure.restrict_apply_univ, volume_cube]; exact ENNReal.one_lt_top⟩

/-- Integrals over the torus (with the Haar measure of total mass one, as in
`Mathlib.Analysis.Fourier.AddCircleMulti`) are integrals over the cube. -/
theorem integral_cube_ofPi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : UnitAddTorus ι → E) : ∫ x in cube ι, F (ofPi x) = ∫ z, F z := by
  rw [integral_preimage F 0]
  have h1 : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      univ.pi fun _ => Ioc (0 : ℝ) 1 := by
    ext x; simp
  rw [h1]
  exact setIntegral_congr_set
    (Measure.univ_pi_Ioo_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm)

/-- The integral over the cube of a periodic function is invariant under translations. -/
theorem integral_cube_comp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (ι → ℝ) → E} (hg : IsPeriodic g) (a : ι → ℝ) :
    ∫ x in cube ι, g (x + a) = ∫ x in cube ι, g x := by
  have h1 : ∀ x, g (x + a) = (g ∘ toPi) (ofPi x + ofPi a) := fun x => by
    rw [Function.comp_apply, ← ofPi_add, hg.comp_toPi_ofPi]
  have h2 : ∀ x, g x = (g ∘ toPi) (ofPi x) := fun x => (hg.comp_toPi_ofPi x).symm
  simp_rw [h1, h2]
  rw [integral_cube_ofPi (fun z => (g ∘ toPi) (z + ofPi a)), integral_cube_ofPi,
    integral_add_right_eq_self]

/-! ### The monomials on `ℝ^ι` -/

theorem mFourier_ofPi (n : ι → ℤ) (x : ι → ℝ) :
    mFourier n (ofPi x) = Complex.exp (2 * π * I * ∑ i, (n i : ℂ) * (x i : ℂ)) := by
  simp only [mFourier, ContinuousMap.coe_mk, ofPi, fourier_coe_apply, ← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem norm_mFourier_ofPi (n : ι → ℤ) (x : ι → ℝ) : ‖mFourier n (ofPi x)‖ = 1 := by
  simp [mFourier, fourier_apply, norm_prod, Circle.norm_coe]

theorem mFourier_ofPi_add (n : ι → ℤ) (x y : ι → ℝ) :
    mFourier n (ofPi (x + y)) = mFourier n (ofPi x) * mFourier n (ofPi y) := by
  simp only [mFourier_ofPi, ← Complex.exp_add, Pi.add_apply]
  congr 1
  push_cast
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mFourier_ofPi_neg (n : ι → ℤ) (x : ι → ℝ) :
    mFourier (-n) (ofPi x) = mFourier n (ofPi (-x)) := by
  simp only [mFourier_ofPi, Pi.neg_apply]
  congr 1
  push_cast
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mFourier_ofPi_add_index (m n : ι → ℤ) (x : ι → ℝ) :
    mFourier (m + n) (ofPi x) = mFourier m (ofPi x) * mFourier n (ofPi x) :=
  mFourier_add

theorem continuous_mFourier_ofPi (n : ι → ℤ) : Continuous fun x : ι → ℝ => mFourier n (ofPi x) :=
  (mFourier n).continuous.comp continuous_ofPi

theorem mFourier_ofPi_isPeriodic (n : ι → ℤ) : IsPeriodic fun x : ι → ℝ => mFourier n (ofPi x) :=
  fun x k => by simp only [ofPi_add_int]

/-- Orthogonality: `∫_{(0,1)^ι} e_m = 1` if `m = 0`, and `0` otherwise. -/
theorem integral_cube_mFourier (m : ι → ℤ) :
    ∫ x in cube ι, mFourier m (ofPi x) = if m = 0 then 1 else 0 := by
  rw [integral_cube_ofPi (fun z => mFourier m z)]
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := ι))) 0 m
  rw [ContinuousMap.inner_toLp] at h
  simp only [mFourier_zero, ContinuousMap.one_apply, map_one, mul_one] at h
  rw [h]
  by_cases hm : m = 0 <;> simp [hm, eq_comm]

/-! ### Fourier coefficients over the cube -/

/-- The `n`-th Fourier coefficient of a function on `ℝ^ι`, over the cube:
`ĝ (n) = ∫_{(0,1)^ι} e^{−2πi ⟨n, x⟩} g (x) dx`. -/
def cubeFourierCoeff (g : (ι → ℝ) → ℂ) (n : ι → ℤ) : ℂ :=
  ∫ x in cube ι, mFourier (-n) (ofPi x) * g x

theorem integrableOn_cube_of_bound {E : Type*} [NormedAddCommGroup E] {g : (ι → ℝ) → E}
    (hg : AEStronglyMeasurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) : IntegrableOn g (cube ι) :=
  Measure.integrableOn_of_bounded (by rw [volume_cube]; exact ENNReal.one_ne_top) hg
    (ae_of_all _ hC)

theorem integrableOn_cube_mFourier_mul {g : (ι → ℝ) → ℂ} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) (n : ι → ℤ) :
    IntegrableOn (fun x => mFourier n (ofPi x) * g x) (cube ι) :=
  integrableOn_cube_of_bound ((continuous_mFourier_ofPi n).aestronglyMeasurable.mul hg)
    (C := C) fun x => by rw [norm_mul, norm_mFourier_ofPi, one_mul]; exact hC x

theorem cubeFourierCoeff_add {g h : (ι → ℝ) → ℂ} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (hh : AEStronglyMeasurable h) {D : ℝ} (hhD : ∀ x, ‖h x‖ ≤ D)
    (n : ι → ℤ) :
    cubeFourierCoeff (fun x => g x + h x) n = cubeFourierCoeff g n + cubeFourierCoeff h n := by
  simp only [cubeFourierCoeff, mul_add]
  exact integral_add (integrableOn_cube_mFourier_mul hg hgC _)
    (integrableOn_cube_mFourier_mul hh hhD _)

theorem cubeFourierCoeff_sub {g h : (ι → ℝ) → ℂ} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (hh : AEStronglyMeasurable h) {D : ℝ} (hhD : ∀ x, ‖h x‖ ≤ D)
    (n : ι → ℤ) :
    cubeFourierCoeff (fun x => g x - h x) n = cubeFourierCoeff g n - cubeFourierCoeff h n := by
  simp only [cubeFourierCoeff, mul_sub]
  exact integral_sub (integrableOn_cube_mFourier_mul hg hgC _)
    (integrableOn_cube_mFourier_mul hh hhD _)

theorem cubeFourierCoeff_const_mul (c : ℂ) (g : (ι → ℝ) → ℂ) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => c * g x) n = c * cubeFourierCoeff g n := by
  simp only [cubeFourierCoeff, mul_left_comm _ c]
  exact integral_const_mul c _

/-- The coefficients of a trigonometric polynomial. -/
theorem cubeFourierCoeff_trig (S : Finset (ι → ℤ)) (c : (ι → ℤ) → ℂ) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => ∑ m ∈ S, c m * mFourier m (ofPi x)) n =
      if n ∈ S then c n else 0 := by
  simp only [cubeFourierCoeff, Finset.mul_sum]
  rw [integral_finsetSum]
  · have : ∀ m ∈ S, ∫ x in cube ι, mFourier (-n) (ofPi x) * (c m * mFourier m (ofPi x)) =
        if n = m then c m else 0 := by
      intro m _
      have e : ∀ x, mFourier (-n) (ofPi x) * (c m * mFourier m (ofPi x)) =
          c m * mFourier (-n + m) (ofPi x) := fun x => by
        rw [mFourier_ofPi_add_index]; ring
      simp_rw [e]
      rw [integral_const_mul, integral_cube_mFourier]
      by_cases h : n = m
      · simp [h]
      · have h' : -n + m ≠ 0 := fun h0 => h (neg_add_eq_zero.mp h0)
        simp [h, h']
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  · intro m _
    exact integrableOn_cube_of_bound ((continuous_mFourier_ofPi _).mul
      (continuous_const.mul (continuous_mFourier_ofPi _))).aestronglyMeasurable (C := ‖c m‖)
      fun x => by rw [norm_mul, norm_mul, norm_mFourier_ofPi, norm_mFourier_ofPi]; simp

/-- **Parseval's identity** on the cube, for a bounded measurable `ℤ^ι`-periodic `g`:
`Σ_n |ĝ (n)|² = ∫_{(0,1)^ι} |g|²`. -/
theorem hasSum_sq_cubeFourierCoeff {g : (ι → ℝ) → ℂ} (hgm : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (hg : IsPeriodic g) :
    HasSum (fun n => ‖cubeFourierCoeff g n‖ ^ 2) (∫ x in cube ι, ‖g x‖ ^ 2) := by
  set G : UnitAddTorus ι → ℂ := g ∘ toPi with hG
  have hGm : Measurable G := hgm.comp measurable_toPi
  have hmem : MemLp G 2 volume := MemLp.of_bound hGm.aestronglyMeasurable C
    (ae_of_all _ fun z => hgC _)
  have key := hasSum_sq_mFourierCoeff (hmem.toLp G)
  have hc : ∀ n, mFourierCoeff (hmem.toLp G) n = cubeFourierCoeff g n := by
    intro n
    have e1 : mFourierCoeff (hmem.toLp G) n = mFourierCoeff G n := by
      refine integral_congr_ae ?_
      filter_upwards [hmem.coeFn_toLp] with z hz
      rw [hz]
    rw [e1, mFourierCoeff, cubeFourierCoeff, ← integral_cube_ofPi]
    refine setIntegral_congr_fun measurableSet_cube fun x _ => ?_
    simp only [hG, Function.comp_apply, hg.comp_toPi_ofPi, smul_eq_mul]
  have hn : ∫ t, ‖(hmem.toLp G) t‖ ^ 2 = ∫ x in cube ι, ‖g x‖ ^ 2 := by
    have e1 : ∫ t, ‖(hmem.toLp G) t‖ ^ 2 = ∫ t, ‖G t‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hmem.coeFn_toLp] with z hz
      rw [hz]
    rw [e1, ← integral_cube_ofPi]
    refine setIntegral_congr_fun measurableSet_cube fun x _ => ?_
    simp only [hG, Function.comp_apply, hg.comp_toPi_ofPi]
  simp only [hc, hn] at key
  exact key

theorem integrableOn_cube_of_continuous {E : Type*} [NormedAddCommGroup E] {g : (ι → ℝ) → E}
    (hg : Continuous g) : IntegrableOn g (cube ι) :=
  (hg.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc
    (a := (0 : ℝ)) (b := 1))).mono_set (pi_mono fun _ _ => Ioo_subset_Icc_self)

/-! ### The derivative of a Lipschitz periodic function -/

/-- The slope `t⁻¹ (e^{2πi t ⟨n, v⟩} − 1)` tends to `2πi ⟨n, v⟩`. -/
theorem tendsto_slope_mFourier_ofPi_smul (n : ι → ℤ) (v : ι → ℝ) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℂ) * (mFourier n (ofPi (t • v)) - 1)) (𝓝[≠] 0)
      (𝓝 (2 * π * I * ∑ i, (n i : ℂ) * (v i : ℂ))) := by
  set c : ℂ := 2 * π * I * ∑ i, (n i : ℂ) * (v i : ℂ) with hc
  have hE : ∀ t : ℝ, mFourier n (ofPi (t • v)) = Complex.exp ((t : ℂ) * c) := fun t => by
    rw [mFourier_ofPi, hc]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c)) c 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * c) c 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const c
    simpa using h1.cexp
  have := hasDerivAt_iff_tendsto_slope_zero.mp hd
  simp only [zero_add, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at this
  refine this.congr fun t => ?_
  rw [hE, Complex.real_smul, Complex.ofReal_inv]

/-- The Fourier coefficients of the derivative of a Lipschitz `ℤ^ι`-periodic `f : ℝ^ι → ℝ` in the
direction `v`: `(∂_v f)^ (n) = 2πi ⟨n, v⟩ f̂ (n)`, with `∂_v f (x) = fderiv ℝ f x v` (the derivative
almost everywhere, by Rademacher's theorem). The proof integrates the difference quotients
`t⁻¹ (f (x + t v) − f (x))` against `e_{−n}`, moves the translation onto `e_{−n}` by the
translation invariance of the integral of a periodic function, and lets `t → 0` (dominated
convergence on one side, the derivative of `t ↦ e^{2πi t ⟨n, v⟩}` on the other). -/
theorem cubeFourierCoeff_fderiv {f : (ι → ℝ) → ℝ} {C : NNReal} (hf : LipschitzWith C f)
    (hper : IsPeriodic f) (v : ι → ℝ) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => (fderiv ℝ f x v : ℂ)) n =
      2 * π * I * (∑ i, (n i : ℂ) * (v i : ℂ)) * cubeFourierCoeff (fun x => (f x : ℂ)) n := by
  set A : ℝ → ℂ := fun t => ∫ x in cube ι,
    mFourier (-n) (ofPi x) * ((t⁻¹ * (f (x + t • v) - f x) : ℝ) : ℂ) with hA
  -- the difference quotients converge to the derivative
  have h1 : Tendsto A (𝓝[≠] 0) (𝓝 (cubeFourierCoeff (fun x => (fderiv ℝ f x v : ℂ)) n)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (C : ℝ) * ‖v‖) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t => ((continuous_mFourier_ofPi _).mul
        (Complex.continuous_ofReal.comp (continuous_const.mul
          ((hf.continuous.comp (continuous_id.add continuous_const)).sub
            hf.continuous)))).aestronglyMeasurable
    · refine Eventually.of_forall fun t => ae_of_all _ fun x => ?_
      rw [norm_mul, norm_mFourier_ofPi, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_inv]
      have h := hf.dist_le_mul (x + t • v) x
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
      by_cases ht : t = 0
      · simp only [ht, abs_zero, inv_zero, zero_mul]; positivity
      · have ht' : 0 < |t| := abs_pos.mpr ht
        calc |t|⁻¹ * |f (x + t • v) - f x| ≤ |t|⁻¹ * (C * (|t| * ‖v‖)) := by gcongr
          _ = C * ‖v‖ := by field_simp
    · exact integrableOn_const (by rw [volume_cube]; exact ENNReal.one_ne_top)
    · filter_upwards [ae_restrict_of_ae hf.ae_differentiableAt] with x hx
      have h0 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      have hd : HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 :=
        hx.hasFDerivAt.comp_hasDerivAt_of_eq 0 h0 (by simp)
      have h2 := hasDerivAt_iff_tendsto_slope_zero.mp hd
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at h2
      exact ((Complex.continuous_ofReal.tendsto _).comp h2).const_mul _
  -- the translation moves onto `e_{−n}`
  have h2 : ∀ t : ℝ, A t = (t⁻¹ : ℂ) * (mFourier n (ofPi (t • v)) - 1) *
      cubeFourierCoeff (fun x => (f x : ℂ)) n := by
    intro t
    have hcont : ∀ w : ι → ℝ, Continuous fun x => mFourier (-n) (ofPi x) * (f (x + w) : ℂ) :=
      fun w => (continuous_mFourier_ofPi _).mul (Complex.continuous_ofReal.comp
        (hf.continuous.comp (continuous_id.add continuous_const)))
    have e1 : ∀ x, mFourier (-n) (ofPi x) * ((t⁻¹ * (f (x + t • v) - f x) : ℝ) : ℂ) =
        (t⁻¹ : ℂ) * (mFourier (-n) (ofPi x) * (f (x + t • v) : ℂ) -
          mFourier (-n) (ofPi x) * (f (x + 0) : ℂ)) := fun x => by
      push_cast; rw [add_zero]; ring
    have hF : IsPeriodic fun y => mFourier (-n) (ofPi (y + -(t • v))) * (f y : ℂ) := by
      intro y k
      simp only
      rw [show y + (fun i => (k i : ℝ)) + -(t • v) = (y + -(t • v)) + fun i => (k i : ℝ) by
        abel, ofPi_add_int, hper]
    have e2 : ∫ x in cube ι, mFourier (-n) (ofPi x) * (f (x + t • v) : ℂ) =
        mFourier n (ofPi (t • v)) * cubeFourierCoeff (fun x => (f x : ℂ)) n := by
      have := integral_cube_comp_add hF (t • v)
      simp only [add_neg_cancel_right] at this
      rw [this, cubeFourierCoeff, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_cube fun y _ => ?_
      rw [mFourier_ofPi_add, mFourier_ofPi_neg n (-(t • v)), neg_neg]
      ring
    simp only [hA]
    simp_rw [e1]
    rw [integral_const_mul, integral_sub (integrableOn_cube_of_continuous (hcont _))
      (integrableOn_cube_of_continuous (hcont 0)), e2]
    simp only [add_zero, cubeFourierCoeff]
    ring
  have h3 := (tendsto_slope_mFourier_ofPi_smul n v).mul_const
    (cubeFourierCoeff (fun x => (f x : ℂ)) n)
  exact tendsto_nhds_unique h1 (h3.congr fun t => (h2 t).symm)

/-! ### Fejér means -/

section Fejer

variable [DecidableEq ι]

/-- The box `B_M = {0, …, M − 1}^ι`. -/
def fejerBox (M : ℕ) : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) M

/-- The frequencies `B_M − B_M` of the Fejér means. -/
def fejerSupport (M : ℕ) : Finset (ι → ℤ) :=
  (fejerBox M ×ˢ fejerBox M).image fun p => p.1 - p.2

/-- The pairs `(a, b) ∈ B_M²` with `a − b = n`. -/
def fejerFiber (M : ℕ) (n : ι → ℤ) : Finset ((ι → ℤ) × (ι → ℤ)) :=
  (fejerBox M ×ˢ fejerBox M).filter fun p => p.1 - p.2 = n

theorem mem_fejerFiber {M : ℕ} {n : ι → ℤ} {p : (ι → ℤ) × (ι → ℤ)} :
    p ∈ fejerFiber M n ↔ (p.1 ∈ fejerBox M ∧ p.2 ∈ fejerBox M) ∧ p.1 - p.2 = n := by
  simp [fejerFiber]

/-- The Fejér weights `λ_M (n) = #{(a, b) ∈ B_M² | a − b = n} / #B_M`. -/
def fejerWeight (M : ℕ) (n : ι → ℤ) : ℝ :=
  (#(fejerFiber M n) : ℝ) / #(fejerBox (ι := ι) M)

/-- The Fejér mean `σ_M g = Σ_n λ_M (n) ĝ (n) e_n`, a trigonometric polynomial. -/
def fejerMean (M : ℕ) (g : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℂ :=
  ∑ n ∈ fejerSupport M, (fejerWeight M n : ℂ) * cubeFourierCoeff g n * mFourier n (ofPi x)

theorem card_fejerBox (M : ℕ) : (#(fejerBox (ι := ι) M) : ℝ) = ∏ _i : ι, (M : ℝ) := by
  simp [fejerBox]

theorem fejerWeight_nonneg (M : ℕ) (n : ι → ℤ) : 0 ≤ fejerWeight M n := by
  unfold fejerWeight; positivity

theorem fejerWeight_le_one (M : ℕ) (n : ι → ℤ) : fejerWeight M n ≤ 1 := by
  unfold fejerWeight
  by_cases h0 : (#(fejerBox (ι := ι) M) : ℝ) = 0
  · rw [h0, div_zero]; exact zero_le_one
  refine (div_le_one (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0))).mpr ?_
  exact_mod_cast Finset.card_le_card_of_injOn (fun p : (ι → ℤ) × (ι → ℤ) => p.2)
    (fun p hp => (mem_fejerFiber.mp hp).1.2)
    (fun p hp q hq h => by
      have hp' := (mem_fejerFiber.mp hp).2
      have hq' := (mem_fejerFiber.mp hq).2
      have h' : p.2 = q.2 := h
      have h1 : p.1 = q.1 := by
        have := hp'.trans hq'.symm
        rw [h'] at this
        exact sub_left_inj.mp this
      exact Prod.ext h1 h')

theorem fejerWeight_eq_zero {M : ℕ} {n : ι → ℤ} (hn : n ∉ fejerSupport M) :
    fejerWeight M n = 0 := by
  unfold fejerWeight
  rw [Finset.card_eq_zero.mpr, Nat.cast_zero, zero_div]
  refine Finset.eq_empty_of_forall_notMem fun p hp => hn ?_
  exact Finset.mem_image.mpr ⟨p, Finset.mem_product.mpr (mem_fejerFiber.mp hp).1,
    (mem_fejerFiber.mp hp).2⟩

theorem fejerWeight_zero {M : ℕ} (hM : (#(fejerBox (ι := ι) M) : ℝ) ≠ 0) :
    fejerWeight M (0 : ι → ℤ) = 1 := by
  unfold fejerWeight
  rw [div_eq_one_iff_eq hM]
  congr 1
  refine Finset.card_nbij' (fun p => p.1) (fun a => (a, a)) ?_ ?_ ?_ ?_
  · intro p hp
    exact (mem_fejerFiber.mp hp).1.1
  · intro a ha
    exact mem_fejerFiber.mpr ⟨⟨ha, ha⟩, sub_self a⟩
  · intro p hp
    have := sub_eq_zero.mp (mem_fejerFiber.mp hp).2
    exact Prod.ext rfl this
  · intro a _; rfl

theorem zero_mem_fejerSupport {M : ℕ} (hM : (#(fejerBox (ι := ι) M) : ℝ) ≠ 0) :
    (0 : ι → ℤ) ∈ fejerSupport M := by
  obtain ⟨a, ha⟩ := Finset.card_ne_zero.mp (by exact_mod_cast hM)
  exact Finset.mem_image.mpr ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩, sub_self a⟩

/-- `λ_M (n) ≥ Π_i (1 − 2 |n_i| / M)` once `M ≥ 2 |n_i|` for all `i`. -/
theorem prod_le_fejerWeight {M : ℕ} (hM : 0 < M) {n : ι → ℤ} (hn : ∀ i, 2 * |n i| ≤ M) :
    ∏ i, (1 - 2 * |(n i : ℝ)| / M) ≤ fejerWeight M n := by
  set I : Finset (ι → ℤ) := Fintype.piFinset fun i => Finset.Ico |n i| (M - |n i|) with hI
  have hcard : #I ≤ #(fejerFiber M n) := by
    refine Finset.card_le_card_of_injOn (fun a => (a + n, a)) (fun a ha => ?_)
      (fun a _ b _ h => (Prod.ext_iff.mp h).2)
    have ha' : ∀ i, |n i| ≤ a i ∧ a i < M - |n i| := fun i =>
      Finset.mem_Ico.mp (Fintype.mem_piFinset.mp (Finset.mem_coe.mp ha) i)
    refine Finset.mem_coe.mpr (mem_fejerFiber.mpr ⟨⟨?_, ?_⟩, add_sub_cancel_left a n⟩)
    · refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Ico.mpr ⟨?_, ?_⟩
      · have := ha' i; have := neg_abs_le (n i); simp only [Pi.add_apply]; linarith
      · have := ha' i; have := le_abs_self (n i); simp only [Pi.add_apply]; linarith
    · refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Ico.mpr ⟨?_, ?_⟩
      · have := ha' i; have := abs_nonneg (n i); linarith
      · have := ha' i; have := abs_nonneg (n i); linarith
  have hIc : (#I : ℝ) = ∏ i, ((M : ℝ) - 2 * |(n i : ℝ)|) := by
    simp only [hI, Fintype.card_piFinset, Int.card_Ico, Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h0 : 0 ≤ (M : ℤ) - |n i| - |n i| := by have := hn i; linarith
    rw [show ((Int.toNat ((M : ℤ) - |n i| - |n i|) : ℕ) : ℝ) =
        (((Int.toNat ((M : ℤ) - |n i| - |n i|) : ℕ) : ℤ) : ℝ) from rfl, Int.toNat_of_nonneg h0]
    push_cast
    ring
  have hB : (0 : ℝ) < #(fejerBox (ι := ι) M) := by
    rw [card_fejerBox]; exact Finset.prod_pos fun _ _ => by exact_mod_cast hM
  unfold fejerWeight
  rw [le_div_iff₀ hB, card_fejerBox, ← Finset.prod_mul_distrib]
  calc ∏ i, ((1 - 2 * |(n i : ℝ)| / M) * M) = (#I : ℝ) := by
        rw [hIc]
        refine Finset.prod_congr rfl fun i _ => ?_
        have : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
        field_simp
    _ ≤ _ := by exact_mod_cast hcard

/-- `λ_M (n) → 1` as `M → ∞`. -/
theorem tendsto_fejerWeight (n : ι → ℤ) : Tendsto (fun M => fejerWeight M n) atTop (𝓝 1) := by
  have hlow : Tendsto (fun M : ℕ => ∏ i, (1 - 2 * |(n i : ℝ)| / M)) atTop (𝓝 1) := by
    have := tendsto_finsetProd (Finset.univ : Finset ι) fun i _ =>
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (2 * |(n i : ℝ)|))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun M => fejerWeight_le_one M n)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ i, 2 * |n i| ≤ K := by
    refine ⟨∑ i, (2 * |n i|).toNat, fun i => ?_⟩
    have h1 : 2 * |n i| ≤ ((2 * |n i|).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (2 * |n i|).toNat ≤ ∑ j, (2 * |n j|).toNat :=
      Finset.single_le_sum (f := fun j => (2 * |n j|).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h3 : (((2 * |n i|).toNat : ℕ) : ℤ) ≤ ((∑ j, (2 * |n j|).toNat : ℕ) : ℤ) := by
      exact_mod_cast h2
    linarith
  filter_upwards [eventually_ge_atTop (K + 1)] with M hM
  exact prod_le_fejerWeight (by omega) fun i => (hK i).trans (by exact_mod_cast (by omega : K ≤ M))

/-- The Fejér kernel `K_M (t) = |Σ_{a ∈ B_M} e_a (t)|² / #B_M`. -/
def fejerKernel (M : ℕ) (t : ι → ℝ) : ℝ :=
  ‖∑ a ∈ fejerBox M, mFourier a (ofPi t)‖ ^ 2 / #(fejerBox (ι := ι) M)

theorem fejerKernel_nonneg (M : ℕ) (t : ι → ℝ) : 0 ≤ fejerKernel M t := by
  unfold fejerKernel; positivity

theorem continuous_fejerKernel (M : ℕ) : Continuous (fejerKernel (ι := ι) M) := by
  unfold fejerKernel
  exact ((continuous_finsetSum _ fun a _ => continuous_mFourier_ofPi a).norm.pow 2).div_const _

theorem fejerKernel_le (M : ℕ) (t : ι → ℝ) : fejerKernel M t ≤ #(fejerBox (ι := ι) M) := by
  unfold fejerKernel
  by_cases h0 : (#(fejerBox (ι := ι) M) : ℝ) = 0
  · rw [h0, div_zero]
  have hpos : (0 : ℝ) < #(fejerBox (ι := ι) M) :=
    lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)
  rw [div_le_iff₀ hpos]
  have h1 : ‖∑ a ∈ fejerBox M, mFourier a (ofPi t)‖ ≤ #(fejerBox (ι := ι) M) := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_mFourier_ofPi]
  calc ‖∑ a ∈ fejerBox M, mFourier a (ofPi t)‖ ^ 2 ≤ (#(fejerBox (ι := ι) M) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = _ := by ring

/-- `Σ_{(a, b) ∈ B_M²} e_{a − b} (t) = |Σ_{a ∈ B_M} e_a (t)|²`. -/
theorem sum_fejerBox_mFourier_sub (M : ℕ) (t : ι → ℝ) :
    ∑ p ∈ fejerBox M ×ˢ fejerBox M, mFourier (p.1 - p.2) (ofPi t) =
      ((‖∑ a ∈ fejerBox M, mFourier a (ofPi t)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Finset.sum_product]
  have h : ∀ a b : ι → ℤ, mFourier (a - b) (ofPi t) =
      mFourier a (ofPi t) * conj (mFourier b (ofPi t)) := by
    intro a b; rw [sub_eq_add_neg, mFourier_add, mFourier_neg]
  simp_rw [h, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The Fejér mean is the convolution with the Fejér kernel:
`σ_M g (x) = ∫_{(0,1)^ι} K_M (x − y) g (y) dy`. -/
theorem fejerMean_eq_integral (M : ℕ) {g : (ι → ℝ) → ℂ} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (x : ι → ℝ) :
    fejerMean M g x = ∫ y in cube ι, (fejerKernel M (x - y) : ℂ) * g y := by
  have h1 : fejerMean M g x = ((#(fejerBox (ι := ι) M) : ℝ)⁻¹ : ℂ) *
      ∑ p ∈ fejerBox M ×ˢ fejerBox M,
        cubeFourierCoeff g (p.1 - p.2) * mFourier (p.1 - p.2) (ofPi x) := by
    rw [Finset.sum_comp (fun n => cubeFourierCoeff g n * mFourier n (ofPi x))
      (fun p : (ι → ℤ) × (ι → ℤ) => p.1 - p.2), fejerMean, fejerSupport, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [fejerWeight, fejerFiber, nsmul_eq_mul]
    push_cast
    ring
  have h2 : ∀ m : ι → ℤ, cubeFourierCoeff g m * mFourier m (ofPi x) =
      ∫ y in cube ι, mFourier m (ofPi (x - y)) * g y := by
    intro m
    rw [cubeFourierCoeff, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_cube fun y _ => ?_
    rw [sub_eq_add_neg, mFourier_ofPi_add, mFourier_ofPi_neg m y]
    ring
  have hint : ∀ m : ι → ℤ,
      IntegrableOn (fun y => mFourier m (ofPi (x - y)) * g y) (cube ι) := fun m =>
    integrableOn_cube_of_bound (((continuous_mFourier_ofPi m).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hg) (C := C) fun y => by
        rw [norm_mul, norm_mFourier_ofPi, one_mul]; exact hgC y
  rw [h1]
  simp_rw [h2]
  rw [← integral_finsetSum _ fun p _ => hint _, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_cube fun y _ => ?_
  rw [← Finset.sum_mul, sum_fejerBox_mFourier_sub, fejerKernel]
  push_cast
  ring

omit [DecidableEq ι] in
theorem cubeFourierCoeff_one (n : ι → ℤ) :
    cubeFourierCoeff (fun _ => (1 : ℂ)) n = if n = 0 then 1 else 0 := by
  rw [cubeFourierCoeff]
  simp only [mul_one]
  rw [integral_cube_mFourier]
  simp only [neg_eq_zero]

/-- The Fejér kernel has mean one. -/
theorem integral_fejerKernel {M : ℕ} (hM : (#(fejerBox (ι := ι) M) : ℝ) ≠ 0) (x : ι → ℝ) :
    ∫ y in cube ι, fejerKernel M (x - y) = 1 := by
  have h := fejerMean_eq_integral M (g := fun _ => (1 : ℂ)) aestronglyMeasurable_const (C := 1)
    (fun _ => by simp) x
  simp only [mul_one] at h
  rw [integral_complex_ofReal] at h
  have h1 : fejerMean M (fun _ => (1 : ℂ)) x = 1 := by
    rw [fejerMean, Finset.sum_eq_single 0]
    · rw [fejerWeight_zero hM, cubeFourierCoeff_one, mFourier_zero]; simp
    · intro n _ hn
      rw [cubeFourierCoeff_one]; simp [hn]
    · intro h; exact absurd (zero_mem_fejerSupport hM) h
  rw [h1] at h
  exact_mod_cast h.symm

/-- The Fejér means of a bounded function are bounded by the same constant. -/
theorem norm_fejerMean_le (M : ℕ) {g : (ι → ℝ) → ℂ} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (x : ι → ℝ) : ‖fejerMean M g x‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hgC 0)
  by_cases hM : (#(fejerBox (ι := ι) M) : ℝ) = 0
  · have : fejerMean M g x = 0 := by
      unfold fejerMean
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [fejerWeight, hM, div_zero]; simp
    rw [this, norm_zero]; exact hC
  have hK : Continuous fun y => fejerKernel M (x - y) :=
    (continuous_fejerKernel M).comp (continuous_const.sub continuous_id)
  rw [fejerMean_eq_integral M hg hgC x]
  calc ‖∫ y in cube ι, (fejerKernel M (x - y) : ℂ) * g y‖
      ≤ ∫ y in cube ι, ‖(fejerKernel M (x - y) : ℂ) * g y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in cube ι, fejerKernel M (x - y) * C := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_cube fun y _ => ?_
        · refine (integrableOn_cube_of_bound ((Complex.continuous_ofReal.comp
            hK).aestronglyMeasurable.mul hg) (C := #(fejerBox (ι := ι) M) * C) fun y => ?_).norm
          show ‖(fejerKernel M (x - y) : ℂ) * g y‖ ≤ _
          rw [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (fejerKernel_nonneg _ _)]
          exact mul_le_mul (fejerKernel_le _ _) (hgC y) (norm_nonneg _) (Nat.cast_nonneg _)
        · exact integrableOn_cube_of_continuous (hK.mul continuous_const)
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg _ _)]
          exact mul_le_mul_of_nonneg_left (hgC y) (fejerKernel_nonneg _ _)
    _ = C := by rw [integral_mul_const, integral_fejerKernel hM x, one_mul]

theorem continuous_fejerMean (M : ℕ) (g : (ι → ℝ) → ℂ) : Continuous (fejerMean M g) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_mFourier_ofPi n)

theorem fejerMean_isPeriodic (M : ℕ) (g : (ι → ℝ) → ℂ) : IsPeriodic (fejerMean M g) := by
  intro x k
  simp only [fejerMean, ofPi_add_int]

theorem cubeFourierCoeff_fejerMean (M : ℕ) (g : (ι → ℝ) → ℂ) (n : ι → ℤ) :
    cubeFourierCoeff (fejerMean M g) n = fejerWeight M n * cubeFourierCoeff g n := by
  have h := cubeFourierCoeff_trig (fejerSupport M)
    (fun m => (fejerWeight M m : ℂ) * cubeFourierCoeff g m) n
  rw [show fejerMean M g = fun x => ∑ m ∈ fejerSupport M,
    ((fejerWeight M m : ℂ) * cubeFourierCoeff g m) * mFourier m (ofPi x) from rfl, h]
  split_ifs with hn
  · rfl
  · rw [fejerWeight_eq_zero hn]; simp

/-- The Fejér means of a bounded measurable periodic `g` converge to `g` in `L²` of the cube:
`‖σ_M g − g‖²_{L²} = Σ_n (1 − λ_M (n))² |ĝ (n)|² → 0` (Parseval and dominated convergence). -/
theorem tendsto_integral_norm_fejerMean_sub_sq {g : (ι → ℝ) → ℂ} (hgm : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (hg : IsPeriodic g) :
    Tendsto (fun M => ∫ x in cube ι, ‖fejerMean M g x - g x‖ ^ 2) atTop (𝓝 0) := by
  have hcoef : ∀ M n, cubeFourierCoeff (fun x => fejerMean M g x - g x) n =
      ((fejerWeight M n : ℂ) - 1) * cubeFourierCoeff g n := by
    intro M n
    rw [cubeFourierCoeff_sub (continuous_fejerMean M g).aestronglyMeasurable
      (norm_fejerMean_le M hgm.aestronglyMeasurable hgC) hgm.aestronglyMeasurable hgC,
      cubeFourierCoeff_fejerMean]
    ring
  have hM : ∀ M, HasSum (fun n => ‖((fejerWeight M n : ℂ) - 1) * cubeFourierCoeff g n‖ ^ 2)
      (∫ x in cube ι, ‖fejerMean M g x - g x‖ ^ 2) := by
    intro M
    have hper : IsPeriodic fun x => fejerMean M g x - g x := fun x k => by
      simp only [fejerMean_isPeriodic M g x k, hg x k]
    have := hasSum_sq_cubeFourierCoeff (g := fun x => fejerMean M g x - g x)
      ((continuous_fejerMean M g).measurable.sub hgm)
      (C := C + C) (fun x => (norm_sub_le _ _).trans
        (add_le_add (norm_fejerMean_le M hgm.aestronglyMeasurable hgC x) (hgC x))) hper
    simpa only [hcoef] using this
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun M n => ‖((fejerWeight M n : ℂ) - 1) * cubeFourierCoeff g n‖ ^ 2)
    (g := fun _ => 0) (bound := fun n => ‖cubeFourierCoeff g n‖ ^ 2)
    (hasSum_sq_cubeFourierCoeff hgm hgC hg).summable ?_ ?_
  · simp only [tsum_zero] at hlim
    exact hlim.congr fun M => (hM M).tsum_eq
  · intro n
    have h1 : Tendsto (fun M => ((fejerWeight M n : ℂ) - 1) * cubeFourierCoeff g n) atTop
        (𝓝 ((((1 : ℝ) : ℂ) - 1) * cubeFourierCoeff g n)) :=
      (((Complex.continuous_ofReal.tendsto _).comp (tendsto_fejerWeight n)).sub_const
        1).mul_const _
    have h2 := (h1.norm).pow 2
    simpa using h2
  · refine Eventually.of_forall fun M n => ?_
    rw [norm_pow, norm_norm, norm_mul, mul_pow]
    have h1 : ‖(fejerWeight M n : ℂ) - 1‖ ≤ 1 := by
      rw [show (fejerWeight M n : ℂ) - 1 = ((fejerWeight M n - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [fejerWeight_nonneg M n, fejerWeight_le_one M n]
    have h2 : ‖(fejerWeight M n : ℂ) - 1‖ ^ 2 ≤ 1 := by
      rw [show (1 : ℝ) = 1 ^ 2 by norm_num]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ‖(fejerWeight M n : ℂ) - 1‖ ^ 2 * ‖cubeFourierCoeff g n‖ ^ 2
        ≤ 1 * ‖cubeFourierCoeff g n‖ ^ 2 := by gcongr
      _ = _ := one_mul _

end Fejer

end UnitAddTorus
