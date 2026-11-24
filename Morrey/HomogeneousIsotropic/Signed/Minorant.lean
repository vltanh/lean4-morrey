module

public import Morrey.HomogeneousIsotropic.Signed.RestrictedSupport
public import Morrey.HomogeneousIsotropic.Signed.Path
public import Morrey.Common.Basic.Analysis.Calculus.Deriv.MeanValue
public import Morrey.Common.Basic.Topology.Order.SelfImproving
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The radial minorant at a hard base

Let `Φ` be a profile of degree `p > 1`, `p ≠ 2`, with `h (−1) < 0` for its slice `h`, and let
`(t₀, m₀)` be a hard base with the restricted support `q₀ = α₀ + v₀ r + c₀ (x² − y²)`.

Along a path of hard bases (`IsPath`) on which the scale `S` grows from `1` to `R`, with slopes
`m = m₀ − e ξ`, base points `T`, intercepts `k` and determinant coefficients `c`, put
`M = S^{p−1} m` (`pathSlope`) and `f = e S^{p−2} c` (`pathDet`).

* `IsPath.hasDerivAt_pathSlope`: `M' = e f S'`.
* `IsPath.monotoneOn_pathDet`: `f` is nondecreasing. The monotonicity of the supporting planes
  (`IsHardBase.scaled_monotone`) gives, for two points of the path,
  `(f₂ − f₁) (S₂ − S₁) W ≥ 2 (r₂ − r₁) (e (M₂ − M₁) − f₁ (S₂ − S₁))` with `r = S (1 − e T)/2`
  and `W = S₂ + e S₁ T₁ > 0`, a self-improving inequality
  (`monotoneOn_of_forall_sub_le_half`).
* `pathEnvelope`: the upper envelope `N` of the lines `s ↦ e M + f (s − S)`. It is convex
  (`IsPath.convexOn_pathEnvelope`), equals `e M` at `S` (`IsPath.pathEnvelope_scale`), and is
  `e c₀ s − v₀/2` for `s ≤ 1` (`IsPath.pathEnvelope_of_le_one`).
* `IsPath.scale_mul_pathSlope_sub_integral`: `α₀ + S N (S) − 2 ∫₀^S N = S^p k` along the path.
* `IsPath.exists_convex_minorant`: the function
  `G = α₀ + (x + y + e (x − y)) N (x + y) − 2 ∫₀^{x+y} N` is `q₀` for `x + y ≤ 1`, and on the
  segment `x + y = S` it is `S^p (k + m (x − y)/S)`, the supporting line of slope `m` of the
  slice: so `G ≤ Φ` for `x + y ≤ R`, with equality at the base point.
* `IsHardBase.exists_convex_minorant`: hence, if the slice is strictly convex, for every hard
  base and every `R ≥ 1` there is such an `N`.

Two general facts are used (`Morrey/Common/Basic/Analysis/Calculus/Deriv/MeanValue.lean`):
`apply_le_apply_of_hasDerivAt_nonneg` and `apply_eq_apply_of_hasDerivAt_zero`, for a function
with a nonnegative, respectively zero, derivative at every point of `[a, b]`.
-/

@[expose] public section

open Set

namespace HomogeneousIsotropic

/-! ### The algebra of the path -/

/-- The identity behind `M' = e f S'`, with `D = 1 + e T` and `gd = p k − e (p − 2) m`. -/
theorem pathSlope_deriv_identity {e : ℝ} (he : e = 1 ∨ e = -1) {p H m T S P D gd : ℝ}
    (hD : D ≠ 0) (hg : gd ≠ 0) (hDdef : D = 1 + e * T)
    (hgdef : gd = p * (H - m * T) - e * (p - 2) * m) :
    -(S * D) / gd * (p - 1) * P * m + P * S * -e =
      e * (e * (P * ((e * p * H + (1 - e * T) * m) / D))) * (-(S * D) / gd) := by
  field_simp
  subst hDdef hgdef
  rcases he with rfl | rfl <;> ring

/-- The identity behind `(S^p k)' = e (S M' − M S')`, with `D = 1 + e T` and
`gd = p k − e (p − 2) m`. -/
theorem scale_rpow_mul_deriv_identity {e : ℝ} (he : e = 1 ∨ e = -1) {p H m T S P D gd : ℝ}
    (hD : D ≠ 0) (hg : gd ≠ 0) (hDdef : D = 1 + e * T)
    (hgdef : gd = p * (H - m * T) - e * (p - 2) * m) :
    -(S * D) / gd * (e * (P * S * m)) +
        S * (e * (e * (e * (P * ((e * p * H + (1 - e * T) * m) / D))) * (-(S * D) / gd))) -
        2 * (e * (P * S * m) * (-(S * D) / gd)) -
        (-(S * D) / gd * p * (P * S) * (H - m * T) + P * S * S * (e * T)) = 0 := by
  field_simp
  subst hDdef hgdef
  rcases he with rfl | rfl <;> ring

/-- The monotonicity of the supporting planes at two points of a path, in terms of
`f = e S^{p−2} c` and `M = S^{p−1} m` (here `P = S^{p−2}`, and `v = 2 e (c − m)`). -/
theorem scaled_monotone_identity {e : ℝ} (he : e = 1 ∨ e = -1)
    (P₁ P₂ S₁ S₂ T₁ T₂ c₁ c₂ m₁ m₂ : ℝ) :
    (P₂ * S₂ * (e * (2 * (c₂ - m₂))) - P₁ * S₁ * (e * (2 * (c₁ - m₁)))) *
          (S₂ * (1 - e * T₂) / 2 - S₁ * (1 - e * T₁) / 2) +
        (P₂ * c₂ - P₁ * c₁) * (S₂ ^ 2 * T₂ - S₁ ^ 2 * T₁) =
      (e * (P₂ * c₂) - e * (P₁ * c₁)) * (S₂ - S₁) * (S₂ + e * S₁ * T₁) -
        2 * (e * (P₂ * S₂ * m₂ - P₁ * S₁ * m₁) - e * (P₁ * c₁) * (S₂ - S₁)) *
          (S₂ * (1 - e * T₂) / 2 - S₁ * (1 - e * T₁) / 2) := by
  rcases he with rfl | rfl <;> ring

/-! ### The functions of the path -/

/-- The slope at the scale `S` along a path, `M = S^{p−1} m` with `m = m₀ − e ξ`: on the segment
`x + y = S` the supporting line of slope `m` of the slice is `S^p k + M (x − y)`. -/
noncomputable def pathSlope (p e m₀ : ℝ) (S : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  S ξ ^ (p - 1) * (m₀ - e * ξ)

/-- The determinant coefficient at the scale `S` along a path, times `e`:
`f = e S^{p−2} c`, with `c` the determinant coefficient of the restricted support at the hard
base `(T ξ, m₀ − e ξ)`. -/
noncomputable def pathDet (p e : ℝ) (Φ : ℝ → ℝ → ℝ) (m₀ : ℝ) (T S : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  e * (S ξ ^ (p - 2) * supportDet p e (slice Φ (T ξ)) (m₀ - e * ξ) (T ξ))

/-- The upper envelope of the lines `s ↦ e M ξ + f ξ (s − S ξ)`, `ξ ∈ [0, L]`, of a path. -/
noncomputable def pathEnvelope (p e : ℝ) (Φ : ℝ → ℝ → ℝ) (m₀ L : ℝ) (T S : ℝ → ℝ) (s : ℝ) : ℝ :=
  sSup ((fun ξ => e * pathSlope p e m₀ S ξ + pathDet p e Φ m₀ T S ξ * (s - S ξ)) '' Icc 0 L)

variable {p e : ℝ} {Φ : ℝ → ℝ → ℝ} {t₀ m₀ L R : ℝ} {T k S : ℝ → ℝ}

namespace IsPath

/-- Along a path the supporting line is negative at `−a`. -/
theorem denom_neg (hpath : IsPath p e Φ t₀ m₀ L R T k S) {ξ : ℝ} (hξ : ξ ∈ Icc 0 L) :
    p * k ξ - e * (p - 2) * (m₀ - e * ξ) < 0 := by
  rw [hpath.intercept ξ hξ]
  exact (hpath.hard ξ hξ).neg

/-- The starting point of a path is a hard base. -/
theorem hard_zero (hpath : IsPath p e Φ t₀ m₀ L R T k S) : IsHardBase p e Φ t₀ m₀ := by
  have h := hpath.hard 0 (left_mem_Icc.2 hpath.length_nonneg)
  rwa [hpath.base_zero, mul_zero, sub_zero] at h

/-- The scale of a path is differentiable. -/
theorem hasDerivAt_scale' (hpath : IsPath p e Φ t₀ m₀ L R T k S) {ξ : ℝ} (hξ : ξ ∈ Icc 0 L) :
    HasDerivAt S (deriv S ξ) ξ :=
  (hpath.hasDerivAt_scale ξ hξ).differentiableAt.hasDerivAt

/-- The scale of a path has a positive derivative. -/
theorem deriv_scale_pos (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S) {ξ : ℝ}
    (hξ : ξ ∈ Icc 0 L) : 0 < deriv S ξ := by
  rw [(hpath.hasDerivAt_scale ξ hξ).deriv]
  exact div_pos_of_neg_of_neg
    (neg_neg_of_pos (mul_pos (hpath.scale_pos ξ hξ) ((hpath.hard ξ hξ).one_add_pos he)))
    (hpath.denom_neg hξ)

/-- The scale of a path is continuous. -/
theorem continuousOn_scale (hpath : IsPath p e Φ t₀ m₀ L R T k S) : ContinuousOn S (Icc 0 L) :=
  fun ξ hξ => (hpath.hasDerivAt_scale ξ hξ).continuousAt.continuousWithinAt

/-- The scale of a path is increasing. -/
theorem strictMonoOn_scale (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S) :
    StrictMonoOn S (Icc 0 L) :=
  strictMonoOn_of_deriv_pos (convex_Icc 0 L) hpath.continuousOn_scale fun _ hξ =>
    hpath.deriv_scale_pos he (interior_subset hξ)

/-- The scale of a path is at least `1`. -/
theorem one_le_scale (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S) {ξ : ℝ}
    (hξ : ξ ∈ Icc 0 L) : 1 ≤ S ξ := by
  rw [← hpath.scale_zero]
  exact (hpath.strictMonoOn_scale he).monotoneOn (left_mem_Icc.2 hpath.length_nonneg) hξ hξ.1

/-- `M = S^{p−1} m` at the start of a path. -/
theorem pathSlope_zero (hpath : IsPath p e Φ t₀ m₀ L R T k S) : pathSlope p e m₀ S 0 = m₀ := by
  simp [pathSlope, hpath.scale_zero]

/-- `f = e S^{p−2} c` at the start of a path. -/
theorem pathDet_zero (hpath : IsPath p e Φ t₀ m₀ L R T k S) :
    pathDet p e Φ m₀ T S 0 = e * supportDet p e (slice Φ t₀) m₀ t₀ := by
  simp [pathDet, hpath.scale_zero, hpath.base_zero]

/-- `M = S^{p−1} m` is continuous along a path. -/
theorem continuousOn_pathSlope (hpath : IsPath p e Φ t₀ m₀ L R T k S) :
    ContinuousOn (pathSlope p e m₀ S) (Icc 0 L) :=
  (hpath.continuousOn_scale.rpow_const fun ξ hξ => Or.inl (hpath.scale_pos ξ hξ).ne').mul
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn

/-- `M' = e f S'`: the derivative of `M = S^{p−1} m` along a path. -/
theorem hasDerivAt_pathSlope (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S)
    {ξ : ℝ} (hξ : ξ ∈ Icc 0 L) :
    HasDerivAt (pathSlope p e m₀ S) (e * pathDet p e Φ m₀ T S ξ * deriv S ξ) ξ := by
  have hS := hpath.hasDerivAt_scale' hξ
  have hSpos := hpath.scale_pos ξ hξ
  have hD := ((hpath.hard ξ hξ).one_add_pos he).ne'
  have hg := (hpath.denom_neg hξ).ne
  have hm : HasDerivAt (fun x : ℝ => m₀ - e * x) (-e) ξ := by
    simpa using ((hasDerivAt_id ξ).const_mul e).const_sub m₀
  have h : HasDerivAt (pathSlope p e m₀ S)
      (deriv S ξ * (p - 1) * S ξ ^ (p - 1 - 1) * (m₀ - e * ξ) + S ξ ^ (p - 1) * -e) ξ :=
    (hS.rpow_const (p := p - 1) (Or.inl hSpos.ne')).mul hm
  have e1 : S ξ ^ (p - 1 - 1) = S ξ ^ (p - 2) := by
    congr 1
    ring
  have e2 : S ξ ^ (p - 1) = S ξ ^ (p - 2) * S ξ := by
    rw [← Real.rpow_add_one hSpos.ne']
    congr 1
    ring
  have hf : pathDet p e Φ m₀ T S ξ = e * (S ξ ^ (p - 2) *
      ((e * p * slice Φ (T ξ) + (1 - e * T ξ) * (m₀ - e * ξ)) / (1 + e * T ξ))) := rfl
  refine h.congr_deriv ?_
  rw [e1, e2, hf, (hpath.hasDerivAt_scale ξ hξ).deriv]
  exact pathSlope_deriv_identity he hD hg rfl (by rw [hpath.intercept ξ hξ])

/-- `f = e S^{p−2} c` is continuous along a path. -/
theorem continuousOn_pathDet (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S) :
    ContinuousOn (pathDet p e Φ m₀ T S) (Icc 0 L) := by
  have hS := hpath.continuousOn_scale
  have hT := hpath.continuousOn_base
  have hk : ContinuousOn k (Icc 0 L) := fun ξ hξ =>
    (hpath.hasDerivAt_intercept ξ hξ).continuousAt.continuousWithinAt
  have hm : ContinuousOn (fun ξ : ℝ => m₀ - e * ξ) (Icc 0 L) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  have hP : ContinuousOn (fun ξ => S ξ ^ (p - 2)) (Icc 0 L) :=
    hS.rpow_const fun ξ hξ => Or.inl (hpath.scale_pos ξ hξ).ne'
  have hc : ContinuousOn (fun ξ => (e * p * (k ξ + (m₀ - e * ξ) * T ξ) +
      (1 - e * T ξ) * (m₀ - e * ξ)) / (1 + e * T ξ)) (Icc 0 L) :=
    ((continuousOn_const.mul (hk.add (hm.mul hT))).add
      ((continuousOn_const.sub (continuousOn_const.mul hT)).mul hm)).div
      (continuousOn_const.add (continuousOn_const.mul hT))
      fun ξ hξ => ((hpath.hard ξ hξ).one_add_pos he).ne'
  have h : ContinuousOn (fun ξ => e * (S ξ ^ (p - 2) * ((e * p * (k ξ + (m₀ - e * ξ) * T ξ) +
      (1 - e * T ξ) * (m₀ - e * ξ)) / (1 + e * T ξ)))) (Icc 0 L) :=
    continuousOn_const.mul (hP.mul hc)
  refine h.congr fun ξ hξ => ?_
  simp only [pathDet, supportDet, hpath.intercept ξ hξ, sub_add_cancel]

/-- **`f = e S^{p−2} c` is nondecreasing along a path.** For two points `x < y` of the path, the
monotonicity of the supporting planes reads
`(f y − f x) (S y − S x) W ≥ 2 (r y − r x) Y`, where `W = S y + e S x T x ≥ 1 − max |T| > 0`,
`r = S (1 − e T)/2` and `Y = e (M y − M x) − f x (S y − S x)`; and `|Y| ≤ D (S y − S x)` if
`|f − f x| ≤ D` on `[x, y]`, since `M' = e f S'`. For `y − x` small, `|r y − r x|` is small, and
the inequality improves itself. -/
theorem monotoneOn_pathDet (hΦ : IsProfile p Φ) (hp : 1 < p) (he : e = 1 ∨ e = -1)
    (hpe : 0 < e * (p - 2)) (hor : slice Φ (-1) < 0) (hpath : IsPath p e Φ t₀ m₀ L R T k S) :
    MonotoneOn (pathDet p e Φ m₀ T S) (Icc 0 L) := by
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  -- a positive lower bound for `1 − |T|`
  obtain ⟨ξm, hξm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hpath.length_nonneg)
    hpath.continuousOn_base.abs
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : ℝ, W₀ = 1 - |T ξm| := ⟨_, rfl⟩
  have hW₀pos : 0 < W₀ := by
    rw [hW₀]
    linarith [(hpath.hard ξm hξm).abs_lt]
  have hTle : ∀ ξ ∈ Icc 0 L, |T ξ| ≤ 1 - W₀ := fun ξ hξ => by
    have h : |T ξ| ≤ |T ξm| := hmax hξ
    rw [hW₀]
    linarith
  -- the uniform continuity of `r = S (1 − e T)/2`
  have hr : ContinuousOn (fun ξ => S ξ * (1 - e * T ξ) / 2) (Icc 0 L) :=
    (hpath.continuousOn_scale.mul
      (continuousOn_const.sub (continuousOn_const.mul hpath.continuousOn_base))).div_const 2
  obtain ⟨δ, hδ, hδr⟩ := Metric.uniformContinuousOn_iff_le.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hr) (W₀ / 4) (by positivity)
  refine monotoneOn_of_forall_sub_le_half hδ (hpath.continuousOn_pathDet he)
    fun x hx y hy hxy hyx D hD => ?_
  have hSx := hpath.scale_pos x hx
  have hSy := hpath.scale_pos y hy
  have hbx := hpath.hard x hx
  have hby := hpath.hard y hy
  have hD0 : 0 ≤ D := by
    have h := hD x (left_mem_Icc.2 hxy.le)
    rwa [sub_self, abs_zero] at h
  -- the monotonicity of the supporting planes
  have hmon := IsHardBase.scaled_monotone hΦ hp he hpe hor hbx hby hSx hSy
  have hvx : supportMod p e (slice Φ (T x)) (m₀ - e * x) (T x) =
      e * (2 * (supportDet p e (slice Φ (T x)) (m₀ - e * x) (T x) - (m₀ - e * x))) := by
    have h := supportDet_sub (p := p) (H := slice Φ (T x)) (m := m₀ - e * x)
      (hbx.one_add_pos he).ne'
    linear_combination (-2 * e) * h -
      supportMod p e (slice Φ (T x)) (m₀ - e * x) (T x) * hee
  have hvy : supportMod p e (slice Φ (T y)) (m₀ - e * y) (T y) =
      e * (2 * (supportDet p e (slice Φ (T y)) (m₀ - e * y) (T y) - (m₀ - e * y))) := by
    have h := supportDet_sub (p := p) (H := slice Φ (T y)) (m := m₀ - e * y)
      (hby.one_add_pos he).ne'
    linear_combination (-2 * e) * h -
      supportMod p e (slice Φ (T y)) (m₀ - e * y) (T y) * hee
  have ePx : S x ^ (p - 1) = S x ^ (p - 2) * S x := by
    rw [← Real.rpow_add_one hSx.ne']
    congr 1
    ring
  have ePy : S y ^ (p - 1) = S y ^ (p - 2) * S y := by
    rw [← Real.rpow_add_one hSy.ne']
    congr 1
    ring
  have hkey := scaled_monotone_identity he (S x ^ (p - 2)) (S y ^ (p - 2)) (S x) (S y) (T x)
    (T y) (supportDet p e (slice Φ (T x)) (m₀ - e * x) (T x))
    (supportDet p e (slice Φ (T y)) (m₀ - e * y) (T y)) (m₀ - e * x) (m₀ - e * y)
  rw [hvx, hvy, ePx, ePy, hkey] at hmon
  have hfx : pathDet p e Φ m₀ T S x =
      e * (S x ^ (p - 2) * supportDet p e (slice Φ (T x)) (m₀ - e * x) (T x)) := rfl
  have hfy : pathDet p e Φ m₀ T S y =
      e * (S y ^ (p - 2) * supportDet p e (slice Φ (T y)) (m₀ - e * y) (T y)) := rfl
  have hMx : pathSlope p e m₀ S x = S x ^ (p - 2) * S x * (m₀ - e * x) := by
    rw [pathSlope, ePx]
  have hMy : pathSlope p e m₀ S y = S y ^ (p - 2) * S y * (m₀ - e * y) := by
    rw [pathSlope, ePy]
  rw [← hfx, ← hfy, ← hMx, ← hMy] at hmon
  -- the bound for `Y = e (M y − M x) − f x (S y − S x)`
  have hsub : ∀ ζ ∈ Icc x y, ζ ∈ Icc 0 L := fun ζ hζ => ⟨hx.1.trans hζ.1, hζ.2.trans hy.2⟩
  have hYle : e * (pathSlope p e m₀ S y - pathSlope p e m₀ S x) -
      pathDet p e Φ m₀ T S x * (S y - S x) ≤ D * (S y - S x) := by
    have h := apply_le_apply_of_hasDerivAt_nonneg
      (g := fun ζ => D * S ζ - (e * pathSlope p e m₀ S ζ - pathDet p e Φ m₀ T S x * S ζ))
      (g' := fun ζ => (D - (pathDet p e Φ m₀ T S ζ - pathDet p e Φ m₀ T S x)) * deriv S ζ)
      hxy.le (fun ζ hζ => by
        have hS := hpath.hasDerivAt_scale' (hsub ζ hζ)
        have hM := hpath.hasDerivAt_pathSlope he (hsub ζ hζ)
        refine ((hS.const_mul D).sub ((hM.const_mul e).sub
          (hS.const_mul (pathDet p e Φ m₀ T S x)))).congr_deriv ?_
        linear_combination (-(pathDet p e Φ m₀ T S ζ * deriv S ζ)) * hee)
      (fun ζ hζ => mul_nonneg (by linarith [(abs_le.1 (hD ζ hζ)).2])
        (hpath.deriv_scale_pos he (hsub ζ hζ)).le)
    linarith
  have hYge : -(D * (S y - S x)) ≤ e * (pathSlope p e m₀ S y - pathSlope p e m₀ S x) -
      pathDet p e Φ m₀ T S x * (S y - S x) := by
    have h := apply_le_apply_of_hasDerivAt_nonneg
      (g := fun ζ => D * S ζ + (e * pathSlope p e m₀ S ζ - pathDet p e Φ m₀ T S x * S ζ))
      (g' := fun ζ => (D + (pathDet p e Φ m₀ T S ζ - pathDet p e Φ m₀ T S x)) * deriv S ζ)
      hxy.le (fun ζ hζ => by
        have hS := hpath.hasDerivAt_scale' (hsub ζ hζ)
        have hM := hpath.hasDerivAt_pathSlope he (hsub ζ hζ)
        refine ((hS.const_mul D).add ((hM.const_mul e).sub
          (hS.const_mul (pathDet p e Φ m₀ T S x)))).congr_deriv ?_
        linear_combination (pathDet p e Φ m₀ T S ζ * deriv S ζ) * hee)
      (fun ζ hζ => mul_nonneg (by linarith [(abs_le.1 (hD ζ hζ)).1])
        (hpath.deriv_scale_pos he (hsub ζ hζ)).le)
    linarith
  have hYabs : |e * (pathSlope p e m₀ S y - pathSlope p e m₀ S x) -
      pathDet p e Φ m₀ T S x * (S y - S x)| ≤ D * (S y - S x) := abs_le.2 ⟨hYge, hYle⟩
  -- the bound for `r y − r x`
  have hrabs : |S y * (1 - e * T y) / 2 - S x * (1 - e * T x) / 2| ≤ W₀ / 4 := by
    have h := hδr x hx y hy (by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 hxy)]
      exact hyx)
    rwa [Real.dist_eq, abs_sub_comm] at h
  -- the lower bound for `W = S y + e S x T x`
  have hSxy : S x < S y := hpath.strictMonoOn_scale he hx hy hxy
  have hS1 : 1 ≤ S x := hpath.one_le_scale he hx
  have hW : W₀ ≤ S y + e * S x * T x := by
    have h1 : -|T x| ≤ e * T x := by
      rcases he with rfl | rfl
      · linarith [neg_abs_le (T x)]
      · linarith [le_abs_self (T x)]
    have h2 := hTle x hx
    have h3 : S x * (-(1 - W₀)) ≤ S x * (e * T x) :=
      mul_le_mul_of_nonneg_left (by linarith) hSx.le
    have h4 : W₀ ≤ S x * W₀ := le_mul_of_one_le_left hW₀pos.le hS1
    linarith
  -- the self-improving inequality
  have h3 : -(D * (S y - S x) * (W₀ / 4)) ≤
      (e * (pathSlope p e m₀ S y - pathSlope p e m₀ S x) -
        pathDet p e Φ m₀ T S x * (S y - S x)) *
      (S y * (1 - e * T y) / 2 - S x * (1 - e * T x) / 2) := by
    have h : |(e * (pathSlope p e m₀ S y - pathSlope p e m₀ S x) -
        pathDet p e Φ m₀ T S x * (S y - S x)) *
        (S y * (1 - e * T y) / 2 - S x * (1 - e * T x) / 2)| ≤ D * (S y - S x) * (W₀ / 4) := by
      rw [abs_mul]
      exact mul_le_mul hYabs hrabs (abs_nonneg _) (mul_nonneg hD0 (by linarith))
    exact (abs_le.1 h).1
  have h4 : 0 ≤ (S y - S x) * ((pathDet p e Φ m₀ T S y - pathDet p e Φ m₀ T S x) *
      (S y + e * S x * T x) + D * W₀ / 2) := by
    linarith
  have h5 : 0 ≤ (pathDet p e Φ m₀ T S y - pathDet p e Φ m₀ T S x) * (S y + e * S x * T x) +
      D * W₀ / 2 := nonneg_of_mul_nonneg_right h4 (sub_pos.2 hSxy)
  by_contra hcon
  have hneg : pathDet p e Φ m₀ T S y - pathDet p e Φ m₀ T S x < -(D / 2) := by
    linarith [not_le.1 hcon]
  have h6 : (pathDet p e Φ m₀ T S y - pathDet p e Φ m₀ T S x) * (S y + e * S x * T x) ≤
      (pathDet p e Φ m₀ T S y - pathDet p e Φ m₀ T S x) * W₀ :=
    mul_le_mul_of_nonpos_left hW (by linarith)
  have h7 : (pathDet p e Φ m₀ T S y - pathDet p e Φ m₀ T S x + D / 2) * W₀ < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hW₀pos
  linarith

/-- **The tangent inequality.** Since `M' = e f S'` with `f` nondecreasing and `S` increasing,
the line `s ↦ e M ξ' + f ξ' (s − S ξ')` lies below `e M ξ` at `s = S ξ`. -/
theorem pathSlope_add_le (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S)
    (hmono : MonotoneOn (pathDet p e Φ m₀ T S) (Icc 0 L)) {ξ ξ' : ℝ} (hξ : ξ ∈ Icc 0 L)
    (hξ' : ξ' ∈ Icc 0 L) :
    e * pathSlope p e m₀ S ξ' + pathDet p e Φ m₀ T S ξ' * (S ξ - S ξ') ≤
      e * pathSlope p e m₀ S ξ := by
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have hder : ∀ ζ ∈ Icc 0 L,
      HasDerivAt (fun ζ => e * pathSlope p e m₀ S ζ - pathDet p e Φ m₀ T S ξ' * S ζ)
        ((pathDet p e Φ m₀ T S ζ - pathDet p e Φ m₀ T S ξ') * deriv S ζ) ζ := by
    intro ζ hζ
    refine (((hpath.hasDerivAt_pathSlope he hζ).const_mul e).sub
      ((hpath.hasDerivAt_scale' hζ).const_mul (pathDet p e Φ m₀ T S ξ'))).congr_deriv ?_
    linear_combination (pathDet p e Φ m₀ T S ζ * deriv S ζ) * hee
  rcases le_total ξ' ξ with h | h
  · have hsub : ∀ ζ ∈ Icc ξ' ξ, ζ ∈ Icc 0 L := fun ζ hζ =>
      ⟨hξ'.1.trans hζ.1, hζ.2.trans hξ.2⟩
    have h1 := apply_le_apply_of_hasDerivAt_nonneg h (fun ζ hζ => hder ζ (hsub ζ hζ))
      (fun ζ hζ => mul_nonneg (sub_nonneg.2 (hmono hξ' (hsub ζ hζ) hζ.1))
        (hpath.deriv_scale_pos he (hsub ζ hζ)).le)
    linarith
  · have hsub : ∀ ζ ∈ Icc ξ ξ', ζ ∈ Icc 0 L := fun ζ hζ =>
      ⟨hξ.1.trans hζ.1, hζ.2.trans hξ'.2⟩
    have h1 := apply_le_apply_of_hasDerivAt_nonneg
      (g := fun ζ => -(e * pathSlope p e m₀ S ζ - pathDet p e Φ m₀ T S ξ' * S ζ))
      (g' := fun ζ => -((pathDet p e Φ m₀ T S ζ - pathDet p e Φ m₀ T S ξ') * deriv S ζ)) h
      (fun ζ hζ => (hder ζ (hsub ζ hζ)).neg)
      (fun ζ hζ => by
        have h2 := mul_nonneg (sub_nonneg.2 (hmono (hsub ζ hζ) hξ' hζ.2))
          (hpath.deriv_scale_pos he (hsub ζ hζ)).le
        linarith)
    linarith

/-! ### The upper envelope -/

/-- The lines of a path are bounded above at every point. -/
theorem bddAbove_pathEnvelope (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S)
    (s : ℝ) : BddAbove ((fun ξ => e * pathSlope p e m₀ S ξ +
      pathDet p e Φ m₀ T S ξ * (s - S ξ)) '' Icc 0 L) :=
  isCompact_Icc.bddAbove_image ((continuousOn_const.mul hpath.continuousOn_pathSlope).add
    ((hpath.continuousOn_pathDet he).mul (continuousOn_const.sub hpath.continuousOn_scale)))

/-- Every line of a path lies below the upper envelope. -/
theorem le_pathEnvelope (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S) {ξ : ℝ}
    (hξ : ξ ∈ Icc 0 L) (s : ℝ) :
    e * pathSlope p e m₀ S ξ + pathDet p e Φ m₀ T S ξ * (s - S ξ) ≤
      pathEnvelope p e Φ m₀ L T S s :=
  le_csSup (hpath.bddAbove_pathEnvelope he s) ⟨ξ, hξ, rfl⟩

/-- A bound for all the lines of a path is a bound for the upper envelope. -/
theorem pathEnvelope_le (hpath : IsPath p e Φ t₀ m₀ L R T k S) {s B : ℝ}
    (h : ∀ ξ ∈ Icc 0 L, e * pathSlope p e m₀ S ξ + pathDet p e Φ m₀ T S ξ * (s - S ξ) ≤ B) :
    pathEnvelope p e Φ m₀ L T S s ≤ B := by
  refine csSup_le ⟨_, 0, left_mem_Icc.2 hpath.length_nonneg, rfl⟩ ?_
  rintro _ ⟨ξ, hξ, rfl⟩
  exact h ξ hξ

/-- The upper envelope of the lines of a path is convex. -/
theorem convexOn_pathEnvelope (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S) :
    ConvexOn ℝ univ (pathEnvelope p e Φ m₀ L T S) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => hpath.pathEnvelope_le fun ξ hξ => ?_⟩
  have h1 := mul_le_mul_of_nonneg_left (hpath.le_pathEnvelope he hξ x) ha
  have h2 := mul_le_mul_of_nonneg_left (hpath.le_pathEnvelope he hξ y) hb
  simp only [smul_eq_mul]
  have e1 : e * pathSlope p e m₀ S ξ + pathDet p e Φ m₀ T S ξ * (a * x + b * y - S ξ) =
      a * (e * pathSlope p e m₀ S ξ + pathDet p e Φ m₀ T S ξ * (x - S ξ)) +
        b * (e * pathSlope p e m₀ S ξ + pathDet p e Φ m₀ T S ξ * (y - S ξ)) := by
    linear_combination (-(e * pathSlope p e m₀ S ξ - pathDet p e Φ m₀ T S ξ * S ξ)) * hab
  rw [e1]
  exact add_le_add h1 h2

/-- The upper envelope is `e M` at the scale `S`. -/
theorem pathEnvelope_scale (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S)
    (hmono : MonotoneOn (pathDet p e Φ m₀ T S) (Icc 0 L)) {ξ : ℝ} (hξ : ξ ∈ Icc 0 L) :
    pathEnvelope p e Φ m₀ L T S (S ξ) = e * pathSlope p e m₀ S ξ := by
  refine le_antisymm (hpath.pathEnvelope_le fun ξ' hξ' => hpath.pathSlope_add_le he hmono hξ hξ')
    ?_
  have h := hpath.le_pathEnvelope he hξ (S ξ)
  rwa [sub_self, mul_zero, add_zero] at h

/-- The upper envelope is the first line, `e c₀ s − v₀/2`, for `s ≤ 1`. -/
theorem pathEnvelope_of_le_one (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S)
    (hmono : MonotoneOn (pathDet p e Φ m₀ T S) (Icc 0 L)) {s : ℝ} (hs : s ≤ 1) :
    pathEnvelope p e Φ m₀ L T S s =
      e * supportDet p e (slice Φ t₀) m₀ t₀ * s - supportMod p e (slice Φ t₀) m₀ t₀ / 2 := by
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have h0 : (0 : ℝ) ∈ Icc 0 L := left_mem_Icc.2 hpath.length_nonneg
  have hsub := supportDet_sub (p := p) (H := slice Φ t₀) (m := m₀)
    (hpath.hard_zero.one_add_pos he).ne'
  have hval : e * m₀ + e * supportDet p e (slice Φ t₀) m₀ t₀ * (s - 1) =
      e * supportDet p e (slice Φ t₀) m₀ t₀ * s - supportMod p e (slice Φ t₀) m₀ t₀ / 2 := by
    linear_combination (-e) * hsub - (supportMod p e (slice Φ t₀) m₀ t₀ / 2) * hee
  refine le_antisymm (hpath.pathEnvelope_le fun ξ hξ => ?_) ?_
  · have h1 := hpath.pathSlope_add_le he hmono h0 hξ
    rw [hpath.scale_zero, hpath.pathSlope_zero] at h1
    have h2 : pathDet p e Φ m₀ T S 0 ≤ pathDet p e Φ m₀ T S ξ := hmono h0 hξ hξ.1
    have h3 := mul_le_mul_of_nonpos_right h2 (sub_nonpos.2 hs)
    rw [hpath.pathDet_zero] at h3
    linarith
  · have h := hpath.le_pathEnvelope he h0 s
    rw [hpath.pathSlope_zero, hpath.pathDet_zero, hpath.scale_zero] at h
    linarith

/-- The primitive of the upper envelope on `(−∞, 1]`. -/
theorem integral_pathEnvelope (he : e = 1 ∨ e = -1) (hpath : IsPath p e Φ t₀ m₀ L R T k S)
    (hmono : MonotoneOn (pathDet p e Φ m₀ T S) (Icc 0 L)) {σ : ℝ} (hσ : σ ≤ 1) :
    ∫ r in (0 : ℝ)..σ, pathEnvelope p e Φ m₀ L T S r =
      e * supportDet p e (slice Φ t₀) m₀ t₀ * σ ^ 2 / 2 -
        supportMod p e (slice Φ t₀) m₀ t₀ / 2 * σ := by
  have hcongr : ∫ r in (0 : ℝ)..σ, pathEnvelope p e Φ m₀ L T S r =
      ∫ r in (0 : ℝ)..σ, (e * supportDet p e (slice Φ t₀) m₀ t₀ * r -
        supportMod p e (slice Φ t₀) m₀ t₀ / 2) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    refine hpath.pathEnvelope_of_le_one he hmono ?_
    rcases le_total 0 σ with h | h
    · rw [uIcc_of_le h] at hr
      linarith [hr.2]
    · rw [uIcc_of_ge h] at hr
      linarith [hr.2]
  have hsplit : ∫ r in (0 : ℝ)..σ, (e * supportDet p e (slice Φ t₀) m₀ t₀ * r -
      supportMod p e (slice Φ t₀) m₀ t₀ / 2) =
      (∫ r in (0 : ℝ)..σ, e * supportDet p e (slice Φ t₀) m₀ t₀ * r) -
        ∫ _ in (0 : ℝ)..σ, supportMod p e (slice Φ t₀) m₀ t₀ / 2 :=
    intervalIntegral.integral_sub
      ((continuous_const.mul continuous_id).intervalIntegrable 0 σ) intervalIntegrable_const
  rw [hcongr, hsplit, intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- **The intercept at the scale `S`.** With `N` the upper envelope,
`α₀ + S N (S) − 2 ∫₀^S N = S^p k` along the path: the two sides have the same derivative, and
the same value at the start of the path. -/
theorem scale_mul_pathSlope_sub_integral (he : e = 1 ∨ e = -1)
    (hpath : IsPath p e Φ t₀ m₀ L R T k S)
    (hmono : MonotoneOn (pathDet p e Φ m₀ T S) (Icc 0 L)) {ξ : ℝ} (hξ : ξ ∈ Icc 0 L) :
    supportConst p e (slice Φ t₀) m₀ t₀ + S ξ * (e * pathSlope p e m₀ S ξ) -
      2 * ∫ r in (0 : ℝ)..S ξ, pathEnvelope p e Φ m₀ L T S r = S ξ ^ p * k ξ := by
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have hNc : Continuous (pathEnvelope p e Φ m₀ L T S) :=
    continuousOn_univ.1 ((hpath.convexOn_pathEnvelope he).continuousOn isOpen_univ)
  have h0 : (0 : ℝ) ∈ Icc 0 L := left_mem_Icc.2 hpath.length_nonneg
  -- the difference of the two sides has the derivative `0`
  have hJ : ∀ ζ ∈ Icc 0 L, HasDerivAt (fun ζ => supportConst p e (slice Φ t₀) m₀ t₀ +
      S ζ * (e * pathSlope p e m₀ S ζ) -
      2 * (∫ r in (0 : ℝ)..S ζ, pathEnvelope p e Φ m₀ L T S r) - S ζ ^ p * k ζ) 0 ζ := by
    intro ζ hζ
    have hS := hpath.hasDerivAt_scale' hζ
    have hSpos := hpath.scale_pos ζ hζ
    have hM := hpath.hasDerivAt_pathSlope he hζ
    have hk := hpath.hasDerivAt_intercept ζ hζ
    have hI : HasDerivAt (fun ζ => ∫ r in (0 : ℝ)..S ζ, pathEnvelope p e Φ m₀ L T S r)
        (pathEnvelope p e Φ m₀ L T S (S ζ) * deriv S ζ) ζ :=
      (hNc.integral_hasStrictDerivAt 0 (S ζ)).hasDerivAt.comp ζ hS
    have hSp : HasDerivAt (fun ζ => S ζ ^ p) (deriv S ζ * p * S ζ ^ (p - 1)) ζ :=
      hS.rpow_const (Or.inl hSpos.ne')
    have h := (((hS.mul (hM.const_mul e)).const_add
      (supportConst p e (slice Φ t₀) m₀ t₀)).sub (hI.const_mul 2)).sub (hSp.mul hk)
    refine h.congr_deriv ?_
    have e2 : S ζ ^ (p - 1) = S ζ ^ (p - 2) * S ζ := by
      rw [← Real.rpow_add_one hSpos.ne']
      congr 1
      ring
    have e3 : S ζ ^ p = S ζ ^ (p - 2) * S ζ * S ζ := by
      rw [← e2, ← Real.rpow_add_one hSpos.ne']
      congr 1
      ring
    have hMeq : pathSlope p e m₀ S ζ = S ζ ^ (p - 2) * S ζ * (m₀ - e * ζ) := by
      rw [pathSlope, e2]
    have hf : pathDet p e Φ m₀ T S ζ = e * (S ζ ^ (p - 2) *
        ((e * p * slice Φ (T ζ) + (1 - e * T ζ) * (m₀ - e * ζ)) / (1 + e * T ζ))) := rfl
    have hg := (hpath.denom_neg hζ).ne
    rw [hpath.intercept ζ hζ] at hg
    rw [hpath.pathEnvelope_scale he hmono hζ, hMeq, hf, (hpath.hasDerivAt_scale ζ hζ).deriv, e2,
      e3, hpath.intercept ζ hζ]
    exact scale_rpow_mul_deriv_identity he ((hpath.hard ζ hζ).one_add_pos he).ne' hg rfl rfl
  have hconst := apply_eq_apply_of_hasDerivAt_zero hξ.1 fun ζ hζ =>
    hJ ζ ⟨hζ.1, hζ.2.trans hξ.2⟩
  -- the value at the start of the path
  have hsub := supportDet_sub (p := p) (H := slice Φ t₀) (m := m₀)
    (hpath.hard_zero.one_add_pos he).ne'
  have hadd := supportConst_add (p := p) (H := slice Φ t₀) (m := m₀)
    (hpath.hard_zero.one_add_pos he).ne'
  have hk0 : k 0 = slice Φ t₀ - m₀ * t₀ := by
    rw [hpath.intercept 0 h0, hpath.base_zero, mul_zero, sub_zero]
  rw [hpath.scale_zero, hpath.pathSlope_zero, hpath.integral_pathEnvelope he hmono le_rfl,
    Real.one_rpow, hk0] at hconst
  linear_combination hconst + hadd + (-e) * hsub -
    (supportMod p e (slice Φ t₀) m₀ t₀ / 2) * hee

end IsPath

/-- **The radial minorant along a path.** Along a path of hard bases from `(t₀, m₀)` on which the
scale grows from `1` to `R`, there is a convex `N` with `N 0 ≤ 0` such that
`α₀ + (x + y + e (x − y)) N (x + y) − 2 ∫₀^{x+y} N ≤ Φ (x, y)` for `x + y ≤ R`, with equality at
`((1 + t₀)/2, (1 − t₀)/2)`. -/
theorem IsPath.exists_convex_minorant (hΦ : IsProfile p Φ) (hp : 1 < p) (he : e = 1 ∨ e = -1)
    (hpe : 0 < e * (p - 2)) (hor : slice Φ (-1) < 0) {t₀ m₀ L R : ℝ} {T k S : ℝ → ℝ}
    (hpath : IsPath p e Φ t₀ m₀ L R T k S) :
    ∃ N : ℝ → ℝ, ConvexOn ℝ univ N ∧ N 0 ≤ 0 ∧
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x + y ≤ R →
        supportConst p e (slice Φ t₀) m₀ t₀ + radialProfile e N x y ≤ Φ x y) ∧
      supportConst p e (slice Φ t₀) m₀ t₀ + radialProfile e N ((1 + t₀) / 2) ((1 - t₀) / 2) =
        slice Φ t₀ := by
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have hmono := hpath.monotoneOn_pathDet hΦ hp he hpe hor
  have hb0 := hpath.hard_zero
  have h1 := (hb0.one_add_pos he).ne'
  -- for `x + y ≤ 1` the function is the restricted support
  have hsmall : ∀ x y : ℝ, x + y ≤ 1 → supportConst p e (slice Φ t₀) m₀ t₀ +
      radialProfile e (pathEnvelope p e Φ m₀ L T S) x y =
      restrictedSupport p e (slice Φ t₀) m₀ t₀ x y := by
    intro x y hxy
    rw [radialProfile, hpath.pathEnvelope_of_le_one he hmono hxy,
      hpath.integral_pathEnvelope he hmono hxy, restrictedSupport]
    linear_combination (supportDet p e (slice Φ t₀) m₀ t₀ * (x + y) * (x - y)) * hee
  refine ⟨pathEnvelope p e Φ m₀ L T S, hpath.convexOn_pathEnvelope he, ?_,
    fun x y hx hy hxy => ?_, ?_⟩
  · rw [hpath.pathEnvelope_of_le_one he hmono zero_le_one]
    have h := hb0.supportMod_nonneg hΦ he
    linarith
  · rcases le_or_gt (x + y) 1 with h | h
    · rw [hsmall x y h]
      exact hb0.restrictedSupport_le_of_add_le_one hΦ hp he hpe hor hx hy h
    · -- the point of the path with the scale `x + y`
      obtain ⟨ξ, hξ, hSξ⟩ := intermediate_value_Icc hpath.length_nonneg hpath.continuousOn_scale
        (show x + y ∈ Icc (S 0) (S L) by
          rw [hpath.scale_zero, hpath.scale_length]
          exact ⟨h.le, hxy⟩)
      have hid := hpath.scale_mul_pathSlope_sub_integral he hmono hξ
      have hmin := (hpath.hard ξ hξ).minorant x y hx hy
      rw [← hpath.intercept ξ hξ, ← hSξ] at hmin
      have e3 : S ξ ^ p = S ξ ^ (p - 1) * S ξ := by
        rw [← Real.rpow_add_one (hpath.scale_pos ξ hξ).ne']
        congr 1
        ring
      rw [radialProfile, ← hSξ, hpath.pathEnvelope_scale he hmono hξ]
      rw [pathSlope] at hid ⊢
      have heq : supportConst p e (slice Φ t₀) m₀ t₀ +
          ((S ξ + e * (x - y)) * (e * (S ξ ^ (p - 1) * (m₀ - e * ξ))) -
            2 * ∫ r in (0 : ℝ)..S ξ, pathEnvelope p e Φ m₀ L T S r) =
          S ξ ^ (p - 1) * (k ξ * S ξ + (m₀ - e * ξ) * (x - y)) := by
        linear_combination hid + k ξ * e3 +
          ((x - y) * (S ξ ^ (p - 1) * (m₀ - e * ξ))) * hee
      rw [heq]
      exact hmin
  · have hxy : (1 + t₀) / 2 + (1 - t₀) / 2 ≤ 1 := by linarith
    rw [hsmall _ _ hxy, restrictedSupport_base h1]

/-- **The radial minorant at a hard base.** Let the slice of the profile `Φ` of degree `p > 1`,
`p ≠ 2`, be strictly convex on `[−1, 1]` and negative at `−1`. For every hard base `(t₀, m₀)`
and every `R ≥ 1` there is a convex `N` with `N 0 ≤ 0` such that
`α₀ + (x + y + e (x − y)) N (x + y) − 2 ∫₀^{x+y} N ≤ Φ (x, y)` for `x + y ≤ R`, with equality at
`((1 + t₀)/2, (1 − t₀)/2)`. -/
theorem IsHardBase.exists_convex_minorant (hΦ : IsProfile p Φ) (hp : 1 < p)
    (he : e = 1 ∨ e = -1) (hpe : 0 < e * (p - 2))
    (hsc : StrictConvexOn ℝ (Icc (-1) 1) (slice Φ)) (hor : slice Φ (-1) < 0) {t₀ m₀ : ℝ}
    (hb : IsHardBase p e Φ t₀ m₀) {R : ℝ} (hR : 1 ≤ R) :
    ∃ N : ℝ → ℝ, ConvexOn ℝ univ N ∧ N 0 ≤ 0 ∧
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x + y ≤ R →
        supportConst p e (slice Φ t₀) m₀ t₀ + radialProfile e N x y ≤ Φ x y) ∧
      supportConst p e (slice Φ t₀) m₀ t₀ + radialProfile e N ((1 + t₀) / 2) ((1 - t₀) / 2) =
        slice Φ t₀ := by
  obtain ⟨L, T, k, S, hpath⟩ := hb.exists_isPath hΦ hp he hpe hsc hR
  exact hpath.exists_convex_minorant hΦ hp he hpe hor

end HomogeneousIsotropic
