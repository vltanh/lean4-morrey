module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Supporting lines of convex functions on the real line

* `ConvexOn.exists_add_mul_le`: a convex function on `ℝ` has a supporting line at every point.
* `ConvexOn.add_mul_le_of_hasDerivAt_le`: if a convex function `g` on `ℝ` lies above a function
  `k` near a point `a` where they agree and `k` is differentiable, then the tangent line of `k` at
  `a` supports `g`.
* `ConvexOn.eq_of_tendsto_div_zero`: a convex function `g` on `ℝ` with `g (t) / t → 0` at `±∞` is
  constant.
-/

@[expose] public section

open Set Filter Topology

/-- A convex function on `ℝ` has a supporting line at every point: a slope `m` with
`f x + m (y - x) ≤ f y` for every `y`. -/
theorem ConvexOn.exists_add_mul_le {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x : ℝ) :
    ∃ m : ℝ, ∀ y, f x + m * (y - x) ≤ f y := by
  have hx : x ∈ interior (univ : Set ℝ) := by simp
  refine ⟨derivWithin f (Ioi x) x, fun y => ?_⟩
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hf.rightDeriv_le_slope_of_mem_interior hx (mem_univ y) hxy
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hxy)] at h
    linarith
  · simp
  · have h := (hf.slope_le_leftDeriv_of_mem_interior (mem_univ y) hx hyx).trans
      (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hyx)] at h
    linarith

/-- If a convex function `g` on `ℝ` lies above `k` near `a`, with `g a = k a`, and `k` has the
derivative `d` at `a`, then `g a + d (τ - a) ≤ g τ` for every `τ`: the tangent line of `k` at `a`
supports `g`. -/
theorem ConvexOn.add_mul_le_of_hasDerivAt_le {g k : ℝ → ℝ} {a d : ℝ} (hg : ConvexOn ℝ univ g)
    (hle : ∀ᶠ τ in 𝓝 a, k τ ≤ g τ) (ha : k a = g a) (hd : HasDerivAt k d a) (τ : ℝ) :
    g a + d * (τ - a) ≤ g τ := by
  have h1 : HasDerivAt (fun ε : ℝ => a + ε * (τ - a)) (τ - a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (τ - a)).const_add a
  have h2 : HasDerivAt k d (a + 0 * (τ - a)) := by simpa using hd
  have hk : HasDerivAt (fun ε : ℝ => k (a + ε * (τ - a))) (d * (τ - a)) 0 := h2.comp 0 h1
  have ht := hk.tendsto_slope_zero_right
  have hcont : Tendsto (fun ε : ℝ => a + ε * (τ - a)) (𝓝[>] 0) (𝓝 a) := by
    have : Tendsto (fun ε : ℝ => a + ε * (τ - a)) (𝓝 0) (𝓝 (a + 0 * (τ - a))) :=
      h1.continuousAt.tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ε⁻¹ • (k (a + (0 + ε) * (τ - a)) - k (a + 0 * (τ - a))) ≤ g τ - g a := by
    filter_upwards [hcont.eventually hle, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε hε01
    have hconv := hg.2 (mem_univ a) (mem_univ τ) (sub_nonneg.2 hε01.2.le) hε01.1.le
      (by ring : 1 - ε + ε = 1)
    simp only [smul_eq_mul] at hconv
    rw [show (1 - ε) * a + ε * τ = a + ε * (τ - a) by ring] at hconv
    simp only [zero_add, zero_mul, add_zero, smul_eq_mul, ha]
    rw [inv_mul_le_iff₀ hε01.1]
    linarith
  have := le_of_tendsto ht hev
  linarith

/-- A convex function on `ℝ` of sublinear growth is constant: if `g (t) / t → 0` as `t → +∞` and
as `t → −∞`, then `g s = g t` for all `s`, `t`. The slopes of `g` are monotone, and the slopes to
`±∞` tend to `0`. -/
theorem ConvexOn.eq_of_tendsto_div_zero {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (h1 : Tendsto (fun t => g t / t) atTop (𝓝 0)) (h2 : Tendsto (fun t => g t / t) atBot (𝓝 0))
    (s t : ℝ) : g s = g t := by
  have key : ∀ s t : ℝ, s < t → g s = g t := by
    intro s t hst
    have hle : (g t - g s) / (t - s) ≤ 0 := by
      have hlim : Tendsto (fun T : ℝ => (g T - g t) / (T - t)) atTop (𝓝 0) := by
        have ht : Tendsto (fun T : ℝ => g t / T) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have ht' : Tendsto (fun T : ℝ => t / T) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h := (h1.sub ht).div (tendsto_const_nhds.sub ht') (by norm_num : (1 : ℝ) - 0 ≠ 0)
        have h' : Tendsto (fun T => (g T / T - g t / T) / (1 - t / T)) atTop (𝓝 0) := by
          rw [show ((0 : ℝ) - 0) / (1 - 0) = 0 by norm_num] at h
          exact h
        refine h'.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with T hT0
        rw [← sub_div, one_sub_div hT0.ne', div_div_div_cancel_right₀ hT0.ne']
      refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_gt_atTop t] with T hT
      exact hg.slope_mono_adjacent (mem_univ s) (mem_univ T) hst hT
    have hge : 0 ≤ (g t - g s) / (t - s) := by
      have hlim : Tendsto (fun T : ℝ => (g s - g T) / (s - T)) atBot (𝓝 0) := by
        have hs : Tendsto (fun T : ℝ => g s / T) atBot (𝓝 0) :=
          tendsto_const_nhds.div_atBot tendsto_id
        have hs' : Tendsto (fun T : ℝ => s / T) atBot (𝓝 0) :=
          tendsto_const_nhds.div_atBot tendsto_id
        have h := (hs.sub h2).div (hs'.sub tendsto_const_nhds) (by norm_num : (0 : ℝ) - 1 ≠ 0)
        have h' : Tendsto (fun T => (g s / T - g T / T) / (s / T - 1)) atBot (𝓝 0) := by
          rw [show ((0 : ℝ) - 0) / (0 - 1) = 0 by norm_num] at h
          exact h
        refine h'.congr' ?_
        filter_upwards [eventually_lt_atBot 0] with T hT0
        rw [← sub_div, div_sub_one hT0.ne, div_div_div_cancel_right₀ hT0.ne]
      refine le_of_tendsto hlim ?_
      filter_upwards [eventually_lt_atBot s] with T hT
      exact hg.slope_mono_adjacent (mem_univ T) (mem_univ t) hT hst
    have h0 : (g t - g s) / (t - s) = 0 := le_antisymm hle hge
    rcases div_eq_zero_iff.1 h0 with h | h
    · linarith
    · exact absurd h (sub_pos.2 hst).ne'
  rcases lt_trichotomy s t with h | rfl | h
  · exact key s t h
  · rfl
  · exact (key t s h).symm
