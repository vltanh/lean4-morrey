module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Convex functions on an interval as limits of combinations of hinge functions

A piecewise linear convex function on `[0, R]` with nodes `ρ₁ < ⋯ < ρₙ` is
`N 0 + n₁ r + ∑ wᵢ max (r − ρᵢ) 0` with `wᵢ ≥ 0` (the jumps of the slope), and the piecewise
linear interpolants of a continuous convex function converge to it uniformly.

* `Finset.sum_range_mul_max_sub`: for nondecreasing nodes `ρ` and `ρ j ≤ r ≤ ρ (j + 1)`, the
  hinges `max (r − ρ (i + 1)) 0` with `i < j` are `r − ρ (i + 1)` and the others vanish.
* `Finset.sum_range_slope_sub_mul`: the telescoping identity of a piecewise linear function with
  the values `a i` at the nodes `ρ i` and the slopes `s i`:
  `a 0 + s 0 (r − ρ 0) + ∑_{i < j} (s (i + 1) − s i) (r − ρ (i + 1)) = a j + s j (r − ρ j)`.
* `ConvexOn.exists_hinge_approx`: a convex, continuous function on `[0, R]` is, within any
  `ε > 0`, uniformly on `[0, R]`, a function `r ↦ N 0 + n₁ r + ∑ wᵢ max (r − ρᵢ) 0` with
  `wᵢ ≥ 0` and `ρᵢ > 0`.
-/

@[expose] public section

open Set

/-- For nondecreasing nodes `ρ` and a point `r` with `ρ j ≤ r ≤ ρ (j + 1)`, a combination of the
hinge functions `max (r − ρ (i + 1)) 0`, `i < n`, with `j ≤ n`, only has the terms `i < j`, and
these are affine in `r`. -/
theorem Finset.sum_range_mul_max_sub {w ρ : ℕ → ℝ} (hρ : Monotone ρ) {j n : ℕ} (hjn : j ≤ n)
    {r : ℝ} (h1 : ρ j ≤ r) (h2 : r ≤ ρ (j + 1)) :
    ∑ i ∈ Finset.range n, w i * max (r - ρ (i + 1)) 0 =
      ∑ i ∈ Finset.range j, w i * (r - ρ (i + 1)) := by
  rw [← Finset.sum_range_add_sum_Ico _ hjn]
  have hzero : ∑ i ∈ Finset.Ico j n, w i * max (r - ρ (i + 1)) 0 = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hle : ρ (j + 1) ≤ ρ (i + 1) := hρ (Nat.succ_le_succ (Finset.mem_Ico.1 hi).1)
    rw [max_eq_right (by linarith), mul_zero]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hle : ρ (i + 1) ≤ ρ j := hρ (Finset.mem_range.1 hi)
  rw [max_eq_left (by linarith)]

/-- The telescoping identity of piecewise linear interpolation. If `s i` is the slope between
the nodes `ρ i` and `ρ (i + 1)` of a function with the values `a i` and `a (i + 1)` there, then
`a 0 + s 0 (r − ρ 0) + ∑_{i < j} (s (i + 1) − s i) (r − ρ (i + 1)) = a j + s j (r − ρ j)`. -/
theorem Finset.sum_range_slope_sub_mul {a ρ s : ℕ → ℝ}
    (h : ∀ i, s i * (ρ (i + 1) - ρ i) = a (i + 1) - a i) (r : ℝ) (j : ℕ) :
    a 0 + s 0 * (r - ρ 0) + ∑ i ∈ Finset.range j, (s (i + 1) - s i) * (r - ρ (i + 1)) =
      a j + s j * (r - ρ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    linear_combination h j

/-- A convex, continuous function `N` on `[0, R]` is uniformly approximated on `[0, R]` by the
functions `r ↦ N 0 + n₁ r + ∑ wᵢ max (r − ρᵢ) 0` with `wᵢ ≥ 0` and `ρᵢ > 0`: its piecewise
linear interpolants on uniform meshes. -/
theorem ConvexOn.exists_hinge_approx {N : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hN : ConvexOn ℝ (Icc 0 R) N) (hc : ContinuousOn N (Icc 0 R)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (n₁ : ℝ) (w ρ : Fin n → ℝ), (∀ i, 0 ≤ w i) ∧ (∀ i, 0 < ρ i) ∧
      ∀ r ∈ Icc 0 R, |N r - (N 0 + n₁ * r + ∑ i, w i * max (r - ρ i) 0)| ≤ ε := by
  -- a mesh finer than the modulus of uniform continuity of `N`
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hc
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (R / δ)
  have hk0 : 0 < (k : ℝ) := lt_trans (div_pos hR hδ) hk
  have hkpos : 0 < k := by exact_mod_cast hk0
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = R / k := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact div_pos hR hk0
  have hkd : k * d = R := by rw [hd]; field_simp
  have hdδ : d < δ := by
    rw [div_lt_iff₀ hδ] at hk
    rw [hd, div_lt_iff₀ hk0]
    linarith
  -- the nodes and the slopes of the interpolant
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ, ∀ j, ρ j = j * d := ⟨_, fun _ => rfl⟩
  have hρmono : Monotone ρ := fun i j hij => by
    rw [hρ, hρ]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) hd0.le
  have hρ0 : ρ 0 = 0 := by rw [hρ]; simp
  have hρk : ρ k = R := by rw [hρ, hkd]
  have hρmem : ∀ j, j ≤ k → ρ j ∈ Icc 0 R := fun j hj =>
    ⟨hρ0 ▸ hρmono (Nat.zero_le j), hρk ▸ hρmono hj⟩
  have hρsucc : ∀ j, ρ (j + 1) - ρ j = d := by
    intro j
    rw [hρ, hρ]
    push_cast
    ring
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ j, s j = (N (ρ (j + 1)) - N (ρ j)) / d := ⟨_, fun _ => rfl⟩
  have hsd : ∀ j, s j * (ρ (j + 1) - ρ j) = N (ρ (j + 1)) - N (ρ j) := by
    intro j
    rw [hρsucc, hs]
    field_simp
  have hsmono : ∀ j, j + 2 ≤ k → s j ≤ s (j + 1) := by
    intro j hj
    have h := hN.slope_mono_adjacent (hρmem j (by omega)) (hρmem (j + 2) hj)
      (show ρ j < ρ (j + 1) by linarith [hρsucc j])
      (show ρ (j + 1) < ρ (j + 2) by linarith [hρsucc (j + 1)])
    rw [hρsucc j, show ρ (j + 2) - ρ (j + 1) = d from hρsucc (j + 1)] at h
    rw [hs, hs]
    exact h
  refine ⟨k - 1, s 0, fun i => s ((i : ℕ) + 1) - s i, fun i => ρ ((i : ℕ) + 1), fun i => ?_,
    fun i => ?_, fun r hr => ?_⟩
  · exact sub_nonneg.2 (hsmono i (by omega))
  · linarith [hρsucc i, (hρmem i (by omega)).1]
  -- the mesh interval of `r`
  obtain ⟨j, hjk, hj1, hj2⟩ : ∃ j, j < k ∧ ρ j ≤ r ∧ r ≤ ρ (j + 1) := by
    rcases hr.2.eq_or_lt with hrR | hrR
    · refine ⟨k - 1, by omega, ?_, ?_⟩
      · rw [hrR, ← hρk]
        exact hρmono (by omega)
      · rw [hrR, ← hρk, show k - 1 + 1 = k by omega]
    · have hrd : 0 ≤ r / d := div_nonneg hr.1 hd0.le
      refine ⟨⌊r / d⌋₊, ?_, ?_, ?_⟩
      · rw [Nat.floor_lt hrd, div_lt_iff₀ hd0, hkd]
        exact hrR
      · have h := Nat.floor_le hrd
        rw [le_div_iff₀ hd0] at h
        rw [hρ]
        exact h
      · have h := Nat.lt_floor_add_one (r / d)
        rw [div_lt_iff₀ hd0] at h
        rw [hρ]
        push_cast
        exact h.le
  -- on that interval the combination of hinges is the chord
  have hsum : ∑ i : Fin (k - 1), (s ((i : ℕ) + 1) - s i) * max (r - ρ ((i : ℕ) + 1)) 0 =
      ∑ i ∈ Finset.range j, (s (i + 1) - s i) * (r - ρ (i + 1)) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (s (i + 1) - s i) * max (r - ρ (i + 1)) 0) (k - 1)]
    exact Finset.sum_range_mul_max_sub hρmono (by omega) hj1 hj2
  have htel : N 0 + s 0 * r + ∑ i ∈ Finset.range j, (s (i + 1) - s i) * (r - ρ (i + 1)) =
      N (ρ j) + s j * (r - ρ j) := by
    have h := Finset.sum_range_slope_sub_mul (a := fun i => N (ρ i)) hsd r j
    simp only [hρ0, sub_zero] at h
    exact h
  change |N r - (N 0 + s 0 * r +
    ∑ i : Fin (k - 1), (s ((i : ℕ) + 1) - s i) * max (r - ρ ((i : ℕ) + 1)) 0)| ≤ ε
  rw [hsum, htel]
  -- the chord is within `ε` of `N`
  have h1 : |N r - N (ρ j)| < ε := by
    have h := hδε r hr (ρ j) (hρmem j hjk.le) (by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hj1)]
      linarith [hρsucc j])
    rwa [Real.dist_eq] at h
  have h2 : |N r - N (ρ (j + 1))| < ε := by
    have h := hδε r hr (ρ (j + 1)) (hρmem (j + 1) hjk) (by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hj2)]
      linarith [hρsucc j])
    rwa [Real.dist_eq] at h
  have hD : 0 < ρ (j + 1) - ρ j := by rw [hρsucc]; exact hd0
  have hid : (N r - (N (ρ j) + s j * (r - ρ j))) * (ρ (j + 1) - ρ j) =
      (ρ (j + 1) - r) * (N r - N (ρ j)) + (r - ρ j) * (N r - N (ρ (j + 1))) := by
    linear_combination (-(r - ρ j)) * hsd j
  have habs : |(N r - (N (ρ j) + s j * (r - ρ j))) * (ρ (j + 1) - ρ j)| ≤
      ε * (ρ (j + 1) - ρ j) := by
    rw [hid]
    calc |(ρ (j + 1) - r) * (N r - N (ρ j)) + (r - ρ j) * (N r - N (ρ (j + 1)))|
        ≤ |(ρ (j + 1) - r) * (N r - N (ρ j))| + |(r - ρ j) * (N r - N (ρ (j + 1)))| :=
          abs_add_le _ _
      _ = (ρ (j + 1) - r) * |N r - N (ρ j)| + (r - ρ j) * |N r - N (ρ (j + 1))| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 hj2),
            abs_of_nonneg (sub_nonneg.2 hj1)]
      _ ≤ (ρ (j + 1) - r) * ε + (r - ρ j) * ε :=
          add_le_add (mul_le_mul_of_nonneg_left h1.le (sub_nonneg.2 hj2))
            (mul_le_mul_of_nonneg_left h2.le (sub_nonneg.2 hj1))
      _ = ε * (ρ (j + 1) - ρ j) := by ring
  rw [abs_mul, abs_of_pos hD] at habs
  exact le_of_mul_le_mul_right habs hD
