module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Monotonicity from a self-improving inequality

* `monotoneOn_of_forall_sub_le_half`: let `f` be continuous on `[a, b]`. If for all `x < y` in
  `[a, b]` with `y − x ≤ δ`, a bound `|f z − f x| ≤ D` on `[x, y]` implies `f x − f y ≤ D/2`,
  then `f` is nondecreasing on `[a, b]`. (On an interval of length at most `δ`, take a minimizer
  `y` of `f`, then a maximizer `x` of `f` to the left of `y`: on `[x, y]` the oscillation is
  `D = f x − f y`, so `D ≤ D/2`.)
-/

@[expose] public section

open Set

/-- A function that is continuous on `[a, b]` and satisfies the following self-improving
inequality is nondecreasing on `[a, b]`: for all `x < y` in `[a, b]` with `y − x ≤ δ` and every
`D` with `|f z − f x| ≤ D` on `[x, y]`, `f x − f y ≤ D/2`. -/
theorem monotoneOn_of_forall_sub_le_half {f : ℝ → ℝ} {a b δ : ℝ} (hδ : 0 < δ)
    (hf : ContinuousOn f (Icc a b))
    (h : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x < y → y - x ≤ δ →
      ∀ D : ℝ, (∀ z ∈ Icc x y, |f z - f x| ≤ D) → f x - f y ≤ D / 2) :
    MonotoneOn f (Icc a b) := by
  -- on an interval of length at most `δ`
  have hloc : ∀ x₀ ∈ Icc a b, ∀ y₀ ∈ Icc a b, x₀ ≤ y₀ → y₀ - x₀ ≤ δ → f x₀ ≤ f y₀ := by
    intro x₀ hx₀ y₀ hy₀ hxy hd
    by_contra hcon
    have hlt : f y₀ < f x₀ := not_le.1 hcon
    have hsub : Icc x₀ y₀ ⊆ Icc a b := Icc_subset_Icc hx₀.1 hy₀.2
    obtain ⟨y, hy, hymin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hxy) (hf.mono hsub)
    have hsub' : Icc x₀ y ⊆ Icc x₀ y₀ := Icc_subset_Icc le_rfl hy.2
    obtain ⟨x, hx, hxmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hy.1)
      (hf.mono (hsub'.trans hsub))
    have h1 : f y ≤ f y₀ := hymin (right_mem_Icc.2 hxy)
    have h2 : f x₀ ≤ f x := hxmax (left_mem_Icc.2 hy.1)
    have hxy' : x < y := by
      rcases hx.2.eq_or_lt with heq | hlt'
      · rw [heq] at h2
        linarith
      · exact hlt'
    have key := h x (hsub (hsub' hx)) y (hsub hy) hxy' (by linarith [hx.1, hy.2]) (f x - f y)
      fun z hz => by
        have hz1 : f y ≤ f z := hymin ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
        have hz2 : f z ≤ f x := hxmax ⟨hx.1.trans hz.1, hz.2⟩
        rw [abs_le]
        constructor <;> linarith
    linarith
  -- chain intervals of length `δ`
  have hchain : ∀ n : ℕ, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → y - x ≤ n * δ → f x ≤ f y := by
    intro n
    induction n with
    | zero =>
      intro x hx y hy hxy hd
      have hyx : y = x := by
        rw [Nat.cast_zero, zero_mul] at hd
        linarith
      rw [hyx]
    | succ n ih =>
      intro x hx y hy hxy hd
      rcases le_or_gt (y - x) δ with h1 | h1
      · exact hloc x hx y hy hxy h1
      · have hz : y - δ ∈ Icc a b := ⟨by linarith [hx.1], by linarith [hy.2]⟩
        have h2 := ih x hx (y - δ) hz (by linarith) (by
          rw [Nat.cast_succ] at hd
          linarith)
        have h3 := hloc (y - δ) hz y hy (by linarith) (by linarith)
        exact h2.trans h3
  intro x hx y hy hxy
  obtain ⟨n, hn⟩ := exists_nat_ge ((y - x) / δ)
  exact hchain n x hx y hy hxy (by rwa [div_le_iff₀ hδ] at hn)
