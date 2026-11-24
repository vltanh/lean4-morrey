module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Functions with a derivative of constant sign at every point of a closed interval

Mathlib's `monotoneOn_of_deriv_nonneg` asks for continuity on the set and for the derivative in
its interior. These are the forms for a function that has a derivative at every point of
`[a, b]`:

* `apply_le_apply_of_hasDerivAt_nonneg`: if the derivative is nonnegative on `[a, b]`, then
  `g a ≤ g b`;
* `apply_eq_apply_of_hasDerivAt_zero`: if the derivative is `0` on `[a, b]`, then `g b = g a`.
-/

@[expose] public section

open Set

/-- If `g` has a nonnegative derivative at every point of `[a, b]`, then `g a ≤ g b`. -/
theorem apply_le_apply_of_hasDerivAt_nonneg {g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Icc a b, 0 ≤ g' x) : g a ≤ g b :=
  (monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hg x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [(hg x (interior_subset hx)).deriv]
      exact hg' x (interior_subset hx)))
    (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab

/-- If `g` has the derivative `0` at every point of `[a, b]`, then `g b = g a`. -/
theorem apply_eq_apply_of_hasDerivAt_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g 0 x) : g b = g a := by
  refine le_antisymm ?_
    (apply_le_apply_of_hasDerivAt_nonneg (g' := fun _ => 0) hab hg fun _ _ => le_rfl)
  have h := apply_le_apply_of_hasDerivAt_nonneg (g := fun x => -g x) (g' := fun _ => 0) hab
    (fun x hx => by simpa using (hg x hx).fun_neg) fun _ _ => le_rfl
  simpa using h
