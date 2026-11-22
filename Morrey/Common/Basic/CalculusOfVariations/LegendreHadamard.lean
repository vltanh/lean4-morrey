module

public import Morrey.Common.Basic.CalculusOfVariations.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic

/-!
# Rank-one convexity and the Legendre–Hadamard condition

For a twice continuously differentiable integrand, rank-one convexity is equivalent to
nonnegativity of the Hessian on every rank-one direction at every base matrix. There is no
restriction on dimensions or polynomial degree. The short scalar calculus proofs are included
here so that this Basic module does not import an External theorem module.
-/

@[expose] public section

open Set

namespace CalculusOfVariations

/-- The scalar second derivative along an affine line, at every line parameter. -/
theorem iteratedDeriv_two_line_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (A H : E) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => f (A + s • H)) t =
      iteratedFDeriv ℝ 2 f (A + t • H) (fun _ => H) := by
  set L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight H
  have hF : ContDiff ℝ 2 (fun y => f (A + y)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have h1 : (fun s : ℝ => f (A + s • H)) = (fun y => f (A + y)) ∘ L := by
    funext s
    simp [L]
  rw [iteratedDeriv_eq_iteratedFDeriv, h1, L.iteratedFDeriv_comp_right hF t le_rfl]
  simp [L, iteratedFDeriv_comp_add_left]

/-- A convex `C²` real function has nonnegative second derivative. -/
theorem iteratedDeriv_two_nonneg_of_convexOn {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : ConvexOn ℝ univ f) (x : ℝ) : 0 ≤ iteratedDeriv 2 f x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hmono : Monotone (deriv f) := fun a b hab =>
    hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ a) (mem_univ b) hab
  exact hmono.deriv_nonneg

/-- Global rank-one convexity is equivalent to the global Legendre–Hadamard inequality
for a twice continuously differentiable integrand. -/
theorem rankOneConvex_iff_iteratedFDeriv_nonneg {d m : ℕ}
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    RankOneConvex f ↔
      ∀ A H : Matrix (Fin d) (Fin m) ℝ, H.rank = 1 →
        0 ≤ iteratedFDeriv ℝ 2 f A (fun _ => H) := by
  constructor
  · intro h A H hH
    have hline := iteratedDeriv_two_nonneg_of_convexOn
      (hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))) (h A H hH) 0
    simpa only [iteratedDeriv_two_line_at hf A H 0, zero_smul, add_zero] using hline
  · intro h A H hH
    have hg : ContDiff ℝ 2 (fun t : ℝ => f (A + t • H)) :=
      hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    have hg' : ContDiff ℝ 1 (deriv fun t : ℝ => f (A + t • H)) := by
      simpa only [deriv] using
        (hg.fderiv_right (m := 1) (by norm_num)).clm_apply
          (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))
    refine convexOn_univ_of_deriv2_nonneg (hg.differentiable (by simp))
      (hg'.differentiable (by simp)) ?_
    intro t
    rw [← iteratedDeriv_eq_iterate, iteratedDeriv_two_line_at hf A H t]
    exact h (A + t • H) H hH

/-- Acceptance of a globally quantified Hessian certificate for rank-one convexity. -/
theorem rankOneConvex_of_iteratedFDeriv_nonneg {d m : ℕ}
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hLH : ∀ A H : Matrix (Fin d) (Fin m) ℝ, H.rank = 1 →
      0 ≤ iteratedFDeriv ℝ 2 f A (fun _ => H)) : RankOneConvex f :=
  (rankOneConvex_iff_iteratedFDeriv_nonneg hf).2 hLH

end CalculusOfVariations
