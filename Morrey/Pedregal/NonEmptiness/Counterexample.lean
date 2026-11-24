module

public import Morrey.Pedregal.NonEmptiness.Statements
public import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Corollary 7.2, Proposition 7.1 and the summary of Step 2 are false

A counterexample at the level `l = 1`, for the mold `TriMold.canonical 1`: the grid has `2 × 2`
cells and `τ_1` has `8` triangles.

* `tri x = |x − round x|`, the distance from `x` to the nearest integer, a `1`-periodic triangle
  wave, affine on each interval `[k/2, (k + 1)/2]`.
* `uCex = tri(x₀) − tri(x₁) − tri(x₀ + x₁)` and `vCex = −tri(x₀) + tri(x₁) − tri(x₀ + x₁)`
  (so `vCex (x₀, x₁) = uCex (x₁, x₀)`) lie in `ℙ_1`. Their values at the nodes
  `(0,0), (½,0), (0,½), (½,½)` are `0, 0, −1, 0` and `0, −1, 0, 0`.
* `tCex`: the uniform weights `1/48`, in `Θ_1`.

The first mixture above the first level of the sub-mold `0` of `TriMold.canonical 1` mixes the
vertical interfaces `(0, 0, 0)` and `(0, 0, 1)`. Across a vertical interface the derivative
`∂₂` of a function of `ℙ_l` is continuous, so the mass points of these two first-level mixtures
have second coordinates `∂₂w` on the interfaces, whatever the weights. For `uCex` and `tCex` the
two mass points are `(1, 0)` and `(−1, 0)`, so the decomposition direction is `(2, 0)`. For `vCex`
the second coordinates are `2` and `−2` for all weights `r`, so the direction is `(*, 4)`, never
parallel to `(2, 0)`. Hence no `r` satisfies the condition of Definition 6.1 at this mixture:
`𝐓(tCex) = ∅` (`T_cex_eq_empty`). The same mixture refutes Proposition 7.1 (with `w := vCex`) and
the summary of Step 2 (with `j = 0`).
-/

@[expose] public section

namespace Pedregal

/-- The distance from `x` to the nearest integer. -/
noncomputable def tri (x : ℝ) : ℝ :=
  |x - round x|

/-- The first component of the counterexample. -/
noncomputable def uCex : (Fin 2 → ℝ) → ℝ :=
  fun x => tri (x 0) - tri (x 1) - tri (x 0 + x 1)

/-- The second component of the counterexample. -/
noncomputable def vCex : (Fin 2 → ℝ) → ℝ :=
  fun x => -tri (x 0) + tri (x 1) - tri (x 0 + x 1)

/-- The uniform weights of `Θ_1`. -/
noncomputable def tCex : Leaf 1 → ℝ :=
  fun _ => 1 / 48

/-- `tri x` is the norm of `x` in `ℝ / ℤ`. -/
theorem cex_tri_eq_unitAddCircle (x : ℝ) : tri x = ‖(x : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq, tri]

/-- `tri` is continuous. -/
theorem cex_continuous_tri : Continuous tri := by
  have : tri = fun x : ℝ => ‖(x : UnitAddCircle)‖ := funext cex_tri_eq_unitAddCircle
  rw [this]
  exact continuous_norm.comp (AddCircle.continuous_mk' 1)

/-- `tri` is `1`-periodic. -/
theorem cex_tri_add_one (x : ℝ) : tri (x + 1) = tri x := by
  simp only [tri, round_add_one, Int.cast_add, Int.cast_one]
  ring_nf

private theorem tri_eq_abs (z : ℤ) {x : ℝ} (h1 : (z : ℝ) - 1 / 2 ≤ x) (h2 : x ≤ z + 1 / 2) :
    tri x = |x - z| := by
  unfold tri
  rcases h2.lt_or_eq with h | h
  · have : round x = z := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> linarith
    rw [this]
  · have : round x = z + 1 := by
      rw [round_eq, Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    rw [this, h]
    push_cast
    rw [show (z : ℝ) + 1 / 2 - (z + 1) = -(1 / 2) by ring, show (z : ℝ) + 1 / 2 - z = 1 / 2 by ring,
      abs_neg]

/-- The constant term of `tri` on `[n/2, (n + 1)/2]`. -/
private noncomputable def triConst (n : ℕ) : ℝ :=
  if Even n then -((n : ℝ) / 2) else ((n : ℝ) + 1) / 2

private theorem tri_eq_affine (n : ℕ) {x : ℝ} (h1 : (n : ℝ) / 2 ≤ x) (h2 : x ≤ ((n : ℝ) + 1) / 2) :
    tri x = triConst n + (-1) ^ n * x := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have he : Even (2 * m) := even_two_mul m
    push_cast at h1 h2
    rw [tri_eq_abs m (by push_cast; linarith) (by push_cast; linarith)]
    simp only [triConst, he, ite_true, pow_mul, neg_one_sq, one_pow, one_mul, Int.cast_natCast]
    push_cast
    rw [abs_of_nonneg (by linarith)]
    ring
  · have ho : ¬ Even (2 * m + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
    push_cast at h1 h2
    rw [tri_eq_abs (m + 1) (by push_cast; linarith) (by push_cast; linarith)]
    simp only [triConst, ho, ite_false, pow_succ, pow_mul]
    push_cast
    rw [abs_of_nonpos (by linarith)]
    ring

/-- The index `a + b + k` of the interval `[n/2, (n + 1)/2]` that contains `x₀ + x₁` on the
triangle `(a, b, k)`. -/
private def triIdx (s : Tri 1) : ℕ := (s.1 : ℕ) + (s.2.1 : ℕ) + (s.2.2 : ℕ)

private theorem bounds_of_mem {s : Tri 1} {x : Fin 2 → ℝ} (hx : x ∈ triangle 1 s) :
    ((s.1 : ℕ) : ℝ) / 2 ≤ x 0 ∧ x 0 ≤ (((s.1 : ℕ) : ℝ) + 1) / 2 ∧
    ((s.2.1 : ℕ) : ℝ) / 2 ≤ x 1 ∧ x 1 ≤ (((s.2.1 : ℕ) : ℝ) + 1) / 2 ∧
    ((triIdx s : ℕ) : ℝ) / 2 ≤ x 0 + x 1 ∧ x 0 + x 1 ≤ (((triIdx s : ℕ) : ℝ) + 1) / 2 := by
  unfold triangle at hx
  unfold triIdx
  split_ifs at hx with hk
  · have : ((s.2.2 : ℕ) : ℝ) = 0 := by simp [hk]
    push_cast
    rw [this]
    simp only [pow_one] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · have : ((s.2.2 : ℕ) : ℝ) = 1 := by
      have : s.2.2 = 1 := by omega
      simp [this]
    push_cast
    rw [this]
    simp only [pow_one] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The slopes of `uCex` on the triangle `s`. -/
private noncomputable def uSlope (s : Tri 1) : Fin 2 → ℝ :=
  ![(-1) ^ (s.1 : ℕ) - (-1) ^ triIdx s, -(-1) ^ (s.2.1 : ℕ) - (-1) ^ triIdx s]

/-- The slopes of `vCex` on the triangle `s`. -/
private noncomputable def vSlope (s : Tri 1) : Fin 2 → ℝ :=
  ![-(-1) ^ (s.1 : ℕ) - (-1) ^ triIdx s, (-1) ^ (s.2.1 : ℕ) - (-1) ^ triIdx s]

private theorem uCex_affine (s : Tri 1) : ∀ x ∈ triangle 1 s,
    uCex x = (triConst s.1 - triConst s.2.1 - triConst (triIdx s)) + uSlope s 0 * x 0 +
      uSlope s 1 * x 1 := by
  intro x hx
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bounds_of_mem hx
  simp only [uCex, uSlope, tri_eq_affine _ h1 h2, tri_eq_affine _ h3 h4, tri_eq_affine _ h5 h6,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem vCex_affine (s : Tri 1) : ∀ x ∈ triangle 1 s,
    vCex x = (-triConst s.1 + triConst s.2.1 - triConst (triIdx s)) + vSlope s 0 * x 0 +
      vSlope s 1 * x 1 := by
  intro x hx
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bounds_of_mem hx
  simp only [vCex, vSlope, tri_eq_affine _ h1 h2, tri_eq_affine _ h3 h4, tri_eq_affine _ h5 h6,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem uCex_mem : uCex ∈ PL 1 := by
  refine ⟨?_, ?_, fun s => ⟨_, _, uCex_affine s⟩⟩
  · unfold uCex
    have h := cex_continuous_tri
    fun_prop
  · intro x i
    fin_cases i <;>
      simp [uCex, add_right_comm _ (1 : ℝ), ← add_assoc, cex_tri_add_one]

theorem vCex_mem : vCex ∈ PL 1 := by
  refine ⟨?_, ?_, fun s => ⟨_, _, vCex_affine s⟩⟩
  · unfold vCex
    have h := cex_continuous_tri
    fun_prop
  · intro x i
    fin_cases i <;>
      simp [vCex, add_right_comm _ (1 : ℝ), ← add_assoc, cex_tri_add_one]

theorem tCex_mem : tCex ∈ Theta (TriMold.canonical 1) := by
  have h := uniform_mem_theta (TriMold.canonical 1)
  norm_num at h
  exact h

private theorem grad_uCex (s : Tri 1) : grad 1 uCex s = uSlope s :=
  grad_eq_of_affine (uCex_affine s)

private theorem grad_vCex (s : Tri 1) : grad 1 vCex s = vSlope s :=
  grad_eq_of_affine (vCex_affine s)

/-- The first-level mixture of the interface `i` of the sub-mold `0`. -/
private def mixF (i : ℕ) : Mold (Leaf 1) :=
  Mold.node (Mold.leaf ((0 : Fin 3), ifaceLeaf (l := 1) i 0)) (Mold.leaf (0, ifaceLeaf i 1))

/-- The mixture of the vertical interfaces `(0, 0, 0)` and `(0, 0, 1)` in the sub-mold `0` of
`TriMold.canonical 1`. -/
private def mixP : Mold (Leaf 1) × Mold (Leaf 1) := (mixF 0, mixF 1)

private theorem mixP_mem_subMold : mixP ∈ (subMold 1 0).nodes := by
  have h1 : mixP ∈ (dyadic 1 mixF).nodes := List.mem_cons_self
  have h2 : mixP ∈ (dyadic 2 mixF).nodes := List.mem_cons_of_mem _ (List.mem_append_left _ h1)
  exact List.mem_cons_of_mem _ (List.mem_append_left _ h2)

private theorem mixP_mem_tree : mixP ∈ (TriMold.canonical 1).tree.nodes :=
  List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_append_left _ mixP_mem_subMold)))

private theorem mixP_not_leaf : ¬ (mixP.1.IsLeaf ∧ mixP.2.IsLeaf) := fun h => h.1

private theorem leafTri_00 : (TriMold.canonical 1).leafTri (0, ifaceLeaf 0 0) = (0, 0, 1) := rfl
private theorem leafTri_01 : (TriMold.canonical 1).leafTri (0, ifaceLeaf 0 1) = (1, 0, 0) := rfl
private theorem leafTri_10 : (TriMold.canonical 1).leafTri (0, ifaceLeaf 1 0) = (0, 1, 1) := rfl
private theorem leafTri_11 : (TriMold.canonical 1).leafTri (0, ifaceLeaf 1 1) = (1, 1, 0) := rfl

private theorem lam_tCex (a b : Leaf 1) : Mold.lam tCex (Mold.leaf a) (Mold.leaf b) = 1 / 2 := by
  norm_num [Mold.lam, Mold.weight, tCex]

/-- The key computation: at the mixture `mixP`, the direction of `vCex` for any weights `r` is
never parallel to the direction `(2, 0)` of `uCex` for `tCex`. -/
private theorem not_parallel (r : Leaf 1 → ℝ) :
    ¬ Parallel (dir (TriMold.canonical 1) uCex tCex mixP)
      (dir (TriMold.canonical 1) vCex r mixP) := by
  simp only [dir, mixP, mixF, Mold.point, leafGrad, leafTri_00, leafTri_01, leafTri_10,
    leafTri_11, grad_uCex, grad_vCex, lam_tCex]
  norm_num [Parallel, uSlope, vSlope, triIdx]
  intro h
  linarith

/-- For the mold `TriMold.canonical 1`, the image `𝐓(tCex)` of the counterexample is empty. -/
theorem T_cex_eq_empty : T (TriMold.canonical 1) uCex vCex tCex = ∅ := by
  ext r
  simp only [Set.mem_empty_iff_false, iff_false]
  exact fun hr => not_parallel r (hr.2 mixP mixP_mem_tree mixP_not_leaf)

/-- **Corollary 7.2** (`cor7_2`) **is false.**

Departure from the paper (reason 1: the statement is false; REPORT.md, E13): the paper
derives Corollary 7.2 from Proposition 7.1; here it is refuted, by the counterexample of the
module docstring (`T_cex_eq_empty`). -/
theorem corollary7_2_false : ¬ Corollary7_2 := by
  intro h
  obtain ⟨r, hr⟩ := h 1 le_rfl (TriMold.canonical 1) uCex vCex uCex_mem vCex_mem tCex tCex_mem
  rw [T_cex_eq_empty] at hr
  exact hr

/-- **Proposition 7.1** (`esta`) **is false.**

Departure from the paper (reason 1: the statement is false; REPORT.md, E13): refuted, with
`w := vCex`, instead of proved. -/
theorem proposition7_1_false : ¬ Proposition7_1 := by
  intro h
  obtain ⟨r, -, hr⟩ := h 1 le_rfl (TriMold.canonical 1) uCex uCex_mem tCex tCex_mem vCex vCex_mem
  exact not_parallel r (hr mixP mixP_mem_tree mixP_not_leaf)

/-- **The summary of Step 2 of the proof of Proposition 7.1, with Claim 7.5** (`positivo`), **is
false**, already for the sub-mold
`j = 0`: no weights at all make the decomposition directions of `vCex` parallel to those of
`uCex` along it.

Departure from the paper (reason 1: the statement is false; REPORT.md, E14): refuted
instead of proved. -/
theorem step2Claim_false : ¬ Step2Claim := by
  intro h
  obtain ⟨r, -, -, hr⟩ :=
    h 1 le_rfl (TriMold.canonical 1) uCex uCex_mem tCex tCex_mem 0 vCex vCex_mem
  exact not_parallel r (hr mixP mixP_mem_subMold mixP_not_leaf)

/-- The summary of Step 2 as the paper states it (with the start from `𝕌_j`) is false too.

Departure from the paper (reason 1: the statement is false; REPORT.md, E14): refuted
instead of proved. -/
theorem step2ClaimPaper_false : ¬ Step2ClaimPaper :=
  fun h => step2Claim_false (step2Claim_of_paper h)

end Pedregal
