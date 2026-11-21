module

public import Morrey.Weights
public import Morrey.Triangulation
public import Morrey.Hn.Laminate
public import External.Kakutani.Theorem

/-!
# Section 6: the map `𝐓`

Definition 6.1 (`Morrey.T`), Proposition 6.1, Subsection 6.1 and Proposition 6.3.

* `proposition6_1`: a fixed point of `𝐓` makes `ν` a laminate.
* `proposition6_3_point`, `proposition6_3_dir`: on `Θ_l`, the mass points of the intermediate
  measures and the decomposition directions above the first level depend linearly on `t`.
* `proposition6_3`: each `𝐓(t)` is convex.
* `section6_1_isClosed_graph`, `section6_1_isCompact`, `section6_1_usc`: the graph of `𝐓` is
  closed, its values are compact, and it is upper semicontinuous on `Θ_l` (Subsection 6.1).
* `T_subset_theta`: `𝐓` maps `Θ_l` into itself.
-/

@[expose] public section

namespace Morrey

variable {l : ℕ}

/-- The leaf vectors `∇w|_{T_s}` for `k ∈ 𝒞_s`, as fed to the mold (eq. (5.9)). -/
noncomputable def leafGrad (S : TriMold l) (w : (Fin 2 → ℝ) → ℝ) : Leaf l → Fin 2 → ℝ :=
  fun q => grad l w (S.leafTri q)

/-- `𝐓(t) ⊆ Θ_l`. -/
theorem T_subset_theta (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ) (t : Leaf l → ℝ) :
    T S u v t ⊆ Theta S :=
  fun _ hr => hr.1

/-- **Proposition 6.3 (1)** (`convexidad`), mass points. On `Θ_l`, the mass point of every
intermediate pair of the mold (every sub-mold that is mixed, and is not a leaf) depends linearly
on the weights. -/
theorem proposition6_3_point (S : TriMold l) (w : Leaf l → Fin 2 → ℝ) :
    ∀ p ∈ S.tree.nodes, ∀ N ∈ [p.1, p.2], ¬ N.IsLeaf →
      ∃ L : (Leaf l → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), ∀ t ∈ Theta S, N.point t w = L t := by
  sorry

/-- **Proposition 6.3 (1)** (`convexidad`), decomposition directions. On `Θ_l`, the decomposition
direction of every mixture above the first level depends linearly on the weights. -/
theorem proposition6_3_dir (S : TriMold l) (w : Leaf l → Fin 2 → ℝ) :
    ∀ p ∈ S.tree.nodes, ¬ (p.1.IsLeaf ∧ p.2.IsLeaf) →
      ∃ L : (Leaf l → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), ∀ t ∈ Theta S, p.1.point t w - p.2.point t w = L t := by
  sorry

/-- **Proposition 6.3 (2)** (`convexidad`). Each `𝐓(t)` is convex. -/
theorem proposition6_3 (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ) (t : Leaf l → ℝ) :
    Convex ℝ (T S u v t) := by
  sorry

/-- **Subsection 6.1** (`cuatro`), closed graph: if `r_n ∈ 𝐓(t_n)`, `t_n ∈ Θ_l`, `r_n → r` and
`t_n → t`, then `r ∈ 𝐓(t)`. -/
theorem section6_1_isClosed_graph (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ) :
    IsClosed {p : (Leaf l → ℝ) × (Leaf l → ℝ) | p.1 ∈ Theta S ∧ p.2 ∈ T S u v p.1} := by
  sorry

/-- **Subsection 6.1** (`cuatro`), compact values: each `𝐓(t)`, `t ∈ Θ_l`, is compact. -/
theorem section6_1_isCompact (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ) {t : Leaf l → ℝ}
    (ht : t ∈ Theta S) : IsCompact (T S u v t) := by
  sorry

/-- **Subsection 6.1** (`cuatro`), upper semicontinuity of `𝐓` on `Θ_l`, which follows from the
closed graph because `Θ_l` is compact (the paper calls the closed graph property upper
semicontinuity). -/
theorem section6_1_usc (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ) :
    External.Kakutani.UpperSemicontinuousOn (T S u v) (Theta S) := by
  sorry

/-- **Proposition 6.1** (`facil`). If `t ∈ Θ_l` is a fixed point of `𝐓`, then the gradient
measure `ν` of `(u, v)` is a laminate. -/
theorem proposition6_1 (S : TriMold l) {u v : (Fin 2 → ℝ) → ℝ} (hu : u ∈ PL l) (hv : v ∈ PL l)
    {t : Leaf l → ℝ} (ht : t ∈ Theta S) (hfix : t ∈ T S u v t) :
    IsLaminate (gradMeasure l u v) := by
  sorry

end Morrey
