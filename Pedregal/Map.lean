module

public import Pedregal.Weights
public import Pedregal.Triangulation
public import Pedregal.Hn.Laminate
public import External.Kakutani.Theorem
public import Basic.LinearAlgebra.Matrix.RankTwo

/-!
# Section 6: the map `𝐓`

Definition 6.1 (`Pedregal.T`), Proposition 6.1, Subsection 6.1 and Proposition 6.3.

* `proposition6_1`: a fixed point of `𝐓` makes `ν` a laminate.
* `proposition6_3_point`, `proposition6_3_dir`: on `Θ_l`, the mass points of the intermediate
  measures and the decomposition directions above the first level depend linearly on `t`.
* `proposition6_3`: each `𝐓(t)` is convex.
* `section6_1_isClosed_graph`, `section6_1_isCompact`, `section6_1_usc`: the graph of `𝐓` is
  closed, its values are compact, and it is upper semicontinuous on `Θ_l` (Subsection 6.1).
* `T_subset_theta`: `𝐓` maps `Θ_l` into itself.
* `equation5_15`: the three barycenters `𝕎_j` average to `0` (eq. (5.15)).
-/

@[expose] public section

namespace Pedregal

variable {l : ℕ}

/-- The leaf vectors `∇w|_{T_s}` for `k ∈ 𝒞_s`, as fed to the mold (eq. (5.9)). -/
noncomputable def leafGrad (S : TriMold l) (w : (Fin 2 → ℝ) → ℝ) : Leaf l → Fin 2 → ℝ :=
  fun q => grad l w (S.leafTri q)

/-! ### Helpers: the structure of the mold and linearity on `Θ_l` -/

open Filter Topology

/-- The mixtures of a dyadic mold `dyadic m f`: either the mixture of two consecutive dyadic
blocks of `2^q` molds, starting at `n` and at `n + 2^q`, or a mixture inside one of the molds
`f n`. -/
theorem map_mem_nodes_dyadic {ι : Type} : ∀ (m : ℕ) (f : ℕ → Mold ι) (p : Mold ι × Mold ι),
    p ∈ (dyadic m f).nodes →
      (∃ q n, n + 2 ^ (q + 1) ≤ 2 ^ m ∧
        p = (dyadic q (fun k => f (n + k)), dyadic q (fun k => f (n + 2 ^ q + k)))) ∨
      ∃ n < 2 ^ m, p ∈ (f n).nodes
  | 0, f, p, hp => Or.inr ⟨0, by norm_num, hp⟩
  | m + 1, f, p, hp => by
    have h2 : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    have hm : 0 < 2 ^ m := by positivity
    simp only [dyadic, Mold.nodes, List.mem_cons, List.mem_append] at hp
    rcases hp with rfl | hp | hp
    · exact Or.inl ⟨m, 0, by simp, by simp⟩
    · rcases map_mem_nodes_dyadic m f p hp with ⟨q, n, hn, rfl⟩ | ⟨n, hn, hp⟩
      · have hq : 0 < 2 ^ q := by positivity
        exact Or.inl ⟨q, n, by omega, rfl⟩
      · exact Or.inr ⟨n, by omega, hp⟩
    · rcases map_mem_nodes_dyadic m _ p hp with ⟨q, n, hn, rfl⟩ | ⟨n, hn, hp⟩
      · have hq : 0 < 2 ^ q := by positivity
        refine Or.inl ⟨q, 2 ^ m + n, by omega, ?_⟩
        simp only [Nat.add_assoc]
      · exact Or.inr ⟨2 ^ m + n, by omega, hp⟩

/-- The weight of a dyadic mold is the sum of the weights of its molds. -/
theorem map_weight_dyadic {ι : Type} (t : ι → ℝ) : ∀ (m : ℕ) (f : ℕ → Mold ι),
    (dyadic m f).weight t = ∑ k ∈ Finset.range (2 ^ m), (f k).weight t
  | 0, f => by simp [dyadic]
  | m + 1, f => by
    rw [dyadic, Mold.weight, map_weight_dyadic t m, map_weight_dyadic t m, pow_succ, mul_two,
      Finset.sum_range_add]

/-- The mixtures of a sub-mold: two consecutive dyadic blocks of first-level mixtures, or a
first-level mixture `[2n, 2n + 1]`. -/
theorem map_mem_nodes_subMold (j : Fin 3) (p : Mold (Leaf l) × Mold (Leaf l))
    (hp : p ∈ (subMold l j).nodes) :
    (∃ q n, n + 2 ^ (q + 1) ≤ 2 ^ (2 * l + 1) ∧
      p = (dyadic q (fun k => Mold.node (Mold.leaf (j, ifaceLeaf (l := l) (n + k) 0))
            (Mold.leaf (j, ifaceLeaf (l := l) (n + k) 1))),
          dyadic q (fun k => Mold.node (Mold.leaf (j, ifaceLeaf (l := l) (n + 2 ^ q + k) 0))
            (Mold.leaf (j, ifaceLeaf (l := l) (n + 2 ^ q + k) 1))))) ∨
    ∃ n < 2 ^ (2 * l + 1),
      p = (Mold.leaf (j, ifaceLeaf (l := l) n 0), Mold.leaf (j, ifaceLeaf (l := l) n 1)) := by
  rcases map_mem_nodes_dyadic _ _ p hp with ⟨q, n, hn, rfl⟩ | ⟨n, hn, hp⟩
  · exact Or.inl ⟨q, n, hn, rfl⟩
  · refine Or.inr ⟨n, hn, ?_⟩
    simpa [Mold.nodes] using hp

private lemma not_isLeaf_dyadic {ι : Type} (q : ℕ) (f : ℕ → Mold ι) (hf : ¬ (f 0).IsLeaf) :
    ¬ (dyadic q f).IsLeaf := by
  cases q with
  | zero => exact hf
  | succ q => simp [dyadic, Mold.IsLeaf]

private lemma not_isLeaf_subMold (j : Fin 3) : ¬ (subMold l j).IsLeaf := by
  simp [subMold, dyadic, Mold.IsLeaf]

/-- A function of the weights that agrees on `Θ_l` with a linear map. -/
private def LinOn {V : Type} [AddCommGroup V] [Module ℝ V] (S : TriMold l)
    (f : (Leaf l → ℝ) → V) : Prop :=
  ∃ L : (Leaf l → ℝ) →ₗ[ℝ] V, ∀ t ∈ Theta S, f t = L t

section LinOn

variable {V : Type} [AddCommGroup V] [Module ℝ V] {S : TriMold l}

private lemma LinOn.add {f g : (Leaf l → ℝ) → V} (hf : LinOn S f) (hg : LinOn S g) :
    LinOn S (fun t => f t + g t) := by
  obtain ⟨L, hL⟩ := hf
  obtain ⟨M, hM⟩ := hg
  exact ⟨L + M, fun t ht => by simp [hL t ht, hM t ht]⟩

private lemma LinOn.sub {f g : (Leaf l → ℝ) → V} (hf : LinOn S f) (hg : LinOn S g) :
    LinOn S (fun t => f t - g t) := by
  obtain ⟨L, hL⟩ := hf
  obtain ⟨M, hM⟩ := hg
  exact ⟨L - M, fun t ht => by simp [hL t ht, hM t ht]⟩

private lemma LinOn.smul {f : (Leaf l → ℝ) → V} (c : ℝ) (hf : LinOn S f) :
    LinOn S (fun t => c • f t) := by
  obtain ⟨L, hL⟩ := hf
  exact ⟨c • L, fun t ht => by simp [hL t ht]⟩

private lemma LinOn.zero : LinOn S (fun _ => (0 : V)) := ⟨0, fun _ _ => rfl⟩

private lemma LinOn.sum {α : Type} {s : Finset α} {f : α → (Leaf l → ℝ) → V}
    (h : ∀ a ∈ s, LinOn S (f a)) : LinOn S (fun t => ∑ a ∈ s, f a t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LinOn.zero : LinOn S (fun _ => (0 : V)))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

private lemma linOn_coord (p : Leaf l) (c : V) : LinOn S (fun t => t p • c) :=
  ⟨(LinearMap.proj p).smulRight c, fun _ _ => rfl⟩

private lemma LinOn.congr {f g : (Leaf l → ℝ) → V} (hf : LinOn S f)
    (h : ∀ t ∈ Theta S, g t = f t) : LinOn S g := by
  obtain ⟨L, hL⟩ := hf
  exact ⟨L, fun t ht => (h t ht).trans (hL t ht)⟩

end LinOn

/-- On `Θ_l`, the barycenter of a sub-mold is linear in the weights (eq. (5.14)). -/
private lemma linOn_subMold {V : Type} [AddCommGroup V] [Module ℝ V] (S : TriMold l)
    (w : Leaf l → V) (j : Fin 3) : LinOn S (fun t => (subMold l j).point t w) :=
  ((LinOn.sum fun k _ => linOn_coord (j, k) (w (j, k))).smul 3).congr
    fun _ ht => point_subMold_theta ht w j

/-- On `Θ_l`, the mass point of a dyadic block of first-level mixtures is linear in the weights
(eqs. (5.10), (5.11)). -/
private lemma linOn_block {V : Type} [AddCommGroup V] [Module ℝ V] (S : TriMold l)
    (w : Leaf l → V) (j : Fin 3) (q n : ℕ) :
    LinOn S (fun t => (dyadic q fun k => Mold.node (Mold.leaf (j, ifaceLeaf (l := l) (n + k) 0))
      (Mold.leaf (j, ifaceLeaf (l := l) (n + k) 1))).point t w) :=
  ((LinOn.sum fun _ _ => ((linOn_coord _ _).add (linOn_coord _ _)).smul _).smul _).congr
    fun _ ht => point_dyadic_theta ht w j q n

/-- On `Θ_l`, each sub-mold has weight `1/3`. -/
private lemma weight_subMold {S : TriMold l} {t : Leaf l → ℝ} (ht : t ∈ Theta S) (j : Fin 3) :
    (subMold l j).weight t = 1 / 3 := by
  have h : ∀ k ∈ Finset.range (2 ^ (2 * l + 1)),
      (Mold.node (Mold.leaf (j, ifaceLeaf (l := l) k 0))
        (Mold.leaf (j, ifaceLeaf (l := l) k 1))).weight t = 1 / (3 * 2 ^ (2 * l + 1)) :=
    fun k hk => ht.2.1 j ⟨k, Finset.mem_range.mp hk⟩
  rw [subMold, map_weight_dyadic, Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  push_cast
  field_simp

/-- Every mixture of the mold `S.tree` is a first-level mixture of two leaves `2n, 2n + 1` of a
sub-mold, or a mixture of two non-leaves whose mass points are linear in the weights on `Θ_l`. -/
private lemma map_nodes_cases {V : Type} [AddCommGroup V] [Module ℝ V] (S : TriMold l)
    (w : Leaf l → V) (p : Mold (Leaf l) × Mold (Leaf l)) (hp : p ∈ S.tree.nodes) :
    (∃ j : Fin 3, ∃ n < 2 ^ (2 * l + 1),
      p = (Mold.leaf (j, ifaceLeaf (l := l) n 0), Mold.leaf (j, ifaceLeaf (l := l) n 1))) ∨
    (¬ p.1.IsLeaf ∧ ¬ p.2.IsLeaf ∧ LinOn S (fun t => p.1.point t w) ∧
      LinOn S (fun t => p.2.point t w)) := by
  have hsub : ∀ (j : Fin 3), ∀ p ∈ (subMold l j).nodes,
      (∃ j : Fin 3, ∃ n < 2 ^ (2 * l + 1),
        p = (Mold.leaf (j, ifaceLeaf (l := l) n 0), Mold.leaf (j, ifaceLeaf (l := l) n 1))) ∨
      (¬ p.1.IsLeaf ∧ ¬ p.2.IsLeaf ∧ LinOn S (fun t => p.1.point t w) ∧
        LinOn S (fun t => p.2.point t w)) := by
    intro j p hp
    rcases map_mem_nodes_subMold j p hp with ⟨q, n, hn, rfl⟩ | ⟨n, hn, rfl⟩
    · have h2 : (2 : ℕ) ^ (q + 1) = 2 ^ q + 2 ^ q := by ring
      have hq : 0 < 2 ^ q := by positivity
      exact Or.inr ⟨not_isLeaf_dyadic _ _ (by simp [Mold.IsLeaf]),
        not_isLeaf_dyadic _ _ (by simp [Mold.IsLeaf]),
        linOn_block S w j q n, linOn_block S w j q (n + 2 ^ q)⟩
    · exact Or.inl ⟨j, n, hn, rfl⟩
  simp only [TriMold.tree, Mold.nodes, List.mem_cons, List.mem_append] at hp
  rcases hp with rfl | (rfl | hp | hp) | hp
  · refine Or.inr ⟨by simp [Mold.IsLeaf], not_isLeaf_subMold _, ?_, linOn_subMold S w _⟩
    refine (((linOn_subMold S w (S.order 0)).smul (1 - 1 / 2)).add
      ((linOn_subMold S w (S.order 1)).smul (1 / 2))).congr fun t ht => ?_
    have hlam : Mold.lam t (subMold l (S.order 0)) (subMold l (S.order 1)) = 1 / 2 := by
      simp only [Mold.lam, weight_subMold ht]
      norm_num
    simp only [Mold.point, hlam]
  · exact Or.inr ⟨not_isLeaf_subMold _, not_isLeaf_subMold _, linOn_subMold S w _,
      linOn_subMold S w _⟩
  · exact hsub _ p hp
  · exact hsub _ p hp
  · exact hsub _ p hp

/-- The mass point of the matrix-valued mold is the matrix whose rows are the mass points for
`∇u` and for `∇v`. -/
private lemma map_point_gradMat (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ) (t : Leaf l → ℝ) :
    ∀ M : Mold (Leaf l), M.point t (fun q => gradMat l u v (S.leafTri q)) =
      Matrix.of ![M.point t (fun q => grad l u (S.leafTri q)),
        M.point t (fun q => grad l v (S.leafTri q))]
  | .leaf q => rfl
  | .node L R => by
    simp only [Mold.point]
    rw [map_point_gradMat S u v t L, map_point_gradMat S u v t R]
    ext i k
    fin_cases i <;> simp

private lemma map_of_sub_of (a b c d : Fin 2 → ℝ) :
    Matrix.of ![a, b] - Matrix.of ![c, d] = Matrix.of ![a - c, b - d] := by
  ext i k
  fin_cases i <;> simp

/-- Across an interface, the difference of the gradients of `w ∈ ℙ_l` on any two of its sides is
a multiple of the normal. -/
private lemma map_jump_normal {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) (f : Iface l) {x y : Tri l}
    (hx : x = f.sides.1 ∨ x = f.sides.2) (hy : y = f.sides.1 ∨ y = f.sides.2) :
    ∃ c : ℝ, grad l w x - grad l w y = c • f.normal := by
  obtain ⟨κ, hκ⟩ := grad_sides_sub hw f
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨κ, hκ⟩
  · exact ⟨-κ, by rw [neg_smul, ← hκ, neg_sub]⟩
  · exact ⟨0, by simp⟩

/-- **Equation (5.15)** (`firstcero`). For `w ∈ ℙ_l` and `t ∈ Θ_l`, the barycenters `𝕎_j` of the
three sub-molds average to `0`: `0 = (𝕎_1 + 𝕎_2 + 𝕎_3)/3`. -/
theorem equation5_15 (S : TriMold l) {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) {t : Leaf l → ℝ}
    (ht : t ∈ Theta S) :
    (1 / 3 : ℝ) • ∑ j : Fin 3, (subMold l j).point t (leafGrad S w) = 0 := by
  simp only [point_subMold_theta ht, ← Finset.smul_sum, smul_smul]
  have h1 : ∑ j : Fin 3, ∑ k : Fin (2 ^ (2 * l + 2)), t (j, k) • leafGrad S w (j, k) =
      ∑ p : Leaf l, t p • grad l w (S.leafTri p) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    rfl
  rw [h1, ← Finset.sum_fiberwise Finset.univ S.leafTri]
  have h2 : ∀ s : Tri l, ∑ p ∈ Finset.univ.filter (fun p => S.leafTri p = s),
      t p • grad l w (S.leafTri p) = (1 / 2 ^ (2 * l + 1) : ℝ) • grad l w s := by
    intro s
    rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2], ← Finset.sum_smul]
    congr 1
    exact ht.2.2 s
  simp only [h2, equation5_13 hw, smul_zero]

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
  intro p hp N hN hNl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
  rcases map_nodes_cases S w p hp with ⟨j, n, -, rfl⟩ | ⟨-, -, h1, h2⟩
  · rcases hN with rfl | rfl <;> exact absurd trivial hNl
  · rcases hN with rfl | rfl
    · exact h1
    · exact h2

/-- **Proposition 6.3 (1)** (`convexidad`), decomposition directions. On `Θ_l`, the decomposition
direction of every mixture above the first level depends linearly on the weights. -/
theorem proposition6_3_dir (S : TriMold l) (w : Leaf l → Fin 2 → ℝ) :
    ∀ p ∈ S.tree.nodes, ¬ (p.1.IsLeaf ∧ p.2.IsLeaf) →
      ∃ L : (Leaf l → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), ∀ t ∈ Theta S, p.1.point t w - p.2.point t w = L t := by
  intro p hp hpl
  rcases map_nodes_cases S w p hp with ⟨j, n, -, rfl⟩ | ⟨-, -, h1, h2⟩
  · exact absurd ⟨trivial, trivial⟩ hpl
  · exact h1.sub h2

/-- **Proposition 6.3 (2)** (`convexidad`). Each `𝐓(t)` is convex. -/
theorem proposition6_3 (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ) (t : Leaf l → ℝ) :
    Convex ℝ (T S u v t) := by
  intro r₀ hr₀ r₁ hr₁ a b ha hb hab
  have hr : a • r₀ + b • r₁ ∈ Theta S := convex_theta S hr₀.1 hr₁.1 ha hb hab
  refine ⟨hr, fun p hp hpl => ?_⟩
  obtain ⟨L, hL⟩ := proposition6_3_dir S (fun q => grad l v (S.leafTri q)) p hp hpl
  have h₀ := hr₀.2 p hp hpl
  have h₁ := hr₁.2 p hp hpl
  rw [hL _ hr₀.1] at h₀
  rw [hL _ hr₁.1] at h₁
  rw [hL _ hr, map_add, map_smul, map_smul]
  unfold Parallel at h₀ h₁ ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination a * h₀ + b * h₁

/-- **Subsection 6.1** (`cuatro`), closed graph: if `r_n ∈ 𝐓(t_n)`, `t_n ∈ Θ_l`, `r_n → r` and
`t_n → t`, then `r ∈ 𝐓(t)`, "because the dependence of elements in (5.12) on `t` is continuous" (the notation of (3.7)).
On `Θ_l` that continuity is the linearity of Proposition 6.3 (1), which the proof uses. -/
theorem section6_1_isClosed_graph (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ) :
    IsClosed {p : (Leaf l → ℝ) × (Leaf l → ℝ) | p.1 ∈ Theta S ∧ p.2 ∈ T S u v p.1} := by
  -- On `Θ_l × Θ_l` the conditions of `𝐓` are `det (L_U t, L_V r) = 0` for the linear maps
  -- `L_U`, `L_V` of Proposition 6.3 (1): the graph is `(Θ_l × Θ_l) ∩ ⋂ {closed sets}`.
  choose LU hLU using proposition6_3_dir S (fun q => grad l u (S.leafTri q))
  choose LV hLV using proposition6_3_dir S (fun q => grad l v (S.leafTri q))
  have heq : {p : (Leaf l → ℝ) × (Leaf l → ℝ) | p.1 ∈ Theta S ∧ p.2 ∈ T S u v p.1} =
      (Theta S ×ˢ Theta S) ∩ ⋂ (q : Mold (Leaf l) × Mold (Leaf l)) (hq : q ∈ S.tree.nodes)
        (hq' : ¬ (q.1.IsLeaf ∧ q.2.IsLeaf)),
        {p | (LU q hq hq' p.1) 0 * (LV q hq hq' p.2) 1 - (LU q hq hq' p.1) 1 * (LV q hq hq' p.2) 0
          = 0} := by
    ext ⟨t, r⟩
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_iInter, T]
    constructor
    · rintro ⟨ht, hr, h⟩
      refine ⟨⟨ht, hr⟩, fun q hq hq' => ?_⟩
      have := h q hq hq'
      rwa [hLU q hq hq' t ht, hLV q hq hq' r hr] at this
    · rintro ⟨⟨ht, hr⟩, h⟩
      refine ⟨ht, hr, fun q hq hq' => ?_⟩
      rw [Parallel, hLU q hq hq' t ht, hLV q hq hq' r hr]
      exact h q hq hq'
  rw [heq]
  refine ((isClosed_theta S).prod (isClosed_theta S)).inter ?_
  refine isClosed_iInter fun q => isClosed_iInter fun hq => isClosed_iInter fun hq' => ?_
  have h₁ : Continuous (LU q hq hq') := LinearMap.continuous_of_finiteDimensional _
  have h₂ : Continuous (LV q hq hq') := LinearMap.continuous_of_finiteDimensional _
  exact isClosed_eq (by fun_prop) continuous_const

/-- **Subsection 6.1** (`cuatro`), compact values: each `𝐓(t)`, `t ∈ Θ_l`, is compact. -/
theorem section6_1_isCompact (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ) {t : Leaf l → ℝ}
    (ht : t ∈ Theta S) : IsCompact (T S u v t) := by
  have hc : IsClosed (T S u v t) := by
    have := (section6_1_isClosed_graph S u v).preimage
      (continuous_const.prodMk continuous_id : Continuous fun r : Leaf l → ℝ => (t, r))
    convert this using 1
    ext r
    simp [ht]
  exact (isCompact_theta S).of_isClosed_subset hc (T_subset_theta S u v t)

/-- **Subsection 6.1** (`cuatro`), upper semicontinuity of `𝐓` on `Θ_l`, which follows from the
closed graph because `Θ_l` is compact (the paper calls the closed graph property upper
semicontinuity). -/
theorem section6_1_usc (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ) :
    External.Kakutani.UpperSemicontinuousOn (T S u v) (Theta S) := by
  -- The compact set `Θ_l \ W` misses `𝐓(t)`, so each of its points `r` has a neighbourhood of
  -- `(t, r)` off the closed graph; by compactness, for `y` near `t`, `𝐓(y) ∩ (Θ_l \ W) = ∅`.
  intro t ht W hW hTW
  have hG : IsOpen {p : (Leaf l → ℝ) × (Leaf l → ℝ) | p.1 ∈ Theta S ∧ p.2 ∈ T S u v p.1}ᶜ :=
    (section6_1_isClosed_graph S u v).isOpen_compl
  have key : ∀ᶠ y in 𝓝 t, ∀ r ∈ Theta S \ W,
      (y, r) ∈ {p : (Leaf l → ℝ) × (Leaf l → ℝ) | p.1 ∈ Theta S ∧ p.2 ∈ T S u v p.1}ᶜ := by
    refine ((isCompact_theta S).diff hW).eventually_forall_of_forall_eventually
      fun r hr => hG.mem_nhds ?_
    rintro ⟨-, hr'⟩
    exact hr.2 (hTW hr')
  filter_upwards [nhdsWithin_le_nhds key, self_mem_nhdsWithin] with y hy hyΘ r hr
  by_contra hrW
  exact hy r ⟨T_subset_theta S u v y hr, hrW⟩ ⟨hyΘ, hr⟩

/-- **Proposition 6.1** (`facil`). If `t ∈ Θ_l` is a fixed point of `𝐓`, then the gradient
measure `ν` of `(u, v)` is a laminate. -/
theorem proposition6_1 (S : TriMold l) {u v : (Fin 2 → ℝ) → ℝ} (hu : u ∈ PL l) (hv : v ∈ PL l)
    {t : Leaf l → ℝ} (ht : t ∈ Theta S) (hfix : t ∈ T S u v t) :
    IsLaminate (gradMeasure l u v) := by
  set A : Leaf l → Matrix (Fin 2) (Fin 2) ℝ := fun q => gradMat l u v (S.leafTri q) with hA
  -- the total weight is `1`
  have hw : S.tree.weight t = 1 := by
    simp only [TriMold.tree, Mold.weight, weight_subMold ht]
    norm_num
  -- the decomposition directions have rank at most one
  have hrank : ∀ p ∈ S.tree.nodes, (p.1.point t A - p.2.point t A).rank ≤ 1 := by
    intro p hp
    rw [map_point_gradMat, map_point_gradMat, map_of_sub_of,
      Matrix.rank_le_one_iff_det_eq_zero_of_fin_two, Matrix.det_of_rows_fin_two]
    rcases map_nodes_cases S A p hp with ⟨j, n, hn, rfl⟩ | ⟨h1, -, -, -⟩
    · -- a first-level mixture: both jumps are multiples of the normal of the interface
      set f := (S.label j ⟨n, hn⟩).1
      have hpair : ({S.leafTri (j, ifaceLeaf n 0), S.leafTri (j, ifaceLeaf n 1)} : Set (Tri l)) =
          {f.sides.1, f.sides.2} := S.leafTri_pair j ⟨n, hn⟩
      have hx : S.leafTri (j, ifaceLeaf n 0) = f.sides.1 ∨
          S.leafTri (j, ifaceLeaf n 0) = f.sides.2 := by
        have h := (Set.ext_iff.mp hpair (S.leafTri (j, ifaceLeaf n 0))).mp (by simp)
        simpa using h
      have hy : S.leafTri (j, ifaceLeaf n 1) = f.sides.1 ∨
          S.leafTri (j, ifaceLeaf n 1) = f.sides.2 := by
        have h := (Set.ext_iff.mp hpair (S.leafTri (j, ifaceLeaf n 1))).mp (by simp)
        simpa using h
      obtain ⟨α, hα⟩ := map_jump_normal hu f hx hy
      obtain ⟨β, hβ⟩ := map_jump_normal hv f hx hy
      simp only [Mold.point]
      rw [hα, hβ]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · -- a mixture above the first level: the fixed point makes the directions parallel
      exact hfix.2 p hp fun h => h1 h.1
  -- the leaf measure is `ν`
  have hsum : ∀ g : Leaf l → (Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ),
      (S.tree.leaves.map g).sum = ∑ p, g p := by
    intro g
    rw [← List.sum_toFinset g S.tree_leaves_nodup]
    congr 1
    ext p
    simp [S.mem_tree_leaves p]
  have hmeas : S.tree.leafMeasure t A = gradMeasure l u v := by
    rw [Mold.leafMeasure_eq_sum, hsum, gradMeasure, ← Finset.sum_fiberwise Finset.univ S.leafTri]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← ht.2.2 s, Finsupp.single_finsetSum, TriMold.C]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [hA, (Finset.mem_filter.mp hp).2]
  rw [← hmeas]
  exact Mold.isLaminate_leafMeasure ht.1 A S.tree hw hrank

end Pedregal
