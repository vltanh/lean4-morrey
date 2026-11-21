module

public import Morrey.Defs

/-!
# Section 3: `(H_n)`-conditions and their molds

Definitions 3.1–3.4 and Proposition 3.3. A mold (Definition 3.2) is a `Mold`: an ordered binary
tree whose leaves are labels of the initial pairs. Fed with weights `t` and vectors `w`, it
produces the `(H_n)`-condition of Definition 3.1 in its bottom-to-top description: the weight of
a mixture `[L, R]` is the sum of the weights of `L` and `R`, its mass point is
`(1 − λ) w_L + λ w_R` with `λ` the relative weight of `R` (eqs. (3.3)–(3.6)), and its
decomposition direction is `w_L − w_R` (eq. (3.5)).

* `Mold.leaves`: the leaves of a mold, from left to right.
* `Mold.IsPerfect m`: every leaf at depth `m`, that is, mixtures done "in a complete,
  pair-wise manner at each level, before proceeding to the next" (Definition 3.3).
* `Mold.IsDyadic m`: a dyadic mold in `m` levels for `2^m` elements (Definition 3.3).
* `proposition3_3`: a dyadic mold is the standard dyadic mold `dyadic m` with its leaves
  relabelled by a unique permutation.
* `Mold.IsTriDyadic m`: the tri-dyadic molds of Definition 3.4.
* `Mold.point_eq_barycenter`: for positive weights, the mass point of a mold is the barycenter of
  its leaves.

Representation. The paper writes molds with brackets (`[[1, 3], 5], 2, 4`); a bracket is a node
of the tree, and the order inside a bracket is the order of the tree, which fixes the sign of the
decomposition direction (3.5). Proposition 3.3's permutation is unique only for this ordered
reading.
-/

@[expose] public section

namespace Morrey

namespace Mold

variable {ι : Type} {V : Type} [AddCommGroup V] [Module ℝ V]

/-- The leaves of a mold, from left to right. -/
def leaves : Mold ι → List ι
  | leaf i => [i]
  | node L R => leaves L ++ leaves R

/-- Every leaf of the mold is at depth `m`. -/
def IsPerfect : ℕ → Mold ι → Prop
  | 0, M => M.IsLeaf
  | _ + 1, leaf _ => False
  | m + 1, node L R => IsPerfect m L ∧ IsPerfect m R

/-- Relabel the leaves of a mold. -/
def map {κ : Type} (σ : ι → κ) : Mold ι → Mold κ
  | leaf i => leaf (σ i)
  | node L R => node (map σ L) (map σ R)

/-- **Definition 3.3**. A dyadic mold in `m` levels for `2^m` elements: the mixtures are done in
a complete, pair-wise manner at each level before the next (`IsPerfect m`), and each of the
`2^m` elements is a leaf exactly once. -/
def IsDyadic (m : ℕ) (M : Mold (Fin (2 ^ m))) : Prop :=
  M.IsPerfect m ∧ M.leaves.Nodup

/-- **Definition 3.4**. A tri-dyadic mold for `3 × 2^m` elements, with the elements of the three
blocks `{0, …, 2^m − 1}`, `{2^m, …}`, `{2 · 2^m, …}` labelled `(j, k)`: the three blocks are first
exhausted separately by dyadic molds, and the three resulting pairs are then mixed in a fixed
way, `[[j₀, j₁], j₂]` for an ordering `(j₀, j₁, j₂)` of the blocks (every mixture of three pairs
is of this form up to the order inside a bracket). -/
def IsTriDyadic (m : ℕ) (M : Mold (Fin 3 × Fin (2 ^ m))) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (D : Fin 3 → Mold (Fin (2 ^ m))), (∀ j, (D j).IsDyadic m) ∧
    M = node (node ((D (σ 0)).map fun k => (σ 0, k)) ((D (σ 1)).map fun k => (σ 1, k)))
      ((D (σ 2)).map fun k => (σ 2, k))

/-- The weight of a mold is the sum of the weights of its leaves. -/
theorem weight_eq_sum_leaves (t : ι → ℝ) (M : Mold ι) :
    M.weight t = (M.leaves.map t).sum := by
  sorry

/-- With nonnegative weights, the weight of a mold is nonnegative. -/
theorem weight_nonneg {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) (M : Mold ι) : 0 ≤ M.weight t := by
  sorry

/-- For a mold of positive weight with nonnegative leaf weights, the mass point is the
barycenter of the leaves: `weight · point = ∑ t_i w_i`. -/
theorem weight_smul_point {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) (w : ι → V) (M : Mold ι)
    (hM : 0 < M.weight t) : M.weight t • M.point t w = (M.leaves.map fun i => t i • w i).sum := by
  sorry

/-- The mass point is linear in the vectors: the point for `a • w + b • w'` is
`a • point w + b • point w'`. -/
theorem point_linear (t : ι → ℝ) (w w' : ι → V) (a b : ℝ) (M : Mold ι) :
    M.point t (fun i => a • w i + b • w' i) = a • M.point t w + b • M.point t w' := by
  sorry

end Mold

/-- The standard dyadic mold `dyadic m` on the leaves `0, …, 2^m − 1` of `Fin (2^m)`. -/
def dyadicStd (m : ℕ) : Mold (Fin (2 ^ m)) :=
  dyadic m fun k => Mold.leaf ⟨k % 2 ^ m, Nat.mod_lt _ (by positivity)⟩

/-- **Proposition 3.3** (`permutacion`). For a dyadic mold in `m` levels there is a unique
permutation `σ` of `{1, …, 2^m}` such that, after relabelling the leaves by `σ`, the mixtures are
`[2i − 1, 2i]` at all levels: the mold is the standard dyadic mold with its leaf `k` labelled
`σ k`. -/
theorem proposition3_3 (m : ℕ) (M : Mold (Fin (2 ^ m))) (hM : M.IsDyadic m) :
    ∃! σ : Equiv.Perm (Fin (2 ^ m)), M = (dyadicStd m).map σ := by
  sorry

end Morrey
