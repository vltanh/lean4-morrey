module

public import Pedregal.Defs

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

namespace Pedregal

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
  induction M with
  | leaf i => simp [weight, leaves]
  | node L R ihL ihR => simp [weight, leaves, ihL, ihR]

/-- With nonnegative weights, the weight of a mold is nonnegative. -/
theorem weight_nonneg {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) (M : Mold ι) : 0 ≤ M.weight t := by
  induction M with
  | leaf i => exact ht i
  | node L R ihL ihR => exact add_nonneg ihL ihR

/-- `weight · point = ∑ t_i w_i` for nonnegative leaf weights, also when the weight vanishes
(both sides are then `0`). -/
private theorem weight_smul_point_aux {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) (w : ι → V)
    (M : Mold ι) : M.weight t • M.point t w = (M.leaves.map fun i => t i • w i).sum := by
  induction M with
  | leaf i => simp [weight, point, leaves]
  | node L R ihL ihR =>
    have hL := weight_nonneg ht L
    have hR := weight_nonneg ht R
    simp only [leaves, List.map_append, List.sum_append, ← ihL, ← ihR, weight, point, lam]
    split_ifs with hs
    · have hs' : weight t L + weight t R ≠ 0 := hs.ne'
      rw [smul_add, smul_smul, smul_smul]
      congr 2
      · field_simp
        ring
      · field_simp
    · have h1 : weight t L = 0 := by linarith
      have h2 : weight t R = 0 := by linarith
      simp [h1, h2]

/-- With nonnegative leaf weights, the mass point of a mold is the barycenter of its leaves:
`weight · point = ∑ t_i w_i` (both sides vanish when the weight is `0`). -/
theorem weight_smul_point {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) (w : ι → V) (M : Mold ι) :
    M.weight t • M.point t w = (M.leaves.map fun i => t i • w i).sum :=
  weight_smul_point_aux ht w M

/-- The mass point is linear in the vectors: the point for `a • w + b • w'` is
`a • point w + b • point w'`. -/
theorem point_linear (t : ι → ℝ) (w w' : ι → V) (a b : ℝ) (M : Mold ι) :
    M.point t (fun i => a • w i + b • w' i) = a • M.point t w + b • M.point t w' := by
  induction M with
  | leaf i => simp [point]
  | node L R ihL ihR =>
    simp only [point, ihL, ihR]
    module

/-- The dyadic mold in `m` levels on `f` only depends on `f 0, …, f (2^m − 1)`. -/
theorem found_dyadic_congr :
    ∀ (m : ℕ) {f f' : ℕ → Mold ι}, (∀ k < 2 ^ m, f k = f' k) → dyadic m f = dyadic m f'
  | 0, _, _, h => h 0 (by norm_num)
  | m + 1, f, f', h => by
    simp only [dyadic]
    rw [found_dyadic_congr m fun k hk => h k (by rw [pow_succ]; omega),
      found_dyadic_congr m (f := fun k => f (2 ^ m + k)) (f' := fun k => f' (2 ^ m + k))
        fun k hk => h _ (by rw [pow_succ]; omega)]

/-- Relabelling the leaves of a dyadic mold relabels its molds. -/
theorem found_map_dyadic {κ : Type} (σ : ι → κ) :
    ∀ (m : ℕ) (f : ℕ → Mold ι), (dyadic m f).map σ = dyadic m fun k => (f k).map σ
  | 0, _ => rfl
  | m + 1, f => by simp only [dyadic, map, found_map_dyadic σ m]

/-- The leaves of the dyadic mold on the leaves `g 0, …, g (2^m − 1)` are these, in order. -/
theorem found_leaves_dyadic :
    ∀ (m : ℕ) (g : ℕ → ι), (dyadic m fun k => leaf (g k)).leaves = (List.range (2 ^ m)).map g
  | 0, _ => rfl
  | m + 1, g => by
    simp only [dyadic, leaves, found_leaves_dyadic m]
    rw [pow_succ, mul_two, List.range_add, List.map_append, List.map_map]
    rfl

/-- A mold with every leaf at depth `m` is the dyadic mold in `m` levels on some leaves. -/
theorem found_exists_eq_dyadic_of_isPerfect :
    ∀ (m : ℕ) (M : Mold ι), M.IsPerfect m → ∃ g : ℕ → ι, M = dyadic m fun k => leaf (g k)
  | 0, leaf i, _ => ⟨fun _ => i, rfl⟩
  | 0, node _ _, h => h.elim
  | _ + 1, leaf _, h => h.elim
  | m + 1, node L R, h => by
    obtain ⟨gL, rfl⟩ := found_exists_eq_dyadic_of_isPerfect m L h.1
    obtain ⟨gR, rfl⟩ := found_exists_eq_dyadic_of_isPerfect m R h.2
    refine ⟨fun k => if k < 2 ^ m then gL k else gR (k - 2 ^ m), ?_⟩
    simp only [dyadic]
    congr 1
    · exact found_dyadic_congr m fun k hk => by simp [hk]
    · exact found_dyadic_congr m fun k _ => by simp

end Mold

/-- The standard dyadic mold `dyadic m` on the leaves `0, …, 2^m − 1` of `Fin (2^m)`. -/
def dyadicStd (m : ℕ) : Mold (Fin (2 ^ m)) :=
  dyadic m fun k => Mold.leaf ⟨k % 2 ^ m, Nat.mod_lt _ (by positivity)⟩

/-- **Proposition 3.3** (`permutacion`). For a dyadic mold in `m` levels there is a unique
permutation `σ` of `{1, …, 2^m}` such that, after relabelling the leaves by `σ⁻¹`, the mixtures
are `[2i − 1, 2i]` at all levels: the mold is the standard dyadic mold with its leaf `k` labelled
`σ k`. -/
theorem proposition3_3 (m : ℕ) (M : Mold (Fin (2 ^ m))) (hM : M.IsDyadic m) :
    ∃! σ : Equiv.Perm (Fin (2 ^ m)), M = (dyadicStd m).map σ := by
  have hpos : 0 < 2 ^ m := by positivity
  -- relabelling the standard dyadic mold by `σ` gives the dyadic mold on `σ 0, …, σ (2^m − 1)`
  have hstd : ∀ σ : Fin (2 ^ m) → Fin (2 ^ m), (dyadicStd m).map σ =
      dyadic m fun k => Mold.leaf (σ ⟨k % 2 ^ m, Nat.mod_lt _ hpos⟩) := fun σ => by
    rw [dyadicStd, Mold.found_map_dyadic]
    rfl
  -- the mold is the dyadic mold on its leaves `g 0, …, g (2^m − 1)`, in this order
  obtain ⟨g, hg⟩ := Mold.found_exists_eq_dyadic_of_isPerfect m M hM.1
  have hleaves : M.leaves = (List.range (2 ^ m)).map g := by
    rw [hg, Mold.found_leaves_dyadic]
  -- `σ k` is the `k`-th leaf; it is a permutation since the leaves are distinct
  have hinj : Function.Injective fun k : Fin (2 ^ m) => g k := by
    intro a b hab
    have hnd := hM.2
    rw [hleaves] at hnd
    exact Fin.ext (List.inj_on_of_nodup_map hnd (List.mem_range.2 a.2) (List.mem_range.2 b.2) hab)
  let σ : Equiv.Perm (Fin (2 ^ m)) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσ : M = (dyadicStd m).map σ := by
    rw [hstd, hg]
    exact Mold.found_dyadic_congr m fun k hk => by simp [σ, Nat.mod_eq_of_lt hk]
  refine ⟨σ, hσ, fun τ hτ => ?_⟩
  -- uniqueness: the leaves of `(dyadicStd m).map τ` are `τ 0, …, τ (2^m − 1)`, in this order
  have h := congrArg Mold.leaves (hτ.symm.trans hσ)
  rw [hstd, hstd, Mold.found_leaves_dyadic, Mold.found_leaves_dyadic, List.map_inj_left] at h
  ext x
  simpa [Nat.mod_eq_of_lt x.2] using congrArg Fin.val (h x (List.mem_range.2 x.2))

end Pedregal
