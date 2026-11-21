module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The paper's objects

Shared definitions for P. Pedregal, *Morrey's conjecture: rank-one convexity implies
quasi-convexity for two-dimensional, two-component maps*, arXiv:1905.06571v5 (2026). The block
between the markers is copied word for word into `Challenge.lean` by
`scripts/sync_challenge_defs.py`.

Points of `ℝ²` are `Fin 2 → ℝ`, `2 × 2` matrices are `Matrix (Fin 2) (Fin 2) ℝ`, and the matrix
of a pair `(u, v)` has rows `∇u` and `∇v`.

* `Tri l`, `triangle`, `centroid`: the triangulation `τ_l` of the unit square `Q` (Section 4):
  `2^l × 2^l` equal squares, each cut along the diagonal with normal `(1, 1)`.
* `PL l`: the space `ℙ_l` of `Q`-periodic, continuous, `τ_l`-piecewise affine functions.
* `grad l w s`: the constant gradient of `w ∈ ℙ_l` on the triangle `s`.
* `Iface`, `Iface.sides`, `ifaceSet`: the planar interfaces of `τ_l` (periodic), their two
  adjacent triangles, and the interfaces with the two normals of the sub-mold `j` (eq. (4.2)).
* `Mold`: a mold (skeleton) of an `(H_n)`-condition (Definitions 3.1, 3.2), an ordered binary
  tree whose leaves are labels of pairs (weight, vector). `Mold.weight`, `Mold.point`: the
  weights and mass points of the bottom-to-top recursion (3.3)–(3.6); the decomposition direction
  at a node `[L, R]` is `L.point − R.point` (3.5). `Mold.nodes`: the mixtures of a mold.
* `dyadic`: the dyadic mold with mixtures `[2i − 1, 2i]` at all levels (after Proposition 3.3).
* `TriMold l`: a tri-dyadic mold `𝒮_l` for `τ_l` (Definition 4.1): a labelling of the
  interfaces of each sub-mold, the side of each interface that receives the first leaf, and the
  order in which the three barycenters are mixed. `TriMold.leafTri`: the triangle of each leaf;
  `TriMold.C s`: the class `𝒞_s` of the six leaves of the triangle `s` (eq. (4.3)).
* `Theta S`: the set `Θ_l` of weights (Definition 5.1).
* `Parallel`, `T`: the set-valued map `𝐓` (Definition 6.1).
* `gradMat`, `gradMeasure`: the matrix `(∇u, ∇v)` on a triangle and the measure `ν` (6.1).
* `IsLaminate`: laminates of finite order.

Indices are from `0`: the leaves `2i − 1, 2i` of the paper's interface `i` are the leaves
`2i, 2i + 1` here, and the leaf `(j − 1)·2^{2l+2} + k` of the paper is `(j, k)` with `j : Fin 3`.
-/

@[expose] public section

namespace Morrey

-- BEGIN SHARED DEFINITIONS

/-! ### The triangulation `τ_l` and the space `ℙ_l` -/

/-- A triangle of `τ_l`: the cell `(a, b)` of the `2^l × 2^l` grid of the unit square (the
square `[a, a + 1] × [b, b + 1]` scaled by `2^{-l}`) and `k = 0` for its lower-left triangle,
`k = 1` for its upper-right triangle. The cell is cut along its diagonal of normal `(1, 1)`. -/
abbrev Tri (l : ℕ) := Fin (2 ^ l) × Fin (2 ^ l) × Fin 2

/-- The closed triangle of `τ_l` with index `s`, as a subset of `ℝ²`. -/
noncomputable def triangle (l : ℕ) (s : Tri l) : Set (Fin 2 → ℝ) :=
  if s.2.2 = 0 then
    {x | (s.1 : ℝ) ≤ 2 ^ l * x 0 ∧ (s.2.1 : ℝ) ≤ 2 ^ l * x 1 ∧
      2 ^ l * x 0 + 2 ^ l * x 1 ≤ (s.1 : ℝ) + s.2.1 + 1}
  else
    {x | 2 ^ l * x 0 ≤ (s.1 : ℝ) + 1 ∧ 2 ^ l * x 1 ≤ (s.2.1 : ℝ) + 1 ∧
      (s.1 : ℝ) + s.2.1 + 1 ≤ 2 ^ l * x 0 + 2 ^ l * x 1}

/-- The centroid of the triangle `s` of `τ_l`. -/
noncomputable def centroid (l : ℕ) (s : Tri l) : Fin 2 → ℝ :=
  if s.2.2 = 0 then ![((s.1 : ℝ) + 1 / 3) / 2 ^ l, ((s.2.1 : ℝ) + 1 / 3) / 2 ^ l]
  else ![((s.1 : ℝ) + 2 / 3) / 2 ^ l, ((s.2.1 : ℝ) + 2 / 3) / 2 ^ l]

/-- The space `ℙ_l` of the paper: continuous functions on `ℝ²` that are `Q`-periodic (of period
`1` in each variable) and affine on every triangle of `τ_l`. -/
def PL (l : ℕ) : Set ((Fin 2 → ℝ) → ℝ) :=
  {w | Continuous w ∧ (∀ (x : Fin 2 → ℝ) (i : Fin 2), w (x + Pi.single i 1) = w x) ∧
    ∀ s : Tri l, ∃ c : ℝ, ∃ g : Fin 2 → ℝ, ∀ x ∈ triangle l s, w x = c + g 0 * x 0 + g 1 * x 1}

/-- The gradient of `w` on the triangle `s`: its derivative at the centroid of `s`. For
`w ∈ ℙ_l` it is the constant gradient `∇w|_{T_s}` of the paper. -/
noncomputable def grad (l : ℕ) (w : (Fin 2 → ℝ) → ℝ) (s : Tri l) : Fin 2 → ℝ :=
  fun i => fderiv ℝ w (centroid l s) (Pi.single i 1)

/-! ### Interfaces -/

/-- A planar interface of `τ_l`, with periodicity: `(0, a, b)` is the vertical edge (normal
`(1, 0)`) between the upper triangle of the cell `(a, b)` and the lower triangle of the cell
`(a + 1, b)`; `(1, a, b)` is the horizontal edge (normal `(0, 1)`) between the upper triangle of
`(a, b)` and the lower triangle of `(a, b + 1)`; `(2, a, b)` is the diagonal (normal `(1, 1)`)
between the two triangles of `(a, b)`. Indices of cells are taken modulo `2^l`. -/
abbrev Iface (l : ℕ) := Fin 3 × Fin (2 ^ l) × Fin (2 ^ l)

/-- The two triangles adjacent to an interface. -/
def Iface.sides {l : ℕ} (f : Iface l) : Tri l × Tri l :=
  if f.1 = 0 then ((f.2.1, f.2.2, 1), (f.2.1 + 1, f.2.2, 0))
  else if f.1 = 1 then ((f.2.1, f.2.2, 1), (f.2.1, f.2.2 + 1, 0))
  else ((f.2.1, f.2.2, 0), (f.2.1, f.2.2, 1))

/-- The interfaces of the sub-mold `j` (eq. (4.2), with `j` from `0`): those with normals
`(1, 0), (0, 1)` for `j = 0`, `(1, 0), (1, 1)` for `j = 1`, and `(0, 1), (1, 1)` for `j = 2`,
that is, every interface except those of kind `2 − j`. -/
def ifaceSet (l : ℕ) (j : Fin 3) : Set (Iface l) :=
  {f | f.1 ≠ ![2, 1, 0] j}

/-! ### Molds of `(H_n)`-conditions -/

/-- A mold (skeleton) of an `(H_n)`-condition: an ordered binary tree whose leaves are labels of
the initial pairs (weight, vector). A node `[L, R]` mixes the pairs produced by `L` and `R`. -/
inductive Mold (ι : Type) where
  | leaf : ι → Mold ι
  | node : Mold ι → Mold ι → Mold ι

namespace Mold

variable {ι : Type} {V : Type} [AddCommGroup V] [Module ℝ V]

/-- The weight of the pair produced by a mold, for leaf weights `t`: the sum of the weights. -/
def weight (t : ι → ℝ) : Mold ι → ℝ
  | leaf i => t i
  | node L R => weight t L + weight t R

/-- The relative volume fraction of the right part of the mixture `[L, R]` (eq. (3.3)). -/
noncomputable def lam (t : ι → ℝ) (L R : Mold ι) : ℝ :=
  if 0 < weight t L + weight t R then weight t R / (weight t L + weight t R) else 1 / 2

/-- The mass point of the pair produced by a mold, for leaf weights `t` and leaf vectors `w`
(eq. (3.6)): a mixture `[L, R]` gives `(1 − λ) · w_L + λ · w_R`. -/
noncomputable def point (t : ι → ℝ) (w : ι → V) : Mold ι → V
  | leaf i => w i
  | node L R => (1 - lam t L R) • point t w L + lam t L R • point t w R

/-- The mixtures `[L, R]` of a mold, as pairs of sub-molds. The decomposition direction of the
mixture `[L, R]` is `L.point t w − R.point t w` (eq. (3.5)). -/
def nodes : Mold ι → List (Mold ι × Mold ι)
  | leaf _ => []
  | node L R => (L, R) :: (nodes L ++ nodes R)

/-- Whether a mold is a single leaf. -/
def IsLeaf : Mold ι → Prop
  | leaf _ => True
  | node _ _ => False

end Mold

/-- The dyadic mold in `m` levels on the molds `f 0, …, f (2^m − 1)`, in this order: the mixtures
are `[2i − 1, 2i]` (counting from `1`) at every level. With `f k = Mold.leaf (g k)` it is the
dyadic mold on the items `g 0, …, g (2^m − 1)`. -/
def dyadic {ι : Type} : ℕ → (ℕ → Mold ι) → Mold ι
  | 0, f => f 0
  | m + 1, f => Mold.node (dyadic m f) (dyadic m fun k => f (2 ^ m + k))

/-! ### Tri-dyadic molds for `τ_l` -/

/-- A tri-dyadic mold `𝒮_l` for `τ_l` (Definition 4.1). For each sub-mold `j`, `label j` numbers
the `2^{2l+1}` interfaces with the normals of `j`; the interface `label j i` is the `i`-th mixture
of the first level, of the leaves `2i` and `2i + 1` (the paper's `2i − 1` and `2i`), and
`flip j i` says which of its two adjacent triangles receives the leaf `2i`. The upper levels mix
`[2p, 2p + 1]` (dyadic rule). The three resulting barycenters are mixed as
`[[order 0, order 1], order 2]`. -/
structure TriMold (l : ℕ) where
  /-- the labelling of the interfaces of each sub-mold -/
  label : (j : Fin 3) → Fin (2 ^ (2 * l + 1)) ≃ ifaceSet l j
  /-- the side of each interface that receives the first of its two leaves -/
  flip : Fin 3 → Fin (2 ^ (2 * l + 1)) → Bool
  /-- the order in which the three barycenters are mixed -/
  order : Equiv.Perm (Fin 3)

/-- The leaves of a tri-dyadic mold for `τ_l`: `(j, k)` is the leaf `k` of the sub-mold `j`. -/
abbrev Leaf (l : ℕ) := Fin 3 × Fin (2 ^ (2 * l + 2))

/-- The interface number `⌊k/2⌋` of the leaf `k` of a sub-mold. -/
def leafIface {l : ℕ} (k : Fin (2 ^ (2 * l + 2))) : Fin (2 ^ (2 * l + 1)) :=
  ⟨k.1 / 2, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq k.2 (by ring))⟩

/-- The leaf `2i` (`b = 0`) or `2i + 1` (`b = 1`) of a sub-mold. -/
def ifaceLeaf {l : ℕ} (i : ℕ) (b : ℕ) : Fin (2 ^ (2 * l + 2)) :=
  ⟨(2 * (i % 2 ^ (2 * l + 1)) + b % 2) % 2 ^ (2 * l + 2), Nat.mod_lt _ (by positivity)⟩

/-- The triangle of `τ_l` that the leaf `p` of the mold `S` stands for. -/
def TriMold.leafTri {l : ℕ} (S : TriMold l) (p : Leaf l) : Tri l :=
  if decide (p.2.1 % 2 = 1) = S.flip p.1 (leafIface p.2) then
    (S.label p.1 (leafIface p.2)).1.sides.1
  else (S.label p.1 (leafIface p.2)).1.sides.2

/-- The class `𝒞_s` of eq. (4.3): the leaves of the mold that stand for the triangle `s`. -/
def TriMold.C {l : ℕ} (S : TriMold l) (s : Tri l) : Finset (Leaf l) :=
  Finset.univ.filter fun p => S.leafTri p = s

/-- The sub-mold `𝒮_{l,j}`: the dyadic mold in `2l + 1` levels on the first-level mixtures
`[2i, 2i + 1]` of the leaves of `j`. -/
def subMold (l : ℕ) (j : Fin 3) : Mold (Leaf l) :=
  dyadic (2 * l + 1) fun i =>
    Mold.node (Mold.leaf (j, ifaceLeaf (l := l) i 0)) (Mold.leaf (j, ifaceLeaf (l := l) i 1))

/-- The whole tri-dyadic mold: the three sub-molds, then the mixture of their barycenters. -/
def TriMold.tree {l : ℕ} (S : TriMold l) : Mold (Leaf l) :=
  Mold.node (Mold.node (subMold l (S.order 0)) (subMold l (S.order 1))) (subMold l (S.order 2))

/-! ### The set of weights `Θ_l` and the map `𝐓` -/

/-- The set `Θ_l` of Definition 5.1: nonnegative weights, the two weights of each first-level
mixture adding up to `3^{-1} 2^{-1-2l}` (5.5), and the six weights of each triangle adding up to
`2^{-1-2l}` (5.6). -/
def Theta {l : ℕ} (S : TriMold l) : Set (Leaf l → ℝ) :=
  {t | (∀ p, 0 ≤ t p) ∧
    (∀ (j : Fin 3) (i : Fin (2 ^ (2 * l + 1))),
      t (j, ifaceLeaf i 0) + t (j, ifaceLeaf i 1) = 1 / (3 * 2 ^ (2 * l + 1))) ∧
    ∀ s : Tri l, ∑ p ∈ S.C s, t p = 1 / 2 ^ (2 * l + 1)}

/-- Two vectors of `ℝ²` are parallel when they are linearly dependent. -/
def Parallel (x y : Fin 2 → ℝ) : Prop :=
  x 0 * y 1 - x 1 * y 0 = 0

/-- The map `𝐓` of Definition 6.1: `𝐓(t)` is the set of `r ∈ Θ_l` whose decomposition directions
for `v` along the mold are parallel to those of `u` for `t`, at every mixture except those of the
first level (where both are parallel to the normal of an interface). -/
def T {l : ℕ} (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ) (t : Leaf l → ℝ) : Set (Leaf l → ℝ) :=
  {r | r ∈ Theta S ∧ ∀ p ∈ S.tree.nodes, ¬ (p.1.IsLeaf ∧ p.2.IsLeaf) →
    Parallel (p.1.point t (fun q => grad l u (S.leafTri q)) -
        p.2.point t (fun q => grad l u (S.leafTri q)))
      (p.1.point r (fun q => grad l v (S.leafTri q)) -
        p.2.point r (fun q => grad l v (S.leafTri q)))}

/-! ### Laminates -/

/-- The matrix `(∇u, ∇v)` on the triangle `s`, with rows `∇u` and `∇v`. -/
noncomputable def gradMat (l : ℕ) (u v : (Fin 2 → ℝ) → ℝ) (s : Tri l) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![grad l u s, grad l v s]

/-- The probability measure `ν` of eq. (6.1), with mass `2^{-2l-1}` at `(∇u, ∇v)|_{T_s}` for
each triangle `s`, as a finitely supported function. -/
noncomputable def gradMeasure (l : ℕ) (u v : (Fin 2 → ℝ) → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ :=
  ∑ s : Tri l, Finsupp.single (gradMat l u v s) (1 / 2 ^ (2 * l + 1))

/-- Laminates of finite order (Dacorogna 1985, Pedregal 1993), as finitely supported
probability measures on `2 × 2` matrices: every Dirac mass is one, and splitting the mass `c` of
an atom `A = θ B + (1 − θ) C` with `rank (B − C) ≤ 1` into masses `θ c` at `B` and `(1 − θ) c` at
`C` gives another one. -/
inductive IsLaminate : (Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ) → Prop
  | dirac (A : Matrix (Fin 2) (Fin 2) ℝ) : IsLaminate (Finsupp.single A 1)
  | split {μ : Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ} {A B C : Matrix (Fin 2) (Fin 2) ℝ} {c θ : ℝ} :
      IsLaminate μ → 0 ≤ c → c ≤ μ A → 0 ≤ θ → θ ≤ 1 → A = θ • B + (1 - θ) • C →
      (B - C).rank ≤ 1 →
      IsLaminate (μ - Finsupp.single A c + Finsupp.single B (θ * c) + Finsupp.single C ((1 - θ) * c))

-- END SHARED DEFINITIONS

end Morrey
