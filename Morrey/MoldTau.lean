module

public import Morrey.Hn.Mold

/-!
# Section 4: tri-dyadic molds for `τ_l`

Definition 4.1 asks for a labelling of the planar interfaces of `τ_l` and of its triangles with
the following properties (the bullets before Definition 4.1): each class `𝒞_s` has six elements,
two in each block `I_j` (eq. (4.4)); the first-level mixtures are the interfaces, with the two
adjacent triangles as leaves `2i − 1, 2i`; the rule `[2p − 1, 2p]` is used at all upper levels.
A `TriMold` builds the mold from the labelling, and this file proves that it has these
properties, and that such molds exist for every `l`.

* `card_ifaceSet`: each sub-mold has `2^{2l+1}` interfaces.
* `TriMold.canonical`: an explicit tri-dyadic mold, numbering the interfaces of each sub-mold
  kind by kind and cell by cell.
* `TriMold.tree_isTriDyadic`: the mold is tri-dyadic (Definition 3.4).
* `TriMold.card_C`, `TriMold.card_C_filter`: the classes `𝒞_s` have six elements, two in each
  sub-mold (eq. (4.3)).
* `TriMold.leafTri_pair`: the two leaves of a first-level mixture stand for the two triangles of
  its interface.
-/

@[expose] public section

namespace Morrey

/-- Each sub-mold has `2^{2l+1}` interfaces (two of the three normals, `4^l` cells). -/
theorem card_ifaceSet (l : ℕ) (j : Fin 3) : Nat.card (ifaceSet l j) = 2 ^ (2 * l + 1) := by
  sorry

/-- An explicit tri-dyadic mold for `τ_l`: in the sub-mold `j`, the interfaces of its first kind
come first, then those of its second kind, each kind cell by cell (`(a, b)` in the order of
`a · 2^l + b`); no side is flipped, and the barycenters are mixed as `[[0, 1], 2]`. -/
def TriMold.canonical (l : ℕ) : TriMold l := sorry

/-- The mold of a `TriMold` is tri-dyadic (Definition 3.4), with the dyadic sub-molds in
`2l + 2` levels on the leaves of each block. -/
theorem TriMold.tree_isTriDyadic {l : ℕ} (S : TriMold l) : S.tree.IsTriDyadic (2 * l + 2) := by
  sorry

/-- Each leaf appears exactly once in the mold of a `TriMold`. -/
theorem TriMold.tree_leaves_nodup {l : ℕ} (S : TriMold l) : S.tree.leaves.Nodup := by
  sorry

/-- Every leaf appears in the mold of a `TriMold`. -/
theorem TriMold.mem_tree_leaves {l : ℕ} (S : TriMold l) (p : Leaf l) : p ∈ S.tree.leaves := by
  sorry

/-- The two leaves `2i, 2i + 1` of the sub-mold `j` stand for the two triangles adjacent to the
interface `label j i`. -/
theorem TriMold.leafTri_pair {l : ℕ} (S : TriMold l) (j : Fin 3) (i : Fin (2 ^ (2 * l + 1))) :
    ({S.leafTri (j, ifaceLeaf i 0), S.leafTri (j, ifaceLeaf i 1)} : Set (Tri l)) =
      {(S.label j i).1.sides.1, (S.label j i).1.sides.2} := by
  sorry

/-- Each class `𝒞_s` has six elements (eq. (4.3)). -/
theorem TriMold.card_C {l : ℕ} (S : TriMold l) (s : Tri l) : (S.C s).card = 6 := by
  sorry

/-- Each class `𝒞_s` has two elements in each sub-mold (eq. (4.4)). -/
theorem TriMold.card_C_filter {l : ℕ} (S : TriMold l) (s : Tri l) (j : Fin 3) :
    ((S.C s).filter fun p => p.1 = j).card = 2 := by
  sorry

end Morrey
