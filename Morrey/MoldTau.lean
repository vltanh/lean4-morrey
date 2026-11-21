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

/-! ### Arithmetic of the numbering of the interfaces -/

private lemma mt_two_pow_two_mul (l : ℕ) : 2 ^ (2 * l) = 2 ^ l * 2 ^ l := by
  rw [two_mul, pow_add]

private lemma mt_lt_sq {N a b : ℕ} (ha : a < N) (hb : b < N) : a * N + b < N * N :=
  calc a * N + b < a * N + N := by omega
    _ = (a + 1) * N := by ring
    _ ≤ N * N := Nat.mul_le_mul_right _ ha

private lemma mt_decomp {N i : ℕ} (hi : i < N * N * 2) :
    (if i < N * N then 0 else N * N) + i % (N * N) / N * N + i % N = i := by
  rw [add_assoc, ← Nat.mod_mul_right_mod i N N, Nat.div_add_mod']
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h, zero_add]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The first kind of interfaces of the sub-mold `j`: vertical, vertical, horizontal. -/
def kind1 : Fin 3 → Fin 3 := ![0, 0, 1]

/-- The second kind of interfaces of the sub-mold `j`: horizontal, diagonal, diagonal. -/
def kind2 : Fin 3 → Fin 3 := ![1, 2, 2]

private lemma mt_kind1_ne_kind2 (j : Fin 3) : kind1 j ≠ kind2 j := by
  fin_cases j <;> decide

private lemma mt_kind_cases (j k : Fin 3) (hk : k ≠ ![2, 1, 0] j) : k = kind1 j ∨ k = kind2 j := by
  revert hk; fin_cases j <;> fin_cases k <;> decide

/-- The numbering of the interfaces of the sub-mold `j` used by `TriMold.canonical`: the
interfaces of its first kind come first, then those of its second kind, each kind cell by cell,
`(a, b)` in the order of `a · 2^l + b`. -/
def canonicalLabel (l : ℕ) (j : Fin 3) : Fin (2 ^ (2 * l + 1)) ≃ ifaceSet l j where
  toFun i := ⟨(if i.1 < 2 ^ (2 * l) then kind1 j else kind2 j,
      ⟨i.1 % 2 ^ (2 * l) / 2 ^ l, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq (Nat.mod_lt _ (by positivity))
        (by rw [← pow_add]; ring_nf))⟩,
      ⟨i.1 % 2 ^ l, Nat.mod_lt _ (by positivity)⟩), by
    simp only [ifaceSet, Set.mem_ofPred_eq]
    fin_cases j <;> split_ifs <;> decide⟩
  invFun f := ⟨(if f.1.1 = kind1 j then 0 else 2 ^ (2 * l)) + f.1.2.1.1 * 2 ^ l + f.1.2.2.1, by
    have h := mt_lt_sq f.1.2.1.2 f.1.2.2.2
    rw [pow_succ, mt_two_pow_two_mul]
    split_ifs <;> omega⟩
  left_inv := by
    intro i
    apply Fin.ext
    have hi : i.1 < 2 ^ l * 2 ^ l * 2 := lt_of_lt_of_eq i.2 (by rw [pow_succ, mt_two_pow_two_mul])
    have hk := mt_kind1_ne_kind2 j
    show (if (if i.1 < 2 ^ (2 * l) then kind1 j else kind2 j) = kind1 j then 0 else 2 ^ (2 * l)) +
      i.1 % 2 ^ (2 * l) / 2 ^ l * 2 ^ l + i.1 % 2 ^ l = i.1
    rw [mt_two_pow_two_mul]
    conv_rhs => rw [← mt_decomp hi]
    split_ifs <;> simp_all
  right_inv := by
    rintro ⟨⟨k, a, b⟩, hk⟩
    have hN : 0 < 2 ^ l := by positivity
    have hab := mt_lt_sq a.2 b.2
    have hmod : ((if k = kind1 j then 0 else 2 ^ (2 * l)) + a.1 * 2 ^ l + b.1) % 2 ^ (2 * l) =
        a.1 * 2 ^ l + b.1 := by
      rw [mt_two_pow_two_mul]
      split_ifs
      · rw [zero_add, Nat.mod_eq_of_lt hab]
      · rw [add_assoc, Nat.add_mod_left, Nat.mod_eq_of_lt hab]
    have hdiv : (a.1 * 2 ^ l + b.1) / 2 ^ l = a.1 := by
      rw [add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt b.2, zero_add]
    have hmod' : ((if k = kind1 j then 0 else 2 ^ (2 * l)) + a.1 * 2 ^ l + b.1) % 2 ^ l = b.1 := by
      rw [← Nat.mod_mul_right_mod _ (2 ^ l) (2 ^ l), ← mt_two_pow_two_mul, hmod, add_comm,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.2]
    have hkind : (if (if k = kind1 j then 0 else 2 ^ (2 * l)) + a.1 * 2 ^ l + b.1 < 2 ^ (2 * l)
        then kind1 j else kind2 j) = k := by
      rw [mt_two_pow_two_mul]
      rcases mt_kind_cases j k hk with rfl | rfl
      · rw [ite_eq_left rfl, ite_eq_left (by omega)]
      · rw [ite_eq_right (mt_kind1_ne_kind2 j).symm, ite_eq_right (by omega)]
    apply Subtype.ext
    simp only [hmod, hdiv, hmod', hkind]

/-- Each sub-mold has `2^{2l+1}` interfaces (two of the three normals, `4^l` cells). -/
theorem card_ifaceSet (l : ℕ) (j : Fin 3) : Nat.card (ifaceSet l j) = 2 ^ (2 * l + 1) := by
  rw [← Nat.card_congr (canonicalLabel l j), Nat.card_eq_fintype_card, Fintype.card_fin]

/-- An explicit tri-dyadic mold for `τ_l`, numbering the interfaces of each sub-mold with
`canonicalLabel`; no side is flipped, and the barycenters are mixed as `[[0, 1], 2]`. -/
def TriMold.canonical (l : ℕ) : TriMold l where
  label := canonicalLabel l
  flip := fun _ _ => false
  order := Equiv.refl _

/-! ### The leaves of the sub-molds -/

/-- Relabelling the leaves of a dyadic mold relabels the molds it mixes. -/
theorem mt_map_dyadic {ι κ : Type} (σ : ι → κ) (m : ℕ) (f : ℕ → Mold ι) :
    (dyadic m f).map σ = dyadic m fun k => (f k).map σ := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => simp only [dyadic, Mold.map, ih]

/-- The leaves of a relabelled mold are the relabelled leaves. -/
theorem mt_leaves_map {ι κ : Type} (σ : ι → κ) (M : Mold ι) :
    (M.map σ).leaves = M.leaves.map σ := by
  induction M with
  | leaf i => rfl
  | node L R ihL ihR => simp only [Mold.map, Mold.leaves, ihL, ihR, List.map_append]

/-- The leaves of the dyadic mold on `f 0, …, f (2^m − 1)` are those of `f 0`, then those of
`f 1`, and so on. -/
theorem mt_leaves_dyadic {ι : Type} (m : ℕ) (f : ℕ → Mold ι) :
    (dyadic m f).leaves = ((List.range (2 ^ m)).map fun k => (f k).leaves).flatten := by
  induction m generalizing f with
  | zero => simp [dyadic]
  | succ m ih =>
    rw [dyadic, Mold.leaves, ih, ih, pow_succ, mul_two, List.range_add]
    simp [List.map_append, List.flatten_append, List.map_map, Function.comp_def]

/-- The dyadic mold in `m` levels on molds that are perfect of depth `d` is perfect of depth
`m + d`. -/
theorem mt_isPerfect_dyadic {ι : Type} (m d : ℕ) (f : ℕ → Mold ι)
    (hf : ∀ k, (f k).IsPerfect d) : (dyadic m f).IsPerfect (m + d) := by
  induction m generalizing f with
  | zero => simpa [dyadic] using hf 0
  | succ m ih =>
    rw [show m + 1 + d = (m + d) + 1 by omega, dyadic, Mold.IsPerfect]
    exact ⟨ih f hf, ih _ fun k => hf _⟩

/-- The value of the leaf `2i + b` of a sub-mold. -/
theorem mt_ifaceLeaf_val {l : ℕ} (i : Fin (2 ^ (2 * l + 1))) {b : ℕ} (hb : b < 2) :
    (ifaceLeaf (l := l) i b).1 = 2 * i.1 + b := by
  have h : 2 * i.1 + b < 2 ^ (2 * l + 2) := by
    have := i.2
    rw [show 2 ^ (2 * l + 2) = 2 * 2 ^ (2 * l + 1) by ring]
    omega
  simp only [ifaceLeaf]
  rw [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt h]

/-- The leaf `2i + b` of a sub-mold belongs to the interface `i`. -/
theorem mt_leafIface_ifaceLeaf {l : ℕ} (i : Fin (2 ^ (2 * l + 1))) {b : ℕ} (hb : b < 2) :
    leafIface (ifaceLeaf (l := l) i b) = i := by
  apply Fin.ext
  simp only [leafIface]
  rw [mt_ifaceLeaf_val i hb]
  omega

/-- The dyadic mold on `Fin (2^{2l+2})` whose relabelling by `k ↦ (j, k)` is the sub-mold `j`:
the first-level mixtures are `[2i, 2i + 1]`. -/
def mt_subDyadic (l : ℕ) : Mold (Fin (2 ^ (2 * l + 2))) :=
  dyadic (2 * l + 1) fun i =>
    Mold.node (Mold.leaf (ifaceLeaf (l := l) i 0)) (Mold.leaf (ifaceLeaf (l := l) i 1))

/-- The sub-mold `j` is `mt_subDyadic l` with its leaves `k` relabelled `(j, k)`. -/
theorem mt_subDyadic_map (l : ℕ) (j : Fin 3) :
    (mt_subDyadic l).map (fun k => (j, k)) = subMold l j := by
  rw [mt_subDyadic, mt_map_dyadic]
  rfl

private lemma mt_flatten_pairs (K : ℕ) :
    ((List.range K).map fun k => [2 * k, 2 * k + 1]).flatten = List.range (2 * K) := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih,
      show 2 * (K + 1) = 2 * K + 1 + 1 by ring, List.range_succ, List.range_succ]
    simp

/-- The leaves of `mt_subDyadic l` are `0, 1, …, 2^{2l+2} − 1`, in this order. -/
theorem mt_subDyadic_leaves (l : ℕ) :
    (mt_subDyadic l).leaves = List.finRange (2 ^ (2 * l + 2)) := by
  apply List.map_injective_iff.2 Fin.val_injective
  rw [List.map_coe_finRange_eq_range, mt_subDyadic, mt_leaves_dyadic, List.map_flatten,
    List.map_map]
  have h : ∀ k ∈ List.range (2 ^ (2 * l + 1)),
      (List.map Fin.val ∘ fun k => (Mold.node (Mold.leaf (ifaceLeaf (l := l) k 0))
        (Mold.leaf (ifaceLeaf (l := l) k 1))).leaves) k = [2 * k, 2 * k + 1] := by
    intro k hk
    have hk' := List.mem_range.1 hk
    simp only [Function.comp_apply, Mold.leaves, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil]
    rw [mt_ifaceLeaf_val ⟨k, hk'⟩ (by norm_num : 0 < 2),
      mt_ifaceLeaf_val ⟨k, hk'⟩ (by norm_num : 1 < 2)]
    rfl
  rw [List.map_congr_left h, mt_flatten_pairs,
    show 2 * 2 ^ (2 * l + 1) = 2 ^ (2 * l + 2) by ring]

/-- `mt_subDyadic l` is a dyadic mold in `2l + 2` levels (Definition 3.3). -/
theorem mt_subDyadic_isDyadic (l : ℕ) : (mt_subDyadic l).IsDyadic (2 * l + 2) := by
  refine ⟨?_, ?_⟩
  · exact mt_isPerfect_dyadic (2 * l + 1) 1 _ fun k =>
      by simp [Mold.IsPerfect, Mold.IsLeaf]
  · rw [mt_subDyadic_leaves]
    exact List.nodup_finRange _

/-- The leaves of the sub-mold `j` are `(j, 0), …, (j, 2^{2l+2} − 1)`, in this order. -/
theorem mt_subMold_leaves (l : ℕ) (j : Fin 3) :
    (subMold l j).leaves = (List.finRange (2 ^ (2 * l + 2))).map fun k => (j, k) := by
  rw [← mt_subDyadic_map, mt_leaves_map, mt_subDyadic_leaves]

/-- The leaves of the sub-mold `j` are the leaves of the block `j`. -/
theorem mt_mem_subMold_leaves {l : ℕ} (j : Fin 3) (p : Leaf l) :
    p ∈ (subMold l j).leaves ↔ p.1 = j := by
  rw [mt_subMold_leaves]
  constructor
  · intro hp
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hp
    rfl
  · intro h
    exact List.mem_map.2 ⟨p.2, List.mem_finRange _, by rw [← h]⟩

/-- The leaves of the mold of a `TriMold`: those of the three sub-molds, in the order `S.order`. -/
theorem mt_tree_leaves {l : ℕ} (S : TriMold l) :
    S.tree.leaves = (subMold l (S.order 0)).leaves ++ (subMold l (S.order 1)).leaves ++
      (subMold l (S.order 2)).leaves := rfl

/-- The mold of a `TriMold` is tri-dyadic (Definition 3.4), with the dyadic sub-molds in
`2l + 2` levels on the leaves of each block. -/
theorem TriMold.tree_isTriDyadic {l : ℕ} (S : TriMold l) : S.tree.IsTriDyadic (2 * l + 2) := by
  refine ⟨S.order, fun _ => mt_subDyadic l, fun _ => mt_subDyadic_isDyadic l, ?_⟩
  simp only [mt_subDyadic_map]
  rfl

/-- Each leaf appears exactly once in the mold of a `TriMold`. -/
theorem TriMold.tree_leaves_nodup {l : ℕ} (S : TriMold l) : S.tree.leaves.Nodup := by
  have hsub : ∀ j, (subMold l j).leaves.Nodup := fun j => by
    rw [mt_subMold_leaves]
    exact (List.nodup_finRange _).map fun a b h => (Prod.mk.inj h).2
  have hdisj : ∀ a b, a ≠ b → ∀ p ∈ (subMold l a).leaves, ∀ q ∈ (subMold l b).leaves, p ≠ q := by
    intro a b hab p hp q hq hpq
    rw [mt_mem_subMold_leaves] at hp hq
    exact hab (hp.symm.trans (hpq ▸ hq))
  have hne : ∀ a b : Fin 3, a ≠ b → S.order a ≠ S.order b := fun a b h => S.order.injective.ne h
  rw [mt_tree_leaves, List.nodup_append, List.nodup_append]
  refine ⟨⟨hsub _, hsub _, hdisj _ _ (hne 0 1 (by decide))⟩, hsub _, ?_⟩
  intro p hp q hq
  rcases List.mem_append.1 hp with hp | hp
  · exact hdisj _ _ (hne 0 2 (by decide)) p hp q hq
  · exact hdisj _ _ (hne 1 2 (by decide)) p hp q hq

/-- Every leaf appears in the mold of a `TriMold`. -/
theorem TriMold.mem_tree_leaves {l : ℕ} (S : TriMold l) (p : Leaf l) : p ∈ S.tree.leaves := by
  simp only [mt_tree_leaves, List.mem_append, mt_mem_subMold_leaves]
  have h : p.1 = S.order (S.order.symm p.1) := (S.order.apply_symm_apply _).symm
  generalize S.order.symm p.1 = i at h
  fin_cases i <;> simp [h]

/-- The two leaves `2i, 2i + 1` of the sub-mold `j` stand for the two triangles adjacent to the
interface `label j i`. -/
theorem TriMold.leafTri_pair {l : ℕ} (S : TriMold l) (j : Fin 3) (i : Fin (2 ^ (2 * l + 1))) :
    ({S.leafTri (j, ifaceLeaf i 0), S.leafTri (j, ifaceLeaf i 1)} : Set (Tri l)) =
      {(S.label j i).1.sides.1, (S.label j i).1.sides.2} := by
  have h0 : S.leafTri (j, ifaceLeaf i 0) =
      if false = S.flip j i then (S.label j i).1.sides.1 else (S.label j i).1.sides.2 := by
    simp only [TriMold.leafTri, mt_leafIface_ifaceLeaf i (by norm_num : 0 < 2),
      mt_ifaceLeaf_val i (by norm_num : 0 < 2)]
    simp
  have h1 : S.leafTri (j, ifaceLeaf i 1) =
      if true = S.flip j i then (S.label j i).1.sides.1 else (S.label j i).1.sides.2 := by
    simp only [TriMold.leafTri, mt_leafIface_ifaceLeaf i (by norm_num : 1 < 2),
      mt_ifaceLeaf_val i (by norm_num : 1 < 2)]
    simp
  rw [h0, h1]
  cases S.flip j i
  · simp
  · simp [Set.pair_comm]

/-- An interface and a side of it are determined by its kind and the triangle on that side. -/
theorem mt_sides_inj {l : ℕ} {f f' : Iface l} (h1 : f.1 = f'.1) {P P' : Prop} [Decidable P]
    [Decidable P']
    (h : (if P then f.sides.1 else f.sides.2) = (if P' then f'.sides.1 else f'.sides.2)) :
    f = f' ∧ (P ↔ P') := by
  obtain ⟨κ, a, b⟩ := f
  obtain ⟨κ', a', b'⟩ := f'
  simp only at h1
  subst h1
  fin_cases κ <;> by_cases hP : P <;> by_cases hP' : P' <;> simp_all [Iface.sides]

private lemma mt_card_C_filter {l : ℕ} (S : TriMold l) (s : Tri l) (j : Fin 3) :
    ((S.C s).filter fun p => p.1 = j).card = 2 := by
  have hkinds : (Finset.univ.filter fun κ : Fin 3 => κ ≠ ![2, 1, 0] j).card = 2 := by
    fin_cases j <;> rfl
  have hle : ∀ s : Tri l, ((S.C s).filter fun p => p.1 = j).card ≤ 2 := by
    intro s
    refine le_trans (Finset.card_le_card_of_injOn
      (t := Finset.univ.filter fun κ : Fin 3 => κ ≠ ![2, 1, 0] j)
      (fun p : Leaf l => (S.label p.1 (leafIface p.2)).1.1) ?_ ?_) hkinds.le
    · intro p hp
      simp only [Finset.coe_filter, TriMold.C, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hp ⊢
      rw [← hp.2]
      exact (S.label p.1 (leafIface p.2)).2
    · rintro ⟨j₁, k⟩ hp ⟨j₂, k'⟩ hp' hkind
      simp only [Finset.coe_filter, TriMold.C, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hp hp'
      obtain ⟨hs, rfl⟩ := hp
      obtain ⟨hs', rfl⟩ := hp'
      have htri := hs.trans hs'.symm
      simp only [TriMold.leafTri] at htri
      obtain ⟨hf, hiff⟩ := mt_sides_inj hkind htri
      have hi : leafIface k = leafIface k' := (S.label j₂).injective (Subtype.ext hf)
      rw [hi] at hiff
      have hk1 : k.1 / 2 = k'.1 / 2 := congrArg Fin.val hi
      have hk2 : k.1 % 2 = k'.1 % 2 := by
        have := Nat.mod_two_eq_zero_or_one k.1
        have := Nat.mod_two_eq_zero_or_one k'.1
        generalize S.flip j₂ (leafIface k') = c at hiff
        cases c <;> simp at hiff <;> omega
      simp only [Prod.mk.injEq, true_and]
      ext
      omega
  have hsum : ∑ s : Tri l, ((S.C s).filter fun p => p.1 = j).card = 2 ^ (2 * l + 2) := by
    have hcard : (Finset.univ.filter fun p : Leaf l => p.1 = j).card = 2 ^ (2 * l + 2) := by
      rw [show (Finset.univ.filter fun p : Leaf l => p.1 = j) = {j} ×ˢ Finset.univ by
        ext p; rw [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]; simp]
      simp
    refine Eq.trans ?_ hcard
    rw [Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter fun p : Leaf l => p.1 = j)
      (f := S.leafTri) (t := Finset.univ) fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    ext p
    simp [TriMold.C, and_comm]
  have hconst : ∑ _s : Tri l, (2 : ℕ) = 2 ^ (2 * l + 2) := by
    simp [Finset.card_univ]
    ring
  exact (Finset.sum_eq_sum_iff_of_le fun s _ => hle s).1 (hsum.trans hconst.symm) s
    (Finset.mem_univ s)

/-- Each class `𝒞_s` has six elements (eq. (4.3)). -/
theorem TriMold.card_C {l : ℕ} (S : TriMold l) (s : Tri l) : (S.C s).card = 6 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)]
  simp [mt_card_C_filter S s]

/-- Each class `𝒞_s` has two elements in each sub-mold (eq. (4.4)). -/
theorem TriMold.card_C_filter {l : ℕ} (S : TriMold l) (s : Tri l) (j : Fin 3) :
    ((S.C s).filter fun p => p.1 = j).card = 2 :=
  mt_card_C_filter S s j

end Morrey
