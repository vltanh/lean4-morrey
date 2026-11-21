module

public import Morrey.MoldTau
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Section 5: the set of weights `Θ_l`

Definition 5.1 asserts that `Θ_l` is "a non-empty, convex, compact subset of the standard
simplex". This file proves it, and the facts (5.10), (5.11), (5.14) about the
`(H_n)`-conditions of a function fed with weights of `Θ_l`.

* `uniform_mem_theta`, `theta_nonempty`, `convex_theta`, `isCompact_theta`,
  `theta_subset_simplex`: the assertions of Definition 5.1.
* `ifacePoint`: the mass point of the first-level mixture of an interface,
  `3 · 2^{2l+1} (t_{2i} w_{2i} + t_{2i+1} w_{2i+1})`, which is linear in `t`.
* `point_dyadic_theta`: on `Θ_l`, the mass point of a block of the dyadic sub-mold is the
  average of the first-level mass points it contains, because the relative weights above the
  first level are all `1/2` (eqs. (5.10), (5.11)).
* `point_subMold_theta`: the barycenter `𝕎_j` of the sub-mold `j` (eq. (5.14)).

Eq. (5.15) is `Morrey.equation5_15` (in `Morrey.Map`), from (5.13) and (5.14).
-/

@[expose] public section

namespace Morrey

variable {l : ℕ}

/-- The uniform weights `1 / (3 · 2^{2l+2})` belong to `Θ_l`. -/
theorem uniform_mem_theta (S : TriMold l) :
    (fun _ => 1 / (3 * 2 ^ (2 * l + 2)) : Leaf l → ℝ) ∈ Theta S := by
  have h : (2 : ℝ) ^ (2 * l + 2) = 2 * 2 ^ (2 * l + 1) := by ring
  refine ⟨fun _ => by positivity, fun j i => ?_, fun s => ?_⟩
  · simp only [h]
    field_simp
    ring
  · rw [Finset.sum_const, S.card_C s, nsmul_eq_mul, h]
    field_simp
    ring

/-- **Definition 5.1** (`pesos-claim`), first assertion: `Θ_l` is nonempty. -/
theorem theta_nonempty (S : TriMold l) : (Theta S).Nonempty :=
  ⟨_, uniform_mem_theta S⟩

/-- **Definition 5.1** (`pesos-claim`), second assertion: `Θ_l` is convex. -/
theorem convex_theta (S : TriMold l) : Convex ℝ (Theta S) := by
  intro t ht r hr a b ha hb hab
  refine ⟨fun p => ?_, fun j i => ?_, fun s => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (ht.1 p)) (mul_nonneg hb (hr.1 p))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination a * ht.2.1 j i + b * hr.2.1 j i + (1 / (3 * 2 ^ (2 * l + 1))) * hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [ht.2.2 s, hr.2.2 s]
    linear_combination (1 / 2 ^ (2 * l + 1)) * hab

/-- `Θ_l` is closed, a step towards its compactness (Definition 5.1). -/
theorem isClosed_theta (S : TriMold l) : IsClosed (Theta S) := by
  have h1 : IsClosed {t : Leaf l → ℝ | ∀ p, 0 ≤ t p} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun p => isClosed_le continuous_const (continuous_apply p)
  have h2 : IsClosed {t : Leaf l → ℝ | ∀ (j : Fin 3) (i : Fin (2 ^ (2 * l + 1))),
      t (j, ifaceLeaf i 0) + t (j, ifaceLeaf i 1) = 1 / (3 * 2 ^ (2 * l + 1))} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun i =>
      isClosed_eq (by fun_prop) continuous_const
  have h3 : IsClosed {t : Leaf l → ℝ | ∀ s : Tri l, ∑ p ∈ S.C s, t p = 1 / 2 ^ (2 * l + 1)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun s =>
      isClosed_eq (by fun_prop) continuous_const
  exact h1.inter (h2.inter h3)

/-- **Definition 5.1** (`pesos-claim`), fourth assertion: `Θ_l` lies in the standard simplex. -/
theorem theta_subset_simplex (S : TriMold l) {t : Leaf l → ℝ} (ht : t ∈ Theta S) :
    (∀ p, 0 ≤ t p) ∧ ∑ p, t p = 1 := by
  refine ⟨ht.1, ?_⟩
  rw [← Finset.sum_fiberwise Finset.univ S.leafTri t]
  have h : ∀ s, ∑ p ∈ Finset.univ.filter (fun p => S.leafTri p = s), t p = 1 / 2 ^ (2 * l + 1) :=
    ht.2.2
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- **Definition 5.1** (`pesos-claim`), fifth assertion: `Θ_l` is compact. -/
theorem isCompact_theta (S : TriMold l) : IsCompact (Theta S) := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    (isClosed_theta S) ?_
  intro t ht p _
  obtain ⟨h0, h1⟩ := theta_subset_simplex S ht
  refine ⟨h0 p, ?_⟩
  rw [← h1]
  exact Finset.single_le_sum (fun q _ => h0 q) (Finset.mem_univ p)

/-- The mass point of the first-level mixture `[2i, 2i + 1]` of the sub-mold `j`, for weights
with `t_{2i} + t_{2i+1} = 3^{-1} 2^{-1-2l}`. -/
noncomputable def ifacePoint {V : Type} [AddCommGroup V] [Module ℝ V] (t : Leaf l → ℝ)
    (w : Leaf l → V) (j : Fin 3) (i : ℕ) : V :=
  (3 * 2 ^ (2 * l + 1) : ℝ) •
    (t (j, ifaceLeaf i 0) • w (j, ifaceLeaf i 0) + t (j, ifaceLeaf i 1) • w (j, ifaceLeaf i 1))

/-- On `Θ_l`, the two weights of a first-level mixture add up to `3^{-1} 2^{-1-2l}`, for every
index `i` (the interface is `i` modulo `2^{2l+1}`). -/
theorem wt_pair_sum {S : TriMold l} {t : Leaf l → ℝ} (ht : t ∈ Theta S) (j : Fin 3) (i : ℕ) :
    t (j, ifaceLeaf (l := l) i 0) + t (j, ifaceLeaf (l := l) i 1) = 1 / (3 * 2 ^ (2 * l + 1)) := by
  have h := ht.2.1 j ⟨i % 2 ^ (2 * l + 1), Nat.mod_lt _ (by positivity)⟩
  have e : ∀ b, ifaceLeaf (l := l) (i % 2 ^ (2 * l + 1)) b = ifaceLeaf (l := l) i b := by
    intro b
    apply Fin.ext
    simp [ifaceLeaf]
  simpa only [Fin.val_mk, e] using h

/-- On `Θ_l`, the weight of a block of `2^q` consecutive first-level mixtures of a sub-mold,
mixed dyadically, is `2^q · 3^{-1} 2^{-1-2l}` (eq. (5.10)). -/
theorem wt_weight_dyadic {S : TriMold l} {t : Leaf l → ℝ} (ht : t ∈ Theta S) (j : Fin 3)
    (q n : ℕ) :
    (dyadic q fun k => Mold.node (Mold.leaf (j, ifaceLeaf (l := l) (n + k) 0))
        (Mold.leaf (j, ifaceLeaf (l := l) (n + k) 1))).weight t =
      2 ^ q * (1 / (3 * 2 ^ (2 * l + 1))) := by
  induction q generalizing n with
  | zero =>
    simp only [dyadic, Mold.weight, pow_zero, one_mul]
    exact wt_pair_sum ht j _
  | succ q ih =>
    have h2 := ih (n + 2 ^ q)
    simp only [add_assoc] at h2
    simp only [dyadic, Mold.weight]
    rw [ih n, h2, pow_succ]
    ring

private lemma wt_point_pair {V : Type} [AddCommGroup V] [Module ℝ V] (t : Leaf l → ℝ)
    (w : Leaf l → V) (A B : Leaf l) {K : ℝ} (hK : 0 < K) (h : t A + t B = 1 / K) :
    (Mold.node (Mold.leaf A) (Mold.leaf B)).point t w = K • (t A • w A + t B • w B) := by
  have hpos : 0 < t A + t B := by rw [h]; positivity
  simp only [Mold.point, Mold.lam, Mold.weight, hpos, ↓reduceIte]
  rw [h]
  have hA : t A = 1 / K - t B := by linarith
  rw [hA, smul_add, smul_smul, smul_smul]
  congr 2
  · field_simp
  · field_simp

/-- **Equations (5.10), (5.11)** (`pesofijo`, `constante`). On `Θ_l`, the mass point of a block
of `2^q` consecutive first-level mixtures of the sub-mold `j`, mixed dyadically, is the average
of their mass points: every relative weight above the first level is `1/2`. (No bound on `n` is
needed: the indices of interfaces are taken modulo `2^{2l+1}`.) -/
theorem point_dyadic_theta {V : Type} [AddCommGroup V] [Module ℝ V] {S : TriMold l}
    {t : Leaf l → ℝ} (ht : t ∈ Theta S) (w : Leaf l → V) (j : Fin 3) (q n : ℕ) :
    (dyadic q fun k => Mold.node (Mold.leaf (j, ifaceLeaf (l := l) (n + k) 0))
        (Mold.leaf (j, ifaceLeaf (l := l) (n + k) 1))).point t w =
      (1 / 2 ^ q : ℝ) • ∑ k ∈ Finset.range (2 ^ q), ifacePoint t w j (n + k) := by
  induction q generalizing n with
  | zero =>
    simp only [dyadic, pow_zero, div_one, one_smul, Finset.range_one, Finset.sum_singleton,
      add_zero, ifacePoint]
    exact wt_point_pair t w _ _ (by positivity) (wt_pair_sum ht j n)
  | succ q ih =>
    have hw2 := wt_weight_dyadic ht j q (n + 2 ^ q)
    have h2 := ih (n + 2 ^ q)
    simp only [add_assoc] at hw2 h2
    simp only [dyadic, Mold.point, Mold.lam]
    rw [wt_weight_dyadic ht j q n, hw2, ih n, h2, ite_eq_left (by positivity),
      show (2 : ℕ) ^ (q + 1) = 2 ^ q + 2 ^ q by ring, Finset.sum_range_add, pow_succ (2 : ℝ) q]
    have : (2 : ℝ) ^ q * (1 / (3 * 2 ^ (2 * l + 1))) /
        (2 ^ q * (1 / (3 * 2 ^ (2 * l + 1))) + 2 ^ q * (1 / (3 * 2 ^ (2 * l + 1)))) = 1 / 2 := by
      field_simp
      ring
    rw [this]
    module

private lemma wt_sum_range_two_mul {V : Type} [AddCommGroup V] (G : ℕ → V) (K : ℕ) :
    ∑ m ∈ Finset.range (2 * K), G m = ∑ i ∈ Finset.range K, (G (2 * i) + G (2 * i + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    abel

/-- A sum over the leaves of a sub-mold, regrouped by first-level mixtures. -/
theorem wt_sum_pairs {V : Type} [AddCommGroup V] (g : Fin (2 ^ (2 * l + 2)) → V) :
    ∑ k, g k = ∑ i ∈ Finset.range (2 ^ (2 * l + 1)), (g (ifaceLeaf i 0) + g (ifaceLeaf i 1)) := by
  set G : ℕ → V := fun m => if h : m < 2 ^ (2 * l + 2) then g ⟨m, h⟩ else 0 with hG
  have h1 : ∑ k, g k = ∑ k : Fin (2 ^ (2 * l + 2)), G k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hG, k.2]
  rw [h1, Fin.sum_univ_eq_sum_range G, show 2 ^ (2 * l + 2) = 2 * 2 ^ (2 * l + 1) by ring,
    wt_sum_range_two_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have e : ∀ b < 2, G (2 * i + b) = g (ifaceLeaf i b) := by
    intro b hb
    have hv := mt_ifaceLeaf_val (l := l) ⟨i, hi'⟩ hb
    have hlt : 2 * i + b < 2 ^ (2 * l + 2) := hv ▸ (ifaceLeaf (l := l) i b).2
    simp only [hG, hlt, dite_true]
    congr 1
    exact Fin.ext hv.symm
  rw [← e 0 (by norm_num), ← e 1 (by norm_num), add_zero]

/-- **Equation (5.14)** (`baricentros`). On `Θ_l`, the barycenter `𝕎_j` of the sub-mold `j` is
`3 ∑_s ∑_{k ∈ 𝒞_s ∩ I_j} t_k w_k`. -/
theorem point_subMold_theta {V : Type} [AddCommGroup V] [Module ℝ V] {S : TriMold l}
    {t : Leaf l → ℝ} (ht : t ∈ Theta S) (w : Leaf l → V) (j : Fin 3) :
    (subMold l j).point t w = (3 : ℝ) • ∑ k : Fin (2 ^ (2 * l + 2)), t (j, k) • w (j, k) := by
  have h := point_dyadic_theta ht w j (2 * l + 1) 0
  simp only [zero_add] at h
  rw [subMold, h]
  simp only [ifacePoint, ← Finset.smul_sum, smul_smul]
  rw [show (1 / 2 ^ (2 * l + 1) : ℝ) * (3 * 2 ^ (2 * l + 1)) = 3 by field_simp]
  congr 1
  exact (wt_sum_pairs fun k => t (j, k) • w (j, k)).symm

end Morrey
