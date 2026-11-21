module

public import Morrey.MoldTau
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Section 5: the set of weights `Θ_l`

Definition 5.1 asserts that `Θ_l` is "a non-empty, convex, compact subset of the standard
simplex". This file proves it, and the facts (5.10), (5.11), (5.14), (5.15) about the
`(H_n)`-conditions of a function fed with weights of `Θ_l`.

* `uniform_mem_theta`, `theta_nonempty`, `convex_theta`, `isCompact_theta`,
  `theta_subset_simplex`: the assertions of Definition 5.1.
* `ifacePoint`: the mass point of the first-level mixture of an interface,
  `3 · 2^{2l+1} (t_{2i} w_{2i} + t_{2i+1} w_{2i+1})`, which is linear in `t`.
* `point_dyadic_theta`: on `Θ_l`, the mass point of a block of the dyadic sub-mold is the
  average of the first-level mass points it contains, because the relative weights above the
  first level are all `1/2` (eqs. (5.10), (5.11)).
* `point_subMold_theta`: the barycenter `𝕎_j` of the sub-mold `j` (eq. (5.14)).
-/

@[expose] public section

namespace Morrey

variable {l : ℕ}

/-- The uniform weights `1 / (3 · 2^{2l+2})` belong to `Θ_l`. -/
theorem uniform_mem_theta (S : TriMold l) :
    (fun _ => 1 / (3 * 2 ^ (2 * l + 2)) : Leaf l → ℝ) ∈ Theta S := by
  sorry

/-- **Definition 5.1** (`pesos`), first assertion: `Θ_l` is nonempty. -/
theorem theta_nonempty (S : TriMold l) : (Theta S).Nonempty :=
  ⟨_, uniform_mem_theta S⟩

/-- **Definition 5.1** (`pesos`), second assertion: `Θ_l` is convex. -/
theorem convex_theta (S : TriMold l) : Convex ℝ (Theta S) := by
  sorry

/-- **Definition 5.1** (`pesos`), third assertion: `Θ_l` is closed. -/
theorem isClosed_theta (S : TriMold l) : IsClosed (Theta S) := by
  sorry

/-- **Definition 5.1** (`pesos`), fourth assertion: `Θ_l` lies in the standard simplex. -/
theorem theta_subset_simplex (S : TriMold l) {t : Leaf l → ℝ} (ht : t ∈ Theta S) :
    (∀ p, 0 ≤ t p) ∧ ∑ p, t p = 1 := by
  sorry

/-- **Definition 5.1** (`pesos`), fifth assertion: `Θ_l` is compact. -/
theorem isCompact_theta (S : TriMold l) : IsCompact (Theta S) := by
  sorry

/-- The mass point of the first-level mixture `[2i, 2i + 1]` of the sub-mold `j`, for weights
with `t_{2i} + t_{2i+1} = 3^{-1} 2^{-1-2l}`. -/
noncomputable def ifacePoint {V : Type} [AddCommGroup V] [Module ℝ V] (t : Leaf l → ℝ)
    (w : Leaf l → V) (j : Fin 3) (i : ℕ) : V :=
  (3 * 2 ^ (2 * l + 1) : ℝ) •
    (t (j, ifaceLeaf i 0) • w (j, ifaceLeaf i 0) + t (j, ifaceLeaf i 1) • w (j, ifaceLeaf i 1))

/-- **Equations (5.10), (5.11)** (`pesofijo`, `constante`). On `Θ_l`, the mass point of a block
of `2^q` consecutive first-level mixtures of the sub-mold `j`, mixed dyadically, is the average
of their mass points: every relative weight above the first level is `1/2`. -/
theorem point_dyadic_theta {V : Type} [AddCommGroup V] [Module ℝ V] {S : TriMold l}
    {t : Leaf l → ℝ} (ht : t ∈ Theta S) (w : Leaf l → V) (j : Fin 3) (q n : ℕ)
    (hn : n + 2 ^ q ≤ 2 ^ (2 * l + 1)) :
    (dyadic q fun k => Mold.node (Mold.leaf (j, ifaceLeaf (l := l) (n + k) 0))
        (Mold.leaf (j, ifaceLeaf (l := l) (n + k) 1))).point t w =
      (1 / 2 ^ q : ℝ) • ∑ k ∈ Finset.range (2 ^ q), ifacePoint t w j (n + k) := by
  sorry

/-- **Equation (5.14)** (`baricentros`). On `Θ_l`, the barycenter `𝕎_j` of the sub-mold `j` is
`3 ∑_s ∑_{k ∈ 𝒞_s ∩ I_j} t_k w_k`. -/
theorem point_subMold_theta {V : Type} [AddCommGroup V] [Module ℝ V] {S : TriMold l}
    {t : Leaf l → ℝ} (ht : t ∈ Theta S) (w : Leaf l → V) (j : Fin 3) :
    (subMold l j).point t w = (3 : ℝ) • ∑ k : Fin (2 ^ (2 * l + 2)), t (j, k) • w (j, k) := by
  sorry

end Morrey
