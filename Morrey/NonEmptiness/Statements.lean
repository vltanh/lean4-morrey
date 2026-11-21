module

public import Morrey.Map

/-!
# Section 7: the non-emptiness of the images, as the paper states it

* `Proposition7_1`, `Corollary7_2`: the statements of Proposition 7.1 and Corollary 7.2, as
  propositions. Both are false (`Morrey.proposition7_1_false`, `Morrey.corollary7_2_false`).
* `corollary7_2_of_proposition7_1`: the paper's proof of Corollary 7.2 from Proposition 7.1,
  which is correct.
* `Step2Claim`: the summary of Step 2 of the proof of Proposition 7.1 (the displayed quotation
  after Step 2), with the positivity of Claim 7.5. It is false as well.
* `claim7_4`: Claim 7.4, proved.

The phrase "admits a decomposition as a `(H_n)`-condition along `𝒮_l` through the top-to-bottom
procedure, with the given system of decomposition directions `{𝐔_k^{(p)}}`" of Proposition 7.1
means that the decomposition directions of `w`, for some weights `r ∈ Θ_l`, are parallel to the
given ones at every level `0 ≤ p ≤ m − 2` (in the top-to-bottom procedure (7.7), a mixture splits
its mass point along `S · 𝐔_k^{(p)}`): this is `r ∈ 𝐓(t)` with `v := w`.
-/

@[expose] public section

namespace Morrey

/-- The decomposition direction of the mixture `p` of a mold, for weights `t` and the gradients of
`w` on the triangles of the leaves. -/
noncomputable def dir {l : ℕ} (S : TriMold l) (w : (Fin 2 → ℝ) → ℝ) (t : Leaf l → ℝ)
    (p : Mold (Leaf l) × Mold (Leaf l)) : Fin 2 → ℝ :=
  p.1.point t (leafGrad S w) - p.2.point t (leafGrad S w)

/-- **Proposition 7.1** (`esta`), as stated in the paper: for `u ∈ ℙ_l` and `t ∈ Θ_l`, the
measure `ν_w` of every `w ∈ ℙ_l` admits an `(H_n)`-condition along `𝒮_l` whose decomposition
directions are those of `u` for `t`, for some weights `r ∈ Θ_l`. It is false
(`Morrey.proposition7_1_false`). -/
def Proposition7_1 : Prop :=
  ∀ l : ℕ, 1 ≤ l → ∀ (S : TriMold l) (u : (Fin 2 → ℝ) → ℝ), u ∈ PL l → ∀ t ∈ Theta S,
    ∀ w ∈ PL l, ∃ r ∈ Theta S, ∀ p ∈ S.tree.nodes, ¬ (p.1.IsLeaf ∧ p.2.IsLeaf) →
      Parallel (dir S u t p) (dir S w r p)

/-- **Corollary 7.2**, as stated in the paper: for all `u, v ∈ ℙ_l` and `t ∈ Θ_l`, the image
`𝐓(t)` is nonempty. It is false (`Morrey.corollary7_2_false`). -/
def Corollary7_2 : Prop :=
  ∀ l : ℕ, 1 ≤ l → ∀ (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ), u ∈ PL l → v ∈ PL l →
    ∀ t ∈ Theta S, (T S u v t).Nonempty

/-- **Corollary 7.2**, the paper's proof: Proposition 7.1 applied to `w := v`. -/
theorem corollary7_2_of_proposition7_1 (h : Proposition7_1) : Corollary7_2 := by
  sorry

/-- The summary of Step 2 of the proof of Proposition 7.1 (the displayed quotation after
Step 2), with the positivity of Claim 7.5 (`positivo`): for the directions of `u ∈ ℙ_l` and
`t ∈ Θ_l` along the sub-mold `𝒮_{l,j}`, and every `w ∈ ℙ_l`, there are nonnegative weights `r`
of the leaves of `j`, adding up to `3^{-1} 2^{-1-2l}` on each first-level mixture, for which the
decomposition directions of `w` along `𝒮_{l,j}` are parallel to those of `u`, and the
top-to-bottom procedure starts from the barycenter `𝕌_j` of `u` (eq. (7.6)). -/
def Step2Claim : Prop :=
  ∀ l : ℕ, 1 ≤ l → ∀ (S : TriMold l) (u : (Fin 2 → ℝ) → ℝ), u ∈ PL l → ∀ t ∈ Theta S,
    ∀ (j : Fin 3), ∀ w ∈ PL l, ∃ r : Leaf l → ℝ, (∀ p, 0 ≤ r p) ∧
      (∀ i : Fin (2 ^ (2 * l + 1)),
        r (j, ifaceLeaf i 0) + r (j, ifaceLeaf i 1) = 1 / (3 * 2 ^ (2 * l + 1))) ∧
      (∀ p ∈ (subMold l j).nodes, ¬ (p.1.IsLeaf ∧ p.2.IsLeaf) →
        Parallel (dir S u t p) (dir S w r p)) ∧
      (subMold l j).point r (leafGrad S w) = (subMold l j).point t (leafGrad S u)

/-- **Claim 7.4** (`corte`). On a triangle `s` of `τ_l`, take two of its interfaces with
different normals, and on each a mass point of a first-level mixture, that is, a point `xₖ` of the
segment between the gradients of `w ∈ ℙ_l` on the two sides of the interface. The two lines
through `x₁` and `x₂` along the two normals meet in exactly one point, the gradient of `w` on
`s`. -/
theorem claim7_4 {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) {s : Tri l} {f₁ f₂ : Iface l}
    (h₁ : s = f₁.sides.1 ∨ s = f₁.sides.2) (h₂ : s = f₂.sides.1 ∨ s = f₂.sides.2)
    (hne : f₁.1 ≠ f₂.1) {x₁ x₂ : Fin 2 → ℝ}
    (hx₁ : ∃ θ : ℝ, x₁ = (1 - θ) • grad l w f₁.sides.1 + θ • grad l w f₁.sides.2)
    (hx₂ : ∃ θ : ℝ, x₂ = (1 - θ) • grad l w f₂.sides.1 + θ • grad l w f₂.sides.2) :
    {z | (∃ a : ℝ, z = x₁ + a • f₁.normal) ∧ ∃ b : ℝ, z = x₂ + b • f₂.normal} = {grad l w s} := by
  sorry

end Morrey
