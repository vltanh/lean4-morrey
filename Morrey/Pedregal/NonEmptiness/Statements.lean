module

public import Morrey.Pedregal.Map

/-!
# Section 7: the non-emptiness of the images, as the paper states it

* `Proposition7_1`, `Corollary7_2`: the statements of Proposition 7.1 and Corollary 7.2, as
  propositions. Both are false (`Pedregal.proposition7_1_false`, `Pedregal.corollary7_2_false`).
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

namespace Pedregal

/-- The decomposition direction of the mixture `p` of a mold, for weights `t` and the gradients of
`w` on the triangles of the leaves. -/
noncomputable def dir {l : ℕ} (S : TriMold l) (w : (Fin 2 → ℝ) → ℝ) (t : Leaf l → ℝ)
    (p : Mold (Leaf l) × Mold (Leaf l)) : Fin 2 → ℝ :=
  p.1.point t (leafGrad S w) - p.2.point t (leafGrad S w)

/-- **Proposition 7.1** (`esta`), as stated in the paper: for `u ∈ ℙ_l` and `t ∈ Θ_l`, the
measure `ν_w` of every `w ∈ ℙ_l` admits an `(H_n)`-condition along `𝒮_l` whose decomposition
directions are those of `u` for `t`, for some weights `r ∈ Θ_l`. It is false
(`Pedregal.proposition7_1_false`). -/
def Proposition7_1 : Prop :=
  ∀ l : ℕ, 1 ≤ l → ∀ (S : TriMold l) (u : (Fin 2 → ℝ) → ℝ), u ∈ PL l → ∀ t ∈ Theta S,
    ∀ w ∈ PL l, ∃ r ∈ Theta S, ∀ p ∈ S.tree.nodes, ¬ (p.1.IsLeaf ∧ p.2.IsLeaf) →
      Parallel (dir S u t p) (dir S w r p)

/-- **Corollary 7.2**, as stated in the paper: for all `u, v ∈ ℙ_l` and `t ∈ Θ_l`, the image
`𝐓(t)` is nonempty. It is false (`Pedregal.corollary7_2_false`). -/
def Corollary7_2 : Prop :=
  ∀ l : ℕ, 1 ≤ l → ∀ (S : TriMold l) (u v : (Fin 2 → ℝ) → ℝ), u ∈ PL l → v ∈ PL l →
    ∀ t ∈ Theta S, (T S u v t).Nonempty

/-- **Corollary 7.2** (`cor7_2`), the paper's proof: Proposition 7.1 applied to `w := v`. -/
theorem corollary7_2_of_proposition7_1 (h : Proposition7_1) : Corollary7_2 := by
  intro l hl S u v hu hv t ht
  obtain ⟨r, hr, hpar⟩ := h l hl S u hu t ht v hv
  exact ⟨r, hr, hpar⟩

/-- The summary of Step 2 of the proof of Proposition 7.1 (the displayed quotation after
Step 2), with the positivity of Claim 7.5 (`positivo`): for the directions of `u ∈ ℙ_l` and
`t ∈ Θ_l` along the sub-mold `𝒮_{l,j}`, and every `w ∈ ℙ_l`, there are nonnegative weights `r`
of the leaves of `j`, adding up to `3^{-1} 2^{-1-2l}` on each first-level mixture, for which the
decomposition directions of `w` along `𝒮_{l,j}` are parallel to those of `u`.

Reading: the paper also starts the top-to-bottom procedure for `w` from the barycenter `𝕌_j` of
`u` (eq. (7.6)), which asks in addition that the barycenter of `w` along `𝒮_{l,j}` be `𝕌_j`. That
clause is left out: the claim stated here is weaker than the paper's (`step2Claim_of_paper`), so
its refutation refutes the paper's too. (With the clause the claim would fail already for
`w = 0` whenever `𝕌_j ≠ 0`.) -/
def Step2Claim : Prop :=
  ∀ l : ℕ, 1 ≤ l → ∀ (S : TriMold l) (u : (Fin 2 → ℝ) → ℝ), u ∈ PL l → ∀ t ∈ Theta S,
    ∀ (j : Fin 3), ∀ w ∈ PL l, ∃ r : Leaf l → ℝ, (∀ p, 0 ≤ r p) ∧
      (∀ i : Fin (2 ^ (2 * l + 1)),
        r (j, ifaceLeaf i 0) + r (j, ifaceLeaf i 1) = 1 / (3 * 2 ^ (2 * l + 1))) ∧
      (∀ p ∈ (subMold l j).nodes, ¬ (p.1.IsLeaf ∧ p.2.IsLeaf) →
        Parallel (dir S u t p) (dir S w r p))

/-- The summary of Step 2 as the paper states it, with the start from the barycenter `𝕌_j` of
`u` (eq. (7.6)). -/
def Step2ClaimPaper : Prop :=
  ∀ l : ℕ, 1 ≤ l → ∀ (S : TriMold l) (u : (Fin 2 → ℝ) → ℝ), u ∈ PL l → ∀ t ∈ Theta S,
    ∀ (j : Fin 3), ∀ w ∈ PL l, ∃ r : Leaf l → ℝ, (∀ p, 0 ≤ r p) ∧
      (∀ i : Fin (2 ^ (2 * l + 1)),
        r (j, ifaceLeaf i 0) + r (j, ifaceLeaf i 1) = 1 / (3 * 2 ^ (2 * l + 1))) ∧
      (∀ p ∈ (subMold l j).nodes, ¬ (p.1.IsLeaf ∧ p.2.IsLeaf) →
        Parallel (dir S u t p) (dir S w r p)) ∧
      (subMold l j).point r (leafGrad S w) = (subMold l j).point t (leafGrad S u)

/-- The paper's form of the summary of Step 2 implies the weaker form `Step2Claim`. -/
theorem step2Claim_of_paper (h : Step2ClaimPaper) : Step2Claim := by
  intro l hl S u hu t ht j w hw
  obtain ⟨r, h0, h1, h2, -⟩ := h l hl S u hu t ht j w hw
  exact ⟨r, h0, h1, h2⟩

/-- Two distinct normals among `(1, 0), (0, 1), (1, 1)` are linearly independent. -/
private lemma normal_indep {l : ℕ} {f₁ f₂ : Iface l} (hne : f₁.1 ≠ f₂.1) {c₁ c₂ : ℝ}
    (h : c₁ • f₁.normal = c₂ • f₂.normal) : c₁ = 0 ∧ c₂ = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  obtain ⟨k₁, a₁, b₁⟩ := f₁
  obtain ⟨k₂, a₂, b₂⟩ := f₂
  simp only at hne h0 h1 ⊢
  fin_cases k₁ <;> fin_cases k₂ <;> simp [Iface.normal] at hne h0 h1 ⊢ <;> (try constructor) <;>
    linarith

/-- **Claim 7.4** (`corte`). On a triangle `s` of `τ_l`, take two of its interfaces with
different normals, and on each a point `xₖ` of the line through the gradients of `w ∈ ℙ_l` on the
two sides of the interface (a mass point of the first-level mixture lies on the segment between
them). The two lines
through `x₁` and `x₂` along the two normals meet in exactly one point, the gradient of `w` on
`s`. -/
theorem claim7_4 {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) {s : Tri l} {f₁ f₂ : Iface l}
    (h₁ : s = f₁.sides.1 ∨ s = f₁.sides.2) (h₂ : s = f₂.sides.1 ∨ s = f₂.sides.2)
    (hne : f₁.1 ≠ f₂.1) {x₁ x₂ : Fin 2 → ℝ}
    (hx₁ : ∃ θ : ℝ, x₁ = (1 - θ) • grad l w f₁.sides.1 + θ • grad l w f₁.sides.2)
    (hx₂ : ∃ θ : ℝ, x₂ = (1 - θ) • grad l w f₂.sides.1 + θ • grad l w f₂.sides.2) :
    {z | (∃ a : ℝ, z = x₁ + a • f₁.normal) ∧ ∃ b : ℝ, z = x₂ + b • f₂.normal} = {grad l w s} := by
  -- each `xₖ` lies on the line through `∇w|_s` along the normal `nₖ` (`grad_sides_sub`)
  have key : ∀ (f : Iface l) (x : Fin 2 → ℝ), (s = f.sides.1 ∨ s = f.sides.2) →
      (∃ θ : ℝ, x = (1 - θ) • grad l w f.sides.1 + θ • grad l w f.sides.2) →
      ∃ α : ℝ, x = grad l w s + α • f.normal := by
    rintro f x hs ⟨θ, rfl⟩
    obtain ⟨κ, hκ⟩ := grad_sides_sub hw f
    have e : grad l w f.sides.1 = grad l w f.sides.2 + κ • f.normal := by
      rw [← hκ]; abel
    rcases hs with rfl | rfl
    · exact ⟨-(θ * κ), by rw [e]; module⟩
    · exact ⟨(1 - θ) * κ, by rw [e]; module⟩
  obtain ⟨α, hα⟩ := key f₁ x₁ h₁ hx₁
  obtain ⟨β, hβ⟩ := key f₂ x₂ h₂ hx₂
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    -- the two lines meet only at `∇w|_s`, the normals being independent
    have h : (α + a) • f₁.normal = (β + b) • f₂.normal := by
      have : grad l w s + (α + a) • f₁.normal = grad l w s + (β + b) • f₂.normal := by
        rw [add_smul, add_smul, ← add_assoc, ← add_assoc, ← hα, ← hβ, ← ha, ← hb]
      exact add_left_cancel this
    obtain ⟨h0, -⟩ := normal_indep hne h
    rw [ha, hα, add_assoc, ← add_smul, h0, zero_smul, add_zero]
  · rintro rfl
    exact ⟨⟨-α, by rw [hα]; module⟩, ⟨-β, by rw [hβ]; module⟩⟩

end Pedregal
