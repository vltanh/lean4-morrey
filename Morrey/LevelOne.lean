module

public import Morrey.Triangulation
public import Basic.LinearAlgebra.Matrix.RankTwo

/-!
# Theorem 1.1 (1) at the level `l = 1`

At `l = 1` the conclusion of Theorem 1.1 (1) holds, although the paper's argument does not prove
it there: Corollary 7.2 already fails at `l = 1`, for the mold `TriMold.canonical 1`
(`Morrey.T_cex_eq_empty`), so Kakutani's theorem cannot be applied.

For `w ∈ ℙ_1` with nodal values `W_{ab}` (`a, b ∈ {0, 1}`), put
`α = (W₁₀ − W₀₀) + (W₁₁ − W₀₁)`, `β = (W₀₁ − W₀₀) + (W₁₁ − W₁₀)`,
`γ = (W₁₀ − W₀₀) − (W₁₁ − W₀₁)`. Then the gradient of `w` on the triangle `(a, b, k)` is
`(−1)^a α (1, 0) + (−1)^b β (0, 1) + (−1)^{a+b+k} γ (1, 1)` (`grad_levelOne`). So the matrix of
`(u, v)` on the triangle `(a, b, k)` is `(−1)^a C₁ + (−1)^b C₂ + (−1)^{a+b+k} C₃`, with the
rank-one matrices `C₁ = (α_u, α_v) ⊗ (1, 0)`, `C₂ = (β_u, β_v) ⊗ (0, 1)`, `C₃ = (γ_u, γ_v) ⊗ (1, 1)`,
and the eight triangles carry the eight sign patterns. The measure `ν` is uniform on the vertices
of this "rank-one cube", which three rank-one splittings of `δ₀` reach: along `C₁`, then `C₂`,
then `C₃`.
-/

@[expose] public section

namespace Morrey

/-- `α = (W₁₀ − W₀₀) + (W₁₁ − W₀₁)` for the nodal values `W` of `w` at the level `1`. -/
private noncomputable def lvl1_alpha (w : (Fin 2 → ℝ) → ℝ) : ℝ :=
  (nodal 1 w 1 0 - nodal 1 w 0 0) + (nodal 1 w 1 1 - nodal 1 w 0 1)

/-- `β = (W₀₁ − W₀₀) + (W₁₁ − W₁₀)`. -/
private noncomputable def lvl1_beta (w : (Fin 2 → ℝ) → ℝ) : ℝ :=
  (nodal 1 w 0 1 - nodal 1 w 0 0) + (nodal 1 w 1 1 - nodal 1 w 1 0)

/-- `γ = (W₁₀ − W₀₀) − (W₁₁ − W₀₁)`. -/
private noncomputable def lvl1_gamma (w : (Fin 2 → ℝ) → ℝ) : ℝ :=
  (nodal 1 w 1 0 - nodal 1 w 0 0) - (nodal 1 w 1 1 - nodal 1 w 0 1)

private theorem lvl1_cases (a : Fin (2 ^ 1)) : a = 0 ∨ a = 1 := by
  revert a; decide

private theorem lvl1_cases' (a : Fin 2) : a = 0 ∨ a = 1 := by
  revert a; decide

private theorem lvl1_val0 : ((0 : Fin (2 ^ 1)) : ℕ) = 0 := rfl
private theorem lvl1_val1 : ((1 : Fin (2 ^ 1)) : ℕ) = 1 := rfl

/-- The gradient of `w ∈ ℙ_1` on the triangle `(a, b, k)`:
`(−1)^a α (1, 0) + (−1)^b β (0, 1) + (−1)^{a+b+k} γ (1, 1)`. -/
private theorem grad_levelOne {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL 1) (a b : Fin (2 ^ 1))
    (k : Fin 2) :
    grad 1 w (a, b, k) =
      ![(-1) ^ (a : ℕ) * lvl1_alpha w + (-1) ^ ((a : ℕ) + b + k) * lvl1_gamma w,
        (-1) ^ (b : ℕ) * lvl1_beta w + (-1) ^ ((a : ℕ) + b + k) * lvl1_gamma w] := by
  rcases lvl1_cases a with rfl | rfl <;> rcases lvl1_cases b with rfl | rfl <;>
    rcases lvl1_cases' k with rfl | rfl
  all_goals first | rw [grad_lower hw] | rw [grad_upper hw]
  all_goals
    ext i
    fin_cases i <;> simp [lvl1_alpha, lvl1_beta, lvl1_gamma] <;> ring

/-- `C₁ = (α_u, α_v) ⊗ (1, 0)`. -/
private noncomputable def lvl1_C1 (u v : (Fin 2 → ℝ) → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![lvl1_alpha u, 0], ![lvl1_alpha v, 0]]

/-- `C₂ = (β_u, β_v) ⊗ (0, 1)`. -/
private noncomputable def lvl1_C2 (u v : (Fin 2 → ℝ) → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![0, lvl1_beta u], ![0, lvl1_beta v]]

/-- `C₃ = (γ_u, γ_v) ⊗ (1, 1)`. -/
private noncomputable def lvl1_C3 (u v : (Fin 2 → ℝ) → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![lvl1_gamma u, lvl1_gamma u], ![lvl1_gamma v, lvl1_gamma v]]

/-- The matrix of `(u, v)` on the triangle `(a, b, k)` is
`(−1)^a C₁ + (−1)^b C₂ + (−1)^{a+b+k} C₃`. -/
private theorem lvl1_gradMat {u v : (Fin 2 → ℝ) → ℝ} (hu : u ∈ PL 1) (hv : v ∈ PL 1)
    (a b : Fin (2 ^ 1)) (k : Fin 2) :
    gradMat 1 u v (a, b, k) = (-1 : ℝ) ^ (a : ℕ) • lvl1_C1 u v + (-1 : ℝ) ^ (b : ℕ) • lvl1_C2 u v +
      (-1 : ℝ) ^ ((a : ℕ) + b + k) • lvl1_C3 u v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gradMat, grad_levelOne hu, grad_levelOne hv, lvl1_C1, lvl1_C2, lvl1_C3]

/-- The finitely supported measure with the masses `p.2` at the matrices `p.1`, `p ∈ l`. -/
private noncomputable def lvl1_meas :
    List (Matrix (Fin 2) (Fin 2) ℝ × ℝ) → (Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ)
  | [] => 0
  | p :: l => Finsupp.single p.1 p.2 + lvl1_meas l

private theorem lvl1_meas_append (l₁ l₂ : List (Matrix (Fin 2) (Fin 2) ℝ × ℝ)) :
    lvl1_meas (l₁ ++ l₂) = lvl1_meas l₁ + lvl1_meas l₂ := by
  induction l₁ with
  | nil => simp [lvl1_meas]
  | cons p l ih => simp [lvl1_meas, ih, add_assoc]

private theorem lvl1_meas_nonneg {l : List (Matrix (Fin 2) (Fin 2) ℝ × ℝ)}
    (hl : ∀ p ∈ l, 0 ≤ p.2) (X : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ lvl1_meas l X := by
  induction l with
  | nil => simp [lvl1_meas]
  | cons p l ih =>
    simp only [lvl1_meas, Finsupp.add_apply, Finsupp.single_apply]
    have h1 := hl p List.mem_cons_self
    have h2 := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    split_ifs <;> linarith

/-- A list of atoms with nonnegative masses whose measure is a laminate. -/
private def lvl1_Good (l : List (Matrix (Fin 2) (Fin 2) ℝ × ℝ)) : Prop :=
  IsLaminate (lvl1_meas l) ∧ ∀ p ∈ l, 0 ≤ p.2

/-- Splitting the first atom `A` of the list into halves at `A ± D`, `rank D ≤ 1`; the two new
atoms go to the end of the list. -/
private theorem lvl1_step {A B C D : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ}
    {l : List (Matrix (Fin 2) (Fin 2) ℝ × ℝ)} (h : lvl1_Good ((A, c) :: l)) (hD : D.det = 0)
    (hB : B = A + D) (hC : C = A - D) : lvl1_Good (l ++ [(B, c / 2), (C, c / 2)]) := by
  obtain ⟨hlam, hnn⟩ := h
  have hc : 0 ≤ c := hnn (A, c) List.mem_cons_self
  have hl : ∀ p ∈ l, 0 ≤ p.2 := fun p hp => hnn p (List.mem_cons_of_mem _ hp)
  refine ⟨?_, ?_⟩
  · have hle : c ≤ lvl1_meas ((A, c) :: l) A := by
      simp only [lvl1_meas, Finsupp.add_apply, Finsupp.single_eq_same]
      linarith [lvl1_meas_nonneg hl A]
    have hAeq : A = (1 / 2 : ℝ) • B + (1 - 1 / 2 : ℝ) • C := by rw [hB, hC]; module
    have hrank : (B - C).rank ≤ 1 := by
      rw [Matrix.rank_le_one_iff_det_eq_zero_of_fin_two]
      have : B - C = (2 : ℝ) • D := by rw [hB, hC]; module
      rw [this, Matrix.det_smul, hD, mul_zero]
    have := IsLaminate.split hlam hc hle (by norm_num) (by norm_num) hAeq hrank
    convert this using 1
    have e1 : (1 / 2 : ℝ) * c = c / 2 := by ring
    have e2 : (1 - 1 / 2 : ℝ) * c = c / 2 := by ring
    rw [e1, e2, lvl1_meas_append]
    simp only [lvl1_meas]
    abel
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hl p hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp only <;> linarith

/-- The sum over the eight triangles of `τ_1`. -/
private theorem lvl1_sum_tri {M : Type*} [AddCommMonoid M] (f : Tri 1 → M) :
    ∑ s, f s = f (0, 0, 0) + f (0, 0, 1) + f (0, 1, 0) + f (0, 1, 1) + f (1, 0, 0) +
      f (1, 0, 1) + f (1, 1, 0) + f (1, 1, 1) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  abel

/-- **Theorem 1.1 (1)** (`objetivo`) at the level `l = 1`: for `u, v ∈ ℙ_1`, the gradient
measure `ν` of `(u, v)` is a laminate.

Departure from the paper: the paper proves Theorem 1.1 (1) with a fixed point of `𝐓`, which needs
Corollary 7.2, false already at `l = 1` (`Morrey.T_cex_eq_empty`). At `l = 1` the formalization
proves it instead by an explicit lamination of three rank-one splittings. -/
theorem theorem1_1_part1_levelOne {u v : (Fin 2 → ℝ) → ℝ} (hu : u ∈ PL 1) (hv : v ∈ PL 1) :
    IsLaminate (gradMeasure 1 u v) := by
  have d1 : (lvl1_C1 u v).det = 0 := by simp [lvl1_C1, Matrix.det_fin_two_of]
  have d2 : (lvl1_C2 u v).det = 0 := by simp [lvl1_C2, Matrix.det_fin_two_of]
  have d3 : (lvl1_C3 u v).det = 0 := by simp [lvl1_C3, Matrix.det_fin_two_of]
  have h0 : lvl1_Good [(0, 1)] :=
    ⟨by simpa [lvl1_meas] using IsLaminate.dirac 0, by simp⟩
  have h1 := lvl1_step (B := lvl1_C1 u v) (C := -lvl1_C1 u v) h0 d1 (zero_add _).symm
    (zero_sub _).symm
  have h2 := lvl1_step (B := lvl1_C1 u v + lvl1_C2 u v) (C := lvl1_C1 u v - lvl1_C2 u v)
    h1 d2 rfl rfl
  have h3 := lvl1_step (B := -lvl1_C1 u v + lvl1_C2 u v) (C := -lvl1_C1 u v - lvl1_C2 u v)
    h2 d2 rfl rfl
  have h4 := lvl1_step (B := gradMat 1 u v (0, 0, 0)) (C := gradMat 1 u v (0, 0, 1)) h3 d3
    (by simp only [lvl1_gradMat hu hv, lvl1_val0]; module)
    (by simp only [lvl1_gradMat hu hv, lvl1_val0, lvl1_val1]; module)
  have h5 := lvl1_step (B := gradMat 1 u v (0, 1, 1)) (C := gradMat 1 u v (0, 1, 0)) h4 d3
    (by simp only [lvl1_gradMat hu hv, lvl1_val0, lvl1_val1]; module)
    (by simp only [lvl1_gradMat hu hv, lvl1_val0, lvl1_val1]; module)
  have h6 := lvl1_step (B := gradMat 1 u v (1, 0, 1)) (C := gradMat 1 u v (1, 0, 0)) h5 d3
    (by simp only [lvl1_gradMat hu hv, lvl1_val0, lvl1_val1]; module)
    (by simp only [lvl1_gradMat hu hv, lvl1_val0, lvl1_val1]; module)
  have h7 := lvl1_step (B := gradMat 1 u v (1, 1, 0)) (C := gradMat 1 u v (1, 1, 1)) h6 d3
    (by simp only [lvl1_gradMat hu hv, lvl1_val0, lvl1_val1]; module)
    (by simp only [lvl1_gradMat hu hv, lvl1_val1]; module)
  have hm : (1 : ℝ) / 2 / 2 / 2 = 1 / 2 ^ (2 * 1 + 1) := by norm_num
  have key : gradMeasure 1 u v = lvl1_meas
      [(gradMat 1 u v (0, 0, 0), 1 / 2 / 2 / 2), (gradMat 1 u v (0, 0, 1), 1 / 2 / 2 / 2),
        (gradMat 1 u v (0, 1, 1), 1 / 2 / 2 / 2), (gradMat 1 u v (0, 1, 0), 1 / 2 / 2 / 2),
        (gradMat 1 u v (1, 0, 1), 1 / 2 / 2 / 2), (gradMat 1 u v (1, 0, 0), 1 / 2 / 2 / 2),
        (gradMat 1 u v (1, 1, 0), 1 / 2 / 2 / 2), (gradMat 1 u v (1, 1, 1), 1 / 2 / 2 / 2)] := by
    rw [hm, gradMeasure, lvl1_sum_tri]
    simp only [lvl1_meas]
    abel
  rw [key]
  exact h7.1

end Morrey
