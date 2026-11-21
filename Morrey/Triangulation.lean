module

public import Morrey.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# The triangulation `τ_l` and the space `ℙ_l`

Facts about `τ_l` and `ℙ_l` that the paper uses without proof (Sections 4 and 5).

* `grad_eq_of_affine`: the gradient `grad l w s` of a function that is affine on the triangle `s`
  is the slope of the affine function. This bridges `grad` (a derivative at the centroid) with the
  paper's "gradient constant on each element".
* `grad_lower`, `grad_upper`: for `w ∈ ℙ_l`, the gradient on each triangle from the values of `w`
  at the nodes of the grid (the vertices of the triangle).
* `Iface.normal`, `grad_sides_sub`: across an interface, the jump of the gradient of `w ∈ ℙ_l`
  is a multiple of the normal of the interface ("rank-one compatibility across planar interfaces
  for gradients", Section 2).
* `sides_adjacent`: the two triangles of an interface share the two endpoints of an edge
  orthogonal to its normal (with periodicity), so `Iface` lists planar interfaces of `τ_l`.
* `equation5_13`: the barycenter of `ν_w` vanishes, by periodicity (eq. (5.13)).
-/

@[expose] public section

namespace Morrey

/-- The node `(a/2^l, b/2^l)` of the grid of `τ_l`. -/
noncomputable def vertex (l : ℕ) (a b : ℕ) : Fin 2 → ℝ :=
  ![(a : ℝ) / 2 ^ l, (b : ℝ) / 2 ^ l]

/-- The value of `w` at the node `(a, b)` of the grid, with `a, b` modulo `2^l`. -/
noncomputable def nodal (l : ℕ) (w : (Fin 2 → ℝ) → ℝ) (a b : Fin (2 ^ l)) : ℝ :=
  w (vertex l a b)

/-- The gradient on the triangle `s` of a function that is affine on it is the slope. -/
theorem grad_eq_of_affine {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} {s : Tri l} {c : ℝ} {g : Fin 2 → ℝ}
    (h : ∀ x ∈ triangle l s, w x = c + g 0 * x 0 + g 1 * x 1) : grad l w s = g := by
  sorry

/-- A `Q`-periodic function takes the same value at the nodes `(a, b)` and `(a mod 2^l,
b mod 2^l)`. -/
theorem nodal_eq {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) (a b : ℕ) :
    w (vertex l a b) =
      nodal l w ⟨a % 2 ^ l, Nat.mod_lt _ (by positivity)⟩ ⟨b % 2 ^ l, Nat.mod_lt _ (by positivity)⟩ := by
  sorry

/-- The gradient of `w ∈ ℙ_l` on the lower triangle of the cell `(a, b)`, with vertices
`(a, b)`, `(a + 1, b)`, `(a, b + 1)`. -/
theorem grad_lower {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) (a b : Fin (2 ^ l)) :
    grad l w (a, b, 0) =
      ![2 ^ l * (nodal l w (a + 1) b - nodal l w a b), 2 ^ l * (nodal l w a (b + 1) - nodal l w a b)] := by
  sorry

/-- The gradient of `w ∈ ℙ_l` on the upper triangle of the cell `(a, b)`, with vertices
`(a + 1, b)`, `(a + 1, b + 1)`, `(a, b + 1)`. -/
theorem grad_upper {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) (a b : Fin (2 ^ l)) :
    grad l w (a, b, 1) =
      ![2 ^ l * (nodal l w (a + 1) (b + 1) - nodal l w a (b + 1)),
        2 ^ l * (nodal l w (a + 1) (b + 1) - nodal l w (a + 1) b)] := by
  sorry

/-- The normal of an interface: `(1, 0)`, `(0, 1)` or `(1, 1)`. -/
def Iface.normal {l : ℕ} (f : Iface l) : Fin 2 → ℝ :=
  if f.1 = 0 then ![1, 0] else if f.1 = 1 then ![0, 1] else ![1, 1]

/-- The two triangles of an interface share an edge orthogonal to its normal: two common
vertices, modulo the period, whose difference is orthogonal to the normal. -/
theorem sides_adjacent {l : ℕ} (f : Iface l) :
    ∃ p q : Fin 2 → ℝ, p ≠ q ∧ (q 0 - p 0) * f.normal 0 + (q 1 - p 1) * f.normal 1 = 0 ∧
      (∃ z : Fin 2 → ℤ, (fun i => p i + z i) ∈ triangle l f.sides.1 ∧
        (fun i => q i + z i) ∈ triangle l f.sides.1) ∧
      (∃ z : Fin 2 → ℤ, (fun i => p i + z i) ∈ triangle l f.sides.2 ∧
        (fun i => q i + z i) ∈ triangle l f.sides.2) := by
  sorry

/-- Across an interface, the jump of the gradient of `w ∈ ℙ_l` is a multiple of the normal. -/
theorem grad_sides_sub {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) (f : Iface l) :
    ∃ κ : ℝ, grad l w f.sides.1 - grad l w f.sides.2 = κ • f.normal := by
  sorry

/-- **Equation (5.13)** (`baricentro`). The barycenter of `ν_w` vanishes, by periodicity. -/
theorem equation5_13 {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) :
    ∑ s : Tri l, (1 / 2 ^ (2 * l + 1) : ℝ) • grad l w s = 0 := by
  sorry

end Morrey
