module

public import Pedregal.Defs
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

namespace Pedregal

/-- The node `(a/2^l, b/2^l)` of the grid of `τ_l`. -/
noncomputable def vertex (l : ℕ) (a b : ℕ) : Fin 2 → ℝ :=
  ![(a : ℝ) / 2 ^ l, (b : ℝ) / 2 ^ l]

/-- The value of `w` at the node `(a, b)` of the grid, with `a, b` modulo `2^l`. -/
noncomputable def nodal (l : ℕ) (w : (Fin 2 → ℝ) → ℝ) (a b : Fin (2 ^ l)) : ℝ :=
  w (vertex l a b)

/-- The closed triangle `s` is a neighbourhood of its centroid. -/
theorem tri_triangle_mem_nhds (l : ℕ) (s : Tri l) : triangle l s ∈ nhds (centroid l s) := by
  have hpos : (0:ℝ) < 2 ^ l := by positivity
  have h0 : Continuous fun x : Fin 2 → ℝ => 2 ^ l * x 0 := by fun_prop
  have h1 : Continuous fun x : Fin 2 → ℝ => 2 ^ l * x 1 := by fun_prop
  have h01 : Continuous fun x : Fin 2 → ℝ => 2 ^ l * x 0 + 2 ^ l * x 1 := by fun_prop
  unfold triangle
  split_ifs with hs
  · have c0 : 2 ^ l * centroid l s 0 = (s.1 : ℝ) + 1 / 3 := by
      simp only [centroid, hs, ite_true, Matrix.cons_val_zero]; field_simp
    have c1 : 2 ^ l * centroid l s 1 = (s.2.1 : ℝ) + 1 / 3 := by
      simp only [centroid, hs, ite_true, Matrix.cons_val_one, Matrix.cons_val_zero]; field_simp
    have e0 : ∀ᶠ x in nhds (centroid l s), (s.1 : ℝ) < 2 ^ l * x 0 :=
      continuousAt_const.eventually_lt h0.continuousAt (by rw [c0]; linarith)
    have e1 : ∀ᶠ x in nhds (centroid l s), (s.2.1 : ℝ) < 2 ^ l * x 1 :=
      continuousAt_const.eventually_lt h1.continuousAt (by rw [c1]; linarith)
    have e2 : ∀ᶠ x in nhds (centroid l s), 2 ^ l * x 0 + 2 ^ l * x 1 < (s.1 : ℝ) + s.2.1 + 1 :=
      h01.continuousAt.eventually_lt continuousAt_const (by rw [c0, c1]; linarith)
    filter_upwards [e0, e1, e2] with x hx0 hx1 hx2
    exact ⟨hx0.le, hx1.le, hx2.le⟩
  · have c0 : 2 ^ l * centroid l s 0 = (s.1 : ℝ) + 2 / 3 := by
      simp only [centroid, hs, ite_false, Matrix.cons_val_zero]; field_simp
    have c1 : 2 ^ l * centroid l s 1 = (s.2.1 : ℝ) + 2 / 3 := by
      simp only [centroid, hs, ite_false, Matrix.cons_val_one, Matrix.cons_val_zero]; field_simp
    have e0 : ∀ᶠ x in nhds (centroid l s), 2 ^ l * x 0 < (s.1 : ℝ) + 1 :=
      h0.continuousAt.eventually_lt continuousAt_const (by rw [c0]; linarith)
    have e1 : ∀ᶠ x in nhds (centroid l s), 2 ^ l * x 1 < (s.2.1 : ℝ) + 1 :=
      h1.continuousAt.eventually_lt continuousAt_const (by rw [c1]; linarith)
    have e2 : ∀ᶠ x in nhds (centroid l s), (s.1 : ℝ) + s.2.1 + 1 < 2 ^ l * x 0 + 2 ^ l * x 1 :=
      continuousAt_const.eventually_lt h01.continuousAt (by rw [c0, c1]; linarith)
    filter_upwards [e0, e1, e2] with x hx0 hx1 hx2
    exact ⟨hx0.le, hx1.le, hx2.le⟩

/-- The gradient on the triangle `s` of a function that is affine on it is the slope. -/
theorem grad_eq_of_affine {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} {s : Tri l} {c : ℝ} {g : Fin 2 → ℝ}
    (h : ∀ x ∈ triangle l s, w x = c + g 0 * x 0 + g 1 * x 1) : grad l w s = g := by
  set L : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    g 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
      g 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 with hL
  have hA : HasFDerivAt (fun x : Fin 2 → ℝ => c + L x) L (centroid l s) :=
    L.hasFDerivAt.const_add c
  have heq : w =ᶠ[nhds (centroid l s)] fun x => c + L x := by
    filter_upwards [tri_triangle_mem_nhds l s] with x hx
    rw [h x hx, hL]
    simp [add_assoc]
  have hd : fderiv ℝ w (centroid l s) = L := (hA.congr_of_eventuallyEq heq).fderiv
  funext i
  unfold grad
  rw [hd, hL]
  fin_cases i <;> simp

/-- Periodicity of `w ∈ ℙ_l` under translations by `n • e_i`, `n : ℕ`. -/
theorem tri_periodic_nat {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) (x : Fin 2 → ℝ)
    (i : Fin 2) (n : ℕ) : w (x + (n : ℝ) • Pi.single i 1) = w x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_smul, one_smul, ← add_assoc, hw.2.1, ih]

/-- A `Q`-periodic function takes the same value at the nodes `(a, b)` and `(a mod 2^l,
b mod 2^l)`. -/
theorem nodal_eq {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) (a b : ℕ) :
    w (vertex l a b) =
      nodal l w ⟨a % 2 ^ l, Nat.mod_lt _ (by positivity)⟩ ⟨b % 2 ^ l, Nat.mod_lt _ (by positivity)⟩ := by
  have hpos : (0:ℝ) < 2 ^ l := by positivity
  have ha : (a : ℝ) = ((a % 2 ^ l : ℕ) : ℝ) + 2 ^ l * ((a / 2 ^ l : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div a (2 ^ l)).symm
  have hb : (b : ℝ) = ((b % 2 ^ l : ℕ) : ℝ) + 2 ^ l * ((b / 2 ^ l : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div b (2 ^ l)).symm
  have hv : vertex l a b = (vertex l (a % 2 ^ l) (b % 2 ^ l) +
      ((a / 2 ^ l : ℕ) : ℝ) • Pi.single 0 1) + ((b / 2 ^ l : ℕ) : ℝ) • Pi.single 1 1 := by
    funext i
    rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    fin_cases i
    · simp [vertex]
      rw [ha]; field_simp
    · simp [vertex]
      rw [hb]; field_simp
  rw [hv, tri_periodic_nat hw, tri_periodic_nat hw]
  rfl

/-- Addition of `1` in `Fin (2^l)` is modular. -/
theorem tri_val_add_one {l : ℕ} (a : Fin (2 ^ l)) :
    ((a + 1 : Fin (2 ^ l)) : ℕ) = (a.val + 1) % 2 ^ l := by
  rw [Fin.val_add]; simp

/-- The value of `w ∈ ℙ_l` at the node `(a, b)`, `a, b : ℕ`, is `nodal` at any representatives
modulo `2^l`. -/
theorem tri_nodal_val {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) (a b : ℕ)
    (a' b' : Fin (2 ^ l)) (ha : a'.val = a % 2 ^ l) (hb : b'.val = b % 2 ^ l) :
    w (vertex l a b) = nodal l w a' b' := by
  rw [nodal_eq hw]
  congr 1 <;> exact Fin.ext (by simp [ha, hb])

/-- Membership in the lower triangle of the cell `(a, b)`. -/
theorem tri_mem_lower {l : ℕ} (a b : Fin (2 ^ l)) (x : Fin 2 → ℝ) :
    x ∈ triangle l (a, b, 0) ↔ ((a : ℝ) ≤ 2 ^ l * x 0 ∧ (b : ℝ) ≤ 2 ^ l * x 1 ∧
      2 ^ l * x 0 + 2 ^ l * x 1 ≤ (a : ℝ) + b + 1) := Iff.rfl

/-- Membership in the upper triangle of the cell `(a, b)`. -/
theorem tri_mem_upper {l : ℕ} (a b : Fin (2 ^ l)) (x : Fin 2 → ℝ) :
    x ∈ triangle l (a, b, 1) ↔ (2 ^ l * x 0 ≤ (a : ℝ) + 1 ∧ 2 ^ l * x 1 ≤ (b : ℝ) + 1 ∧
      (a : ℝ) + b + 1 ≤ 2 ^ l * x 0 + 2 ^ l * x 1) := Iff.rfl

/-- A node in the lower triangle of the cell `(a, b)`. -/
theorem tri_vertex_mem_lower {l : ℕ} (a b : Fin (2 ^ l)) (m n : ℕ) (h1 : a.val ≤ m)
    (h2 : b.val ≤ n) (h3 : m + n ≤ a.val + b.val + 1) : vertex l m n ∈ triangle l (a, b, 0) := by
  have hpos : (0:ℝ) < 2 ^ l := by positivity
  rw [tri_mem_lower]
  simp only [vertex, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_div_cancel₀ _ hpos.ne', mul_div_cancel₀ _ hpos.ne']
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

/-- A node in the upper triangle of the cell `(a, b)`. -/
theorem tri_vertex_mem_upper {l : ℕ} (a b : Fin (2 ^ l)) (m n : ℕ) (h1 : m ≤ a.val + 1)
    (h2 : n ≤ b.val + 1) (h3 : a.val + b.val + 1 ≤ m + n) : vertex l m n ∈ triangle l (a, b, 1) := by
  have hpos : (0:ℝ) < 2 ^ l := by positivity
  rw [tri_mem_upper]
  simp only [vertex, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_div_cancel₀ _ hpos.ne', mul_div_cancel₀ _ hpos.ne']
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

/-- The affine representation of `w` on a triangle, evaluated at a node of the triangle. -/
theorem tri_eval_vertex {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} {s : Tri l} {c : ℝ} {g : Fin 2 → ℝ}
    (h : ∀ x ∈ triangle l s, w x = c + g 0 * x 0 + g 1 * x 1) (m n : ℕ)
    (hmn : vertex l m n ∈ triangle l s) :
    w (vertex l m n) = c + g 0 * ((m : ℝ) / 2 ^ l) + g 1 * ((n : ℝ) / 2 ^ l) := by
  rw [h _ hmn]; simp [vertex]

/-- The gradient of `w ∈ ℙ_l` on the lower triangle of the cell `(a, b)`, with vertices
`(a, b)`, `(a + 1, b)`, `(a, b + 1)`. -/
theorem grad_lower {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) (a b : Fin (2 ^ l)) :
    grad l w (a, b, 0) =
      ![2 ^ l * (nodal l w (a + 1) b - nodal l w a b), 2 ^ l * (nodal l w a (b + 1) - nodal l w a b)] := by
  obtain ⟨c, g, hg⟩ := hw.2.2 (a, b, 0)
  rw [grad_eq_of_affine hg]
  have hpos : (0:ℝ) < 2 ^ l := by positivity
  have e00 : nodal l w a b = c + g 0 * ((a.val : ℝ) / 2 ^ l) + g 1 * ((b.val : ℝ) / 2 ^ l) :=
    tri_eval_vertex hg _ _ (tri_vertex_mem_lower a b _ _ le_rfl le_rfl (by omega))
  have e10 : nodal l w (a + 1) b =
      c + g 0 * (((a.val + 1 : ℕ) : ℝ) / 2 ^ l) + g 1 * ((b.val : ℝ) / 2 ^ l) := by
    rw [← tri_nodal_val hw (a.val + 1) b.val _ _ (tri_val_add_one a) (Nat.mod_eq_of_lt b.2).symm]
    exact tri_eval_vertex hg _ _ (tri_vertex_mem_lower a b _ _ (by omega) le_rfl (by omega))
  have e01 : nodal l w a (b + 1) =
      c + g 0 * ((a.val : ℝ) / 2 ^ l) + g 1 * (((b.val + 1 : ℕ) : ℝ) / 2 ^ l) := by
    rw [← tri_nodal_val hw a.val (b.val + 1) _ _ (Nat.mod_eq_of_lt a.2).symm (tri_val_add_one b)]
    exact tri_eval_vertex hg _ _ (tri_vertex_mem_lower a b _ _ le_rfl (by omega) (by omega))
  rw [e00, e10, e01]
  funext i
  fin_cases i
  · simp; field_simp; ring
  · simp; field_simp; ring

/-- The gradient of `w ∈ ℙ_l` on the upper triangle of the cell `(a, b)`, with vertices
`(a + 1, b)`, `(a + 1, b + 1)`, `(a, b + 1)`. -/
theorem grad_upper {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) (a b : Fin (2 ^ l)) :
    grad l w (a, b, 1) =
      ![2 ^ l * (nodal l w (a + 1) (b + 1) - nodal l w a (b + 1)),
        2 ^ l * (nodal l w (a + 1) (b + 1) - nodal l w (a + 1) b)] := by
  obtain ⟨c, g, hg⟩ := hw.2.2 (a, b, 1)
  rw [grad_eq_of_affine hg]
  have hpos : (0:ℝ) < 2 ^ l := by positivity
  have e11 : nodal l w (a + 1) (b + 1) =
      c + g 0 * (((a.val + 1 : ℕ) : ℝ) / 2 ^ l) + g 1 * (((b.val + 1 : ℕ) : ℝ) / 2 ^ l) := by
    rw [← tri_nodal_val hw (a.val + 1) (b.val + 1) _ _ (tri_val_add_one a) (tri_val_add_one b)]
    exact tri_eval_vertex hg _ _ (tri_vertex_mem_upper a b _ _ le_rfl le_rfl (by omega))
  have e10 : nodal l w (a + 1) b =
      c + g 0 * (((a.val + 1 : ℕ) : ℝ) / 2 ^ l) + g 1 * ((b.val : ℝ) / 2 ^ l) := by
    rw [← tri_nodal_val hw (a.val + 1) b.val _ _ (tri_val_add_one a) (Nat.mod_eq_of_lt b.2).symm]
    exact tri_eval_vertex hg _ _ (tri_vertex_mem_upper a b _ _ le_rfl (by omega) (by omega))
  have e01 : nodal l w a (b + 1) =
      c + g 0 * ((a.val : ℝ) / 2 ^ l) + g 1 * (((b.val + 1 : ℕ) : ℝ) / 2 ^ l) := by
    rw [← tri_nodal_val hw a.val (b.val + 1) _ _ (Nat.mod_eq_of_lt a.2).symm (tri_val_add_one b)]
    exact tri_eval_vertex hg _ _ (tri_vertex_mem_upper a b _ _ (by omega) le_rfl (by omega))
  rw [e11, e10, e01]
  funext i
  fin_cases i
  · simp; field_simp; ring
  · simp; field_simp; ring

/-- The normal of an interface: `(1, 0)`, `(0, 1)` or `(1, 1)`. -/
def Iface.normal {l : ℕ} (f : Iface l) : Fin 2 → ℝ :=
  if f.1 = 0 then ![1, 0] else if f.1 = 1 then ![0, 1] else ![1, 1]

/-- The value of `a + 1` in `Fin (2^l)`, as a real number, with the wrap-around. -/
theorem tri_val_add_one_real {l : ℕ} (a : Fin (2 ^ l)) :
    (((a + 1 : Fin (2 ^ l)) : ℕ) : ℝ) = (a : ℝ) + 1 - 2 ^ l * (((a.val + 1) / 2 ^ l : ℕ) : ℝ) := by
  have h : (((a.val + 1) % 2 ^ l : ℕ) : ℝ) + 2 ^ l * (((a.val + 1) / 2 ^ l : ℕ) : ℝ) =
      (a : ℝ) + 1 := by
    exact_mod_cast Nat.mod_add_div (a.val + 1) (2 ^ l)
  rw [tri_val_add_one]
  linarith

/-- The two triangles of an interface share an edge orthogonal to its normal: two common
vertices, modulo the period, whose difference is orthogonal to the normal. -/
theorem sides_adjacent {l : ℕ} (f : Iface l) :
    ∃ p q : Fin 2 → ℝ, p ≠ q ∧ (q 0 - p 0) * f.normal 0 + (q 1 - p 1) * f.normal 1 = 0 ∧
      (∃ z : Fin 2 → ℤ, (fun i => p i + z i) ∈ triangle l f.sides.1 ∧
        (fun i => q i + z i) ∈ triangle l f.sides.1) ∧
      (∃ z : Fin 2 → ℤ, (fun i => p i + z i) ∈ triangle l f.sides.2 ∧
        (fun i => q i + z i) ∈ triangle l f.sides.2) := by
  obtain ⟨k, a, b⟩ := f
  have hN : (2 : ℝ) ^ l ≠ 0 := by positivity
  have ha := tri_val_add_one_real a
  have hb := tri_val_add_one_real b
  have e : ∀ x y : ℝ, 2 ^ l * (x / 2 ^ l + y) = x + 2 ^ l * y := fun x y => by
    rw [mul_add, mul_div_cancel₀ _ hN]
  have e' : ∀ x : ℝ, 2 ^ l * (x / 2 ^ l) = x := fun x => mul_div_cancel₀ _ hN
  fin_cases k
  · show ∃ p q : Fin 2 → ℝ, p ≠ q ∧ (q 0 - p 0) * ![(1 : ℝ), 0] 0 + (q 1 - p 1) * ![(1 : ℝ), 0] 1 = 0 ∧
      (∃ z : Fin 2 → ℤ, (fun i => p i + z i) ∈ triangle l (a, b, 1) ∧
        (fun i => q i + z i) ∈ triangle l (a, b, 1)) ∧
      (∃ z : Fin 2 → ℤ, (fun i => p i + z i) ∈ triangle l (a + 1, b, 0) ∧
        (fun i => q i + z i) ∈ triangle l (a + 1, b, 0))
    refine ⟨![((a : ℝ) + 1) / 2 ^ l, (b : ℝ) / 2 ^ l], ![((a : ℝ) + 1) / 2 ^ l, ((b : ℝ) + 1) / 2 ^ l],
      ?_, by simp, ⟨0, ?_, ?_⟩, ⟨![-(((a.val + 1) / 2 ^ l : ℕ) : ℤ), 0], ?_, ?_⟩⟩
    · intro h
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      rw [div_left_inj' hN] at h1
      linarith
    all_goals
      first
      | rw [tri_mem_upper]
      | rw [tri_mem_lower]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, Int.cast_zero,
        add_zero, Int.cast_neg, Int.cast_natCast, e, e', mul_neg]
      refine ⟨?_, ?_, ?_⟩ <;> linarith
  · show ∃ p q : Fin 2 → ℝ, p ≠ q ∧ (q 0 - p 0) * ![(0 : ℝ), 1] 0 + (q 1 - p 1) * ![(0 : ℝ), 1] 1 = 0 ∧
      (∃ z : Fin 2 → ℤ, (fun i => p i + z i) ∈ triangle l (a, b, 1) ∧
        (fun i => q i + z i) ∈ triangle l (a, b, 1)) ∧
      (∃ z : Fin 2 → ℤ, (fun i => p i + z i) ∈ triangle l (a, b + 1, 0) ∧
        (fun i => q i + z i) ∈ triangle l (a, b + 1, 0))
    refine ⟨![(a : ℝ) / 2 ^ l, ((b : ℝ) + 1) / 2 ^ l], ![((a : ℝ) + 1) / 2 ^ l, ((b : ℝ) + 1) / 2 ^ l],
      ?_, by simp, ⟨0, ?_, ?_⟩, ⟨![0, -(((b.val + 1) / 2 ^ l : ℕ) : ℤ)], ?_, ?_⟩⟩
    · intro h
      have h0 := congrFun h 0
      simp only [Matrix.cons_val_zero] at h0
      rw [div_left_inj' hN] at h0
      linarith
    all_goals
      first
      | rw [tri_mem_upper]
      | rw [tri_mem_lower]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, Int.cast_zero,
        add_zero, Int.cast_neg, Int.cast_natCast, e, e', mul_neg]
      refine ⟨?_, ?_, ?_⟩ <;> linarith
  · show ∃ p q : Fin 2 → ℝ, p ≠ q ∧ (q 0 - p 0) * ![(1 : ℝ), 1] 0 + (q 1 - p 1) * ![(1 : ℝ), 1] 1 = 0 ∧
      (∃ z : Fin 2 → ℤ, (fun i => p i + z i) ∈ triangle l (a, b, 0) ∧
        (fun i => q i + z i) ∈ triangle l (a, b, 0)) ∧
      (∃ z : Fin 2 → ℤ, (fun i => p i + z i) ∈ triangle l (a, b, 1) ∧
        (fun i => q i + z i) ∈ triangle l (a, b, 1))
    refine ⟨![((a : ℝ) + 1) / 2 ^ l, (b : ℝ) / 2 ^ l], ![(a : ℝ) / 2 ^ l, ((b : ℝ) + 1) / 2 ^ l],
      ?_, ?_, ⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩⟩
    · intro h
      have h0 := congrFun h 0
      simp only [Matrix.cons_val_zero] at h0
      rw [div_left_inj' hN] at h0
      linarith
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
      ring
    all_goals
      first
      | rw [tri_mem_upper]
      | rw [tri_mem_lower]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, Int.cast_zero,
        add_zero, e']
      refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Across an interface, the jump of the gradient of `w ∈ ℙ_l` is a multiple of the normal. -/
theorem grad_sides_sub {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) (f : Iface l) :
    ∃ κ : ℝ, grad l w f.sides.1 - grad l w f.sides.2 = κ • f.normal := by
  obtain ⟨k, a, b⟩ := f
  fin_cases k
  · show ∃ κ : ℝ, grad l w (a, b, 1) - grad l w (a + 1, b, 0) = κ • ![1, 0]
    rw [grad_upper hw, grad_lower hw]
    refine ⟨2 ^ l * (nodal l w (a + 1) (b + 1) - nodal l w a (b + 1)) -
      2 ^ l * (nodal l w (a + 1 + 1) b - nodal l w (a + 1) b), ?_⟩
    funext i
    fin_cases i <;> simp
  · show ∃ κ : ℝ, grad l w (a, b, 1) - grad l w (a, b + 1, 0) = κ • ![0, 1]
    rw [grad_upper hw, grad_lower hw]
    refine ⟨2 ^ l * (nodal l w (a + 1) (b + 1) - nodal l w (a + 1) b) -
      2 ^ l * (nodal l w a (b + 1 + 1) - nodal l w a (b + 1)), ?_⟩
    funext i
    fin_cases i <;> simp
  · show ∃ κ : ℝ, grad l w (a, b, 0) - grad l w (a, b, 1) = κ • ![1, 1]
    rw [grad_upper hw, grad_lower hw]
    refine ⟨2 ^ l * (nodal l w (a + 1) b - nodal l w a b) -
      2 ^ l * (nodal l w (a + 1) (b + 1) - nodal l w a (b + 1)), ?_⟩
    funext i
    fin_cases i
    · simp
    · simp; ring

/-- Translation by `1` permutes `Fin (2^l)`. -/
theorem tri_sum_add_one {l : ℕ} (F : Fin (2 ^ l) → ℝ) : ∑ a, F (a + 1) = ∑ a, F a :=
  Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ => rfl

/-- **Equation (5.13)** (`baricentro`). The barycenter of `ν_w` vanishes, by periodicity. -/
theorem equation5_13 {l : ℕ} {w : (Fin 2 → ℝ) → ℝ} (hw : w ∈ PL l) :
    ∑ s : Tri l, (1 / 2 ^ (2 * l + 1) : ℝ) • grad l w s = 0 := by
  rw [← Finset.smul_sum]
  have hA : ∀ b : Fin (2 ^ l), ∑ a : Fin (2 ^ l), (nodal l w (a + 1) b - nodal l w a b) = 0 := by
    intro b
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact tri_sum_add_one fun a => nodal l w a b
  have hB : ∀ a : Fin (2 ^ l), ∑ b : Fin (2 ^ l), (nodal l w a (b + 1) - nodal l w a b) = 0 := by
    intro a
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact tri_sum_add_one fun b => nodal l w a b
  have hsum : ∑ s : Tri l, grad l w s = 0 := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, grad_lower hw, grad_upper hw]
    funext i
    fin_cases i
    · simp only [Finset.sum_apply, Pi.add_apply, Pi.zero_apply]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hA, mul_zero, add_zero,
        Finset.sum_const_zero]
    · simp only [Finset.sum_apply, Pi.add_apply, Pi.zero_apply]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hB, mul_zero, add_zero,
        Finset.sum_const_zero]
  rw [hsum, smul_zero]

end Pedregal
