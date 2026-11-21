module

public import Morrey.Hn.Mold

/-!
# `(H_n)`-conditions with rank-one directions are laminates

A mold fed with nonnegative weights and matrices whose decomposition directions all have rank at
most one describes, in its top-to-bottom form (Definition 3.1), a sequence of splittings of the
Dirac mass at its final mass point into its leaf measure along rank-one segments. So the leaf
measure is a laminate of finite order. This is the mechanism behind Proposition 6.1 ("fixed
points for such a map are identified with joint `(H_n)`-conditions whose decomposition
directions are parallel, i.e. with laminates", Section 1).
-/

@[expose] public section

namespace Morrey

namespace Mold

variable {ι : Type}

/-- The measure of the leaves of a mold, for weights `t` and matrices `A`: mass `t i` at `A i`
for each leaf `i`. -/
noncomputable def leafMeasure (t : ι → ℝ) (A : ι → Matrix (Fin 2) (Fin 2) ℝ) :
    Mold ι → (Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ)
  | leaf i => Finsupp.single (A i) (t i)
  | node L R => leafMeasure t A L + leafMeasure t A R

/-- The leaf measure of a mold is the sum over its leaves. -/
theorem leafMeasure_eq_sum (t : ι → ℝ) (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (M : Mold ι) :
    M.leafMeasure t A = (M.leaves.map fun i => Finsupp.single (A i) (t i)).sum := by
  induction M with
  | leaf i => simp [leafMeasure, leaves]
  | node L R ihL ihR => simp [leafMeasure, leaves, ihL, ihR]

/-- With nonnegative weights, the leaf measure is nonnegative. -/
private theorem leafMeasure_nonneg {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i)
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (M : Mold ι) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    0 ≤ M.leafMeasure t A X := by
  induction M with
  | leaf i =>
    simp only [leafMeasure, Finsupp.single_apply]
    split_ifs
    · exact ht i
    · exact le_rfl
  | node L R ihL ihR =>
    simp only [leafMeasure, Finsupp.add_apply]
    exact add_nonneg ihL ihR

/-- With nonnegative weights, a mold of weight `0` has the zero leaf measure. -/
private theorem leafMeasure_eq_zero {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i)
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (M : Mold ι) (hM : M.weight t = 0) :
    M.leafMeasure t A = 0 := by
  induction M with
  | leaf i =>
    simp only [weight] at hM
    simp [leafMeasure, hM]
  | node L R ihL ihR =>
    simp only [weight] at hM
    have hL := weight_nonneg ht L
    have hR := weight_nonneg ht R
    simp only [leafMeasure, ihL (by linarith), ihR (by linarith), add_zero]

/-- If every decomposition direction of a mold, for nonnegative weights `t` and matrices `A`,
has rank at most one, then splitting the atom at the mold's mass point gives the leaf measure:
whenever `ρ + δ_{point}·weight` is a laminate (for a nonnegative `ρ`), so is
`ρ + leafMeasure`. -/
theorem isLaminate_add_leafMeasure {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i)
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (M : Mold ι)
    (hrank : ∀ p ∈ M.nodes, (p.1.point t A - p.2.point t A).rank ≤ 1)
    {ρ : Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ} (hρ : ∀ X, 0 ≤ ρ X)
    (h : IsLaminate (ρ + Finsupp.single (M.point t A) (M.weight t))) :
    IsLaminate (ρ + M.leafMeasure t A) := by
  induction M generalizing ρ with
  | leaf i => exact h
  | node L R ihL ihR =>
    have hwL := weight_nonneg ht L
    have hwR := weight_nonneg ht R
    have hrankLR := hrank (L, R) (by simp [nodes])
    have hrankL : ∀ p ∈ L.nodes, (p.1.point t A - p.2.point t A).rank ≤ 1 :=
      fun p hp => hrank p (by simp [nodes, hp])
    have hrankR : ∀ p ∈ R.nodes, (p.1.point t A - p.2.point t A).rank ≤ 1 :=
      fun p hp => hrank p (by simp [nodes, hp])
    rcases (add_nonneg hwL hwR).lt_or_eq with hs | hs
    · -- split the atom at the mass point, of weight `s = s_L + s_R`, into atoms at `P_L` and
      -- `P_R`, of weights `s_L` and `s_R`, along the rank-one direction `P_L − P_R`
      have hs' : weight t L + weight t R ≠ 0 := hs.ne'
      have hθ : 1 - weight t R / (weight t L + weight t R) =
          weight t L / (weight t L + weight t R) := by
        field_simp
        ring
      have hθ' : weight t R / (weight t L + weight t R) =
          1 - weight t L / (weight t L + weight t R) := by
        rw [← hθ]
        ring
      have hsplit := IsLaminate.split (A := (node L R).point t A) (B := L.point t A)
        (C := R.point t A)
        (c := weight t L + weight t R) (θ := weight t L / (weight t L + weight t R)) h hs.le
        (by
          simp only [Finsupp.add_apply, Finsupp.single_eq_same, weight]
          linarith [hρ ((node L R).point t A)])
        (div_nonneg hwL hs.le) (by rw [div_le_one hs]; linarith)
        (by simp only [point, lam, hs, ↓reduceIte]; rw [hθ, hθ']) hrankLR
      have e : ρ + Finsupp.single ((node L R).point t A) ((node L R).weight t) -
          Finsupp.single ((node L R).point t A) (weight t L + weight t R) +
          Finsupp.single (L.point t A)
            (weight t L / (weight t L + weight t R) * (weight t L + weight t R)) +
          Finsupp.single (R.point t A)
            ((1 - weight t L / (weight t L + weight t R)) * (weight t L + weight t R)) =
          ρ + Finsupp.single (R.point t A) (weight t R) +
            Finsupp.single (L.point t A) (weight t L) := by
        rw [← hθ', div_mul_cancel₀ _ hs', div_mul_cancel₀ _ hs']
        simp only [weight, add_sub_cancel_right]
        abel
      rw [e] at hsplit
      -- then split the atoms at `P_L` and `P_R` along `L` and `R`
      have hL := ihL hrankL (ρ := ρ + Finsupp.single (R.point t A) (weight t R))
        (fun X => add_nonneg (hρ X) (by
          rw [Finsupp.single_apply]
          split_ifs
          · exact hwR
          · exact le_rfl)) hsplit
      have hR := ihR hrankR (ρ := ρ + L.leafMeasure t A)
        (fun X => add_nonneg (hρ X) (leafMeasure_nonneg ht A L X))
        (by rwa [add_right_comm])
      simpa only [leafMeasure, add_assoc] using hR
    · -- the mold has weight `0`: all its leaf weights vanish
      have hL0 : weight t L = 0 := by linarith
      have hR0 : weight t R = 0 := by linarith
      have h0 : (node L R).leafMeasure t A = 0 :=
        leafMeasure_eq_zero ht A _ (by simp [weight, hL0, hR0])
      rw [h0, add_zero]
      simpa [weight, hL0, hR0] using h

/-- A mold of total weight `1` whose decomposition directions all have rank at most one, for
nonnegative weights, has a laminate as its leaf measure. -/
theorem isLaminate_leafMeasure {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i)
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (M : Mold ι) (hw : M.weight t = 1)
    (hrank : ∀ p ∈ M.nodes, (p.1.point t A - p.2.point t A).rank ≤ 1) :
    IsLaminate (M.leafMeasure t A) := by
  have h := isLaminate_add_leafMeasure ht A M hrank (ρ := 0) (fun _ => le_rfl)
    (by rw [zero_add, hw]; exact IsLaminate.dirac _)
  rwa [zero_add] at h

end Mold

end Morrey
