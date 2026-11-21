module

public import Morrey.Common.Basic.CalculusOfVariations.Basic
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Data.Matrix.Basis

/-!
# Separately convex functions are locally Lipschitz

The argument of Rindler, *Calculus of variations* (2018), proof of Lemma 5.6 (Dacorogna 2008,
Theorem 2.31), for a function `f : ℝ^{d×m} → ℝ` convex along each coordinate direction `E_{ij}`.
Used in the proof of Dacorogna's formula (`Formula.lean`): the infimum formula is separately convex,
hence continuous. The proof is that of `External.Rindler.lemma5_6` (Cassese's Lemma 2.1), copied
because the files of `External/` import only Mathlib and `Morrey.Common.Basic`.
-/

@[expose] public section

namespace External.KinderlehrerPedregal

open CalculusOfVariations Metric Set

variable {d m : ℕ}

/-- The coordinate direction `(i, j)` of `ℝ^{d×m} = Fin d → Fin m → ℝ`. -/
def kpE (i : Fin d) (j : Fin m) : Fin d → Fin m → ℝ := fun a b => if i = a ∧ j = b then 1 else 0

private lemma kpE_apply (i : Fin d) (j : Fin m) (a : Fin d) (b : Fin m) :
    kpE i j a b = if i = a ∧ j = b then 1 else 0 := rfl

private lemma add_smul_kpE_apply (y : Fin d → Fin m → ℝ) (t : ℝ) (i : Fin d) (j : Fin m)
    (a : Fin d) (b : Fin m) :
    (y + t • kpE i j) a b = if i = a ∧ j = b then y a b + t else y a b := by
  simp only [Pi.add_apply, Pi.smul_apply, kpE_apply, smul_eq_mul]
  split_ifs <;> ring

theorem kp_of_add_smul_kpE (y : Fin d → Fin m → ℝ) (t : ℝ) (i : Fin d) (j : Fin m) :
    Matrix.of (y + t • kpE i j) = Matrix.of y + t • Matrix.single i j 1 := by
  ext a b
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply,
    add_smul_kpE_apply, smul_eq_mul]
  split_ifs <;> ring

private lemma mem_closedBall_iff_entries {x y : Fin d → Fin m → ℝ} {r : ℝ} (hr : 0 ≤ r) :
    y ∈ closedBall x r ↔ ∀ a b, |y a b - x a b| ≤ r := by
  rw [mem_closedBall, dist_pi_le_iff hr]
  refine forall_congr' fun a => ?_
  rw [dist_pi_le_iff hr]
  simp only [Real.dist_eq]

private lemma abs_sub_le_dist (y z : Fin d → Fin m → ℝ) (a : Fin d) (b : Fin m) :
    |y a b - z a b| ≤ dist y z := by
  rw [← Real.dist_eq]
  exact (dist_le_pi_dist (y a) (z a) b).trans (dist_le_pi_dist y z a)

/-- Upper bound on a cube by the values at the vertices, by convexity in one entry at a time. -/
private lemma upper_bound {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hsep : ∀ (y : Fin d → Fin m → ℝ) (i : Fin d) (j : Fin m),
      ConvexOn ℝ univ (fun t : ℝ => f (Matrix.of (y + t • kpE i j))))
    (x : Fin d → Fin m → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ M, ∀ y ∈ closedBall x r, f (Matrix.of y) ≤ M := by
  set F : (Fin d → Fin m → ℝ) → ℝ := fun X => f (Matrix.of X)
  set v : (Fin d → Fin m → Bool) → Fin d → Fin m → ℝ :=
    fun σ a b => x a b + if σ a b then r else -r
  suffices h : ∀ T : Finset (Fin d × Fin m), ∃ M, ∀ y ∈ closedBall x r,
      (∀ q ∉ T, |y q.1 q.2 - x q.1 q.2| = r) → F y ≤ M by
    obtain ⟨M, hM⟩ := h Finset.univ
    exact ⟨M, fun y hy => hM y hy (by simp)⟩
  intro T
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨∑ σ, |F (v σ)|, fun y _ hy => ?_⟩
    have hyv : y = v (fun a b => decide (y a b - x a b = r)) := by
      funext a b
      have h := hy (a, b) (Finset.notMem_empty _)
      simp only at h
      simp only [v]
      rcases (abs_eq hr).1 h with h' | h'
      · simp [h']; linarith
      · by_cases hr0 : r = 0
        · simp [hr0] at h' ⊢; linarith
        · have : y a b - x a b ≠ r := by intro h''; apply hr0; linarith
          simp [this]; linarith
    rw [hyv]
    exact (le_abs_self _).trans
      (Finset.single_le_sum (f := fun σ => |F (v σ)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ _))
  | insert p T hp ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨M, fun y hy hyT => ?_⟩
    obtain ⟨i, j⟩ := p
    set y₀ := y + (x i j - y i j) • kpE i j with hy₀
    have hent : ∀ s a b, (y₀ + s • kpE i j) a b = if i = a ∧ j = b then x a b + s else y a b := by
      intro s a b
      simp only [hy₀, add_smul_kpE_apply]
      split_ifs with h1 <;> [(obtain ⟨rfl, rfl⟩ := h1; ring); ring]
    have hmem : ∀ s, |s| ≤ r → y₀ + s • kpE i j ∈ closedBall x r := by
      intro s hs
      rw [mem_closedBall_iff_entries hr]
      intro a b
      rw [hent]
      split_ifs
      · simpa using hs
      · exact (mem_closedBall_iff_entries hr).1 hy a b
    have hvert : ∀ s, |s| = r → F (y₀ + s • kpE i j) ≤ M := by
      intro s hs
      refine hM _ (hmem s hs.le) fun q hq => ?_
      rw [hent]
      split_ifs with h1
      · simpa using hs
      · exact hyT q (by
          simp only [Finset.mem_insert, not_or]
          refine ⟨fun h2 => h1 ?_, hq⟩
          subst h2; exact ⟨rfl, rfl⟩)
    have hconv := hsep y₀ i j
    have hseg : y i j - x i j ∈ segment ℝ (-r) r := by
      rw [segment_eq_Icc (by linarith)]
      exact abs_le.1 ((mem_closedBall_iff_entries hr).1 hy i j)
    have key := hconv.le_on_segment (mem_univ (-r)) (mem_univ r) hseg
    have e : y₀ + (y i j - x i j) • kpE i j = y := by
      funext a b
      rw [hent]
      split_ifs with h1
      · obtain ⟨rfl, rfl⟩ := h1; ring
      · rfl
    rw [e] at key
    exact key.trans (max_le (hvert _ (by simp [abs_of_nonneg hr])) (hvert _ (abs_of_nonneg hr)))

/-- Lower bound on a cube, from the upper bound, by convexity in one entry at a time. -/
private lemma lower_bound {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hsep : ∀ (y : Fin d → Fin m → ℝ) (i : Fin d) (j : Fin m),
      ConvexOn ℝ univ (fun t : ℝ => f (Matrix.of (y + t • kpE i j))))
    (x : Fin d → Fin m → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ L, ∀ y ∈ closedBall x r, L ≤ f (Matrix.of y) := by
  set F : (Fin d → Fin m → ℝ) → ℝ := fun X => f (Matrix.of X)
  obtain ⟨M, hM⟩ := upper_bound hsep x hr
  suffices h : ∀ S : Finset (Fin d × Fin m), ∃ L, ∀ y ∈ closedBall x r,
      (∀ q ∉ S, y q.1 q.2 = x q.1 q.2) → L ≤ F y by
    obtain ⟨L, hL⟩ := h Finset.univ
    exact ⟨L, fun y hy => hL y hy (by simp)⟩
  intro S
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨F x, fun y _ hy => ?_⟩
    have : y = x := funext fun a => funext fun b => hy (a, b) (Finset.notMem_empty _)
    rw [this]
  | insert p S hp ih =>
    obtain ⟨L, hL⟩ := ih
    refine ⟨2 * L - M, fun y hy hyS => ?_⟩
    obtain ⟨i, j⟩ := p
    set y₀ := y + (x i j - y i j) • kpE i j with hy₀
    have hent : ∀ s a b, (y₀ + s • kpE i j) a b = if i = a ∧ j = b then x a b + s else y a b := by
      intro s a b
      simp only [hy₀, add_smul_kpE_apply]
      split_ifs with h1 <;> [(obtain ⟨rfl, rfl⟩ := h1; ring); ring]
    have hmem : ∀ s, |s| ≤ r → y₀ + s • kpE i j ∈ closedBall x r := by
      intro s hs
      rw [mem_closedBall_iff_entries hr]
      intro a b
      rw [hent]
      split_ifs
      · simpa using hs
      · exact (mem_closedBall_iff_entries hr).1 hy a b
    set t := y i j - x i j
    have ht : |t| ≤ r := (mem_closedBall_iff_entries hr).1 hy i j
    have e : ∀ s, y₀ + s • kpE i j = (fun a b => if i = a ∧ j = b then x a b + s else y a b) :=
      fun s => funext fun a => funext fun b => hent s a b
    have ey : y₀ + t • kpE i j = y := by
      rw [e]; funext a b; split_ifs with h1
      · obtain ⟨rfl, rfl⟩ := h1; simp [t]
      · rfl
    have e0 : y₀ + (0 : ℝ) • kpE i j = y₀ := by simp
    have hy0 : L ≤ F y₀ := by
      refine hL y₀ (e0 ▸ hmem 0 (by simp [hr])) fun q hq => ?_
      have := hent 0 q.1 q.2
      rw [e0] at this
      rw [this]
      split_ifs with h1
      · simp
      · exact hyS q (by
          simp only [Finset.mem_insert, not_or]
          refine ⟨fun h2 => h1 ?_, hq⟩
          subst h2; exact ⟨rfl, rfl⟩)
    have hconv := (hsep y₀ i j).2 (mem_univ t) (mem_univ (-t))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hconv
    rw [show 1 / 2 * t + 1 / 2 * -t = (0 : ℝ) by ring, e0] at hconv
    have hrefl : F (y₀ + (-t) • kpE i j) ≤ M := hM _ (hmem _ (by rwa [abs_neg]))
    change F y₀ ≤ 1 / 2 * F (y₀ + t • kpE i j) + 1 / 2 * F (y₀ + (-t) • kpE i j) at hconv
    rw [ey] at hconv
    linarith

/-- The Lipschitz bound along a coordinate line, from the convexity of the restriction and the
bound on a larger cube. -/
private lemma line_lipschitz {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hsep : ∀ (y : Fin d → Fin m → ℝ) (i : Fin d) (j : Fin m),
      ConvexOn ℝ univ (fun t : ℝ => f (Matrix.of (y + t • kpE i j))))
    (x : Fin d → Fin m → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ C, 0 ≤ C ∧ ∀ y ∈ closedBall x r, ∀ (i : Fin d) (j : Fin m) (t : ℝ),
      y + t • kpE i j ∈ closedBall x r →
        |f (Matrix.of (y + t • kpE i j)) - f (Matrix.of y)| ≤ C * |t| := by
  obtain ⟨M, hM⟩ := upper_bound hsep x (r := 5 * r) (by linarith)
  obtain ⟨L, hL⟩ := lower_bound hsep x (r := 5 * r) (by linarith)
  set K := max M (-L)
  have hK : ∀ y ∈ closedBall x (5 * r), |f (Matrix.of y)| ≤ K := fun y hy =>
    abs_le.2 ⟨by have := hL y hy; linarith [le_max_right M (-L)],
      (hM y hy).trans (le_max_left _ _)⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK x (mem_closedBall_self (by linarith)))
  refine ⟨2 * K / r, by positivity, fun y hy i j t hyt => ?_⟩
  set g : ℝ → ℝ := fun s => f (Matrix.of (y + s • kpE i j))
  have hg : ConvexOn ℝ (ball 0 (4 * r)) g :=
    (hsep y i j).subset (subset_univ _) (convex_ball _ _)
  have hgb : ∀ s, dist s 0 < 4 * r → |g s| ≤ K := by
    intro s hs
    apply hK
    rw [mem_closedBall_iff_entries (by linarith)]
    intro a b
    rw [add_smul_kpE_apply]
    have hya := abs_le.1 ((mem_closedBall_iff_entries hr.le).1 hy a b)
    rw [Real.dist_eq, sub_zero] at hs
    have hs' := abs_lt.1 hs
    split_ifs
    · exact abs_le.2 ⟨by linarith, by linarith⟩
    · exact abs_le.2 ⟨by linarith, by linarith⟩
  have hlip := hg.lipschitzOnWith_of_abs_le (ε := r) hr hgb
  have ht : |t| ≤ 2 * r := by
    have h1 := (mem_closedBall_iff_entries hr.le).1 hyt i j
    have h2 := abs_le.1 ((mem_closedBall_iff_entries hr.le).1 hy i j)
    rw [add_smul_kpE_apply, ite_eq_left_iff.mpr (fun h => absurd ⟨rfl, rfl⟩ h)] at h1
    have h1' := abs_le.1 h1
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h0 : (0 : ℝ) ∈ ball 0 (4 * r - r) := mem_ball_self (by linarith)
  have htb : t ∈ ball (0 : ℝ) (4 * r - r) := by
    rw [mem_ball, Real.dist_eq, sub_zero]; linarith
  have := hlip.dist_le_mul t htb 0 h0
  simp only [g, zero_smul, add_zero, Real.dist_eq, sub_zero] at this
  rwa [Real.coe_toNNReal _ (by positivity)] at this

/-- The Lipschitz bound on a cube, along a path that changes one entry at a time. -/
private lemma path_bound {F : (Fin d → Fin m → ℝ) → ℝ} {x : Fin d → Fin m → ℝ} {r C : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hline : ∀ y ∈ closedBall x r, ∀ (i : Fin d) (j : Fin m) (t : ℝ),
      y + t • kpE i j ∈ closedBall x r → |F (y + t • kpE i j) - F y| ≤ C * |t|) :
    ∀ S : Finset (Fin d × Fin m), ∀ y ∈ closedBall x r, ∀ z ∈ closedBall x r,
      (∀ q ∉ S, y q.1 q.2 = z q.1 q.2) → |F y - F z| ≤ S.card * C * dist y z := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro y _ z _ h
    have : y = z := funext fun a => funext fun b => h (a, b) (Finset.notMem_empty _)
    simp [this]
  | insert p S hp ih =>
    intro y hy z hz hyz
    obtain ⟨i, j⟩ := p
    set w := y + (z i j - y i j) • kpE i j with hw_def
    have hwent : ∀ a b, w a b = if i = a ∧ j = b then z a b else y a b := by
      intro a b
      simp only [hw_def, add_smul_kpE_apply]
      split_ifs with h1
      · obtain ⟨rfl, rfl⟩ := h1; ring
      · rfl
    have hw : w ∈ closedBall x r := by
      rw [mem_closedBall_iff_entries hr]
      intro a b
      rw [hwent]
      split_ifs
      · exact (mem_closedBall_iff_entries hr).1 hz a b
      · exact (mem_closedBall_iff_entries hr).1 hy a b
    have hwz : ∀ q ∉ S, w q.1 q.2 = z q.1 q.2 := by
      intro q hq
      rw [hwent]
      split_ifs with h1
      · rfl
      · exact hyz q (by
          simp only [Finset.mem_insert, not_or]
          refine ⟨fun h2 => h1 ?_, hq⟩
          subst h2; exact ⟨rfl, rfl⟩)
    have hdwz : dist w z ≤ dist y z := by
      rw [dist_pi_le_iff dist_nonneg]
      intro a
      rw [dist_pi_le_iff dist_nonneg]
      intro b
      rw [Real.dist_eq, hwent]
      split_ifs
      · simp
      · rw [← Real.dist_eq]
        exact (dist_le_pi_dist (y a) (z a) b).trans (dist_le_pi_dist y z a)
    have h1 := hline y hy i j _ hw
    have h2 := ih w hw z hz hwz
    have h3 : |z i j - y i j| ≤ dist y z := by
      rw [abs_sub_comm]; exact abs_sub_le_dist y z i j
    rw [Finset.card_insert_of_notMem hp]
    push_cast
    have e1 := abs_le.1 h1
    have e2 := abs_le.1 h2
    have e3 : C * |z i j - y i j| ≤ C * dist y z := mul_le_mul_of_nonneg_left h3 hC
    have e4 : (S.card : ℝ) * C * dist w z ≤ S.card * C * dist y z :=
      mul_le_mul_of_nonneg_left hdwz (by positivity)
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

/-- A function convex in each entry is locally Lipschitz: the standard argument for separately
convex functions (Rindler, proof of Lemma 5.6; Dacorogna 2008, Theorem 2.31), reproduced here from
`External.Rindler` (which this file may not import): bounds above at the vertices of a cube and
below by reflection, a Lipschitz bound along each coordinate line, and a path changing one entry
at a time. -/
theorem kp_locallyLipschitz_of_sep {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hsep : ∀ (y : Fin d → Fin m → ℝ) (i : Fin d) (j : Fin m),
      ConvexOn ℝ univ (fun t : ℝ => f (Matrix.of (y + t • kpE i j)))) :
    LocallyLipschitz fun X : Fin d → Fin m → ℝ => f (Matrix.of X) := by
  intro x
  obtain ⟨C, hC, hline⟩ := line_lipschitz hsep x one_pos
  refine ⟨(Fintype.card (Fin d × Fin m) * C).toNNReal, closedBall x 1,
    closedBall_mem_nhds x one_pos, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
  have := path_bound (F := fun X => f (Matrix.of X)) zero_le_one hC hline Finset.univ y hy z hz
    (by simp)
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  simpa [Finset.card_univ] using this



end External.KinderlehrerPedregal
