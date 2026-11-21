module

public import Morrey.Common.Basic.CalculusOfVariations.Basic
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Data.Matrix.Basis
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Rindler and Dacorogna: rank-one convex functions and quasiconvexity

F. Rindler, *Calculus of variations*, Springer 2018, Lemma 5.6 and Propositions 5.1, 5.3;
B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer 2008,
Propositions 5.11, 5.13. Cassese quotes them as Lemma 2.1 and Lemma 2.2. They are standard and
within reach (class Mod of the inventory). Proved here: Lemma 2.1 (`lemma5_6`), "quasiconvex ⇒
rank-one convex" (`rankOneConvex_of_quasiconvex`) and the periodic form of Lemma 2.2
(`quasiconvexAtOn_iff_periodic`), and the domain independence (`quasiconvexAtOn_iff`). Helpers are
private, prefixed `rd_` (and unprefixed private lemmas for Lemma 5.6), except the public
`rd_quasiconvexAtOn_of_unitCube` (one direction of the domain independence, for bounded measurable
sets), which `Cassese.Toolkit` uses.

Integrands are lower semicontinuous and locally bounded, as in Cassese (Section 1.5).
-/

@[expose] public section

namespace External.Rindler

open CalculusOfVariations Metric Set MeasureTheory Filter Topology
open scoped Pointwise

variable {d m : ℕ}

/-! ### Lemma 5.6: rank-one convex functions are locally Lipschitz -/

private lemma rank_eq_zero_imp {A : Matrix (Fin d) (Fin m) ℝ} (h : A.rank = 0) : A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun F => F (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply] using this

private lemma rank_single_one (i : Fin d) (j : Fin m) : (Matrix.single i j (1 : ℝ)).rank = 1 := by
  apply le_antisymm
  · rw [Matrix.single_eq_single_vecMulVec_single]; exact Matrix.rank_vecMulVec_le _ _
  · rw [Nat.one_le_iff_ne_zero]; intro h
    have := congrArg (fun M => M i j) (rank_eq_zero_imp h)
    simp at this

/-- The coordinate direction `(i, j)` of `ℝ^{d×m} = Fin d → Fin m → ℝ`. -/
private def rE (i : Fin d) (j : Fin m) : Fin d → Fin m → ℝ := fun a b => if i = a ∧ j = b then 1 else 0

private lemma rE_apply (i : Fin d) (j : Fin m) (a : Fin d) (b : Fin m) :
    rE i j a b = if i = a ∧ j = b then 1 else 0 := rfl

private lemma add_smul_rE_apply (y : Fin d → Fin m → ℝ) (t : ℝ) (i : Fin d) (j : Fin m)
    (a : Fin d) (b : Fin m) :
    (y + t • rE i j) a b = if i = a ∧ j = b then y a b + t else y a b := by
  simp only [Pi.add_apply, Pi.smul_apply, rE_apply, smul_eq_mul]
  split_ifs <;> ring

private lemma of_add_smul_rE (y : Fin d → Fin m → ℝ) (t : ℝ) (i : Fin d) (j : Fin m) :
    Matrix.of (y + t • rE i j) = Matrix.of y + t • Matrix.single i j 1 := by
  ext a b
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply,
    add_smul_rE_apply, smul_eq_mul]
  split_ifs <;> ring

private lemma sep_convex {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f)
    (y : Fin d → Fin m → ℝ) (i : Fin d) (j : Fin m) :
    ConvexOn ℝ univ (fun t : ℝ => f (Matrix.of (y + t • rE i j))) := by
  have := hf (Matrix.of y) (Matrix.single i j 1) (rank_single_one i j)
  simpa only [of_add_smul_rE] using this

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
      ConvexOn ℝ univ (fun t : ℝ => f (Matrix.of (y + t • rE i j))))
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
    set y₀ := y + (x i j - y i j) • rE i j with hy₀
    have hent : ∀ s a b, (y₀ + s • rE i j) a b = if i = a ∧ j = b then x a b + s else y a b := by
      intro s a b
      simp only [hy₀, add_smul_rE_apply]
      split_ifs with h1 <;> [(obtain ⟨rfl, rfl⟩ := h1; ring); ring]
    have hmem : ∀ s, |s| ≤ r → y₀ + s • rE i j ∈ closedBall x r := by
      intro s hs
      rw [mem_closedBall_iff_entries hr]
      intro a b
      rw [hent]
      split_ifs
      · simpa using hs
      · exact (mem_closedBall_iff_entries hr).1 hy a b
    have hvert : ∀ s, |s| = r → F (y₀ + s • rE i j) ≤ M := by
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
    have e : y₀ + (y i j - x i j) • rE i j = y := by
      funext a b
      rw [hent]
      split_ifs with h1
      · obtain ⟨rfl, rfl⟩ := h1; ring
      · rfl
    rw [e] at key
    exact key.trans (max_le (hvert _ (by simp [abs_of_nonneg hr])) (hvert _ (abs_of_nonneg hr)))

/-- Lower bound on a cube, from the upper bound, by convexity in one entry at a time. -/
private lemma lower_bound {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hsep : ∀ (y : Fin d → Fin m → ℝ) (i : Fin d) (j : Fin m),
      ConvexOn ℝ univ (fun t : ℝ => f (Matrix.of (y + t • rE i j))))
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
    set y₀ := y + (x i j - y i j) • rE i j with hy₀
    have hent : ∀ s a b, (y₀ + s • rE i j) a b = if i = a ∧ j = b then x a b + s else y a b := by
      intro s a b
      simp only [hy₀, add_smul_rE_apply]
      split_ifs with h1 <;> [(obtain ⟨rfl, rfl⟩ := h1; ring); ring]
    have hmem : ∀ s, |s| ≤ r → y₀ + s • rE i j ∈ closedBall x r := by
      intro s hs
      rw [mem_closedBall_iff_entries hr]
      intro a b
      rw [hent]
      split_ifs
      · simpa using hs
      · exact (mem_closedBall_iff_entries hr).1 hy a b
    set t := y i j - x i j
    have ht : |t| ≤ r := (mem_closedBall_iff_entries hr).1 hy i j
    have e : ∀ s, y₀ + s • rE i j = (fun a b => if i = a ∧ j = b then x a b + s else y a b) :=
      fun s => funext fun a => funext fun b => hent s a b
    have ey : y₀ + t • rE i j = y := by
      rw [e]; funext a b; split_ifs with h1
      · obtain ⟨rfl, rfl⟩ := h1; simp [t]
      · rfl
    have e0 : y₀ + (0 : ℝ) • rE i j = y₀ := by simp
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
    have hrefl : F (y₀ + (-t) • rE i j) ≤ M := hM _ (hmem _ (by rwa [abs_neg]))
    change F y₀ ≤ 1 / 2 * F (y₀ + t • rE i j) + 1 / 2 * F (y₀ + (-t) • rE i j) at hconv
    rw [ey] at hconv
    linarith

/-- The Lipschitz bound along a coordinate line, from the convexity of the restriction and the
bound on a larger cube. -/
private lemma line_lipschitz {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hsep : ∀ (y : Fin d → Fin m → ℝ) (i : Fin d) (j : Fin m),
      ConvexOn ℝ univ (fun t : ℝ => f (Matrix.of (y + t • rE i j))))
    (x : Fin d → Fin m → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ C, 0 ≤ C ∧ ∀ y ∈ closedBall x r, ∀ (i : Fin d) (j : Fin m) (t : ℝ),
      y + t • rE i j ∈ closedBall x r →
        |f (Matrix.of (y + t • rE i j)) - f (Matrix.of y)| ≤ C * |t| := by
  obtain ⟨M, hM⟩ := upper_bound hsep x (r := 5 * r) (by linarith)
  obtain ⟨L, hL⟩ := lower_bound hsep x (r := 5 * r) (by linarith)
  set K := max M (-L)
  have hK : ∀ y ∈ closedBall x (5 * r), |f (Matrix.of y)| ≤ K := fun y hy =>
    abs_le.2 ⟨by have := hL y hy; linarith [le_max_right M (-L)],
      (hM y hy).trans (le_max_left _ _)⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK x (mem_closedBall_self (by linarith)))
  refine ⟨2 * K / r, by positivity, fun y hy i j t hyt => ?_⟩
  set g : ℝ → ℝ := fun s => f (Matrix.of (y + s • rE i j))
  have hg : ConvexOn ℝ (ball 0 (4 * r)) g :=
    (hsep y i j).subset (subset_univ _) (convex_ball _ _)
  have hgb : ∀ s, dist s 0 < 4 * r → |g s| ≤ K := by
    intro s hs
    apply hK
    rw [mem_closedBall_iff_entries (by linarith)]
    intro a b
    rw [add_smul_rE_apply]
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
    rw [add_smul_rE_apply, ite_eq_left_iff.mpr (fun h => absurd ⟨rfl, rfl⟩ h)] at h1
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
      y + t • rE i j ∈ closedBall x r → |F (y + t • rE i j) - F y| ≤ C * |t|) :
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
    set w := y + (z i j - y i j) • rE i j with hw_def
    have hwent : ∀ a b, w a b = if i = a ∧ j = b then z a b else y a b := by
      intro a b
      simp only [hw_def, add_smul_rE_apply]
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

/-- A function convex in each entry is locally Lipschitz (the argument of Lemma 5.6). -/
private lemma rd_locallyLipschitz_of_sep {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hsep : ∀ (y : Fin d → Fin m → ℝ) (i : Fin d) (j : Fin m),
      ConvexOn ℝ univ (fun t : ℝ => f (Matrix.of (y + t • rE i j)))) :
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


/-- **Lemma 2.1** (`cs-lem2.1`) of Cassese, citing Rindler, Lemma 5.6: a rank-one convex
integrand is locally Lipschitz. (`Matrix.of` identifies `ℝ^{d×m}` with `Fin d → Fin m → ℝ`, with
its product metric.)

Proof: the standard argument for separately convex functions (Rindler, proof of Lemma 5.6;
Dacorogna 2008, Theorem 2.31). A rank-one convex `f` is convex along every coordinate direction
`E_{ij}` (a matrix of rank one). On a cube `x + [-r, r]^{d×m}` (a closed ball of the product
metric) `f` is bounded above by its values at the vertices (`upper_bound`, convexity in one entry
at a time) and below (`lower_bound`, by reflection in one entry at a time); convexity along each
coordinate line with these bounds gives a Lipschitz bound along the line (`line_lipschitz`), and a
path that changes one entry at a time gives the Lipschitz bound on the cube (`path_bound`). -/
theorem lemma5_6 {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f) :
    LocallyLipschitz fun X : Fin d → Fin m → ℝ => f (Matrix.of X) := by
  exact rd_locallyLipschitz_of_sep (sep_convex hf)

/-! ### Test maps: bounds and integrability -/

/-- `|∂_k φ_i| ≤ K` for a `K`-Lipschitz `φ`. -/
private lemma rd_grad_abs_le {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (x : Fin m → ℝ) (i : Fin d) (k : Fin m) : |grad φ x i k| ≤ K := by
  have hi : LipschitzWith K (fun y => φ y i) := by
    have h := (LipschitzWith.eval (α := fun _ : Fin d => ℝ) i).comp hφ
    rw [one_mul] at h
    exact h
  simp only [grad, Matrix.of_apply]
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ (fun y => φ y i) x (Pi.single k 1)‖
      ≤ ‖fderiv ℝ (fun y => φ y i) x‖ * ‖(Pi.single k 1 : Fin m → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * 1 := by
        gcongr
        · exact norm_fderiv_le_of_lipschitz ℝ hi
        · rw [Pi.norm_single, norm_one]
    _ = K := mul_one _

private lemma rd_measurable_add_grad (A : Matrix (Fin d) (Fin m) ℝ) (φ : (Fin m → ℝ) → Fin d → ℝ) :
    Measurable fun x => A + grad φ x :=
  Measurable.of_eval_matrix _ fun i k => by
    simp only [Matrix.add_apply, grad, Matrix.of_apply]
    exact measurable_const.add (measurable_fderiv_apply_const ℝ (fun y => φ y i) _)

/-- A locally bounded function is bounded on compact sets. -/
private lemma rd_bdd_of_compact {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hbdd : IsLocallyBounded f)
    {K : Set (Matrix (Fin d) (Fin m) ℝ)} (hK : IsCompact K) : ∃ C, ∀ M ∈ K, |f M| ≤ C := by
  choose U hU C hC using hbdd
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover U (fun x _ => hU x)
  refine ⟨∑ x ∈ t, |C x|, fun M hM => ?_⟩
  obtain ⟨x, hx, hMx⟩ := Set.mem_iUnion₂.1 (hcover hM)
  exact (hC x M hMx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |C x|) (fun _ _ => abs_nonneg _) hx))

private lemma rd_isCompact_box (B : Matrix (Fin d) (Fin m) ℝ) (K : ℝ) :
    IsCompact {M : Matrix (Fin d) (Fin m) ℝ | ∀ i k, |M i k - B i k| ≤ K} := by
  have : {M : Matrix (Fin d) (Fin m) ℝ | ∀ i k, |M i k - B i k| ≤ K} =
      Set.pi univ fun i => Set.pi univ fun k => Icc (B i k - K) (B i k + K) := by
    ext M
    constructor
    · intro h i _ k _
      exact ⟨by linarith [(abs_le.1 (h i k)).1], by linarith [(abs_le.1 (h i k)).2]⟩
    · intro h i k
      have := h i (Set.mem_univ _) k (Set.mem_univ _)
      exact abs_le.2 ⟨by linarith [this.1], by linarith [this.2]⟩
  rw [this]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun k => isCompact_Icc

/-- A bound for `f` on all matrices `A + G` with entries `|G_{ik}| ≤ L`. -/
private lemma rd_bound_near {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hbdd : IsLocallyBounded f)
    (A : Matrix (Fin d) (Fin m) ℝ) (L : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ G : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |G i k| ≤ L) → |f (A + G)| ≤ C := by
  obtain ⟨C, hC⟩ := rd_bdd_of_compact hbdd (rd_isCompact_box A L)
  refine ⟨max C 0, le_max_right _ _, fun G hG => (hC _ fun i k => ?_).trans (le_max_left _ _)⟩
  simpa using hG i k

/-- For a lower semicontinuous, locally bounded `f` and a Lipschitz `φ`, `x ↦ f (A + ∇φ (x))` is
integrable on sets of finite measure (it is measurable and bounded). -/
private lemma rd_integrableOn {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hlsc : LowerSemicontinuous f)
    (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ}
    {K : NNReal} (hφ : LipschitzWith K φ) {s : Set (Fin m → ℝ)} (hs : volume s < ⊤) :
    IntegrableOn (fun x => f (A + grad φ x)) s := by
  obtain ⟨C, -, hC⟩ := rd_bound_near hbdd A K
  refine IntegrableOn.of_bound hs
    (hlsc.measurable.comp (rd_measurable_add_grad A φ)).aestronglyMeasurable C
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hC _ (rd_grad_abs_le hφ x)

private lemma rd_volume_unitCube (m : ℕ) : volume (unitCube m) = 1 := by
  simp [unitCube, Real.volume_pi_Ioo]

/-! ### Periodic extension of a test map -/

/-- The periodic extension `x ↦ φ (fract x)` of a map on the unit cube. -/
private noncomputable def rd_perExt (φ : (Fin m → ℝ) → Fin d → ℝ) : (Fin m → ℝ) → Fin d → ℝ :=
  fun x => φ (fun i => Int.fract (x i))

/-- On a closed integer cell `z + [0, 1]^m`, the periodic extension of a map vanishing off the open
cube is its translate. -/
private lemma rd_perExt_cell {φ : (Fin m → ℝ) → Fin d → ℝ} (h0 : ∀ x ∉ unitCube m, φ x = 0)
    (z : Fin m → ℤ) {x : Fin m → ℝ} (hx : ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) :
    rd_perExt φ x = φ (x - fun i => (z i : ℝ)) := by
  by_cases h : ∀ i, (z i : ℝ) < x i ∧ x i < z i + 1
  · have : (fun i => Int.fract (x i)) = x - fun i => (z i : ℝ) := by
      funext i
      rw [← Int.self_sub_floor, Int.floor_eq_iff.2 ⟨(h i).1.le, (h i).2⟩]
      rfl
    simp only [rd_perExt, this]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hint : x i = z i ∨ x i = z i + 1 := by
      rcases eq_or_lt_of_le (hx i).1 with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr (le_antisymm (hx i).2 (hi h1))
    have h1 : (fun i => Int.fract (x i)) ∉ unitCube m := by
      intro hmem
      have := (hmem i (Set.mem_univ _)).1
      dsimp only at this
      rcases hint with h2 | h2
      · rw [h2, Int.fract_intCast] at this; exact lt_irrefl _ this
      · rw [h2, show (z i : ℝ) + 1 = ((z i + 1 : ℤ) : ℝ) by push_cast; ring,
          Int.fract_intCast] at this
        exact lt_irrefl _ this
    have h2 : (x - fun i => (z i : ℝ)) ∉ unitCube m := by
      intro hmem
      have := hmem i (Set.mem_univ _)
      simp only [Pi.sub_apply] at this
      rcases hint with h3 | h3 <;> rw [h3] at this <;> linarith [this.1, this.2]
    simp only [rd_perExt, h0 _ h1, h0 _ h2]

private lemma rd_perExt_eq_zero_of_int {φ : (Fin m → ℝ) → Fin d → ℝ}
    (h0 : ∀ x ∉ unitCube m, φ x = 0) {x : Fin m → ℝ} {c : Fin m} {n : ℤ} (hc : x c = n) :
    rd_perExt φ x = 0 := by
  apply h0
  intro hmem
  have := (hmem c (Set.mem_univ _)).1
  dsimp only at this
  rw [hc, Int.fract_intCast] at this
  exact lt_irrefl _ this

private lemma rd_dist_update (w : Fin m → ℝ) (c : Fin m) (a b : ℝ) :
    dist (Function.update w c a) (Function.update w c b) ≤ |a - b| := by
  rw [dist_pi_le_iff (abs_nonneg _)]
  intro i
  rcases eq_or_ne i c with rfl | hi
  · simp [Real.dist_eq]
  · simp [Function.update_of_ne hi]

/-- The one-dimensional step: along a coordinate line the periodic extension is `K`-Lipschitz
(it is the translate of `φ` on each closed cell, and vanishes at the integer points). -/
private lemma rd_perExt_line {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (h0 : ∀ x ∉ unitCube m, φ x = 0) (w : Fin m → ℝ) (c : Fin m) (s s' : ℝ) :
    dist (rd_perExt φ (Function.update w c s)) (rd_perExt φ (Function.update w c s')) ≤
      K * |s - s'| := by
  wlog hss : s ≤ s' generalizing s s'
  · rw [dist_comm, abs_sub_comm]; exact this s' s (le_of_not_ge hss)
  -- the cell of a point of the line
  have hcell : ∀ t : ℝ, ∀ i, ((fun j => ⌊Function.update w c t j⌋) i : ℝ) ≤
      Function.update w c t i ∧ Function.update w c t i ≤
        ((fun j => ⌊Function.update w c t j⌋) i : ℝ) + 1 := fun t i =>
    ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  -- moving coordinate `c` inside the cell of `t`
  have hmove : ∀ t u : ℝ, (⌊t⌋ : ℝ) ≤ u → u ≤ ⌊t⌋ + 1 →
      dist (rd_perExt φ (Function.update w c t)) (rd_perExt φ (Function.update w c u)) ≤
        K * |t - u| := by
    intro t u hu1 hu2
    set z := fun j => ⌊Function.update w c t j⌋
    have hzu : ∀ i, (z i : ℝ) ≤ Function.update w c u i ∧ Function.update w c u i ≤ z i + 1 := by
      intro i
      rcases eq_or_ne i c with rfl | hi
      · simp only [z, Function.update_self]; exact ⟨hu1, hu2⟩
      · simp only [z, Function.update_of_ne hi]
        exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
    rw [rd_perExt_cell h0 z (hcell t), rd_perExt_cell h0 z hzu]
    calc dist (φ (Function.update w c t - fun i => (z i : ℝ)))
          (φ (Function.update w c u - fun i => (z i : ℝ)))
        ≤ K * dist (Function.update w c t - fun i => (z i : ℝ))
          (Function.update w c u - fun i => (z i : ℝ)) := hφ.dist_le_mul _ _
      _ = K * dist (Function.update w c t) (Function.update w c u) := by rw [dist_sub_right]
      _ ≤ K * |t - u| := by gcongr; exact rd_dist_update w c t u
  rcases eq_or_lt_of_le (Int.floor_le_floor hss) with heq | hlt
  · -- the same cell
    exact hmove s s' (by rw [heq]; exact Int.floor_le s')
      (by rw [heq]; exact (Int.lt_floor_add_one s').le)
  · -- through the integer points `⌊s⌋ + 1 ≤ ⌊s'⌋`
    have hle : (⌊s⌋ : ℝ) + 1 ≤ ⌊s'⌋ := by exact_mod_cast hlt
    have hp : rd_perExt φ (Function.update w c ((⌊s⌋ : ℝ) + 1)) = 0 :=
      rd_perExt_eq_zero_of_int h0 (c := c) (n := ⌊s⌋ + 1) (by simp)
    have hq : rd_perExt φ (Function.update w c (⌊s'⌋ : ℝ)) = 0 :=
      rd_perExt_eq_zero_of_int h0 (c := c) (n := ⌊s'⌋) (by simp)
    have h1 := hmove s ((⌊s⌋ : ℝ) + 1) (by linarith) le_rfl
    have h2 := hmove s' (⌊s'⌋ : ℝ) le_rfl (by linarith)
    rw [hp] at h1
    rw [hq] at h2
    have e1 : |s - ((⌊s⌋ : ℝ) + 1)| = (⌊s⌋ : ℝ) + 1 - s := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [Int.lt_floor_add_one s])]
    have e2 : |s' - (⌊s'⌋ : ℝ)| = s' - ⌊s'⌋ := abs_of_nonneg (by linarith [Int.floor_le s'])
    rw [e1] at h1
    rw [e2] at h2
    calc dist (rd_perExt φ (Function.update w c s)) (rd_perExt φ (Function.update w c s'))
        ≤ dist (rd_perExt φ (Function.update w c s)) 0 +
          dist 0 (rd_perExt φ (Function.update w c s')) := dist_triangle _ _ _
      _ ≤ K * ((⌊s⌋ : ℝ) + 1 - s) + K * (s' - ⌊s'⌋) := by
          rw [dist_comm 0]; exact add_le_add h1 h2
      _ ≤ K * |s - s'| := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          have : (0 : ℝ) ≤ K := K.2
          nlinarith

/-- The periodic extension of a Lipschitz map vanishing off the open cube is Lipschitz (a path
that changes one coordinate at a time). -/
private lemma rd_perExt_lipschitz {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (h0 : ∀ x ∉ unitCube m, φ x = 0) :
    LipschitzWith (m * K) (rd_perExt φ) := by
  suffices h : ∀ S : Finset (Fin m), ∀ x y : Fin m → ℝ, (∀ i ∉ S, x i = y i) →
      dist (rd_perExt φ x) (rd_perExt φ y) ≤ S.card * K * dist x y by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := h Finset.univ x y (by simp)
    simpa [Finset.card_univ] using this
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro x y h
    have : x = y := funext fun i => h i (Finset.notMem_empty _)
    simp [this]
  | insert c S hc ih =>
    intro x y hxy
    set w := Function.update x c (y c)
    have hwy : ∀ i ∉ S, w i = y i := by
      intro i hi
      rcases eq_or_ne i c with rfl | hic
      · simp [w]
      · simp only [w, Function.update_of_ne hic]
        exact hxy i (by simp [hic, hi])
    have hdwy : dist w y ≤ dist x y := by
      rw [dist_pi_le_iff dist_nonneg]
      intro i
      rcases eq_or_ne i c with rfl | hic
      · simp [w]
      · simp only [w, Function.update_of_ne hic]; exact dist_le_pi_dist x y i
    have h1 : dist (rd_perExt φ x) (rd_perExt φ w) ≤ K * dist x y := by
      have := rd_perExt_line hφ h0 x c (x c) (y c)
      rw [Function.update_eq_self] at this
      refine this.trans ?_
      gcongr
      rw [← Real.dist_eq]; exact dist_le_pi_dist x y c
    have h2 := ih w y hwy
    rw [Finset.card_insert_of_notMem hc]
    push_cast
    have hK : (0 : ℝ) ≤ K := K.2
    calc dist (rd_perExt φ x) (rd_perExt φ y)
        ≤ dist (rd_perExt φ x) (rd_perExt φ w) + dist (rd_perExt φ w) (rd_perExt φ y) :=
          dist_triangle _ _ _
      _ ≤ K * dist x y + S.card * K * dist w y := add_le_add h1 h2
      _ ≤ K * dist x y + S.card * K * dist x y := by gcongr
      _ = (S.card + 1) * K * dist x y := by ring

private lemma rd_perExt_periodic (φ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) (z : Fin m → ℤ) :
    rd_perExt φ (x + fun i => (z i : ℝ)) = rd_perExt φ x := by
  simp only [rd_perExt, Pi.add_apply, Int.fract_add_intCast]

/-- On the open cube, the periodic extension is `φ`, so their gradients agree there. -/
private lemma rd_grad_perExt {φ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ} (hx : x ∈ unitCube m) :
    grad (rd_perExt φ) x = grad φ x := by
  have hopen : IsOpen (unitCube m) := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have heq : rd_perExt φ =ᶠ[𝓝 x] φ := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    simp only [rd_perExt]
    congr 1
    funext i
    have := hy i (Set.mem_univ _)
    rw [← Int.self_sub_floor, Int.floor_eq_zero_iff.2 ⟨this.1.le, this.2⟩, Int.cast_zero, sub_zero]
  ext i k
  simp only [grad, Matrix.of_apply]
  have hi : (fun y => rd_perExt φ y i) =ᶠ[𝓝 x] fun y => φ y i :=
    heq.mono fun y hy => by show rd_perExt φ y i = φ y i; rw [hy]
  rw [Filter.EventuallyEq.fderiv_eq hi]

/-! ### The cutoff near the boundary of the cube -/

/-- The one-dimensional profile: `0` off `(0, 1)`, `1` on `[δ, 1 − δ]`, `(1/δ)`-Lipschitz. -/
private noncomputable def rd_h (δ t : ℝ) : ℝ := max 0 (min 1 (min (t / δ) ((1 - t) / δ)))

private lemma rd_h_mem (δ t : ℝ) : 0 ≤ rd_h δ t ∧ rd_h δ t ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private lemma rd_h_lip {δ : ℝ} (hδ : 0 < δ) (s t : ℝ) : |rd_h δ s - rd_h δ t| ≤ |s - t| / δ := by
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (min 1 (min (s / δ) ((1 - s) / δ))) 0
    (min 1 (min (t / δ) ((1 - t) / δ)))
  have h2 := abs_min_sub_min_le_max (1 : ℝ) (min (s / δ) ((1 - s) / δ)) 1 (min (t / δ) ((1 - t) / δ))
  have h3 := abs_min_sub_min_le_max (s / δ) ((1 - s) / δ) (t / δ) ((1 - t) / δ)
  have e1 : |s / δ - t / δ| = |s - t| / δ := by rw [← sub_div, abs_div, abs_of_pos hδ]
  have e2 : |(1 - s) / δ - (1 - t) / δ| = |s - t| / δ := by
    rw [← sub_div, abs_div, abs_of_pos hδ, show 1 - s - (1 - t) = -(s - t) by ring, abs_neg]
  show |max 0 _ - max 0 _| ≤ _
  calc _ ≤ _ := h1
    _ = |min 1 (min (s / δ) ((1 - s) / δ)) - min 1 (min (t / δ) ((1 - t) / δ))| := by simp
    _ ≤ _ := h2
    _ = |min (s / δ) ((1 - s) / δ) - min (t / δ) ((1 - t) / δ)| := by simp
    _ ≤ _ := h3
    _ = |s - t| / δ := by rw [e1, e2, max_self]

private lemma rd_h_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ 0 ∨ 1 ≤ t) : rd_h δ t = 0 := by
  apply max_eq_left
  refine (min_le_right _ _).trans ?_
  rcases ht with ht | ht
  · exact (min_le_left _ _).trans (div_nonpos_of_nonpos_of_nonneg ht hδ.le)
  · exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)

private lemma rd_h_one {δ t : ℝ} (hδ : 0 < δ) (h1 : δ ≤ t) (h2 : t ≤ 1 - δ) : rd_h δ t = 1 := by
  have a : 1 ≤ t / δ := (one_le_div hδ).2 h1
  have b : 1 ≤ (1 - t) / δ := (one_le_div hδ).2 (by linarith)
  simp only [rd_h, min_eq_left (le_min a b), max_eq_right zero_le_one]

/-- The cutoff `η_δ (x) = ∏ h_δ (x_i)`. -/
private noncomputable def rd_eta (δ : ℝ) (x : Fin m → ℝ) : ℝ := ∏ i, rd_h δ (x i)

private lemma rd_abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hP : |∏ i ∈ s, a i| ≤ 1 := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => (ha i).1)]
      exact Finset.prod_le_one₀ (fun i _ => (ha i).1) fun i _ => (ha i).2
    have hbj : |b j| ≤ 1 := by rw [abs_of_nonneg (hb j).1]; exact (hb j).2
    calc |a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i|
        = |(a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| := by ring_nf
      _ ≤ |a j - b j| * |∏ i ∈ s, a i| + |b j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a j - b j| * 1 + 1 * ∑ i ∈ s, |a i - b i| := by
          gcongr
      _ = |a j - b j| + ∑ i ∈ s, |a i - b i| := by ring

private lemma rd_eta_mem (δ : ℝ) (x : Fin m → ℝ) : 0 ≤ rd_eta δ x ∧ rd_eta δ x ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (rd_h_mem δ _).1,
    Finset.prod_le_one₀ (fun _ _ => (rd_h_mem δ _).1) fun _ _ => (rd_h_mem δ _).2⟩

private lemma rd_eta_lip {δ : ℝ} (hδ : 0 < δ) (x y : Fin m → ℝ) :
    |rd_eta δ x - rd_eta δ y| ≤ m * dist x y / δ := by
  refine (rd_abs_prod_sub_prod_le _ _ _ (fun i => rd_h_mem δ _) fun i => rd_h_mem δ _).trans ?_
  calc ∑ i, |rd_h δ (x i) - rd_h δ (y i)| ≤ ∑ _i : Fin m, dist x y / δ := by
        gcongr with i
        refine (rd_h_lip hδ _ _).trans ?_
        gcongr
        rw [← Real.dist_eq]; exact dist_le_pi_dist x y i
    _ = m * dist x y / δ := by simp [Finset.card_univ]; ring

private lemma rd_eta_zero {δ : ℝ} (hδ : 0 < δ) {x : Fin m → ℝ} (hx : x ∉ unitCube m) :
    rd_eta δ x = 0 := by
  simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, not_forall,
    not_and_or, not_lt] at hx
  obtain ⟨i, hi⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (rd_h_zero hδ hi)

/-- The inner cube `(δ, 1 − δ)^m`. -/
private def rd_inner (δ : ℝ) : Set (Fin m → ℝ) := Set.pi univ fun _ => Ioo δ (1 - δ)

private lemma rd_inner_isOpen (δ : ℝ) : IsOpen (rd_inner (m := m) δ) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

private lemma rd_eta_one {δ : ℝ} (hδ : 0 < δ) {x : Fin m → ℝ} (hx : x ∈ rd_inner δ) :
    rd_eta δ x = 1 :=
  Finset.prod_eq_one fun i _ => rd_h_one hδ (hx i (Set.mem_univ _)).1.le (hx i (Set.mem_univ _)).2.le

/-! ### The periodic average identity -/

/-- The open unit cube and `[0, 1)^m` differ by a null set. -/
private lemma rd_setIntegral_unitCube_eq_Ico (g : (Fin m → ℝ) → ℝ) :
    ∫ x in unitCube m, g x = ∫ x in Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1), g x := by
  apply setIntegral_congr_set
  have h1 := Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ))
    (f := fun _ => (0:ℝ)) (g := fun _ => 1)
  have h2 := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ))
    (f := fun _ => (0:ℝ)) (g := fun _ => 1)
  exact h1.trans h2.symm

/-- The unit cell `z + [0, 1)^m`. -/
private def rd_cell (z : Fin m → ℝ) : Set (Fin m → ℝ) :=
  Set.pi Set.univ fun i => Set.Ico (z i) (z i + 1)

private lemma rd_setIntegral_cell {G : (Fin m → ℝ) → ℝ}
    (hper : ∀ x (z : Fin m → ℤ), G (x + fun i => (z i : ℝ)) = G x) (z : Fin m → ℤ) :
    ∫ x in rd_cell (fun i => (z i : ℝ)), G x = ∫ x in rd_cell 0, G x := by
  have h := (measurePreserving_add_right (volume : Measure (Fin m → ℝ))
    (fun i => (z i : ℝ))).setIntegral_preimage_emb (measurableEmbedding_addRight _) G
    (rd_cell (fun i => (z i : ℝ)))
  have hpre : (fun x => x + fun i => (z i : ℝ)) ⁻¹' rd_cell (fun i => (z i : ℝ)) = rd_cell 0 := by
    ext x
    simp only [rd_cell, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico,
      Pi.add_apply, Pi.zero_apply, zero_add]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [← h, hpre]
  exact setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    fun x _ => hper x z

/-- The periodic average identity (the technique of `Sverak.l1_setIntegral_comp_nsmul`, here for
bounded measurable `G`): for a `ℤ^m`-periodic `G` and an integer `N ≥ 1`,
`∫_{(0,1)^m} G (N x) dx = ∫_{(0,1)^m} G`. -/
private lemma rd_setIntegral_comp_nsmul {G : (Fin m → ℝ) → ℝ} (hGm : Measurable G) {C : ℝ}
    (hGb : ∀ x, |G x| ≤ C) (hper : ∀ x (z : Fin m → ℤ), G (x + fun i => (z i : ℝ)) = G x)
    {N : ℕ} (hN : 0 < N) :
    ∫ x in unitCube m, G ((N : ℝ) • x) = ∫ x in unitCube m, G x := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [rd_setIntegral_unitCube_eq_Ico, rd_setIntegral_unitCube_eq_Ico,
    Measure.setIntegral_comp_smul_of_pos volume G _ hN']
  have hQ : Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1) = rd_cell (0 : Fin m → ℝ) := by
    simp [rd_cell]
  have hcells : (N : ℝ) • Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1) =
      ⋃ z : Fin m → Fin N, rd_cell (fun i => (((z i : ℕ) : ℤ) : ℝ)) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hN'.ne', Set.mem_iUnion]
    simp only [rd_cell, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico, Pi.smul_apply,
      smul_eq_mul, Int.cast_natCast]
    constructor
    · intro h
      have h0 : ∀ i, 0 ≤ y i := fun i => by
        have := mul_nonneg hN'.le (h i).1
        rwa [mul_inv_cancel_left₀ hN'.ne'] at this
      have h1 : ∀ i, y i < N := fun i => by
        simpa using (inv_mul_lt_iff₀ hN').1 (h i).2
      refine ⟨fun i => ⟨⌊y i⌋₊, (Nat.floor_lt (h0 i)).2 (h1 i)⟩, fun i => ?_⟩
      exact ⟨Nat.floor_le (h0 i), Nat.lt_floor_add_one (y i)⟩
    · rintro ⟨z, hz⟩ i
      have hzN : ((z i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast (z i).isLt
      have h0 : 0 ≤ y i := le_trans (Nat.cast_nonneg _) (hz i).1
      refine ⟨mul_nonneg (inv_nonneg.2 hN'.le) h0, ?_⟩
      rw [inv_mul_lt_iff₀ hN', mul_one]
      linarith [(hz i).2]
  have hint : ∀ z : Fin m → Fin N, IntegrableOn G (rd_cell (fun i => (((z i : ℕ) : ℤ) : ℝ))) := by
    intro z
    refine IntegrableOn.of_bound ?_ hGm.aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hGb x)
    simp only [rd_cell, Real.volume_pi_Ico]
    exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
  have hdisj : Pairwise (Function.onFun Disjoint fun z : Fin m → Fin N =>
      rd_cell (fun i => (((z i : ℕ) : ℤ) : ℝ))) := by
    intro z z' hzz'
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hzz'
    refine Set.disjoint_left.2 fun y hy hy' => hi ?_
    have a := hy i (Set.mem_univ _)
    have b := hy' i (Set.mem_univ _)
    simp only [Set.mem_Ico, Int.cast_natCast] at a b
    have c1 : ((z i : ℕ) : ℝ) < (z' i : ℕ) + 1 := by linarith [a.1, b.2]
    have c2 : ((z' i : ℕ) : ℝ) < (z i : ℕ) + 1 := by linarith [a.2, b.1]
    have d1 : (z i : ℕ) < (z' i : ℕ) + 1 := by exact_mod_cast c1
    have d2 : (z' i : ℕ) < (z i : ℕ) + 1 := by exact_mod_cast c2
    exact Fin.ext (by omega)
  have hmeas : ∀ z : Fin m → Fin N, MeasurableSet (rd_cell (fun i => (((z i : ℕ) : ℤ) : ℝ))) :=
    fun z => MeasurableSet.univ_pi fun _ => measurableSet_Ico
  rw [hcells, integral_iUnion_fintype hmeas hdisj hint]
  simp_rw [rd_setIntegral_cell hper, hQ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, ← mul_assoc]
  push_cast
  rw [inv_mul_cancel₀ (by positivity), one_mul]

/-! ### Lemma 2.2 (iii): periodic test maps -/

/-- A Lipschitz `ℤ^m`-periodic map is bounded: it takes all its values on `[0, 1]^m`. -/
private lemma rd_periodic_bounded {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ),
      φ (x + fun i => (z i : ℝ)) = φ x) :
    ∃ M, 0 ≤ M ∧ ∀ x, ‖φ x‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ =>
    isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hφ.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : (x + fun i => ((-⌊x i⌋ : ℤ) : ℝ)) ∈ Set.pi Set.univ fun _ => Set.Icc (0:ℝ) 1 := by
    intro i _
    simp only [Pi.add_apply, Int.cast_neg]
    constructor
    · linarith [Int.floor_le (x i)]
    · linarith [Int.lt_floor_add_one (x i)]
  rw [← hper x (fun i => -⌊x i⌋)]
  exact (hC _ hx).trans (le_max_left _ _)

/-- The gradient of a periodic map is periodic. -/
private lemma rd_grad_periodic {φ : (Fin m → ℝ) → Fin d → ℝ}
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (x : Fin m → ℝ) (z : Fin m → ℤ) : grad φ (x + fun i => (z i : ℝ)) = grad φ x := by
  ext i k
  simp only [grad, Matrix.of_apply]
  rw [← fderiv_comp_add_right (f := fun y => φ y i)]
  congr 2
  funext y
  rw [hper]

/-- `∇ (x ↦ k⁻¹ φ (k x)) = (∇φ) (k x)`. -/
private lemma rd_grad_rescale (φ : (Fin m → ℝ) → Fin d → ℝ) {k : ℝ} (hk : k ≠ 0)
    (x : Fin m → ℝ) : grad (fun y => k⁻¹ • φ (k • y)) x = grad φ (k • x) := by
  ext i j
  simp only [grad, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  have : (fun y => k⁻¹ * φ (k • y) i) = k⁻¹ • ((fun y => φ y i) <| k • ·) := rfl
  have h2 := fderiv_comp_smul (𝕜 := ℝ) (f := fun y => φ y i) (x := x) k
  rw [this, fderiv_const_smul_field, Pi.smul_apply]
  erw [h2]
  simp only [smul_apply, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]

/-- The test map `ψ = η_δ · k⁻¹ φ (k ·)` and its Lipschitz constant. -/
private lemma rd_testMap_lipschitz {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k) :
    LipschitzWith (K + m * M / (δ * k)).toNNReal
      (fun x => rd_eta δ x • (k⁻¹ • φ (k • x))) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  have e : rd_eta δ x • (k⁻¹ • φ (k • x)) - rd_eta δ y • (k⁻¹ • φ (k • y)) =
      rd_eta δ x • (k⁻¹ • φ (k • x) - k⁻¹ • φ (k • y)) +
        (rd_eta δ x - rd_eta δ y) • (k⁻¹ • φ (k • y)) := by
    rw [smul_sub, sub_smul]; abel
  rw [e]
  have h1 : ‖k⁻¹ • φ (k • x) - k⁻¹ • φ (k • y)‖ ≤ K * ‖x - y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hk)]
    have := hφ.dist_le_mul (k • x) (k • y)
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
      at this
    calc k⁻¹ * ‖φ (k • x) - φ (k • y)‖ ≤ k⁻¹ * (K * (k * ‖x - y‖)) := by gcongr
      _ = K * ‖x - y‖ := by field_simp
  have h2 : ‖k⁻¹ • φ (k • y)‖ ≤ M / k := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hk), inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hM _) hk.le
  have h3 := rd_eta_lip hδ x y
  rw [dist_eq_norm] at h3
  have h4 := rd_eta_mem δ x
  calc ‖rd_eta δ x • (k⁻¹ • φ (k • x) - k⁻¹ • φ (k • y)) +
        (rd_eta δ x - rd_eta δ y) • (k⁻¹ • φ (k • y))‖
      ≤ |rd_eta δ x| * ‖k⁻¹ • φ (k • x) - k⁻¹ • φ (k • y)‖ +
        |rd_eta δ x - rd_eta δ y| * ‖k⁻¹ • φ (k • y)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * (K * ‖x - y‖) + (m * ‖x - y‖ / δ) * (M / k) := by
        gcongr
        · rw [abs_of_nonneg h4.1]; exact h4.2
    _ = (K + m * M / (δ * k)) * ‖x - y‖ := by field_simp

/-- The "only if" part of Lemma 2.2 (iii): quasiconvexity on the cube gives the inequality for
periodic test maps. The maps `ψ_j = η_{1/j} · j⁻² φ (j² ·)` are admissible on the cube, with a
Lipschitz constant bounded in `j`; they agree with `j⁻² φ (j² ·)` on the inner cube
`(1/j, 1 − 1/j)^m`, where `∫ f (A + ∇φ (j² x)) = ∫ f (A + ∇φ)` by periodicity, and the boundary
layer has measure `1 − (1 − 2/j)^m → 0`. -/
private lemma rd_periodic_of_cube {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ)
    (hq : QuasiconvexAtOn (unitCube m) f A) : QuasiconvexAtPeriodic f A := by
  intro φ K hφ hper _
  obtain ⟨M, hM0, hM⟩ := rd_periodic_bounded hφ hper
  obtain ⟨C, hC0, hC⟩ := rd_bound_near hbdd A (K + m * M)
  have hvolQ : volume (unitCube m) < ⊤ := by rw [rd_volume_unitCube]; exact ENNReal.one_lt_top
  set I := ∫ x in unitCube m, f (A + grad φ x)
  have hFm : Measurable fun x => f (A + grad φ x) :=
    hlsc.measurable.comp (rd_measurable_add_grad A φ)
  have key : ∀ j : ℕ, 3 ≤ j → f A ≤ I + 2 * C * (1 - (1 - 2 / (j : ℝ)) ^ m) := by
    intro j hj
    have hj' : (3 : ℝ) ≤ j := by exact_mod_cast hj
    have hjpos : (0 : ℝ) < j := by linarith
    set δ : ℝ := 1 / j with hδdef
    have hδ : 0 < δ := by positivity
    set k : ℝ := (j : ℝ) ^ 2 with hkdef
    have hk : 0 < k := by positivity
    set ψ : (Fin m → ℝ) → Fin d → ℝ := fun x => rd_eta δ x • (k⁻¹ • φ (k • x)) with hψdef
    have hψ := rd_testMap_lipschitz hφ hM hδ hk
    have hδk : m * M / (δ * k) ≤ m * M := by
      rw [show δ * k = j by rw [hδdef, hkdef]; field_simp]
      exact div_le_self (by positivity) (by linarith)
    have hψK : ((K + m * M / (δ * k)).toNNReal : ℝ) ≤ K + m * M := by
      rw [Real.coe_toNNReal _ (by positivity)]; linarith
    have h0 : ∀ x ∉ unitCube m, ψ x = 0 := fun x hx => by
      simp only [hψdef, rd_eta_zero hδ hx, zero_smul]
    have hq' := hq ψ _ hψ h0 (rd_integrableOn hlsc hbdd A hψ hvolQ)
    rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul] at hq'
    -- the two integrands agree on the inner cube
    set F₁ : (Fin m → ℝ) → ℝ := fun x => f (A + grad ψ x)
    set F₂ : (Fin m → ℝ) → ℝ := fun x => f (A + grad φ (k • x))
    have hagree : ∀ x ∈ unitCube m ∩ rd_inner δ, F₁ x = F₂ x := by
      intro x hx
      have heq : ψ =ᶠ[𝓝 x] fun y => k⁻¹ • φ (k • y) := by
        filter_upwards [(rd_inner_isOpen δ).mem_nhds hx.2] with y hy
        simp only [hψdef, rd_eta_one hδ hy, one_smul]
      have hg : grad ψ x = grad (fun y => k⁻¹ • φ (k • y)) x := by
        ext i l
        simp only [grad, Matrix.of_apply]
        have hi : (fun y => ψ y i) =ᶠ[𝓝 x] fun y => (k⁻¹ • φ (k • y)) i :=
          heq.mono fun y hy => by show ψ y i = (k⁻¹ • φ (k • y)) i; rw [hy]
        rw [Filter.EventuallyEq.fderiv_eq hi]
      simp only [F₁, F₂, hg, rd_grad_rescale φ hk.ne']
    have hF₁b : ∀ x, |F₁ x| ≤ C := fun x => hC _ fun i l =>
      (rd_grad_abs_le hψ x i l).trans hψK
    have hF₂b : ∀ x, |F₂ x| ≤ C := fun x => hC _ fun i l =>
      (rd_grad_abs_le hφ _ i l).trans (by linarith [mul_nonneg (Nat.cast_nonneg m) hM0])
    have hint₁ : IntegrableOn F₁ (unitCube m) := rd_integrableOn hlsc hbdd A hψ hvolQ
    have hint₂ : IntegrableOn F₂ (unitCube m) := by
      refine IntegrableOn.of_bound hvolQ ?_ C (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hF₂b x)
      exact (hFm.comp (measurable_const_smul k)).aestronglyMeasurable
    have hmeas : MeasurableSet (rd_inner (m := m) δ) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Ioo
    have hsplit₁ := integral_inter_add_sdiff hmeas hint₁
    have hsplit₂ := integral_inter_add_sdiff hmeas hint₂
    have hin : ∫ x in unitCube m ∩ rd_inner δ, F₁ x = ∫ x in unitCube m ∩ rd_inner δ, F₂ x :=
      setIntegral_congr_fun ((MeasurableSet.univ_pi fun _ => measurableSet_Ioo).inter hmeas)
        hagree
    -- the boundary layer
    have hinner_sub : rd_inner (m := m) δ ⊆ unitCube m := by
      intro x hx i _
      have := hx i (Set.mem_univ _)
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hδ2 : 2 * δ ≤ 1 := by rw [hδdef, mul_one_div, div_le_one hjpos]; linarith
    have hvol_layer : volume.real (unitCube m \ rd_inner (m := m) δ) =
        1 - (1 - 2 / (j : ℝ)) ^ m := by
      rw [Measure.real, measure_sdiff hinner_sub hmeas.nullMeasurableSet (by
          simp only [rd_inner, Real.volume_pi_Ioo]
          exact (ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top).ne),
        rd_volume_unitCube]
      simp only [rd_inner, Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      have hle : ENNReal.ofReal (1 - δ - δ) ^ m ≤ 1 := by
        apply pow_le_one₀ (by simp)
        rw [ENNReal.ofReal_le_one]; linarith
      rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]
      congr 2
      rw [hδdef]; ring
    have hvol_lt : volume (unitCube m \ rd_inner (m := m) δ) < ⊤ :=
      (measure_mono Set.sdiff_subset).trans_lt hvolQ
    have hb₁ := norm_setIntegral_le_of_norm_le_const hvol_lt (f := F₁) (C := C)
      fun x _ => by rw [Real.norm_eq_abs]; exact hF₁b x
    have hb₂ := norm_setIntegral_le_of_norm_le_const hvol_lt (f := F₂) (C := C)
      fun x _ => by rw [Real.norm_eq_abs]; exact hF₂b x
    rw [hvol_layer, Real.norm_eq_abs] at hb₁ hb₂
    -- the periodic average
    have havg : ∫ x in unitCube m, F₂ x = I := by
      have hGb : ∀ y, |f (A + grad φ y)| ≤ C := fun y => hC _ fun i l =>
        (rd_grad_abs_le hφ y i l).trans (by linarith [mul_nonneg (Nat.cast_nonneg m) hM0])
      have := rd_setIntegral_comp_nsmul hFm hGb ?_ (N := j ^ 2) (by positivity)
      · simpa [F₂, hkdef] using this
      · intro x z
        rw [rd_grad_periodic hper]
    have hF₂avg : ∫ x in unitCube m, F₂ x = I := havg
    have e₁ := abs_le.1 hb₁
    have e₂ := abs_le.1 hb₂
    have hfin : ∫ x in unitCube m, F₁ x ≤ I + 2 * C * (1 - (1 - 2 / (j : ℝ)) ^ m) := by
      rw [← hsplit₁, hin, ← hF₂avg, ← hsplit₂]
      linarith
    exact hq'.trans hfin
  -- the limit `j → ∞`
  have ht : Tendsto (fun j : ℕ => I + 2 * C * (1 - (1 - 2 / (j : ℝ)) ^ m)) atTop
      (𝓝 (I + 2 * C * (1 - (1 - 0) ^ m))) := by
    refine tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.sub
      ((tendsto_const_nhds.sub ?_).pow m)))
    exact tendsto_const_div_atTop_nhds_zero_nat 2
  simp only [sub_zero, one_pow, sub_self, mul_zero, add_zero] at ht
  exact ge_of_tendsto ht (eventually_atTop.2 ⟨3, key⟩)

/-- The "if" part of Lemma 2.2 (iii): a test map on the cube extends periodically (`rd_perExt`,
Lipschitz since it vanishes on the boundary of the cube), with the same gradient on the open
cube. -/
private lemma rd_cube_of_periodic {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (A : Matrix (Fin d) (Fin m) ℝ) (hp : QuasiconvexAtPeriodic f A) :
    QuasiconvexAtOn (unitCube m) f A := by
  intro φ K hφ h0 hint
  have hopen : IsOpen (unitCube m) := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have heq : ∀ x ∈ unitCube m, f (A + grad (rd_perExt φ) x) = f (A + grad φ x) :=
    fun x hx => by rw [rd_grad_perExt hx]
  have hmeas : MeasurableSet (unitCube m) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hint' : IntegrableOn (fun x => f (A + grad (rd_perExt φ) x)) (unitCube m) :=
    hint.congr_fun (fun x hx => (heq x hx).symm) hmeas
  have := hp (rd_perExt φ) _ (rd_perExt_lipschitz hφ h0) (rd_perExt_periodic φ) hint'
  rw [setIntegral_congr_fun hmeas heq] at this
  rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul]
  exact this

/-! ### Lemma 2.2 (i): laminates by periodic test maps -/

/-- The one-dimensional substitution for a `1`-periodic `F` and an integer `N ≠ 0`:
`∫_0^1 F (N t + b) dt = ∫_0^1 F`. -/
private lemma rd_integral_comp_mul_add_periodic {F : ℝ → ℝ} (hF : Function.Periodic F 1)
    (hFi : ∀ a b, IntervalIntegrable F volume a b) {N : ℤ} (hN : N ≠ 0) (b : ℝ) :
    ∫ t in (0 : ℝ)..1, F (N * t + b) = ∫ t in (0 : ℝ)..1, F t := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [intervalIntegral.integral_comp_mul_add F hN' b]
  simp only [mul_zero, zero_add, mul_one]
  have h1 := hF.intervalIntegral_add_zsmul_eq N b hFi
  rw [show (N : ℝ) + b = b + N • (1 : ℝ) by rw [zsmul_eq_mul, mul_one, add_comm], h1,
    hF.intervalIntegral_add_eq b 0, zero_add, zsmul_eq_mul, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hN', one_mul]

/-- The average along an integer direction: for a bounded measurable `1`-periodic `F` and
`n ∈ ℤ^m ∖ {0}`, `∫_{(0,1)^m} F (n · x) dx = ∫_0^1 F` (Fubini in a coordinate `c` with
`n_c ≠ 0`, and the one-dimensional substitution). -/
private lemma rd_integral_dir {F : ℝ → ℝ} (hFm : Measurable F) {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hF : Function.Periodic F 1) {n : Fin m → ℤ} (hn : n ≠ 0) :
    ∫ x in unitCube m, F (∑ j, (n j : ℝ) * x j) = ∫ t in (0 : ℝ)..1, F t := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hn
  cases m with
  | zero => exact c.elim0
  | succ m' =>
  have hFi : ∀ a b, IntervalIntegrable F volume a b := fun a b =>
    (IntegrableOn.of_bound (by rw [Set.uIcc]; exact measure_Icc_lt_top) hFm.aestronglyMeasurable C
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hFb t)).intervalIntegrable
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m' + 1) => ℝ) c
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m' + 1) => ℝ) c
  set G : (Fin (m' + 1) → ℝ) → ℝ := fun x => F (∑ j, (n j : ℝ) * x j)
  have hpre : e ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ unitCube m') = unitCube (m' + 1) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, unitCube, Set.mem_pi, Set.mem_univ, true_implies,
      e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.coe_mk, Fin.insertNthEquiv,
      Equiv.coe_fn_symm_mk]
    constructor
    · rintro ⟨h1, h2⟩ i
      rcases Fin.eq_self_or_eq_succAbove c i with rfl | ⟨j, rfl⟩
      · exact h1
      · exact h2 j
    · intro h
      exact ⟨h c, fun j => h _⟩
  have h1 := hmp.setIntegral_preimage_emb e.measurableEmbedding (G ∘ e.symm)
    (Ioo (0 : ℝ) 1 ×ˢ unitCube m')
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply, hpre] at h1
  rw [h1, show (volume : Measure (ℝ × (Fin m' → ℝ))) = volume.prod volume from rfl,
    ← setIntegral_prod_swap (Ioo (0 : ℝ) 1) (unitCube m') (fun y => G (e.symm y))]
  have hint : IntegrableOn (fun z : (Fin m' → ℝ) × ℝ => G (e.symm z.swap))
      (unitCube m' ×ˢ Ioo (0 : ℝ) 1) (volume.prod volume) := by
    refine IntegrableOn.of_bound ?_ ?_ C (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hFb _)
    · rw [Measure.prod_prod]
      simp only [unitCube, Real.volume_pi_Ioo, Real.volume_Ioo]
      exact ENNReal.mul_lt_top (ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top)
        ENNReal.ofReal_lt_top
    · refine Measurable.aestronglyMeasurable ?_
      exact hFm.comp ((Finset.measurable_sum _ fun j _ => (measurable_const.mul
        (measurable_pi_apply j))).comp (e.symm.measurable.comp measurable_swap))
  rw [setIntegral_prod _ hint]
  -- the inner integral, over the coordinate `c`
  have hinner : ∀ y : Fin m' → ℝ, ∫ t in Ioo (0 : ℝ) 1, G (e.symm (y, t).swap) =
      ∫ t in (0 : ℝ)..1, F t := by
    intro y
    have hsum : ∀ t : ℝ, ∑ j, (n j : ℝ) * (e.symm (t, y)) j =
        (n c : ℝ) * t + ∑ j, (n (c.succAbove j) : ℝ) * y j := by
      intro t
      rw [Fin.sum_univ_succAbove _ c]
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    simp only [Prod.swap_prod_mk, G, hsum]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact rd_integral_comp_mul_add_periodic hF hFi hc _
  simp only [hinner]
  rw [setIntegral_const]
  simp [unitCube, Real.volume_pi_Ioo, Measure.real]


/-- The profile of the sawtooth, vanishing off `(0, 1)`. -/
private noncomputable def rd_tooth (l : ℝ) (s : Fin 1 → ℝ) : Fin 1 → ℝ :=
  fun _ => max 0 (min ((1 - l) * s 0) (l * (1 - s 0)))

private lemma rd_tooth_lipschitz {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    LipschitzWith 1 (rd_tooth l) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro _
  simp only [rd_tooth, Real.dist_eq]
  have h0 : |s 0 - t 0| ≤ dist s t := by rw [← Real.dist_eq]; exact dist_le_pi_dist s t 0
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  simp only [sub_self, abs_zero]
  refine max_le dist_nonneg ((abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_))
  · rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith)]
    nlinarith [abs_nonneg (s 0 - t 0)]
  · rw [show l * (1 - s 0) - l * (1 - t 0) = l * (t 0 - s 0) by ring, abs_mul,
      abs_of_nonneg hl0, abs_sub_comm]
    nlinarith [abs_nonneg (s 0 - t 0)]

private lemma rd_tooth_zero {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    ∀ s ∉ unitCube 1, rd_tooth l s = 0 := by
  intro s hs
  have hs' : s 0 ≤ 0 ∨ 1 ≤ s 0 := by
    by_contra h
    push Not at h
    exact hs fun i _ => by rw [Subsingleton.elim i 0]; exact ⟨h.1, h.2⟩
  funext _
  simp only [rd_tooth, Pi.zero_apply]
  apply max_eq_left
  rcases hs' with h | h
  · exact (min_le_left _ _).trans (mul_nonpos_of_nonneg_of_nonpos (by linarith) h)
  · exact (min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos hl0 (by linarith))

/-- The sawtooth `h_λ (t) = max 0 (min ((1 − λ) fract t) (λ (1 − fract t)))`: slope `1 − λ` on
`(k, k + λ)`, slope `−λ` on `(k + λ, k + 1)`, `1`-periodic and `1`-Lipschitz. -/
private noncomputable def rd_saw (l t : ℝ) : ℝ := rd_perExt (rd_tooth l) (fun _ => t) 0

private lemma rd_saw_eq (l t : ℝ) :
    rd_saw l t = max 0 (min ((1 - l) * Int.fract t) (l * (1 - Int.fract t))) := rfl

private lemma rd_saw_lipschitz {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    LipschitzWith 1 (rd_saw l) := by
  have h := rd_perExt_lipschitz (rd_tooth_lipschitz hl0 hl1) (rd_tooth_zero hl0 hl1)
  have hc : LipschitzWith 1 (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    LipschitzWith.of_dist_le_mul fun s t => by
      rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]; intro _; exact le_rfl
  have := (LipschitzWith.eval (α := fun _ : Fin 1 => ℝ) 0).comp (h.comp hc)
  exact this.weaken (by simp)

private lemma rd_saw_add_int (l t : ℝ) (k : ℤ) : rd_saw l (t + k) = rd_saw l t := by
  simp only [rd_saw_eq, Int.fract_add_intCast]

private lemma rd_saw_hasDerivAt_up {l t : ℝ} (hl1 : l < 1) (h0 : 0 < Int.fract t)
    (h1 : Int.fract t < l) : HasDerivAt (rd_saw l) (1 - l) t := by
  set k : ℤ := ⌊t⌋
  have hkt : t = Int.fract t + k := by rw [← Int.self_sub_floor]; ring
  have hev : rd_saw l =ᶠ[𝓝 t] fun s => (1 - l) * (s - k) := by
    filter_upwards [Ioo_mem_nhds (show (k : ℝ) < t by linarith)
      (show t < k + l by linarith)] with s hs
    have hfs : Int.fract s = s - k := by
      rw [← Int.self_sub_floor, Int.floor_eq_iff.2 ⟨hs.1.le, by linarith [hs.2]⟩]
    rw [rd_saw_eq, hfs]
    have a : 0 ≤ (1 - l) * (s - k) := mul_nonneg (by linarith) (by linarith [hs.1])
    have b : (1 - l) * (s - k) ≤ l * (1 - (s - k)) := by nlinarith [hs.2]
    rw [min_eq_left b, max_eq_right a]
  have hd : HasDerivAt (fun s => (1 - l) * (s - k)) (1 - l) t := by
    simpa using HasDerivAt.const_mul (1 - l) (HasDerivAt.sub_const (k : ℝ) (hasDerivAt_id t))
  exact hd.congr_of_eventuallyEq hev

private lemma rd_saw_hasDerivAt_down {l t : ℝ} (hl0 : 0 < l) (h0 : l < Int.fract t) :
    HasDerivAt (rd_saw l) (-l) t := by
  set k : ℤ := ⌊t⌋
  have hkt : t = Int.fract t + k := by rw [← Int.self_sub_floor]; ring
  have h1 := Int.fract_lt_one t
  have hev : rd_saw l =ᶠ[𝓝 t] fun s => l * (1 - (s - k)) := by
    filter_upwards [Ioo_mem_nhds (show (k : ℝ) + l < t by linarith)
      (show t < k + 1 by linarith)] with s hs
    have hfs : Int.fract s = s - k := by
      rw [← Int.self_sub_floor, Int.floor_eq_iff.2 ⟨by linarith [hs.1], hs.2⟩]
    rw [rd_saw_eq, hfs]
    have a : 0 ≤ l * (1 - (s - k)) := mul_nonneg hl0.le (by linarith [hs.2])
    have b : l * (1 - (s - k)) ≤ (1 - l) * (s - k) := by nlinarith [hs.1]
    rw [min_eq_right b, max_eq_right a]
  have hd : HasDerivAt (fun s => l * (1 - (s - k))) (-l) t := by
    simpa using HasDerivAt.const_mul l
      (HasDerivAt.const_sub 1 (HasDerivAt.sub_const (k : ℝ) (hasDerivAt_id t)))
  exact hd.congr_of_eventuallyEq hev

/-- The linear form `x ↦ n · x`. -/
private noncomputable def rd_lin (n : Fin m → ℤ) : (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ j, (n j : ℝ) • ContinuousLinearMap.proj j

private lemma rd_lin_apply (n : Fin m → ℤ) (x : Fin m → ℝ) :
    rd_lin n x = ∑ j, (n j : ℝ) * x j := by
  simp [rd_lin]

/-- The chain rule for `h ∘ (n · )`, also where `h` is not differentiable (then neither is the
composite, since `n ≠ 0`). -/
private lemma rd_fderiv_comp_lin {h : ℝ → ℝ} {n : Fin m → ℤ} (hn : n ≠ 0) (x : Fin m → ℝ) :
    fderiv ℝ (fun y => h (rd_lin n y)) x = deriv h (rd_lin n x) • rd_lin n := by
  by_cases hd : DifferentiableAt ℝ h (rd_lin n x)
  · exact (HasDerivAt.comp_hasFDerivAt x hd.hasDerivAt (rd_lin n).hasFDerivAt).fderiv
  · obtain ⟨c, hc⟩ := Function.ne_iff.1 hn
    have hc' : (n c : ℝ) ≠ 0 := by exact_mod_cast hc
    set γ : ℝ → Fin m → ℝ := fun t => x + ((t - rd_lin n x) / n c) • Pi.single c 1
    have hγ : ∀ t, rd_lin n (γ t) = t := by
      intro t
      simp only [γ, map_add, map_smul, smul_eq_mul]
      rw [rd_lin_apply n (Pi.single c 1)]
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      field_simp
      ring
    have hnd : ¬ DifferentiableAt ℝ (fun y => h (rd_lin n y)) x := by
      intro hdiff
      apply hd
      have hγx : γ (rd_lin n x) = x := by simp [γ]
      have heq : h = (fun y => h (rd_lin n y)) ∘ γ := funext fun t => by simp [hγ]
      rw [heq]
      refine DifferentiableAt.comp _ (by rw [hγx]; exact hdiff) ?_
      exact (((differentiableAt_id.sub_const _).div_const _).smul_const _).const_add x
    rw [fderiv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hd, zero_smul]

/-- The laminate test map `u (x) = h_λ (n · x) a`, with gradient `h_λ' (n · x) a ⊗ n`. -/
private lemma rd_grad_laminate {l : ℝ} (a : Fin d → ℝ) {n : Fin m → ℤ} (hn : n ≠ 0)
    (x : Fin m → ℝ) :
    grad (fun y => rd_saw l (rd_lin n y) • a) x =
      deriv (rd_saw l) (rd_lin n x) • Matrix.vecMulVec a (fun k => (n k : ℝ)) := by
  ext i k
  simp only [grad, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  have : (fun y => rd_saw l (rd_lin n y) * a i) = a i • fun y => rd_saw l (rd_lin n y) := by
    funext y; simp [mul_comm]
  rw [this, fderiv_const_smul_field, Pi.smul_apply, rd_fderiv_comp_lin hn]
  have hk : rd_lin n (Pi.single k 1) = n k := by
    rw [rd_lin_apply]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  simp only [smul_apply, smul_eq_mul, hk, Matrix.smul_apply, Matrix.vecMulVec_apply]
  ring

/-- The two-point inequality along an integer rank-one direction, from the periodic laminate
`u (x) = h_λ (n · x) a`: `f (A) ≤ λ f (A + (1 − λ) a ⊗ n) + (1 − λ) f (A − λ a ⊗ n)`
(Rindler, proof of Proposition 5.1; Dacorogna 2008, Theorem 5.3, with periodic laminates). -/
private lemma rd_two_point {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hlsc : LowerSemicontinuous f)
    (hbdd : IsLocallyBounded f) {A : Matrix (Fin d) (Fin m) ℝ} (hper : QuasiconvexAtPeriodic f A)
    (a : Fin d → ℝ) {n : Fin m → ℤ} (hn : n ≠ 0) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    f A ≤ l * f (A + (1 - l) • Matrix.vecMulVec a (fun k => (n k : ℝ))) +
      (1 - l) * f (A - l • Matrix.vecMulVec a (fun k => (n k : ℝ))) := by
  set R := Matrix.vecMulVec a (fun k => (n k : ℝ))
  set u : (Fin m → ℝ) → Fin d → ℝ := fun y => rd_saw l (rd_lin n y) • a
  set F : ℝ → ℝ := fun t => f (A + deriv (rd_saw l) t • R)
  have hsaw := rd_saw_lipschitz hl0.le hl1.le
  -- `u` is a periodic Lipschitz test map
  have hu : LipschitzWith (‖a‖₊ * (1 * ‖rd_lin n‖₊)) u := by
    have h3 : LipschitzWith ‖a‖₊ (fun t : ℝ => t • a) := LipschitzWith.of_dist_le_mul fun s t => by
      rw [dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, mul_comm]; rfl
    exact h3.comp (hsaw.comp (rd_lin n).lipschitzWith)
  have huper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), u (x + fun i => (z i : ℝ)) = u x := by
    intro x z
    simp only [u, map_add]
    rw [rd_lin_apply n (fun i => (z i : ℝ)),
      show ∑ j, (n j : ℝ) * (z j : ℝ) = ((∑ j, n j * z j : ℤ) : ℝ) by push_cast; rfl,
      rd_saw_add_int]
  -- the integrand is `F (n · x)`
  have hgrad : ∀ x, f (A + grad u x) = F (∑ j, (n j : ℝ) * x j) := fun x => by
    show f (A + grad (fun y => rd_saw l (rd_lin n y) • a) x) = _
    rw [rd_grad_laminate a hn x, rd_lin_apply]
  have hderiv : ∀ t, |deriv (rd_saw l) t| ≤ 1 := fun t => by
    have := norm_deriv_le_of_lipschitz (x₀ := t) hsaw
    simpa using this
  obtain ⟨C, -, hC⟩ := rd_bound_near hbdd A (∑ i, ∑ k, |R i k|)
  have hFb : ∀ t, |F t| ≤ C := fun t => hC _ fun i k => by
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul]
    calc |deriv (rd_saw l) t| * |R i k| ≤ 1 * |R i k| := by gcongr; exact hderiv t
      _ ≤ ∑ i, ∑ k, |R i k| := by
        rw [one_mul]
        exact (Finset.single_le_sum (f := fun k' => |R i k'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ k)).trans (Finset.single_le_sum (f := fun i' => ∑ k', |R i' k'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hFm : Measurable F := by
    refine hlsc.measurable.comp (Measurable.of_eval_matrix _ fun i k => ?_)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact measurable_const.add ((measurable_deriv (rd_saw l)).mul measurable_const)
  have hFper : Function.Periodic F 1 := fun t => by
    have : deriv (rd_saw l) (t + 1) = deriv (rd_saw l) t := by
      rw [← deriv_comp_add_const]
      congr 1
      funext s
      have := rd_saw_add_int l s 1
      simpa using this
    simp only [F, this]
  have hFi : ∀ a b, IntervalIntegrable F volume a b := fun a b =>
    (IntegrableOn.of_bound (by rw [Set.uIcc]; exact measure_Icc_lt_top) hFm.aestronglyMeasurable C
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hFb t)).intervalIntegrable
  have hvolQ : volume (unitCube m) < ⊤ := by rw [rd_volume_unitCube]; exact ENNReal.one_lt_top
  have key := hper u _ hu huper (rd_integrableOn hlsc hbdd A hu hvolQ)
  simp only [hgrad] at key
  rw [rd_integral_dir hFm hFb hFper hn,
    ← intervalIntegral.integral_add_adjacent_intervals (hFi 0 l) (hFi l 1)] at key
  have hne : ∀ b : ℝ, ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({b} : Set ℝ) := fun b =>
    measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton)
  have hI1 : ∫ t in (0 : ℝ)..l, F t = l * f (A + (1 - l) • R) := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => f (A + (1 - l) • R)) ?_,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    filter_upwards [hne l] with t ht htmem
    rw [Set.uIoc_of_le hl0.le] at htmem
    have htl : t < l := lt_of_le_of_ne htmem.2 (by simpa using ht)
    have hft : Int.fract t = t := Int.fract_eq_self.2 ⟨htmem.1.le, by linarith⟩
    simp only [F]
    rw [(rd_saw_hasDerivAt_up hl1 (by rw [hft]; exact htmem.1) (by rw [hft]; exact htl)).deriv]
  have hI2 : ∫ t in l..1, F t = (1 - l) * f (A - l • R) := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => f (A - l • R)) ?_,
      intervalIntegral.integral_const, smul_eq_mul]
    filter_upwards [hne 1] with t ht htmem
    rw [Set.uIoc_of_le hl1.le] at htmem
    have ht1 : t < 1 := lt_of_le_of_ne htmem.2 (by simpa using ht)
    have hft : Int.fract t = t := Int.fract_eq_self.2 ⟨by linarith [htmem.1], ht1⟩
    simp only [F]
    rw [(rd_saw_hasDerivAt_down hl0 (by rw [hft]; exact htmem.1)).deriv, neg_smul,
      ← sub_eq_add_neg]
  rw [hI1, hI2] at key
  exact key


/-- A function satisfying the two-point convexity inequality is convex. -/
private lemma rd_convex_of_two_point {g : ℝ → ℝ}
    (h : ∀ x y l : ℝ, 0 < l → l < 1 → g (l * x + (1 - l) * y) ≤ l * g x + (1 - l) * g y) :
    ConvexOn ℝ univ g := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  simp only [smul_eq_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  rcases eq_or_lt_of_le hb with hb0 | hb'
  · have : a = 1 := by linarith
    subst this; simp
  · exact h x y a ha' (by linarith)

/-- Convexity along the line `t ↦ A₀ + t B` from the two-point inequality in the directions
`c B`. -/
private lemma rd_convex_line {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (A₀ B : Matrix (Fin d) (Fin m) ℝ)
    (h2 : ∀ (P : Matrix (Fin d) (Fin m) ℝ) (c l : ℝ), 0 < l → l < 1 →
      f P ≤ l * f (P + (1 - l) • (c • B)) + (1 - l) * f (P - l • (c • B))) :
    ConvexOn ℝ univ (fun t : ℝ => f (A₀ + t • B)) := by
  apply rd_convex_of_two_point
  intro x y l hl0 hl1
  have := h2 (A₀ + (l * x + (1 - l) * y) • B) (x - y) l hl0 hl1
  rwa [show A₀ + (l * x + (1 - l) * y) • B + (1 - l) • ((x - y) • B) = A₀ + x • B by module,
    show A₀ + (l * x + (1 - l) * y) • B - l • ((x - y) • B) = A₀ + y • B by module] at this

/-- A matrix of rank one is `a ⊗ q`. -/
private lemma rd_rank_one_eq {B : Matrix (Fin d) (Fin m) ℝ} (hB : B.rank = 1) :
    ∃ (a : Fin d → ℝ) (q : Fin m → ℝ), B = Matrix.vecMulVec a q := by
  rw [Matrix.rank_eq_finrank_span_cols] at hB
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 hB
  choose c hc using fun k : Fin m => hv ⟨B.col k, Submodule.subset_span ⟨k, rfl⟩⟩
  refine ⟨(v : Fin d → ℝ), c, ?_⟩
  ext i k
  have h1 : ((c k • v : Submodule.span ℝ (Set.range B.col)) : Fin d → ℝ) i = B i k :=
    congrArg (fun w : Submodule.span ℝ (Set.range B.col) => (w : Fin d → ℝ) i) (hc k)
  rw [Matrix.vecMulVec_apply, ← h1, mul_comm]
  rfl

/-- The approximants `⌊(N + 1) x⌋ / (N + 1) → x`. -/
private lemma rd_tendsto_floor_div (x : ℝ) :
    Tendsto (fun N : ℕ => (⌊((N : ℝ) + 1) * x⌋ : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 x) := by
  have hlow : Tendsto (fun N : ℕ => x - 1 / ((N : ℝ) + 1)) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun N => ?_)
    (fun N => ?_)
  · have hN : (0 : ℝ) < N + 1 := by positivity
    rw [le_div_iff₀ hN, sub_mul, one_div_mul_cancel hN.ne']
    linarith [Int.lt_floor_add_one (((N : ℝ) + 1) * x), mul_comm x ((N : ℝ) + 1)]
  · have hN : (0 : ℝ) < N + 1 := by positivity
    rw [div_le_iff₀ hN]
    linarith [Int.floor_le (((N : ℝ) + 1) * x), mul_comm x ((N : ℝ) + 1)]

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, first assertion, citing Rindler, Proposition 5.1, and
Dacorogna, Proposition 5.11: a quasiconvex integrand is rank-one convex. 

Proof: the standard laminate argument (Rindler, proof of Proposition 5.1; Dacorogna 2008,
Theorem 5.3), with periodic test maps: by the periodic form of Lemma 2.2 (`rd_periodic_of_cube`),
`f` is quasiconvex at every `A` with periodic test maps. For an integer direction `n ≠ 0`, a vector
`a` and `λ ∈ (0, 1)`, the periodic laminate `u (x) = h_λ (n · x) a` (`h_λ` the sawtooth with slopes
`1 − λ` and `−λ`) has `∇u = h_λ' (n · x) a ⊗ n`, and `∫_{(0,1)^m} F (n · x) dx = ∫_0^1 F` for
`1`-periodic `F` (Fubini in a coordinate with `n_c ≠ 0`, `rd_integral_dir`), which gives
`f (A) ≤ λ f (A + (1 − λ) a ⊗ n) + (1 − λ) f (A − λ a ⊗ n)` (`rd_two_point`). In the coordinate
directions this makes `f` convex in each entry, hence continuous (the argument of Lemma 5.6); the
inequality extends to rational directions by scaling and to real ones by continuity, and a rank-one
matrix is `a ⊗ q` (`rd_rank_one_eq`). Departure from the sources: the textbook argument cuts off a laminate in an arbitrary direction
`n ∈ ℝ^m` near the boundary of the cube; here the laminates are periodic, which needs integer
directions, and the other directions follow by scaling and continuity. Reason (2): the volume
fractions of the layers of a laminate in an irrational direction on the cube need an
equidistribution estimate that is not available here, while for integer directions they are an
exact computation (`rd_integral_dir`).-/
theorem rankOneConvex_of_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (hf : Quasiconvex f) :
    RankOneConvex f := by
  have hper : ∀ A, QuasiconvexAtPeriodic f A := fun A => rd_periodic_of_cube hlsc hbdd A (hf A)
  -- the two-point inequality along integer directions (periodic laminates)
  have h2int : ∀ (P : Matrix (Fin d) (Fin m) ℝ) (a : Fin d → ℝ) (n : Fin m → ℤ) (l : ℝ),
      0 < l → l < 1 → f P ≤ l * f (P + (1 - l) • Matrix.vecMulVec a (fun k => (n k : ℝ))) +
        (1 - l) * f (P - l • Matrix.vecMulVec a (fun k => (n k : ℝ))) := by
    intro P a n l hl0 hl1
    by_cases hn : n = 0
    · subst hn
      have : Matrix.vecMulVec a (fun k => ((0 : Fin m → ℤ) k : ℝ)) = 0 := by
        ext i k; simp [Matrix.vecMulVec_apply]
      rw [this, smul_zero, smul_zero, add_zero, sub_zero]
      linarith
    · exact rd_two_point hlsc hbdd (hper P) a hn hl0 hl1
  -- convexity in each entry, hence continuity (the argument of Lemma 5.6)
  have hsep : ∀ (y : Fin d → Fin m → ℝ) (i : Fin d) (j : Fin m),
      ConvexOn ℝ univ (fun t : ℝ => f (Matrix.of (y + t • rE i j))) := by
    intro y i j
    simp only [of_add_smul_rE]
    refine rd_convex_line _ _ fun P c l hl0 hl1 => ?_
    have e : c • Matrix.single i j (1 : ℝ) = Matrix.vecMulVec (c • Pi.single i 1)
        (fun k => ((Pi.single j (1 : ℤ) : Fin m → ℤ) k : ℝ)) := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.single_apply, Matrix.vecMulVec_apply, Pi.smul_apply,
        Pi.single_apply, smul_eq_mul]
      split_ifs <;> simp_all
    rw [e]
    exact h2int P _ _ l hl0 hl1
  have hcont : Continuous f := (rd_locallyLipschitz_of_sep hsep).continuous
  -- the two-point inequality along every rank-one direction `a ⊗ q`, by rational approximation
  have h2real : ∀ (P : Matrix (Fin d) (Fin m) ℝ) (a : Fin d → ℝ) (q : Fin m → ℝ) (l : ℝ),
      0 < l → l < 1 → f P ≤ l * f (P + (1 - l) • Matrix.vecMulVec a q) +
        (1 - l) * f (P - l • Matrix.vecMulVec a q) := by
    intro P a q l hl0 hl1
    set qs : ℕ → Fin m → ℝ := fun N k => (⌊((N : ℝ) + 1) * q k⌋ : ℝ) / ((N : ℝ) + 1)
    have hq : Tendsto qs atTop (𝓝 q) := tendsto_pi_nhds.2 fun k => rd_tendsto_floor_div (q k)
    have hineq : ∀ N, f P ≤ l * f (P + (1 - l) • Matrix.vecMulVec a (qs N)) +
        (1 - l) * f (P - l • Matrix.vecMulVec a (qs N)) := by
      intro N
      have e : Matrix.vecMulVec a (qs N) = Matrix.vecMulVec (((N : ℝ) + 1)⁻¹ • a)
          (fun k => ((⌊((N : ℝ) + 1) * q k⌋ : ℤ) : ℝ)) := by
        ext i k
        simp only [qs, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact h2int P _ _ l hl0 hl1
    have hc : Continuous fun q' : Fin m → ℝ => l * f (P + (1 - l) • Matrix.vecMulVec a q') +
        (1 - l) * f (P - l • Matrix.vecMulVec a q') := by
      have hv : Continuous fun q' : Fin m → ℝ => Matrix.vecMulVec a q' :=
        continuous_const.matrix_vecMulVec continuous_id
      exact (continuous_const.mul (hcont.comp (continuous_const.add (hv.const_smul (1 - l))))).add
        (continuous_const.mul (hcont.comp (continuous_const.sub (hv.const_smul l))))
    exact ge_of_tendsto ((hc.tendsto q).comp hq) (Eventually.of_forall hineq)
  -- a rank-one matrix is `a ⊗ q`
  intro A B hB
  obtain ⟨a, q, rfl⟩ := rd_rank_one_eq hB
  refine rd_convex_line _ _ fun P c l hl0 hl1 => ?_
  rw [show c • Matrix.vecMulVec a q = Matrix.vecMulVec (c • a) q by
    ext i k; simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring]
  exact h2real P _ q l hl0 hl1


/-! ### Lemma 2.2 (ii), from the cube to a bounded open set -/

/-- A Lipschitz map has vanishing derivative at almost every point of its zero set: at a Lebesgue
density point `x` of the zero set where `φ` is differentiable, a derivative `L` with `L v ≠ 0`
would make `φ` nonzero on the ball `B (x + (r/2) v, ρ r/2)`, a fixed proportion of `B (x, r)`. -/
private lemma rd_ae_fderiv_eq_zero {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) : ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), φ x = 0 → fderiv ℝ φ x = 0 := by
  set E := {x | φ x = 0}
  have hE : MeasurableSet E := (isClosed_eq hφ.continuous continuous_const).measurableSet
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hE,
    hφ.ae_differentiableAt] with x hden hdiff hx
  rw [Set.indicator_of_mem (show x ∈ E from hx), Pi.one_apply] at hden
  by_contra hL
  set L := fderiv ℝ φ x
  -- a direction `v`, `‖v‖ ≤ 1`, with `L v ≠ 0`
  obtain ⟨v, hv1, hc⟩ : ∃ v : Fin m → ℝ, ‖v‖ ≤ 1 ∧ 0 < ‖L v‖ := by
    by_contra h
    push Not at h
    apply hL
    ext w : 1
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · have h1 := h (‖w‖⁻¹ • w) (by rw [norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)])
      rw [map_smul, norm_smul, norm_inv, norm_norm] at h1
      have h2 : ‖L w‖ ≤ 0 := by
        have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
        have := mul_le_mul_of_nonneg_left h1 hw'.le
        rwa [← mul_assoc, mul_inv_cancel₀ hw'.ne', one_mul, mul_zero] at this
      simpa using norm_le_zero_iff.1 h2
  set c := ‖L v‖
  set ρ : ℝ := min 1 (c / (2 * (‖L‖ + 1)))
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρL : ‖L‖ * ρ ≤ c / 2 := by
    calc ‖L‖ * ρ ≤ (‖L‖ + 1) * (c / (2 * (‖L‖ + 1))) := by
          gcongr
          · linarith [norm_nonneg L]
          · exact min_le_right _ _
      _ = c / 2 := by field_simp
  -- differentiability with `ε = c/8`
  have hlo := hdiff.hasFDerivAt.isLittleO.def (show (0 : ℝ) < c / 8 by positivity)
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.1 hlo
  -- for `0 < r < δ`, the zero set misses `B (x + (r/2) v, ρ r/2)`
  have hmiss : ∀ r, 0 < r → r < δ →
      E ∩ Metric.closedBall x r ⊆ Metric.closedBall x r \ Metric.closedBall (x + (r / 2) • v) (ρ * (r / 2)) := by
    intro r hr0 hrδ y ⟨hyE, hyr⟩
    refine ⟨hyr, fun hy => ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hy hyr
    set z := y - (x + (r / 2) • v)
    have hyx : y - x = (r / 2) • v + z := by simp only [z]; abel
    have hnorm : ‖y - x‖ ≤ r := hyr
    have h1 := hδ (show dist y x < δ by rw [dist_eq_norm]; linarith)
    have hyE' : φ y = 0 := hyE
    rw [hyE', hx, sub_zero, zero_sub, norm_neg] at h1
    have h2 : ‖L (y - x)‖ ≥ (r / 2) * c - ‖L‖ * (ρ * (r / 2)) := by
      rw [hyx, map_add, map_smul]
      calc ‖(r / 2) • L v + L z‖ ≥ ‖(r / 2) • L v‖ - ‖L z‖ := norm_sub_le_norm_add _ _
        _ ≥ (r / 2) * c - ‖L‖ * (ρ * (r / 2)) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
          have := L.le_opNorm z
          have hz : ‖z‖ ≤ ρ * (r / 2) := hy
          nlinarith [norm_nonneg L]
    have h3 : ‖L‖ * (ρ * (r / 2)) ≤ (c / 2) * (r / 2) := by nlinarith
    have h4 : c / 8 * ‖y - x‖ ≤ c / 8 * r := by gcongr
    nlinarith
  -- the density ratio stays below `1 − (ρ/2)^m`
  set V := volume (Metric.closedBall (0 : Fin m → ℝ) 1)
  have hV0 : V ≠ 0 := (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hVt : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hfin : Module.finrank ℝ (Fin m → ℝ) = m := by simp
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      volume (E ∩ Metric.closedBall x r) / volume (Metric.closedBall x r) ≤
        ENNReal.ofReal (1 - (ρ / 2) ^ m) := by
    filter_upwards [Ioo_mem_nhdsGT hδ0] with r hr
    have hsub : Metric.closedBall (x + (r / 2) • v) (ρ * (r / 2)) ⊆ Metric.closedBall x r := by
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
      calc ‖y - x‖ = ‖(y - (x + (r / 2) • v)) + (r / 2) • v‖ := by congr 1; abel
        _ ≤ ‖y - (x + (r / 2) • v)‖ + ‖(r / 2) • v‖ := norm_add_le _ _
        _ ≤ ρ * (r / 2) + r / 2 := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hr.1])]
          nlinarith [hr.1]
        _ ≤ r := by nlinarith [hr.1]
    have hB : volume (Metric.closedBall x r) = ENNReal.ofReal (r ^ m) * V := by
      rw [Measure.addHaar_closedBall' volume x hr.1.le, hfin]
    have hb : volume (Metric.closedBall (x + (r / 2) • v) (ρ * (r / 2))) =
        ENNReal.ofReal ((ρ * (r / 2)) ^ m) * V := by
      rw [Measure.addHaar_closedBall' volume _ (by nlinarith [hr.1]), hfin]
    have hle := measure_mono (μ := volume) (hmiss r hr.1 hr.2)
    rw [measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet
      (measure_closedBall_lt_top.ne), hB, hb] at hle
    have hr0 : 0 < r := hr.1
    have hpos : 0 < ENNReal.ofReal (r ^ m) * V :=
      ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' hV0
    rw [hB, ENNReal.div_le_iff hpos.ne' (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt)]
    refine hle.trans (le_of_eq ?_)
    rw [← ENNReal.sub_mul (fun _ _ => hVt), ← mul_assoc, ← ENNReal.ofReal_mul (by
      have : (ρ / 2) ^ m ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
      linarith), ← ENNReal.ofReal_sub _ (by positivity)]
    congr 2
    simp only [mul_pow, div_pow]
    ring
  have hlim := le_of_tendsto hden hbound
  rw [ENNReal.one_le_ofReal] at hlim
  have : 0 < (ρ / 2) ^ m := by positivity
  linarith


/-- The gradient vanishes almost everywhere off the open set outside which `φ` vanishes. -/
private lemma rd_ae_grad_eq_zero {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), φ x = 0 → grad φ x = 0 := by
  filter_upwards [rd_ae_fderiv_eq_zero hφ, hφ.ae_differentiableAt] with x hx hdiff h0
  ext i k
  have hi := (hasFDerivAt_pi'.1 hdiff.hasFDerivAt i).fderiv
  simp only [grad, Matrix.of_apply, Matrix.zero_apply]
  rw [hi, hx h0]
  simp

/-- Lemma 2.2 (ii), the direction used here: quasiconvexity at `A` on the unit cube gives it on
every bounded measurable `Ω` (in particular on every bounded open set). The proof is the standard
one (Dacorogna 2008, Proposition 5.11; Rindler, Proposition 5.3): put `Ω` in a cube
`Q_R = x₀ + R (0, 1)^m`; a test map `φ` on `Ω`, rescaled to the unit cube, gives
`R^m f (A) ≤ ∫_{Q_R} f (A + ∇φ)`; on `Q_R ∖ Ω` the map vanishes, so its gradient vanishes almost
everywhere (`rd_ae_grad_eq_zero`), and the inequality becomes `|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)`. -/
theorem rd_quasiconvexAtOn_of_unitCube {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) {A : Matrix (Fin d) (Fin m) ℝ}
    {Ω : Set (Fin m → ℝ)} (hb : Bornology.IsBounded Ω) (hΩm : MeasurableSet Ω)
    (h : QuasiconvexAtOn (unitCube m) f A) : QuasiconvexAtOn Ω f A := by
  intro φ K hφ h0 _
  obtain ⟨ρ, hρ⟩ := hb.subset_closedBall 0
  set a : ℝ := |ρ| + 1 with ha_def
  have ha : 1 ≤ a := by have := abs_nonneg ρ; linarith
  set R : ℝ := 2 * a with hR_def
  have hR : 0 < R := by linarith
  set x₀ : Fin m → ℝ := fun _ => -a
  set T : (Fin m → ℝ) → Fin m → ℝ := fun y => x₀ + R • y
  set ψ : (Fin m → ℝ) → Fin d → ℝ := fun y => R⁻¹ • φ (T y)
  have hT : LipschitzWith ‖R‖₊ T := LipschitzWith.of_dist_le_mul fun y z => by
    simp only [T, dist_add_left]; exact (lipschitzWith_smul R).dist_le_mul y z
  have hψ : LipschitzWith (‖R⁻¹‖₊ * (K * ‖R‖₊)) ψ := (lipschitzWith_smul R⁻¹).comp (hφ.comp hT)
  have hent : ∀ x ∈ Ω, ∀ i, |x i| ≤ ρ := fun x hx i => by
    have := hρ hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm x i).trans this
  have hρa : ρ ≤ a - 1 := by rw [ha_def]; linarith [le_abs_self ρ]
  have hTΩ : ∀ y, T y ∈ Ω → y ∈ unitCube m := by
    intro y hy i _
    have := abs_le.1 (hent _ hy i)
    simp only [T, x₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    constructor
    · by_contra hneg; push Not at hneg; nlinarith
    · by_contra hneg; push Not at hneg; nlinarith
  have hψ0 : ∀ y ∉ unitCube m, ψ y = 0 := fun y hy => by
    simp only [ψ, h0 _ fun h => hy (hTΩ y h), smul_zero]
  have hgrad : ∀ y, grad ψ y = grad φ (T y) := by
    intro y
    ext i k
    simp only [grad, Matrix.of_apply, ψ, T, Pi.smul_apply, smul_eq_mul]
    have e1 : (fun z => R⁻¹ * φ (x₀ + R • z) i) =
        R⁻¹ • ((fun w => (fun u => φ u i) (x₀ + w)) <| R • ·) := rfl
    have h2 := fderiv_comp_smul (𝕜 := ℝ) (f := fun w => (fun u => φ u i) (x₀ + w)) (x := y) R
    rw [e1, fderiv_const_smul_field, Pi.smul_apply]
    erw [h2]
    have h3 := fderiv_comp_add_left (𝕜 := ℝ) (f := fun u => φ u i) (x := R • y) x₀
    erw [h3]
    simp only [smul_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  have hvolQ : volume (unitCube m) < ⊤ := by rw [rd_volume_unitCube]; exact ENNReal.one_lt_top
  have hq := h ψ _ hψ hψ0 (rd_integrableOn hlsc hbdd A hψ hvolQ)
  rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul] at hq
  simp only [hgrad] at hq
  -- change of variables `x = x₀ + R y`
  set G : (Fin m → ℝ) → ℝ := fun x => f (A + grad φ x)
  set QR : Set (Fin m → ℝ) := Set.pi univ fun _ => Ioo (-a) a
  have hfin : Module.finrank ℝ (Fin m → ℝ) = m := by simp
  have hcv : ∫ y in unitCube m, G (T y) = (R ^ m)⁻¹ * ∫ x in QR, G x := by
    have h1 := Measure.setIntegral_comp_smul_of_pos volume (fun z => G (x₀ + z)) (unitCube m) hR
    have h2 := (measurePreserving_add_left volume x₀).setIntegral_preimage_emb
      (measurableEmbedding_addLeft x₀) G QR
    have hset : R • unitCube m = (fun z => x₀ + z) ⁻¹' QR := by
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
      simp only [unitCube, QR, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo,
        Set.mem_preimage, Pi.smul_apply, smul_eq_mul, Pi.add_apply, x₀]
      refine forall_congr' fun i => ?_
      rw [← div_eq_inv_mul, div_pos_iff_of_pos_right hR, div_lt_one hR, hR_def]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [T] at h1 ⊢
    rw [h1, hset, h2, hfin, smul_eq_mul]
  have hQRvol : volume QR = ENNReal.ofReal (R ^ m) := by
    simp only [QR, Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by linarith), hR_def]
    congr 2
    ring
  have hQRfin : volume QR < ⊤ := by rw [hQRvol]; exact ENNReal.ofReal_lt_top
  have hΩQR : Ω ⊆ QR := fun x hx i _ => by
    have := abs_le.1 (hent x hx i)
    exact ⟨by linarith, by linarith⟩
  have hΩfin : volume Ω < ⊤ := (measure_mono hΩQR).trans_lt hQRfin
  have hint : IntegrableOn G QR := rd_integrableOn hlsc hbdd A hφ hQRfin
  have hsplit := integral_inter_add_sdiff hΩm hint
  rw [Set.inter_eq_right.2 hΩQR] at hsplit
  -- on `Q_R ∖ Ω` the gradient vanishes almost everywhere
  have hout : ∫ x in QR \ Ω, G x = volume.real (QR \ Ω) * f A := by
    rw [setIntegral_congr_ae (g := fun _ => f A) ((MeasurableSet.univ_pi fun _ =>
      measurableSet_Ioo).diff hΩm) ?_, setIntegral_const, smul_eq_mul]
    filter_upwards [rd_ae_grad_eq_zero hφ] with x hx hxs
    simp only [G, hx (h0 x hxs.2), add_zero]
  have hvol : volume.real (QR \ Ω) = R ^ m - volume.real Ω := by
    rw [Measure.real, measure_sdiff hΩQR hΩm.nullMeasurableSet hΩfin.ne, hQRvol,
      ENNReal.toReal_sub_of_le ((measure_mono hΩQR).trans_eq hQRvol) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity), Measure.real]
  rw [hcv, ← hsplit, hout, hvol] at hq
  have hRm : 0 < R ^ m := by positivity
  rw [← mul_le_mul_iff_of_pos_left hRm, ← mul_assoc, mul_inv_cancel₀ hRm.ne', one_mul] at hq
  rw [← Measure.real]
  nlinarith


/-- Quasiconvexity on `Ω₁` gives it on every measurable `Ω₂ ⊆ Ω₁`: a test map on `Ω₂` is one on
`Ω₁`, and its gradient vanishes almost everywhere on `Ω₁ ∖ Ω₂`. -/
private lemma rd_quasiconvexAtOn_mono {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) {A : Matrix (Fin d) (Fin m) ℝ}
    {Ω₁ Ω₂ : Set (Fin m → ℝ)} (hsub : Ω₂ ⊆ Ω₁) (h₁ : MeasurableSet Ω₁) (h₂ : MeasurableSet Ω₂)
    (hfin : volume Ω₁ < ⊤) (h : QuasiconvexAtOn Ω₁ f A) : QuasiconvexAtOn Ω₂ f A := by
  intro φ K hφ h0 _
  have hq := h φ K hφ (fun x hx => h0 x fun h => hx (hsub h)) (rd_integrableOn hlsc hbdd A hφ hfin)
  have hint : IntegrableOn (fun x => f (A + grad φ x)) Ω₁ := rd_integrableOn hlsc hbdd A hφ hfin
  have hsplit := integral_inter_add_sdiff h₂ hint
  rw [Set.inter_eq_right.2 hsub] at hsplit
  have hout : ∫ x in Ω₁ \ Ω₂, f (A + grad φ x) = volume.real (Ω₁ \ Ω₂) * f A := by
    rw [setIntegral_congr_ae (g := fun _ => f A) (h₁.diff h₂) ?_, setIntegral_const, smul_eq_mul]
    filter_upwards [rd_ae_grad_eq_zero hφ] with x hx hxs
    simp only [hx (h0 x hxs.2), add_zero]
  have hvol : volume.real (Ω₁ \ Ω₂) = volume.real Ω₁ - volume.real Ω₂ := by
    rw [Measure.real, measure_sdiff hsub h₂.nullMeasurableSet
      ((measure_mono hsub).trans_lt hfin).ne,
      ENNReal.toReal_sub_of_le (measure_mono hsub) hfin.ne, Measure.real, Measure.real]
  rw [← hsplit, hout, hvol] at hq
  change volume.real Ω₁ * f A ≤ _ at hq
  rw [← Measure.real]
  linarith

/-- Lemma 2.2 (ii), the other direction: quasiconvexity on a nonempty open `Ω` gives it on the
unit cube. `Ω` contains a cube `Q' = x₀ + R (0, 1)^m`, on which `f` is quasiconvex at `A`
(`rd_quasiconvexAtOn_mono`); a test map on the unit cube, rescaled to `Q'`, gives the inequality. -/
private lemma rd_unitCube_of_quasiconvexAtOn {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) {A : Matrix (Fin d) (Fin m) ℝ}
    {Ω : Set (Fin m → ℝ)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (h : QuasiconvexAtOn Ω f A) : QuasiconvexAtOn (unitCube m) f A := by
  obtain ⟨x₁, hx₁⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x₁ hx₁
  set R : ℝ := ε
  set x₀ : Fin m → ℝ := fun i => x₁ i - ε / 2
  set Q' : Set (Fin m → ℝ) := Set.pi univ fun i => Ioo (x₀ i) (x₀ i + R)
  have hQ'Ω : Q' ⊆ Ω := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    have := hx i (Set.mem_univ _)
    simp only [x₀, R, Set.mem_Ioo] at this
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hΩfin : volume Ω < ⊤ := hb.measure_lt_top
  have hQ' : QuasiconvexAtOn Q' f A := rd_quasiconvexAtOn_mono hlsc hbdd hQ'Ω hΩ.measurableSet
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) hΩfin h
  intro φ K hφ h0 _
  have hR : 0 < R := hε
  set S : (Fin m → ℝ) → Fin m → ℝ := fun x => R⁻¹ • (x - x₀)
  set ψ : (Fin m → ℝ) → Fin d → ℝ := fun x => R • φ (S x)
  have hS : LipschitzWith ‖R⁻¹‖₊ S := LipschitzWith.of_dist_le_mul fun y z => by
    simp only [S]
    rw [dist_smul₀, dist_sub_right]
    rfl
  have hψ : LipschitzWith (‖R‖₊ * (K * ‖R⁻¹‖₊)) ψ := (lipschitzWith_smul R).comp (hφ.comp hS)
  have hSQ : ∀ x, S x ∈ unitCube m → x ∈ Q' := by
    intro x hx i _
    have := hx i (Set.mem_univ _)
    simp only [S, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Set.mem_Ioo] at this
    rw [← div_eq_inv_mul, div_pos_iff_of_pos_right hR, div_lt_one hR] at this
    exact ⟨by linarith, by linarith⟩
  have hψ0 : ∀ x ∉ Q', ψ x = 0 := fun x hx => by
    simp only [ψ, h0 _ fun h => hx (hSQ x h), smul_zero]
  have hgrad : ∀ x, grad ψ x = grad φ (S x) := by
    intro x
    ext i k
    simp only [grad, Matrix.of_apply, ψ, S, Pi.smul_apply, smul_eq_mul]
    have e1 : (fun z => R * φ (R⁻¹ • (z - x₀)) i) =
        R • ((fun w => (fun u => φ u i) (R⁻¹ • w)) ∘ fun z => z - x₀) := rfl
    rw [e1, fderiv_const_smul_field, Pi.smul_apply]
    have h2 : fderiv ℝ ((fun w => (fun u => φ u i) (R⁻¹ • w)) ∘ fun z => z - x₀) x =
        fderiv ℝ (fun w => (fun u => φ u i) (R⁻¹ • w)) (x - x₀) := by
      exact fderiv_comp_sub (𝕜 := ℝ) (f := fun w => (fun u => φ u i) (R⁻¹ • w)) (x := x) x₀
    rw [h2]
    have h3 := fderiv_comp_smul (𝕜 := ℝ) (f := fun u => φ u i) (x := x - x₀) R⁻¹
    erw [h3]
    simp only [smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
  have hQ'fin : volume Q' < ⊤ := (measure_mono hQ'Ω).trans_lt hΩfin
  have hq := hQ' ψ _ hψ hψ0 (rd_integrableOn hlsc hbdd A hψ hQ'fin)
  simp only [hgrad] at hq
  -- change of variables `y = R⁻¹ (x − x₀)`
  set G : (Fin m → ℝ) → ℝ := fun y => f (A + grad φ y)
  have hfin : Module.finrank ℝ (Fin m → ℝ) = m := by simp
  have hcv : ∫ x in Q', G (S x) = R ^ m * ∫ y in unitCube m, G y := by
    have h1 := (measurePreserving_sub_right volume x₀).setIntegral_preimage_emb
      (measurableEmbedding_subRight x₀) (fun z => G (R⁻¹ • z)) (R • unitCube m)
    have h4 := Measure.setIntegral_comp_smul_of_pos volume G (R • unitCube m) (inv_pos.2 hR)
    rw [inv_smul_smul₀ hR.ne'] at h4
    have hset : (fun z => z - x₀) ⁻¹' (R • unitCube m) = Q' := by
      ext z
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
      simp only [unitCube, Q', Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      refine forall_congr' fun i => ?_
      rw [← div_eq_inv_mul, div_pos_iff_of_pos_right hR, div_lt_one hR]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [S]
    rw [← hset, h1, h4, hfin, smul_eq_mul, inv_pow, inv_inv]
  have hQ'vol : volume.real Q' = R ^ m := by
    simp only [Q', Measure.real, Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, add_sub_cancel_left]
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le]
  rw [hcv, ← Measure.real, hQ'vol] at hq
  rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul]
  have hRm : 0 < R ^ m := by positivity
  exact le_of_mul_le_mul_left hq hRm

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, second assertion, citing Rindler, Proposition 5.3,
and Dacorogna, Proposition 5.13: quasiconvexity at `A` does not depend on the bounded open domain
of the test maps. 

Proof: the standard argument by rescaling and restriction (Dacorogna 2008, Proposition 5.11;
Rindler, Proposition 5.3), where those texts use a Vitali covering of the cube by copies of `Ω`:
quasiconvexity on a set passes to its measurable subsets, because a test map on the subset vanishes
on the rest, so its gradient vanishes almost everywhere there (`rd_quasiconvexAtOn_mono`, from
`rd_ae_fderiv_eq_zero`: at a density point of the zero set of a Lipschitz map, its derivative is
`0`); and quasiconvexity on the unit cube is quasiconvexity on every cube `x₀ + R (0, 1)^m`, by the
change of variables `x = x₀ + R y`. "⇒": `Ω` lies in a large cube (`rd_quasiconvexAtOn_of_unitCube`);
"⇐": `Ω` contains a small cube (`rd_unitCube_of_quasiconvexAtOn`).
Departure from the sources: they tile the cube by disjoint rescaled copies of `Ω` (Vitali), which
needs `|∂Ω| = 0` or the same vanishing of gradients on zero sets; the formal proof uses the
vanishing directly, with a single cube, which avoids the covering theorem (reason 2: no Vitali
covering by copies of an arbitrary open set is available here).-/
theorem quasiconvexAtOn_iff {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hlsc : LowerSemicontinuous f)
    (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) {Ω : Set (Fin m → ℝ)}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtOn Ω f A :=
  ⟨rd_quasiconvexAtOn_of_unitCube hlsc hbdd hb hΩ.measurableSet,
    rd_unitCube_of_quasiconvexAtOn hlsc hbdd hΩ hb hne⟩

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, third assertion, citing Rindler, Proposition 5.3, and
Dacorogna, Proposition 5.13: quasiconvexity at `A` is equivalent to the inequality for periodic
Lipschitz test maps on the torus `𝕋^m = ℝ^m / ℤ^m`. 

Proof: the standard argument (Dacorogna 2008, Proposition 5.13; the same cutoff as in Šverák's
Lemma 1, whose technique `Morrey/Sverak/Lemma1.lean` formalizes for smooth maps, here for Lipschitz
ones). "⇒": for a periodic `φ`, the maps `ψ_j = η_{1/j} · j⁻² φ (j² ·)` vanish off the cube, where
`η_δ = ∏ h_δ (x_i)` is a Lipschitz cutoff equal to `1` on `[δ, 1 − δ]^m`; their Lipschitz
constants are bounded in `j`, they agree with `j⁻² φ (j² ·)` on `(δ, 1 − δ)^m`, where
`∫ f (A + ∇φ (j² x)) dx = ∫ f (A + ∇φ)` by periodicity (`rd_setIntegral_comp_nsmul`), and the
boundary layer has measure `1 − (1 − 2/j)^m → 0`, on which the integrands are bounded (`f` is
locally bounded); so `f (A) ≤ ∫ f (A + ∇ψ_j) → ∫ f (A + ∇φ)`. "⇐": a test map on the cube
extends periodically (`rd_perExt`, `x ↦ φ (fract x)`), Lipschitz because it vanishes on the
boundary of the cube, with the same gradient on the open cube.-/
theorem quasiconvexAtOn_iff_periodic {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtPeriodic f A :=
  ⟨rd_periodic_of_cube hlsc hbdd A, rd_cube_of_periodic A⟩

end External.Rindler
