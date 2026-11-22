module

public import Morrey.Cassese.TwoByThree.Polynomial
public import Morrey.Cassese.TwoByThree.ExtensionAux
public import Morrey.Cassese.Toolkit

/-!
# Section 5.3: extensions from subspaces (Lemma 5.1) and the quartic `q_{δ,Λ}`

Lemma 5.1 is stated for a subspace `L` and a map `π` with the defining property of the orthogonal
projection onto `L` (`IsFrobProj`); functions "on `L`" are functions on `ℝ^{d×m}` of which only the
values on `L` matter (every function on `L` is the restriction of one, for instance of `f ∘ π`),
and "`C²` away from the origin" is read on `f ∘ π`, which is `C²` on `{π A ≠ 0}` exactly when
`f|_L` is `C²` on `L ∖ {0}`. An `L`-valued rank-one Rademacher martingale is one whose increments
lie in `L`.

Helpers are prefixed `tbt_`; the analytic tools of Lemma 5.1 (2) are in
`Morrey/Cassese/TwoByThree/ExtensionAux.lean` (prefix `tbt2_`).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-- **Lemma 5.1 (2)** (`lem:extension-from-subspace`): with `L`, `π`, `κ` as in (1), let `p ≥ 2`
and let `f` be globally rank-one convex on `L`, `p`-homogeneous, and `C²` away from the origin.
Then there is `c₀ = c₀ (f, L)` such that for every `δ ∈ (0, 1)` and every `Λ ≥ c₀ / δ`, the map
(26) `A ↦ f (π A) + δ (|π A|² + Λ² |π^⊥ A|²)^{p/2}` is globally rank-one convex. (The paper's
proof uses Burkholder's inequality, Theorem 2.3, for (27); this one does not need it: see the
departures below.)

Proof: the paper's argument (TeX lines 1870–1966) for a one-step rank-one Rademacher martingale
`M₁ = A ± R`, which is all that global rank-one convexity needs: a continuous function is convex
along a line as soon as it is midpoint convex there (`tbt2_convexOn_of_midpoint`), so (26) is
rank-one convex once `2 F (A) ≤ F (A + R) + F (A − R)` for every rank-one `R`
(`tbt2_midpoint`). With `X = π A`, `W = π R`, `N = π^⊥ R`, the correction `R_L` of (25) and
`𝓔 = W − R_L`: `f (X + R_L) + f (X − R_L) ≥ 2 f (X)` (rank-one convexity on `L`); (28) for one step,
`|f (X ± W) − f (X ± R_L)| ≤ 2 C (|X| + |W| + 2|𝓔|)^{p−2} (|W| + 2|𝓔|) |𝓔|` (`tbt2_comparison`,
from the Lipschitz-type bound `‖D (f∘π) (Y) − D (f∘π) (Y')‖ ≤ C max (‖Y‖, ‖Y'‖)^{p−2} ‖Y − Y'‖`
on `L`, `tbt2_lipschitz`, which follows from the `C²` regularity and the homogeneity); (29) for one
step (`tbt2_gain`); and the absorption with `ε ≍ δ`, `Λ ≥ c₀ / δ` (`tbt2_absorb`).

Departures from the paper. (i) Only one-step martingales are used, so (27) is the pointwise
subordination `|𝓔₁| ≤ κ |N₁|` of (25) and Burkholder's inequality (Theorem 2.3) is not
invoked; the paper runs the same estimates for `n`-step martingales, which global rank-one
convexity does not need (the conclusion is the same and the intermediate claims (28), (29) are
the paper's at `n = 1`; reason 1 in the form of a repair: the general-`n` version of (28) has the
gap E3). (ii) (28) is proved with the first-order cancellation made explicit (inventory E3): the
first-order terms `Df (X) (±𝓔)` cancel between the two symmetric points, and the remainder is
controlled by the Lipschitz-type bound on `Df` (reason 1: the paper's (28) omits this step).
(iii) (29), "uniform convexity of `|·|^p`", which the paper does not prove or cite, is proved by
the elementary inequality `(u^q + v^q)/2 ≥ ((u + v)/2)^q` (convexity of `t^q`, `q = p/2`)
followed by `(x + y)^q − x^q ≥ (q x^{q−1} y + y^q)/2` (Bernoulli and superadditivity). -/
theorem lemma5_1_part2
    (L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ))
    (π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ) (hπ : IsFrobProj L π) (κ : ℝ)
    (hκ : HasRankOneCorrection L π κ) {p : ℝ} (hp : 2 ≤ p) (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (hrc : ∀ X ∈ L, ∀ R ∈ L, R.rank = 1 → ConvexOn ℝ Set.univ fun t : ℝ => f (X + t • R))
    (hhom : ∀ (t : ℝ), ∀ X ∈ L, f (t • X) = |t| ^ p * f X)
    (hC2 : ContDiffOn ℝ 2 (fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X)))
      {X | π (Matrix.of X) ≠ 0}) :
    ∃ c₀ : ℝ, ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ Λ : ℝ, c₀ / δ ≤ Λ →
      RankOneConvex fun A =>
        f (π A) + δ * (frobSq (π A) + Λ ^ 2 * frobSq (A - π A)) ^ (p / 2) := by
  -- the constant `C` of the comparison (28), from the `C²` regularity and the homogeneity of `f`
  obtain ⟨C, hC1, hcmp⟩ := tbt2_comparison hπ hp hhom hC2
  refine ⟨tbt2_c0 p C |κ|, fun δ hδ hδ1 Λ hΛ => ?_⟩
  set F := fun A : Matrix (Fin d) (Fin m) ℝ =>
    f (π A) + δ * (frobSq (π A) + Λ ^ 2 * frobSq (A - π A)) ^ (p / 2) with hF
  -- `F` is continuous
  have hFc : Continuous F := by
    have hg := (tbt2_differentiable hπ hp hhom hC2).continuous
    have hof : Continuous fun A : Matrix (Fin d) (Fin m) ℝ =>
        (Matrix.of.symm A : Fin d → Fin m → ℝ) := continuous_id
    have hπc : Continuous π := by
      have : π = fun A => Matrix.of (tbt2_piV hπ (Matrix.of.symm A)) := by
        funext A; rw [tbt2_of_piV]; rfl
      rw [this]
      exact (show Continuous fun Y : Fin d → Fin m → ℝ => (Matrix.of Y : Matrix (Fin d) (Fin m) ℝ)
        from continuous_id).comp ((tbt2_piV hπ).continuous.comp hof)
    have hfπ : Continuous fun A => f (π A) := by
      have : (fun A => f (π A)) = (fun Y : Fin d → Fin m → ℝ => f (π (Matrix.of Y))) ∘
          fun A => Matrix.of.symm A := by
        funext A; simp
      rw [this]; exact hg.comp hof
    have hsq : Continuous fun A : Matrix (Fin d) (Fin m) ℝ => frobSq A := by
      unfold frobSq; fun_prop
    refine hfπ.add (continuous_const.mul (Continuous.rpow_const ?_ fun _ => Or.inr (by linarith)))
    exact (hsq.comp hπc).add (continuous_const.mul (hsq.comp (continuous_id.sub hπc)))
  -- the midpoint inequality along rank-one segments, and continuity, give convexity
  intro A B hAB
  have hmid := tbt2_midpoint hπ κ hκ hp hrc hC1 hcmp hδ hδ1 hΛ
  have hconv : ConvexOn ℝ Set.univ fun t : ℝ => F (t • A + (1 - t) • B) := by
    apply tbt2_convexOn_of_midpoint
    · exact hFc.comp (by fun_prop)
    · intro t h
      rcases eq_or_ne h 0 with rfl | hh
      · simp only [add_zero, sub_zero]; linarith
      · have hR : (h • (A - B)).rank = 1 := by
          rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hh), hAB]
        have := hmid (t • A + (1 - t) • B) (h • (A - B)) hR
        rw [show (t + h) • A + (1 - (t + h)) • B = t • A + (1 - t) • B + h • (A - B) by module,
          show (t - h) • A + (1 - (t - h)) • B = t • A + (1 - t) • B - h • (A - B) by module]
        exact this
  exact hconv.subset (Set.subset_univ _) (convex_Icc 0 1)

/-- Sums of rank-one convex functions are rank-one convex. -/
theorem tbt_rankOneConvex_add {f g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f)
    (hg : RankOneConvex g) : RankOneConvex fun A => f A + g A :=
  fun A B h => (hf A B h).add (hg A B h)

/-- `|P + t V|² = |V|² t² + 2 ⟨P, V⟩ t + |P|²`. -/
theorem tbt_frobSq_add_smul (P V : Matrix (Fin d) (Fin m) ℝ) (t : ℝ) :
    frobSq (P + t • V) = frobSq V * t ^ 2 + 2 * frobInner P V * t + frobSq P := by
  simp only [frobSq, frobInner, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem tbt_projL3_add_smul (P V : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ) :
    projL3 (P + t • V) = projL3 P + t • projL3 V := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [projL3] <;> ring

/-- The penalty `(|π A|² + Λ² |π^⊥ A|²)²` is convex, hence rank-one convex. -/
theorem tbt_rankOneConvex_penalty (c Λ : ℝ) (hc : 0 ≤ c) :
    RankOneConvex fun A : Matrix (Fin 2) (Fin 3) ℝ =>
      c * (frobSq (projL3 A) + Λ ^ 2 * frobSq (A - projL3 A)) ^ 2 := by
  intro A B _
  have hline : ∀ t : ℝ, t • A + (1 - t) • B = B + t • (A - B) := fun t => by module
  have hq : ConvexOn ℝ Set.univ fun t : ℝ =>
      frobSq (projL3 (B + t • (A - B))) + Λ ^ 2 * frobSq (B + t • (A - B) - projL3 (B + t • (A - B))) := by
    have e : ∀ t : ℝ, frobSq (projL3 (B + t • (A - B))) +
        Λ ^ 2 * frobSq (B + t • (A - B) - projL3 (B + t • (A - B))) =
        (frobSq (projL3 (A - B)) + Λ ^ 2 * frobSq ((A - B) - projL3 (A - B))) * t ^ 2 +
          (2 * frobInner (projL3 B) (projL3 (A - B)) +
            Λ ^ 2 * (2 * frobInner (B - projL3 B) ((A - B) - projL3 (A - B)))) * t +
          (frobSq (projL3 B) + Λ ^ 2 * frobSq (B - projL3 B)) := by
      intro t
      rw [tbt_projL3_add_smul, show B + t • (A - B) - (projL3 B + t • projL3 (A - B)) =
        (B - projL3 B) + t • ((A - B) - projL3 (A - B)) by module, tbt_frobSq_add_smul,
        tbt_frobSq_add_smul]
      ring
    simp_rw [e]
    exact tbt_convexOn_quadratic (by
      have := tbt_frobSq_nonneg (projL3 (A - B))
      have := tbt_frobSq_nonneg ((A - B) - projL3 (A - B))
      positivity)
  have hq2 := (hq.pow (fun t _ => by
    have := tbt_frobSq_nonneg (projL3 (B + t • (A - B)))
    have := tbt_frobSq_nonneg (B + t • (A - B) - projL3 (B + t • (A - B)))
    positivity) 2).smul hc
  refine ⟨convex_Icc 0 1, fun x _ y _ a b ha hb hab => ?_⟩
  have := hq2.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul, Pi.pow_apply] at this ⊢
  rw [hline, hline, hline]
  exact this

/-- **Proof of Theorem 1.3** (`cs-qdl-rc`, lines 1980–1991): for a sufficiently large fixed `K`
and every `0 < δ ≤ 1`, `q_{δ, K/δ}` is a globally rank-one convex homogeneous quartic polynomial
(from Lemma 5.1 (2) applied to `q₃` on `𝓛₃`). (The text has `0 < δ ≤ 1`; Lemma 5.1 (2) is stated
for `δ ∈ (0, 1)`.) -/
theorem qDeltaLambda_rankOneConvex :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K ≥ K₀, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      IsHomogeneousPolynomial 4 (qDeltaLambda δ (K / δ)) ∧
        RankOneConvex (qDeltaLambda δ (K / δ)) := by
  -- Lemma 5.1 (2) for `f = q₃` on `𝓛₃` (`p = 4`, `κ = 2`)
  obtain ⟨c₀, hc₀⟩ := lemma5_1_part2 L3Submodule projL3 isFrobProj_projL3 2
    hasRankOneCorrection_L3 (p := 4) (by norm_num) q3
    (fun X hX R hR hR1 => q3_rankOneConvexOn_L3 X R hX hR hR1)
    (fun t X _ => by
      rw [tbt_q3_smul, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        pow_abs, abs_of_nonneg (by positivity)])
    tbt_contDiff_q3_projL3.contDiffOn
  have hq : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ Λ : ℝ, c₀ / δ ≤ Λ → RankOneConvex (qDeltaLambda δ Λ) := by
    intro δ hδ hδ1 Λ hΛ
    have := hc₀ δ hδ hδ1 Λ hΛ
    convert this using 2 with A
    rw [qDeltaLambda, show (4 : ℝ) / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine ⟨max (2 * c₀) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun K hK δ hδ hδ1 => ?_⟩
  refine ⟨tbt_ihp_qDeltaLambda δ (K / δ), ?_⟩
  have hc₀K : c₀ ≤ K := by
    rcases le_or_gt 0 c₀ with h | h
    · linarith [le_max_left (2 * c₀) 1]
    · linarith [le_max_right (2 * c₀) 1]
  rcases hδ1.lt_or_eq with hlt | rfl
  · exact hq δ hδ hlt (K / δ) (div_le_div_of_nonneg_right hc₀K hδ.le)
  · -- `δ = 1`: `q_{1,K} = q_{1/2,K} + (1/2) (|π A|² + K² |π^⊥ A|²)²`, with `K ≥ c₀ / (1/2)`
    have h1 := hq (1 / 2) (by norm_num) (by norm_num) (K / 1) (by
      rw [div_one]; linarith [le_max_left (2 * c₀) 1])
    have h2 := tbt_rankOneConvex_penalty (1 / 2) (K / 1) (by norm_num)
    convert tbt_rankOneConvex_add h1 h2 using 1
    funext A
    simp only [qDeltaLambda]
    ring

end Cassese
