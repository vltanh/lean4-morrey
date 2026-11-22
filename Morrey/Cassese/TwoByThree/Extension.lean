module

public import Morrey.Cassese.TwoByThree.Polynomial
public import Morrey.Cassese.TwoByThree.ExtensionAux
public import Morrey.Cassese.TwoByThree.ExtensionOne
public import Morrey.Cassese.Toolkit

/-!
# Section 5.3: extensions from subspaces (Lemma 5.1) and the quartic `q_{δ,Λ}`

Lemma 5.1 is stated for a subspace `L` and a map `π` with the defining property of the orthogonal
projection onto `L` (`IsFrobProj`); functions "on `L`" are functions on `ℝ^{d×m}` of which only the
values on `L` matter (every function on `L` is the restriction of one, for instance of `f ∘ π`),
and "`C²` away from the origin" is read on `f ∘ π`, which is `C²` on `{π A ≠ 0}` exactly when
`f|_L` is `C²` on `L ∖ {0}`. An `L`-valued rank-one Rademacher martingale is one whose increments
lie in `L`.

The proof of Lemma 5.1 (2) runs the paper's argument on `n`-step rank-one Rademacher martingales:
the averages over the signs that it needs (mean zero of a martingale started at `0`, Jensen's
inequality along a martingale) and the passage to global rank-one convexity through
Proposition 2.5 are below. Helpers are prefixed `tbt_`; the analytic tools of Lemma 5.1 (2) are in
`Morrey/Cassese/TwoByThree/ExtensionAux.lean` (prefix `tbt2_`), and the tools shared with
Lemma 5.1 (1) (the correction (25), Burkholder's inequality (27) for the Frobenius norm) in
`Morrey/Cassese/TwoByThree/ExtensionOne.lean` (prefix `tbt1_`).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-! ### Averages over the signs: mean zero and Jensen's inequality -/

/-- The average of a constant. -/
theorem tbt_avg_const {N : ℕ} (c : ℝ) : avg (fun _ : Fin N → Bool => c) = c := by
  simp only [avg, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- Flipping one sign preserves the uniform probability. -/
theorem tbt_avg_flip {N : ℕ} (k : Fin N) (h : (Fin N → Bool) → ℝ) :
    avg (fun ε => h (rad_flip k ε)) = avg h := by
  simp only [avg]
  congr 1
  exact Equiv.sum_comp ((rad_flip_involutive k).toPerm _) h

/-- A Rademacher martingale started at `0` has mean zero: `E ℓ (Σ_{k<n} ε_k ξ_k) = 0` for every
linear functional `ℓ` (each `ε_k ℓ (ξ_k)` changes sign when `ε_k` is flipped). -/
theorem tbt_avg_mart_linear {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] (ℓ : E →ₗ[ℝ] ℝ)
    {ξ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ) (n : ℕ) :
    avg (fun ε => ℓ (mart ξ n ε)) = 0 := by
  have hk : ∀ k : Fin N, ∑ ε : Fin N → Bool, coin (ε k) * ℓ (ξ k ε) = 0 := by
    intro k
    set g : (Fin N → Bool) → ℝ := fun ε => coin (ε k) * ℓ (ξ k ε)
    have hg : ∀ ε, g (rad_flip k ε) = -g ε := by
      intro ε
      simp only [g, rad_flip_apply_self, rad_coin_not]
      rw [hξ k (rad_flip k ε) ε fun j hj => rad_flip_apply_ne (ne_of_lt hj) ε]
      ring
    have h := Equiv.sum_comp ((rad_flip_involutive k).toPerm _) g
    simp only [Function.Involutive.coe_toPerm, hg, Finset.sum_neg_distrib] at h
    show ∑ ε, g ε = 0
    linarith
  simp only [avg, mart, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_zero fun k _ => hk k, zero_div]

/-- Jensen's inequality along a Rademacher martingale for a function that is midpoint convex along
its increments: if `2 φ (Y₀ + M_k) ≤ φ (Y₀ + M_k + ξ_k) + φ (Y₀ + M_k − ξ_k)` for every `k`, then
`φ (Y₀) ≤ E φ (Y₀ + M_n)`. -/
theorem tbt_avg_jensen {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] (φ : E → ℝ) (Y₀ : E)
    {ξ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ)
    (hmid : ∀ (k : Fin N) (ε : Fin N → Bool), 2 * φ (Y₀ + mart ξ k ε) ≤
      φ (Y₀ + mart ξ k ε + ξ k ε) + φ (Y₀ + mart ξ k ε - ξ k ε)) :
    ∀ n : ℕ, φ Y₀ ≤ avg (fun ε => φ (Y₀ + mart ξ n ε)) := by
  intro n
  induction n with
  | zero => simp only [rad_mart_zero, add_zero, tbt_avg_const, le_refl]
  | succ n ih =>
    by_cases hn : n < N
    · set i : Fin N := ⟨n, hn⟩
      set h : (Fin N → Bool) → ℝ := fun ε => φ (Y₀ + mart ξ (n + 1) ε)
      have hflip : ∀ ε, h ε + h (rad_flip i ε) =
          φ (Y₀ + mart ξ i ε + ξ i ε) + φ (Y₀ + mart ξ i ε - ξ i ε) := by
        intro ε
        have hM : mart ξ n (rad_flip i ε) = mart ξ n ε :=
          rad_mart_congr hξ n fun j hj => rad_flip_apply_ne (fun h => by
            rw [h] at hj; exact lt_irrefl _ hj) ε
        have hX : ξ i (rad_flip i ε) = ξ i ε :=
          hξ i (rad_flip i ε) ε fun j hj => rad_flip_apply_ne (ne_of_lt hj) ε
        simp only [h, rad_mart_succ, dite_eq_left hn]
        rw [hM, hX, rad_flip_apply_self, rad_coin_not]
        show φ (Y₀ + (mart ξ n ε + coin (ε i) • ξ i ε)) +
          φ (Y₀ + (mart ξ n ε + -coin (ε i) • ξ i ε)) = _
        cases ε i <;> simp only [coin, Bool.false_eq_true, ite_false, ite_true, one_smul,
          neg_smul, neg_neg, ← add_assoc, ← sub_eq_add_neg] <;> rw [← add_sub_assoc]
        exact add_comm _ _
      have h2 : 2 * avg h = avg (fun ε => h ε + h (rad_flip i ε)) := by
        rw [rad_avg_add, tbt_avg_flip]; ring
      have h3 : avg (fun ε => 2 * φ (Y₀ + mart ξ n ε)) ≤ avg (fun ε => h ε + h (rad_flip i ε)) :=
        rad_avg_mono fun ε => by rw [hflip]; exact hmid i ε
      rw [rad_avg_mul_left] at h3
      show φ Y₀ ≤ avg h
      linarith
    · have : ∀ ε, mart ξ (n + 1) ε = mart ξ n ε := fun ε => by
        rw [rad_mart_succ, dite_eq_right hn, add_zero]
      simp only [this]
      exact ih

/-! ### Rank-one convexity from the martingale inequality (Proposition 2.5) -/

/-- Rank-one convexity from the martingale inequality at every point, by Proposition 2.5: if the
continuous `F` satisfies `F (M₀) ≤ E F (M_N)` for every rank-one Rademacher martingale `M` (any
start `M₀`), then `F` is rank-one convex at every point (Proposition 2.5 for `B ↦ F (M₀ + B)`),
hence rank-one convex: at a point `P` of a rank-one segment, a rank-one convex minorant touching
`F` at `P` gives `F (P) ≤` the chord. -/
theorem tbt_rankOneConvex_of_avg {F : Matrix (Fin d) (Fin m) ℝ → ℝ} (hF : Continuous F)
    (h : ∀ (M₀ : Matrix (Fin d) (Fin m) ℝ) (N : ℕ)
      (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ),
        IsRankOneIncrements A → F M₀ ≤ avg fun ε => F (radMart M₀ A N ε)) :
    RankOneConvex F := by
  -- rank-one convexity at every point (Proposition 2.5)
  have hat : ∀ M₀ : Matrix (Fin d) (Fin m) ℝ, RankOneConvexAt (fun B => F (M₀ + B)) 0 := by
    intro M₀
    refine (proposition2_5 (show Continuous fun B => F (M₀ + B) from
      hF.comp (continuous_const.add continuous_id))).mpr fun N A hA => ?_
    simpa only [add_zero, radMart, zero_add] using h M₀ N A hA
  intro A B hAB
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  set P : ℝ → Matrix (Fin d) (Fin m) ℝ := fun t => t • A + (1 - t) • B
  obtain ⟨g, -, hgR, hgF, hg0⟩ := hat (P (a • x + b • y))
  set P₀ := P (a • x + b • y)
  have hline : ∀ t : ℝ, t • (A - P₀) + (1 - t) • (B - P₀) = P t - P₀ := fun t => by
    simp only [P]; module
  have hc := (hgR (A - P₀) (B - P₀) (by rw [sub_sub_sub_cancel_right]; exact hAB)).2 hx hy ha
    hb hab
  simp only [hline] at hc
  rw [show P (a • x + b • y) - P₀ = 0 from sub_self _, hg0] at hc
  have h1 := hgF (P x - P₀)
  have h2 := hgF (P y - P₀)
  simp only [add_sub_cancel, add_zero] at h1 h2 hc
  simp only [smul_eq_mul] at hc ⊢
  have := mul_le_mul_of_nonneg_left h1 ha
  have := mul_le_mul_of_nonneg_left h2 hb
  exact hc.trans (by simp only [P] at *; linarith)

/-! ### The estimates (28) and (29) at one sign sequence -/

/-- `|P + V|² = |P|² + 2 ⟨V, P⟩ + |V|²`. -/
theorem tbt_frobSq_add (P V : Matrix (Fin d) (Fin m) ℝ) :
    frobSq (P + V) = frobSq P + 2 * frobInner V P + frobSq V := by
  simp only [frobSq, frobInner, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The pointwise form of the estimates (28) and (29) at one sign sequence. With `X = π M₀`,
`Z₀ = π^⊥ M₀`, `W = π M_N − X`, `N = π^⊥ M_N − Z₀`, `𝓔 = π M_N − M̃_N`, `u = f (X + W)`,
`v = f (M̃_N) = f (X + W − 𝓔)`, `D = Df (X) 𝓔` and `τ = c δ` (`ε = τ` in (28)): the second-order
remainder `|u − v − D|` of (28) is split as in (28), and the gain (29) of the penalty
`(|π A|² + Λ² |π^⊥ A|²)^{p/2}` at `V₀ = (X, Λ Z₀)` along `V_N − V₀ = (W, Λ N)` is bounded below
after removing its first-order term `p |V₀|^{p−2} ⟨V₀, V_N − V₀⟩`; the terms in `|W|`
cancel (`ε = τ`). -/
theorem tbt_part2_pointwise {p C C' c δ Λ : ℝ} (hp : 2 ≤ p) (hc0 : 0 < c) (hδ : 0 < δ)
    (hΛ0 : 0 ≤ Λ) (hτ1 : δ * c ≤ 1)
    (hyoung : ∀ ε a w e : ℝ, 0 < ε → ε ≤ 1 → 0 ≤ a → 0 ≤ w → 0 ≤ e →
      C * (a + w + e) ^ (p - 2) * (w + e) * e ≤
        ε * (a ^ (p - 2) * w ^ 2 + w ^ p) + C' * (ε⁻¹ * a ^ (p - 2) * e ^ 2 + ε ^ (1 - p) * e ^ p))
    (hgain : ∀ x y σ : ℝ, 0 ≤ x → 0 ≤ y → σ ^ 2 ≤ 4 * x * y →
      c * (x ^ (p / 2 - 1) * y + y ^ (p / 2)) ≤
        (x + σ + y) ^ (p / 2) - x ^ (p / 2) - p / 2 * x ^ (p / 2 - 1) * σ)
    (X W E Nn Z₀ : Matrix (Fin d) (Fin m) ℝ) (u v D : ℝ)
    (h28 : |u - v - D| ≤ C * (frobNorm X + frobNorm W + frobNorm E) ^ (p - 2) *
      (frobNorm W + frobNorm E) * frobNorm E) :
    v + D + (δ * (frobSq X + Λ ^ 2 * frobSq Z₀) ^ (p / 2) +
        δ * (p / 2) * (frobSq X + Λ ^ 2 * frobSq Z₀) ^ (p / 2 - 1) *
          (2 * (frobInner W X + Λ ^ 2 * frobInner Nn Z₀))) +
      (δ * c * Λ ^ 2 * frobNorm X ^ (p - 2) * frobNorm Nn ^ 2 +
        δ * c * Λ ^ p * frobNorm Nn ^ p - C' * (δ * c)⁻¹ * frobNorm X ^ (p - 2) * frobNorm E ^ 2 -
        C' * (δ * c) ^ (1 - p) * frobNorm E ^ p) ≤
      u + δ * (frobSq (X + W) + Λ ^ 2 * frobSq (Z₀ + Nn)) ^ (p / 2) := by
  have hq : 1 ≤ p / 2 := by linarith
  have hi1 := tbt1_abs_frobInner_le W X
  have hi2 := tbt1_abs_frobInner_le Nn Z₀
  have ha0 := tbt1_frobNorm_nonneg X
  have hw0 := tbt1_frobNorm_nonneg W
  have he0 := tbt1_frobNorm_nonneg E
  have hn0 := tbt1_frobNorm_nonneg Nn
  have hz0 := tbt1_frobNorm_nonneg Z₀
  rw [tbt_frobSq_add, tbt_frobSq_add, ← tbt2_frobNorm_sq X, ← tbt2_frobNorm_sq W,
    ← tbt2_frobNorm_sq Z₀, ← tbt2_frobNorm_sq Nn]
  generalize frobNorm X = a at *
  generalize frobNorm W = w at *
  generalize frobNorm E = e at *
  generalize frobNorm Nn = n at *
  generalize frobNorm Z₀ = z at *
  generalize frobInner W X = i1 at *
  generalize frobInner Nn Z₀ = i2 at *
  -- `x = |V₀|²`, `y = |V_N − V₀|²`, `σ = 2 ⟨V₀, V_N − V₀⟩`
  have hx0 : 0 ≤ a ^ 2 + Λ ^ 2 * z ^ 2 := by positivity
  have hy0 : 0 ≤ w ^ 2 + Λ ^ 2 * n ^ 2 := by positivity
  have hσ : (2 * (i1 + Λ ^ 2 * i2)) ^ 2 ≤
      4 * (a ^ 2 + Λ ^ 2 * z ^ 2) * (w ^ 2 + Λ ^ 2 * n ^ 2) := by
    have h1 : |i1 + Λ ^ 2 * i2| ≤ w * a + Λ ^ 2 * (n * z) :=
      (abs_add_le _ _).trans (add_le_add hi1 (by
        rw [abs_mul, abs_of_nonneg (sq_nonneg Λ)]
        exact mul_le_mul_of_nonneg_left hi2 (sq_nonneg Λ)))
    have h2 := abs_le.mp h1
    have h3 : (i1 + Λ ^ 2 * i2) ^ 2 ≤ (w * a + Λ ^ 2 * (n * z)) ^ 2 := sq_le_sq' h2.1 h2.2
    have h4 : (a ^ 2 + Λ ^ 2 * z ^ 2) * (w ^ 2 + Λ ^ 2 * n ^ 2) -
        (w * a + Λ ^ 2 * (n * z)) ^ 2 = Λ ^ 2 * (a * n - z * w) ^ 2 := by ring
    have h5 : 0 ≤ Λ ^ 2 * (a * n - z * w) ^ 2 := by positivity
    have h6 : (2 * (i1 + Λ ^ 2 * i2)) ^ 2 = 4 * (i1 + Λ ^ 2 * i2) ^ 2 := by ring
    rw [h6]
    nlinarith
  -- (29)
  have h29 := hgain _ _ _ hx0 hy0 hσ
  have hxa : a ^ (p - 2) ≤ (a ^ 2 + Λ ^ 2 * z ^ 2) ^ (p / 2 - 1) := by
    have e : a ^ (p - 2) = (a ^ 2) ^ (p / 2 - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha0]; congr 1; push_cast; ring
    rw [e]
    exact Real.rpow_le_rpow (sq_nonneg a) (le_add_of_nonneg_right (by positivity)) (by linarith)
  have hyq : w ^ p + Λ ^ p * n ^ p ≤ (w ^ 2 + Λ ^ 2 * n ^ 2) ^ (p / 2) := by
    have := Real.add_rpow_le_rpow_add (sq_nonneg w) (sq_nonneg (Λ * n)) hq
    rw [tbt2_sq_rpow hw0, tbt2_sq_rpow (mul_nonneg hΛ0 hn0), Real.mul_rpow hΛ0 hn0] at this
    convert this using 2
    ring
  have hlow : c * (a ^ (p - 2) * (w ^ 2 + Λ ^ 2 * n ^ 2) + (w ^ p + Λ ^ p * n ^ p)) ≤
      c * ((a ^ 2 + Λ ^ 2 * z ^ 2) ^ (p / 2 - 1) * (w ^ 2 + Λ ^ 2 * n ^ 2) +
        (w ^ 2 + Λ ^ 2 * n ^ 2) ^ (p / 2)) :=
    mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hxa hy0) hyq) hc0.le
  have hδ29 := mul_le_mul_of_nonneg_left h29 hδ.le
  have hδlow := mul_le_mul_of_nonneg_left hlow hδ.le
  -- (28), split with `ε = τ = δ c`
  have hspl := hyoung (δ * c) a w e (mul_pos hδ hc0) hτ1 ha0 hw0 he0
  have habs := abs_le.mp h28
  have e1 : a ^ 2 + 2 * i1 + w ^ 2 + Λ ^ 2 * (z ^ 2 + 2 * i2 + n ^ 2) =
      a ^ 2 + Λ ^ 2 * z ^ 2 + 2 * (i1 + Λ ^ 2 * i2) + (w ^ 2 + Λ ^ 2 * n ^ 2) := by ring
  rw [e1]
  linarith

/-! ### Lemma 5.1 (2) -/

/-- **Lemma 5.1 (2)** (`lem:extension-from-subspace`): with `L`, `π`, `κ` as in (1), let `p ≥ 2`
and let `f` be globally rank-one convex on `L`, `p`-homogeneous, and `C²` away from the origin.
Then there is `c₀ = c₀ (f, L)` such that for every `δ ∈ (0, 1)` and every `Λ ≥ c₀ / δ`, the map
(26) `A ↦ f (π A) + δ (|π A|² + Λ² |π^⊥ A|²)^{p/2}` is globally rank-one convex.

Proof: the paper's (TeX lines 1870–1966), for `n`-step rank-one Rademacher martingales. Write `F`
for the map (26). By Proposition 2.5 at every point (`proposition2_5`, through
`tbt_rankOneConvex_of_avg`), it suffices that `E F (M_N) ≥ F (M₀)` for every rank-one Rademacher
martingale `M`, with any start `M₀`. Applying (25) predictably to the increments of `M`
(`tbt1_corr`) gives the `L`-valued rank-one martingale `M̃` started at `X = π M₀`, and
`𝓔 = π M − M̃` is differentially subordinate to `κ N`, `N = π^⊥ M − π^⊥ M₀`; Burkholder's inequality
(Theorem 2.3, through `tbt1_burkholder_frob`) gives (27) for `s = 2` and `s = p`. With
`W = π M_N − X`: rank-one convexity of `f` on `L` gives `E f (M̃_N) ≥ f (X)` (Jensen's inequality
along `M̃`, `tbt_avg_jensen`); (28) holds for every `0 < ε ≤ 1`, with a constant `C` from the `C²`
regularity and the homogeneity of `f` (`tbt2_taylor`, and `tbt2_young` for the splitting in `ε`);
(29) holds with some `c_p > 0` (`tbt2_gain`); and with `ε = c_p δ ≍ δ`, `Λ ≥ c₀ / δ` gives
`δ Λ² ≳ δ⁻¹` and `δ Λ^p ≳ δ^{1−p}`, which absorb the last two terms of (28) through (27)
(`tbt_part2_pointwise`, then the averages).

Gaps of the paper, filled along its own lines (no departure from its proof). (i) Inventory E3:
(28) omits the first-order term. Since `π M_N = M̃_N + 𝓔_N`,
`f (π M_N) − f (M̃_N) = Df (X) 𝓔_N + R`, where `E Df (X) 𝓔_N = 0` because `𝓔` is a martingale
started at `0` (`tbt_avg_mart_linear`), and the remainder `R` is controlled by the Lipschitz-type
bound `‖Df (Y) − Df (Y')‖ ≤ C max (|Y|, |Y'|)^{p−2} |Y − Y'|` on `L`, valid across the origin
(`tbt2_lipschitz`, from the `C²` regularity and the homogeneity). (ii) (29), "uniform convexity of
`|·|^p`", is neither proved nor cited in the paper; it is proved pointwise (`tbt2_gain`) for
`V = (π M, Λ π^⊥ M)`, whose first-order term `p |V₀|^{p−2} ⟨V₀, V_N − V₀⟩` has mean zero as well.
(iii) The paper leaves implicit that `E F (M_N) ≥ F (M₀)` for all such martingales gives global
rank-one convexity; this is Proposition 2.5 at every point (with Proposition 2.4 in its proof). -/
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
  have hp1 : 1 < p := by linarith
  have hq : 1 ≤ p / 2 := by linarith
  -- the constants: `C` of (28), from the `C²` regularity and the homogeneity of `f`; `C'` of the
  -- splitting of (28) with `ε`; `c` of (29); `κ' = max κ 0`; Burkholder's `(p* − 1)^p`
  obtain ⟨C, hC1, htay⟩ := tbt2_taylor hπ hp hhom hC2
  obtain ⟨C', hC'0, hyoung⟩ := tbt2_young hp hC1
  obtain ⟨c, hc0, hc1, hgain⟩ := tbt2_gain hq
  set κ' := max κ 0
  have hκ' : 0 ≤ κ' := le_max_right _ _
  set Bp := (pStar p - 1) ^ p
  have hpstar : 0 ≤ pStar p - 1 := by
    have : p ≤ pStar p := le_max_left _ _
    linarith
  have hBp : 0 ≤ Bp := Real.rpow_nonneg hpstar _
  set K₁ := √C' * κ' with hK₁_def
  set K₂ := (C' * Bp) ^ (1 / p) * κ' with hK₂_def
  have hK₁ : 0 ≤ K₁ := mul_nonneg (Real.sqrt_nonneg _) hκ'
  have hK₂ : 0 ≤ K₂ := mul_nonneg (Real.rpow_nonneg (mul_nonneg hC'0 hBp) _) hκ'
  refine ⟨(K₁ + K₂) / c, fun δ hδ hδ1 Λ hΛ => ?_⟩
  -- `ε = τ = c δ`, and `Λ ≥ c₀ / δ` gives `τ Λ ≥ K₁ + K₂`
  set τ := δ * c
  have hτ : 0 < τ := mul_pos hδ hc0
  have hτ1 : τ ≤ 1 := by
    calc τ = δ * c := rfl
      _ ≤ 1 * 1 := mul_le_mul hδ1.le hc1 hc0.le zero_le_one
      _ = 1 := one_mul 1
  have hτΛ : K₁ + K₂ ≤ τ * Λ := by
    rw [div_div, div_le_iff₀ (mul_pos hc0 hδ)] at hΛ
    linarith
  have hΛ0 : 0 ≤ Λ := by
    by_contra h
    push Not at h
    have := mul_neg_of_pos_of_neg hτ h
    linarith
  -- the absorption: `C' κ'² / τ ≤ τ Λ²` and `C' τ^{1−p} (p* − 1)^p κ'^p ≤ τ Λ^p`
  have hco1 : C' * τ⁻¹ * κ' ^ 2 ≤ τ * Λ ^ 2 := by
    have h1 : K₁ ^ 2 ≤ (τ * Λ) ^ 2 := pow_le_pow_left₀ hK₁ (by linarith) 2
    have h2 : K₁ ^ 2 = C' * κ' ^ 2 := by rw [hK₁_def, mul_pow, Real.sq_sqrt hC'0]
    rw [h2] at h1
    have e : C' * τ⁻¹ * κ' ^ 2 = (C' * κ' ^ 2) / τ := by field_simp
    rw [e, div_le_iff₀ hτ]
    nlinarith
  have hco2 : C' * τ ^ (1 - p) * (Bp * κ' ^ p) ≤ τ * Λ ^ p := by
    have h1 : K₂ ^ p ≤ (τ * Λ) ^ p := Real.rpow_le_rpow hK₂ (by linarith) (by linarith)
    have h2 : K₂ ^ p = C' * Bp * κ' ^ p := by
      rw [hK₂_def, Real.mul_rpow (Real.rpow_nonneg (mul_nonneg hC'0 hBp) _) hκ',
        ← Real.rpow_mul (mul_nonneg hC'0 hBp), one_div_mul_cancel (by linarith), Real.rpow_one]
    rw [h2, Real.mul_rpow hτ.le hΛ0] at h1
    have hτp : 0 < τ ^ (1 - p) := Real.rpow_pos_of_pos hτ _
    have e : τ ^ (1 - p) * τ ^ p = τ := by
      rw [← Real.rpow_add hτ, show 1 - p + p = 1 by ring, Real.rpow_one]
    calc C' * τ ^ (1 - p) * (Bp * κ' ^ p) = τ ^ (1 - p) * (C' * Bp * κ' ^ p) := by ring
      _ ≤ τ ^ (1 - p) * (τ ^ p * Λ ^ p) := mul_le_mul_of_nonneg_left h1 hτp.le
      _ = τ * Λ ^ p := by rw [← mul_assoc, e]
  set F := fun A : Matrix (Fin d) (Fin m) ℝ =>
    f (π A) + δ * (frobSq (π A) + Λ ^ 2 * frobSq (A - π A)) ^ (p / 2)
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
  -- by Proposition 2.5 at every point, it suffices that `F (M₀) ≤ E F (M_N)` for every rank-one
  -- Rademacher martingale `M`
  refine tbt_rankOneConvex_of_avg hFc fun A₀ N A hA => ?_
  -- the corrected martingale `M̃` (increments `(dM_k)_L`), `𝓔 = π M − M̃` and `N = π^⊥ M − π^⊥ M₀`
  obtain ⟨corr, hcorrL, hcorrr, hcorrle⟩ := tbt1_corr hπ hκ
  set B : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ := fun k ε => corr (A k ε)
  have hBpred : IsPredictable B := fun k ε ε' h => by simp only [B, hA.1 k ε ε' h]
  have hAπ : IsPredictable fun k ε => π (A k ε) := fun k ε ε' h => by simp only [hA.1 k ε ε' h]
  have hAperp : IsPredictable fun k ε => A k ε - π (A k ε) := fun k ε ε' h => by
    simp only [hA.1 k ε ε' h]
  have hAE : IsPredictable fun k ε => π (A k ε) - B k ε := fun k ε ε' h => by
    simp only [B, hA.1 k ε ε' h]
  set X := π A₀
  set Z₀ := A₀ - π A₀ with hZ₀_def
  have hXL : X ∈ L := (hπ A₀).1
  set W : (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ :=
    fun ε => mart (fun k ε => π (A k ε)) N ε
  set Nn : (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ :=
    fun ε => mart (fun k ε => A k ε - π (A k ε)) N ε
  set E : (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ :=
    fun ε => mart (fun k ε => π (A k ε) - B k ε) N ε
  have hWL : ∀ ε, W ε ∈ L := fun ε => tbt1_mart_mem L (fun k ε => (hπ _).1) N ε
  have hEL : ∀ ε, E ε ∈ L := fun ε =>
    tbt1_mart_mem L (fun k ε => L.sub_mem (hπ _).1 (hcorrL _)) N ε
  have hπmart : ∀ ε, π (mart A N ε) = W ε := fun ε => tbt1_mart_map (tbt1ProjLin hπ) A N ε
  have hπM : ∀ ε, π (radMart A₀ A N ε) = X + W ε := fun ε => by
    rw [radMart, tbt2_proj_add hπ, hπmart]
  have hperp : ∀ ε, radMart A₀ A N ε - π (radMart A₀ A N ε) = Z₀ + Nn ε := fun ε => by
    have hN : Nn ε = mart A N ε - W ε := tbt1_mart_sub _ _ N ε
    rw [hπM, hN, radMart, hZ₀_def]
    abel
  have hMt : ∀ ε, X + mart B N ε = X + W ε - E ε := fun ε => by
    simp only [E, W, tbt1_mart_sub]
    abel
  -- rank-one convexity of `f` on `L`: `E f (M̃_N) ≥ f (X)`
  have hjen : f X ≤ avg (fun ε => f (X + mart B N ε)) := by
    refine tbt_avg_jensen f X hBpred (fun k ε => ?_) N
    have hY : X + mart B k ε ∈ L := L.add_mem hXL (tbt1_mart_mem L (fun k ε => hcorrL _) k ε)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hcorrr (A k ε)) with h0 | h1
    · rw [show B k ε = 0 from eq_zero_of_rank_eq_zero h0, add_zero, sub_zero]
      linarith
    · have := (hrc _ hY _ (hcorrL _) h1).2 (Set.mem_univ (1 : ℝ)) (Set.mem_univ (-1 : ℝ))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul, one_smul, neg_smul, ← sub_eq_add_neg] at this
      norm_num at this
      show 2 * f (X + mart B k ε) ≤ f (X + mart B k ε + corr (A k ε)) +
        f (X + mart B k ε - corr (A k ε))
      linarith
  -- `𝓔` and `π M − π M₀`, `π^⊥ M − π^⊥ M₀` are martingales started at `0`: mean zero
  set Dg := fderiv ℝ (fun Y : Fin d → Fin m → ℝ => f (π (Matrix.of Y))) (Matrix.of.symm X)
  set ℓD : Matrix (Fin d) (Fin m) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => Dg (Matrix.of.symm M)
      map_add' := fun M M' => map_add Dg (Matrix.of.symm M) (Matrix.of.symm M')
      map_smul' := fun c M => map_smul Dg c (Matrix.of.symm M) }
  have hmz1 : avg (fun ε => Dg (Matrix.of.symm (E ε))) = 0 := tbt_avg_mart_linear ℓD hAE N
  have hinner : ∀ Y : Matrix (Fin d) (Fin m) ℝ, ∀ {ξ : Fin N → (Fin N → Bool) →
      Matrix (Fin d) (Fin m) ℝ}, IsPredictable ξ → avg (fun ε => frobInner (mart ξ N ε) Y) = 0 :=
    fun Y ξ hξ => tbt_avg_mart_linear
      { toFun := fun M => frobInner M Y
        map_add' := fun M M' => tbt_frobInner_add_left M M' Y
        map_smul' := fun c M => tbt_frobInner_smul_left c M Y } hξ N
  obtain ⟨σ, hσ_def⟩ : ∃ σ : (Fin N → Bool) → ℝ,
      σ = fun ε => 2 * (frobInner (W ε) X + Λ ^ 2 * frobInner (Nn ε) Z₀) := ⟨_, rfl⟩
  have hmz2 : avg σ = 0 := by
    rw [hσ_def, rad_avg_mul_left, rad_avg_add, rad_avg_mul_left, hinner X hAπ, hinner Z₀ hAperp]
    ring
  -- (27), Burkholder's inequality, for `s = 2` and `s = p`
  have hbk2 : avg (fun ε => frobNorm (E ε) ^ 2) ≤ κ' ^ 2 * avg (fun ε => frobNorm (Nn ε) ^ 2) := by
    have := tbt1_burkholder_frob hAE hAperp hκ' (fun k ε => hcorrle _ (hA.2 k ε))
      (by norm_num : (1 : ℝ) < 2)
    have h2 : pStar 2 = 2 := by unfold pStar; norm_num
    simp only [Real.rpow_two, h2] at this
    norm_num at this
    exact this
  have hbkp : avg (fun ε => frobNorm (E ε) ^ p) ≤
      Bp * κ' ^ p * avg (fun ε => frobNorm (Nn ε) ^ p) :=
    tbt1_burkholder_frob hAE hAperp hκ' (fun k ε => hcorrle _ (hA.2 k ε)) hp1
  -- the pointwise estimate: (28) with the first-order term `Df (X) 𝓔`, its splitting with `ε = τ`,
  -- and (29) with the first-order term `p |V₀|^{p−2} ⟨V₀, V_N − V₀⟩`
  set a := frobNorm X
  set x := frobSq X + Λ ^ 2 * frobSq Z₀
  have hAp : 0 ≤ a ^ (p - 2) := Real.rpow_nonneg (tbt1_frobNorm_nonneg X) _
  obtain ⟨G, hG_def⟩ : ∃ G : (Fin N → Bool) → ℝ, G = fun ε =>
    τ * Λ ^ 2 * a ^ (p - 2) * frobNorm (Nn ε) ^ 2 + τ * Λ ^ p * frobNorm (Nn ε) ^ p -
      C' * τ⁻¹ * a ^ (p - 2) * frobNorm (E ε) ^ 2 - C' * τ ^ (1 - p) * frobNorm (E ε) ^ p :=
    ⟨_, rfl⟩
  have hpt : ∀ ε, f (X + mart B N ε) + Dg (Matrix.of.symm (E ε)) +
      (δ * x ^ (p / 2) + δ * (p / 2) * x ^ (p / 2 - 1) * σ ε) + G ε ≤ F (radMart A₀ A N ε) := by
    intro ε
    simp only [hσ_def, hG_def]
    have h28 := htay X (W ε) (E ε) hXL (hWL ε) (hEL ε)
    rw [← hMt] at h28
    have := tbt_part2_pointwise hp hc0 hδ hΛ0 hτ1 hyoung hgain X (W ε) (E ε) (Nn ε) Z₀ _ _ _ h28
    rw [show F (radMart A₀ A N ε) = f (X + W ε) +
      δ * (frobSq (X + W ε) + Λ ^ 2 * frobSq (Z₀ + Nn ε)) ^ (p / 2) by
        simp only [F]; rw [hperp, hπM]]
    exact this
  -- averaging
  have havg := rad_avg_mono hpt
  rw [rad_avg_add, rad_avg_add, rad_avg_add, rad_avg_add, rad_avg_mul_left, tbt_avg_const,
    rad_avg_mul_left, hmz1, hmz2] at havg
  have hGavg : 0 ≤ avg G := by
    rw [hG_def, rad_avg_sub, rad_avg_sub, rad_avg_add, rad_avg_mul_left, rad_avg_mul_left,
      rad_avg_mul_left, rad_avg_mul_left]
    have hn2 : 0 ≤ avg (fun ε => frobNorm (Nn ε) ^ 2) := rad_avg_nonneg fun ε => sq_nonneg _
    have hnp : 0 ≤ avg (fun ε => frobNorm (Nn ε) ^ p) :=
      rad_avg_nonneg fun ε => Real.rpow_nonneg (tbt1_frobNorm_nonneg _) _
    have hτi : 0 ≤ C' * τ⁻¹ * a ^ (p - 2) := by positivity
    have hτp : 0 ≤ C' * τ ^ (1 - p) := mul_nonneg hC'0 (Real.rpow_nonneg hτ.le _)
    have t1 := mul_le_mul_of_nonneg_left hbk2 hτi
    have t2 := mul_le_mul_of_nonneg_left hbkp hτp
    have t3 : C' * τ⁻¹ * a ^ (p - 2) * (κ' ^ 2 * avg (fun ε => frobNorm (Nn ε) ^ 2)) ≤
        τ * Λ ^ 2 * a ^ (p - 2) * avg (fun ε => frobNorm (Nn ε) ^ 2) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hco1 hAp) hn2
      calc _ = C' * τ⁻¹ * κ' ^ 2 * a ^ (p - 2) * avg (fun ε => frobNorm (Nn ε) ^ 2) := by ring
        _ ≤ _ := this
    have t4 : C' * τ ^ (1 - p) * (Bp * κ' ^ p * avg (fun ε => frobNorm (Nn ε) ^ p)) ≤
        τ * Λ ^ p * avg (fun ε => frobNorm (Nn ε) ^ p) := by
      have := mul_le_mul_of_nonneg_right hco2 hnp
      calc _ = C' * τ ^ (1 - p) * (Bp * κ' ^ p) * avg (fun ε => frobNorm (Nn ε) ^ p) := by ring
        _ ≤ _ := this
    linarith
  show f X + δ * x ^ (p / 2) ≤ _
  linarith

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
