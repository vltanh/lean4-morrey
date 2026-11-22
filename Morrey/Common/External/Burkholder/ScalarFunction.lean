module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Burkholder's function for the exponent `6`, and for a real exponent `q ≥ 2`

D. L. Burkholder, *Sharp inequalities for martingales and stochastic integrals*, Colloque Paul
Lévy, Astérisque 157–158 (1988), proof of Theorem 1.1 (see also V. Vasyunin and A. Volberg 2010).
Cassese uses two properties of `u (a, b) = α (|b| − 5 |a|) (|a| + |b|)^5`, `α = 6 (5/6)^5`, for
complex `a`, `b` (the proof of Proposition 4.2, (13) and (14)): the proposition
`ScalarFunction`. It is proved here (`scalarFunction_holds`), by Burkholder's standard argument:
(13) is a polynomial inequality in `|a|`, `|b|`, and (14) follows from the sign of the second
derivative of `t ↦ u (a + t h, b + t ε h)` where both lines avoid `0`, and by approximation
elsewhere.

Remark 4.5 extends the argument to `1 < p < ∞`, `p + 2 < q < ∞`; it needs the same two properties
of `u_q (a, b) = α_q (|b| − (q − 1) |a|) (|a| + |b|)^{q−1}`, `α_q = q (1 − 1/q)^{q−1}`
(`ScalarFunctionQ q`), proved here for every real `q ≥ 2` (`scalarFunctionQ_holds`) by the same
argument: (13) by homogeneity and a one-variable calculus argument on `|a| + |b| = 1`
(`burkholderF_nonneg`), (14) from Burkholder's second-derivative identity (`phiQ_concave`).
`uq_six` identifies `u_6` with `u6`.
-/

@[expose] public section

namespace External.Burkholder

/-- Burkholder's function for the exponent `6`: `u (a, b) = α (|b| − 5 |a|) (|a| + |b|)^5` with
`α = 6 (5/6)^5 = 5^5 / 6^4`. -/
noncomputable def u6 (a b : ℂ) : ℝ :=
  5 ^ 5 / 6 ^ 4 * (‖b‖ - 5 * ‖a‖) * (‖a‖ + ‖b‖) ^ 5

/-- **Equations (13), (14)** (`eq:scalar-properties`, `eq:scalar-zigzag`) of Cassese, citing
Burkholder 1988 (proof of Theorem 1.1) and Vasyunin–Volberg:
`u (a, b) ≥ |b|^6 − 5^6 |a|^6`, and `t ↦ u (a + t h, b + t ε h)` is concave for all complex
`a`, `b`, `h` and `|ε| ≤ 1`. Proved in `scalarFunction_holds`. -/
def ScalarFunction : Prop :=
  (∀ a b : ℂ, ‖b‖ ^ 6 - 5 ^ 6 * ‖a‖ ^ 6 ≤ u6 a b) ∧
    ∀ a b h ε : ℂ, ‖ε‖ ≤ 1 →
      ConcaveOn ℝ Set.univ fun t : ℝ => u6 (a + (t : ℂ) * h) (b + (t : ℂ) * ε * h)

/-- `φ (X, Y) = α (Y − 5 X) (X + Y)^5`, so that `u (a, b) = φ (|a|, |b|)`. -/
noncomputable def burkholderPhi (X Y : ℝ) : ℝ := 5 ^ 5 / 6 ^ 4 * (Y - 5 * X) * (X + Y) ^ 5

/-- (13) in the variables `X = |a|`, `Y = |b|`: `φ (X, Y) − (Y⁶ − 5⁶ X⁶)` is
`(5X − Y)² q (X, Y) / 6⁴` with `q ≥ 0` on `[0, ∞)²`. -/
theorem burkholderPhi_ge {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Y ^ 6 - 5 ^ 6 * X ^ 6 ≤ burkholderPhi X Y := by
  have key : burkholderPhi X Y - (Y ^ 6 - 5 ^ 6 * X ^ 6) = (5 * X - Y) ^ 2 *
      (809375 * X ^ 4 + 320750 * X ^ 3 * Y + 90300 * X ^ 2 * Y ^ 2 + 18290 * X * Y ^ 3 +
        1829 * Y ^ 4) / 1296 := by
    unfold burkholderPhi; ring
  have : 0 ≤ (5 * X - Y) ^ 2 * (809375 * X ^ 4 + 320750 * X ^ 3 * Y + 90300 * X ^ 2 * Y ^ 2 +
      18290 * X * Y ^ 3 + 1829 * Y ^ 4) / 1296 := by positivity
  linarith

/-- Burkholder's computation: along a curve `t ↦ (X (t), Y (t))` of positive norms of affine
maps, with `X'' = (H − X'²) / X`, `Y'' = (K − Y'²) / Y`, `Y'² ≤ K ≤ H`, the function
`φ (X (t), Y (t))` is concave, because
`Y (φ ∘ (X, Y))'' = α (X + Y)³ (−120 X Y (X' + Y')² − 24 (X + Y) Y (H − Y'²)
  − 24 (X + Y) X (K − Y'²) − 6 (X + Y) Y (H − K)) ≤ 0`. -/
theorem burkholderPhi_concave {x y dx dy ddx ddy : ℝ → ℝ} {H K : ℝ}
    (hx0 : ∀ t, 0 < x t) (hy0 : ∀ t, 0 < y t)
    (hx : ∀ t, HasDerivAt x (dx t) t) (hy : ∀ t, HasDerivAt y (dy t) t)
    (hdx : ∀ t, HasDerivAt dx (ddx t) t) (hdy : ∀ t, HasDerivAt dy (ddy t) t)
    (hddx : ∀ t, ddx t = (H - dx t ^ 2) / x t) (hddy : ∀ t, ddy t = (K - dy t ^ 2) / y t)
    (hKH : K ≤ H) (hdyK : ∀ t, dy t ^ 2 ≤ K) :
    ConcaveOn ℝ Set.univ fun t => burkholderPhi (x t) (y t) := by
  set α : ℝ := 5 ^ 5 / 6 ^ 4
  set G' : ℝ → ℝ := fun t => α * ((dy t - 5 * dx t) * (x t + y t) ^ 5 +
    (y t - 5 * x t) * (5 * (x t + y t) ^ 4 * (dx t + dy t)))
  set G'' : ℝ → ℝ := fun t => α * ((ddy t - 5 * ddx t) * (x t + y t) ^ 5 +
    (dy t - 5 * dx t) * (5 * (x t + y t) ^ 4 * (dx t + dy t)) +
    ((dy t - 5 * dx t) * (5 * (x t + y t) ^ 4 * (dx t + dy t)) +
      (y t - 5 * x t) * (5 * (4 * (x t + y t) ^ 3 * (dx t + dy t)) * (dx t + dy t) +
        5 * (x t + y t) ^ 4 * (ddx t + ddy t))))
  have hG : ∀ t, HasDerivAt (fun t => burkholderPhi (x t) (y t)) (G' t) t := fun t => by
    have := (((hy t).fun_sub ((hx t).const_mul 5)).const_mul α).fun_mul
      (((hx t).fun_add (hy t)).fun_pow 5)
    convert this using 1
    · rfl
    · simp only [G']; norm_num; ring
  have hG' : ∀ t, HasDerivAt G' (G'' t) t := fun t => by
    have h1 := ((hdy t).fun_sub ((hdx t).const_mul 5)).fun_mul (((hx t).fun_add (hy t)).fun_pow 5)
    have h2 := ((hy t).fun_sub ((hx t).const_mul 5)).fun_mul
      ((((hx t).fun_add (hy t)).fun_pow 4).const_mul 5 |>.fun_mul ((hdx t).fun_add (hdy t)))
    have := (h1.fun_add h2).const_mul α
    convert this using 1
  refine concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
    (fun t _ => (hG t).continuousAt.continuousWithinAt)
    (fun t _ => (hG t).hasDerivWithinAt) (fun t _ => (hG' t).hasDerivWithinAt) fun t _ => ?_
  have hx0' := hx0 t
  have hy0' := hy0 t
  have hs : 0 < x t + y t := by linarith
  have hcert : y t * G'' t = α * (x t + y t) ^ 3 * (-120 * x t * y t * (dx t + dy t) ^ 2 -
      24 * (x t + y t) * y t * (H - dy t ^ 2) - 24 * (x t + y t) * x t * (K - dy t ^ 2) -
      6 * (x t + y t) * y t * (H - K)) := by
    simp only [G'', hddx, hddy]
    field_simp
    ring
  have hK := hdyK t
  have hbr : -120 * x t * y t * (dx t + dy t) ^ 2 -
      24 * (x t + y t) * y t * (H - dy t ^ 2) - 24 * (x t + y t) * x t * (K - dy t ^ 2) -
      6 * (x t + y t) * y t * (H - K) ≤ 0 := by
    have e1 : 0 ≤ 120 * x t * y t * (dx t + dy t) ^ 2 := by positivity
    have e2 : 0 ≤ 24 * (x t + y t) * y t * (H - dy t ^ 2) :=
      mul_nonneg (by positivity) (by linarith)
    have e3 : 0 ≤ 24 * (x t + y t) * x t * (K - dy t ^ 2) :=
      mul_nonneg (by positivity) (by linarith)
    have e4 : 0 ≤ 6 * (x t + y t) * y t * (H - K) := mul_nonneg (by positivity) (by linarith)
    linarith
  have : y t * G'' t ≤ 0 := by
    rw [hcert]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hbr
  by_contra hc
  push Not at hc
  have := mul_pos hy0' hc
  linarith


/-- The norm of `c + t w` and its first two derivatives in `t`, where it does not vanish:
`|c + t w|' = ⟨c + t w, w⟩ / |c + t w|` and `|c + t w|'' = (|w|² − |c + t w|'²) / |c + t w|`. -/
theorem norm_line_hasDerivAt {c w : ℂ} (hc : ∀ t : ℝ, c + t * w ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ‖c + t * w‖)
      ((w.re * (c.re + t * w.re) + w.im * (c.im + t * w.im)) / ‖c + t * w‖) t ∧
    HasDerivAt (fun t : ℝ => (w.re * (c.re + t * w.re) + w.im * (c.im + t * w.im)) / ‖c + t * w‖)
      ((‖w‖ ^ 2 - ((w.re * (c.re + t * w.re) + w.im * (c.im + t * w.im)) / ‖c + t * w‖) ^ 2) /
        ‖c + t * w‖) t := by
  have hn : ∀ s : ℝ, ‖c + s * w‖ = √((c.re + s * w.re) ^ 2 + (c.im + s * w.im) ^ 2) := fun s => by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; simp
  have hpos : ∀ s : ℝ, 0 < (c.re + s * w.re) ^ 2 + (c.im + s * w.im) ^ 2 := fun s => by
    have := norm_pos_iff.2 (hc s)
    rw [hn] at this
    exact Real.sqrt_pos.1 this
  have hP : HasDerivAt (fun s : ℝ => (c.re + s * w.re) ^ 2 + (c.im + s * w.im) ^ 2)
      (2 * (w.re * (c.re + t * w.re) + w.im * (c.im + t * w.im))) t := by
    have h1 := (((hasDerivAt_id' t).mul_const w.re).const_add c.re).fun_pow 2
    have h2 := (((hasDerivAt_id' t).mul_const w.im).const_add c.im).fun_pow 2
    convert h1.fun_add h2 using 1
    ring
  have hx : HasDerivAt (fun t : ℝ => ‖c + t * w‖)
      ((w.re * (c.re + t * w.re) + w.im * (c.im + t * w.im)) / ‖c + t * w‖) t := by
    have := hP.sqrt (hpos t).ne'
    simp only [hn]
    convert this using 1
    field_simp
  refine ⟨hx, ?_⟩
  have hR : HasDerivAt (fun s : ℝ => w.re * (c.re + s * w.re) + w.im * (c.im + s * w.im))
      (w.re ^ 2 + w.im ^ 2) t := by
    have h1 := (((hasDerivAt_id' t).mul_const w.re).const_add c.re).const_mul w.re
    have h2 := (((hasDerivAt_id' t).mul_const w.im).const_add c.im).const_mul w.im
    convert h1.fun_add h2 using 1
    ring
  have hx0 : ‖c + t * w‖ ≠ 0 := norm_ne_zero_iff.2 (hc t)
  convert hR.div hx hx0 using 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  field_simp

/-- Cauchy–Schwarz: `|c + t w|'² ≤ |w|²`. -/
theorem norm_line_deriv_sq_le {c w : ℂ} (hc : ∀ t : ℝ, c + t * w ≠ 0) (t : ℝ) :
    ((w.re * (c.re + t * w.re) + w.im * (c.im + t * w.im)) / ‖c + t * w‖) ^ 2 ≤ ‖w‖ ^ 2 := by
  have hx0 : 0 < ‖c + t * w‖ := norm_pos_iff.2 (hc t)
  have hsq : ‖c + t * w‖ ^ 2 = (c.re + t * w.re) ^ 2 + (c.im + t * w.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [div_pow, div_le_iff₀ (by positivity), hsq, Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg (w.re * (c.im + t * w.im) - w.im * (c.re + t * w.re))]

/-- (14) where both lines avoid `0`: `t ↦ u (a + t h, b + t k)` is concave if `|k| ≤ |h|`. -/
theorem u6_concave_generic {a b h k : ℂ} (hk : ‖k‖ ≤ ‖h‖) (ha : ∀ t : ℝ, a + t * h ≠ 0)
    (hb : ∀ t : ℝ, b + t * k ≠ 0) :
    ConcaveOn ℝ Set.univ fun t : ℝ => u6 (a + t * h) (b + t * k) := by
  have := burkholderPhi_concave (H := ‖h‖ ^ 2) (K := ‖k‖ ^ 2)
    (fun t => norm_pos_iff.2 (ha t)) (fun t => norm_pos_iff.2 (hb t))
    (fun t => (norm_line_hasDerivAt ha t).1) (fun t => (norm_line_hasDerivAt hb t).1)
    (fun t => (norm_line_hasDerivAt ha t).2) (fun t => (norm_line_hasDerivAt hb t).2)
    (fun t => rfl) (fun t => rfl) (pow_le_pow_left₀ (norm_nonneg _) hk 2)
    (norm_line_deriv_sq_le hb)
  exact this


open Filter Topology in
/-- Every `c` is a limit of points `c'` for which the line `c' + t w` avoids `0`. -/
theorem exists_seq_line_ne_zero (c w : ℂ) :
    ∃ c' : ℕ → ℂ, Tendsto c' atTop (𝓝 c) ∧ ∀ (m : ℕ) (t : ℝ), c' m + t * w ≠ 0 := by
  have hδ : ∀ σ : ℝ, Tendsto (fun m : ℕ => ((σ * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    intro σ
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul σ
    rw [mul_zero] at h
    have := (Complex.continuous_ofReal.tendsto 0).comp h
    rw [Complex.ofReal_zero] at this
    exact this
  have hδpos : ∀ m : ℕ, 0 < 1 / ((m : ℝ) + 1) := fun m => by positivity
  by_cases hw : w = 0
  · subst hw
    by_cases hc : c = 0
    · subst hc
      refine ⟨fun m => ((1 * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ), hδ 1, fun m t => ?_⟩
      simp only [mul_zero, add_zero, ne_eq, Complex.ofReal_eq_zero, one_mul]
      exact (hδpos m).ne'
    · exact ⟨fun _ => c, tendsto_const_nhds, fun m t => by simpa using hc⟩
  · set z := c / w
    set σ : ℝ := if 0 ≤ z.im then 1 else -1
    refine ⟨fun m => c + ((σ * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ) * Complex.I * w, ?_, fun m t => ?_⟩
    · have := (((hδ σ).mul_const Complex.I).mul_const w).const_add c
      simpa using this
    · have hc : c = z * w := (div_mul_cancel₀ c hw).symm
      rw [hc, show z * w + ((σ * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ) * Complex.I * w + t * w =
        (z + ((σ * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ) * Complex.I + t) * w by ring]
      refine mul_ne_zero (fun h0 => ?_) hw
      have him := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.zero_im, mul_zero, mul_one, add_zero] at him
      have h1 := hδpos m
      simp only [σ] at him
      split_ifs at him with hz <;> nlinarith

open Filter Topology in
/-- A pointwise limit of concave functions is concave. -/
theorem concaveOn_univ_of_tendsto {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ}
    (hF : ∀ m, ConcaveOn ℝ Set.univ (F m)) (hlim : ∀ t, Tendsto (fun m => F m t) atTop (𝓝 (G t))) :
    ConcaveOn ℝ Set.univ G :=
  ⟨convex_univ, fun x _ y _ p q hp hq hpq =>
    le_of_tendsto_of_tendsto' (((hlim x).const_smul p).add ((hlim y).const_smul q)) (hlim _)
      fun m => (hF m).2 trivial trivial hp hq hpq⟩

theorem continuous_u6 : Continuous fun z : ℂ × ℂ => u6 z.1 z.2 := by
  unfold u6; fun_prop

open Filter Topology in
/-- **Equations (13), (14)** (`eq:scalar-properties`, `eq:scalar-zigzag`), Burkholder's function
for the exponent `6`.

Proof: Burkholder's standard argument (Burkholder 1988, proof of Theorem 1.1; see also
Burkholder 1984, and Osękowski 2012, Section 3.1). (13) is the inequality `φ (X, Y) ≥ Y⁶ − 5⁶ X⁶`
for `φ (X, Y) = α (Y − 5X) (X + Y)^5` on `[0, ∞)²`, whose difference is `(5X − Y)²` times a
quartic with positive coefficients (`burkholderPhi_ge`). (14): where `a + t h` and `b + t ε h` do
not vanish, `X (t) = |a + t h|` and `Y (t) = |b + t ε h|` are smooth, with
`X'' = (|h|² − X'²) / X`, `Y'' = (|εh|² − Y'²) / Y`, `Y'² ≤ |ε h|² ≤ |h|²`, and the second
derivative of `φ (X, Y)` is a sum of nonpositive terms (`burkholderPhi_concave`); in general,
`a` and `b` are limits of points for which the lines avoid `0`
(`exists_seq_line_ne_zero`), and concavity passes to pointwise limits. -/
theorem scalarFunction_holds : ScalarFunction := by
  refine ⟨fun a b => burkholderPhi_ge (norm_nonneg a) (norm_nonneg b), fun a b h ε hε => ?_⟩
  have hk : ‖ε * h‖ ≤ ‖h‖ := by
    rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg h) hε
  have heq : (fun t : ℝ => u6 (a + (t : ℂ) * h) (b + (t : ℂ) * ε * h)) =
      fun t : ℝ => u6 (a + (t : ℂ) * h) (b + (t : ℂ) * (ε * h)) := by
    funext t; rw [mul_assoc]
  rw [heq]
  by_cases hh : h = 0
  · subst hh; simpa using concaveOn_const (c := u6 a b) convex_univ
  obtain ⟨a', ha', ha'0⟩ := exists_seq_line_ne_zero a h
  obtain ⟨b', hb', hb'0⟩ := exists_seq_line_ne_zero b (ε * h)
  refine concaveOn_univ_of_tendsto (F := fun m t => u6 (a' m + t * h) (b' m + t * (ε * h)))
    (fun m => u6_concave_generic hk (ha'0 m) (hb'0 m)) fun t => ?_
  exact (continuous_u6.tendsto _).comp
    ((ha'.add_const ((t : ℂ) * h)).prodMk_nhds (hb'.add_const ((t : ℂ) * (ε * h))))

/-! ### Burkholder's function for a real exponent `q ≥ 2`

The same two properties for `u_q (a, b) = α_q (|b| − (q − 1) |a|) (|a| + |b|)^{q−1}`,
`α_q = q (1 − 1/q)^{q−1}`, and every real `q ≥ 2` (Burkholder 1984, 1988; Remark 4.5 of Cassese
uses them for `q = p + 3`). For `q < 2` the formula is not Burkholder's function (his function for
`1 < q < 2` has the constant `1/(q − 1)` in place of `q − 1`), and (13) fails there:
`u_q (0, b) = α_q |b|^q` with `α_q < 1` for `q` near `1`. -/

/-- `α_q = q (1 − 1/q)^{q−1}`. -/
noncomputable def alphaQ (q : ℝ) : ℝ := q * (1 - 1 / q) ^ (q - 1)

/-- Burkholder's function for the exponent `q`:
`u_q (a, b) = α_q (|b| − (q − 1) |a|) (|a| + |b|)^{q−1}`. -/
noncomputable def uq (q : ℝ) (a b : ℂ) : ℝ :=
  alphaQ q * (‖b‖ - (q - 1) * ‖a‖) * (‖a‖ + ‖b‖) ^ (q - 1)

/-- **Equations (13), (14)** for the exponent `q` (Burkholder 1988, proof of Theorem 1.1):
`u_q (a, b) ≥ |b|^q − (q − 1)^q |a|^q`, and `t ↦ u_q (a + t h, b + t ε h)` is concave for all
complex `a`, `b`, `h` and `|ε| ≤ 1`. Proved for `q ≥ 2` in `scalarFunctionQ_holds`. -/
def ScalarFunctionQ (q : ℝ) : Prop :=
  (∀ a b : ℂ, ‖b‖ ^ q - (q - 1) ^ q * ‖a‖ ^ q ≤ uq q a b) ∧
    ∀ a b h ε : ℂ, ‖ε‖ ≤ 1 →
      ConcaveOn ℝ Set.univ fun t : ℝ => uq q (a + (t : ℂ) * h) (b + (t : ℂ) * ε * h)

/-- `φ_q (X, Y) = α_q (Y − (q − 1) X) (X + Y)^{q−1}`, so that `u_q (a, b) = φ_q (|a|, |b|)`. -/
noncomputable def phiQ (q X Y : ℝ) : ℝ := alphaQ q * (Y - (q - 1) * X) * (X + Y) ^ (q - 1)

/-- `α_q ≥ 1` for `q ≥ 2` (Bernoulli: `(1 − 1/q)^{q−1} ≥ 1 − (q − 1)/q = 1/q`). -/
theorem one_le_alphaQ {q : ℝ} (hq : 2 ≤ q) : 1 ≤ alphaQ q := by
  have hq0 : 0 < q := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := -(1 / q)) (by
    rw [neg_le_neg_iff, div_le_one hq0]; linarith) (p := q - 1) (by linarith)
  rw [← sub_eq_add_neg] at h
  unfold alphaQ
  have e : 1 + (q - 1) * -(1 / q) = 1 / q := by field_simp; ring
  rw [e] at h
  calc (1 : ℝ) = q * (1 / q) := by field_simp
    _ ≤ q * (1 - 1 / q) ^ (q - 1) := mul_le_mul_of_nonneg_left h hq0.le

/-- The one-variable function `h (t) = (1 − t)^{q−1} + (q − 1)^q t^{q−1}` of the proof of (13):
`h (1/q) = α_q`. -/
theorem burkholderH_inv {q : ℝ} (hq : 2 ≤ q) :
    (1 - 1 / q) ^ (q - 1) + (q - 1) ^ q * (1 / q) ^ (q - 1) = alphaQ q := by
  have hq0 : 0 < q := by linarith
  have hc : 0 < q - 1 := by linarith
  have e1 : 1 - 1 / q = (q - 1) * (1 / q) := by field_simp
  have e2 : (q - 1) ^ q = (q - 1) * (q - 1) ^ (q - 1) := by
    rw [Real.rpow_sub_one hc.ne', mul_div_cancel₀ _ hc.ne']
  rw [e2, mul_assoc, ← Real.mul_rpow hc.le (by positivity), ← e1, alphaQ]
  ring

/-- For `q = 6`, `u_q` is the function `u6` of Proposition 4.2. -/
theorem uq_six : uq 6 = u6 := by
  funext a b
  have h1 : (1 - 1 / 6 : ℝ) ^ ((6 : ℝ) - 1) = (5 / 6) ^ 5 := by
    rw [show (6 : ℝ) - 1 = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h2 : (‖a‖ + ‖b‖) ^ ((6 : ℝ) - 1) = (‖a‖ + ‖b‖) ^ 5 := by
    rw [show (6 : ℝ) - 1 = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [uq, alphaQ, h1, h2, u6]
  norm_num

/-- (13) on the segment `X + Y = 1`: `F (t) = α_q (1 − q t) − (1 − t)^q + (q − 1)^q t^q ≥ 0` for
`t ∈ [0, 1]`. `F' = q (h − α_q)` with `h (t) = (1 − t)^{q−1} + (q − 1)^q t^{q−1}` convex,
`h (0) = 1 ≤ α_q = h (1/q)`, so `h ≤ α_q` on `[0, 1/q]` and `h ≥ α_q` on `[1/q, 1]`: `F` decreases
and then increases, and `F (1/q) = 0`. -/
theorem burkholderF_nonneg {q : ℝ} (hq : 2 ≤ q) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ alphaQ q * (1 - q * t) - (1 - t) ^ q + (q - 1) ^ q * t ^ q := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hc : 0 < q - 1 := by linarith
  set α := alphaQ q with hα
  set c := (q - 1) ^ q with hcdef
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun t => α * (1 - q * t) - (1 - t) ^ q + c * t ^ q :=
    ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun t => (1 - t) ^ (q - 1) + c * t ^ (q - 1) := ⟨_, rfl⟩
  have hF' : ∀ t, HasDerivAt F (q * (h t - α)) t := fun t => by
    have h1 := ((hasDerivAt_id' t).const_sub 1).rpow_const (p := q) (Or.inr hq1)
    have h2 := (Real.hasDerivAt_rpow_const (x := t) (Or.inr hq1)).const_mul c
    have h3 := (((hasDerivAt_id' t).const_mul q).const_sub 1).const_mul α
    have := (h3.fun_sub h1).fun_add h2
    rw [hF, hh]
    convert this using 1
    ring
  have hcont : Continuous F := by
    rw [hF]
    exact ((continuous_const.mul (continuous_const.sub (continuous_const.mul continuous_id))).sub
      ((continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hq0.le)).add
      (continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr hq0.le))
  -- `h` is convex on `[0, 1]`
  have hconv : ConvexOn ℝ (Set.Icc 0 1) h := by
    have hr : 1 ≤ q - 1 := by linarith
    refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
    have h1 := (convexOn_rpow hr).2 (show 1 - x ∈ Set.Ici (0 : ℝ) by simp; linarith [hx.2])
      (show 1 - y ∈ Set.Ici (0 : ℝ) by simp; linarith [hy.2]) ha hb hab
    have h2 := (convexOn_rpow hr).2 (show x ∈ Set.Ici (0 : ℝ) from hx.1)
      (show y ∈ Set.Ici (0 : ℝ) from hy.1) ha hb hab
    have e : 1 - (a • x + b • y) = a • (1 - x) + b • (1 - y) := by
      simp only [smul_eq_mul]; rw [show b = 1 - a by linarith]; ring
    simp only [smul_eq_mul] at h1 h2 e ⊢
    rw [hh]
    simp only
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h2 hc0]
  have hα1 : 1 ≤ α := one_le_alphaQ hq
  have hh0 : h 0 = 1 := by
    simp [hh, Real.zero_rpow hc.ne']
  have hhq : h (1 / q) = α := by rw [hh]; exact burkholderH_inv hq
  have hq' : 1 / q ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, by rw [div_le_one hq0]; linarith⟩
  have hF0 : F (1 / q) = 0 := by
    rw [hF]
    simp only
    have e1 : 1 - 1 / q = (q - 1) * (1 / q) := by field_simp
    rw [mul_one_div_cancel hq0.ne', sub_self, mul_zero, e1, Real.mul_rpow hc.le (by positivity)]
    ring
  rcases le_total t (1 / q) with htq | htq
  · -- on `[0, 1/q]`, `h ≤ α`, so `F` decreases to `F (1/q) = 0`
    have hanti : AntitoneOn F (Set.Icc 0 (1 / q)) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (1 / q))
        hcont.continuousOn (fun x _ => (hF' x).hasDerivWithinAt) fun x hx => ?_
      rw [interior_Icc] at hx
      -- `x = (1 − λ) 0 + λ (1/q)`, `λ = q x`
      have hl0 : 0 ≤ q * x := by nlinarith [hx.1]
      have hl1 : q * x ≤ 1 := by
        have := hx.2.le; rw [le_div_iff₀ hq0] at this; linarith
      have := hconv.2 (Set.left_mem_Icc.2 zero_le_one) hq' (show 0 ≤ 1 - q * x by linarith) hl0
        (by ring)
      simp only [smul_eq_mul, mul_zero, zero_add] at this
      rw [show q * x * (1 / q) = x by field_simp, hh0, hhq] at this
      have : h x ≤ α := by nlinarith
      nlinarith
    have := hanti ⟨ht0, htq⟩ ⟨hq'.1, le_rfl⟩ htq
    rw [hF] at this hF0
    simp only at this hF0
    linarith
  · -- on `[1/q, 1]`, `h ≥ α`, so `F` increases from `F (1/q) = 0`
    have hmono : MonotoneOn F (Set.Icc (1 / q) 1) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (1 / q) 1)
        hcont.continuousOn (fun x _ => (hF' x).hasDerivWithinAt) fun x hx => ?_
      rw [interior_Icc] at hx
      have hx0 : 0 < x := lt_of_le_of_lt hq'.1 hx.1
      have hx1 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0.le, hx.2.le⟩
      -- `1/q = (1 − μ) 0 + μ x`, `μ = 1 / (q x)`
      have hqx : 1 < q * x := by
        have := hx.1; rw [div_lt_iff₀ hq0] at this; linarith
      set μ := 1 / (q * x)
      have hμ0 : 0 < μ := by positivity
      have hμ1 : μ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have := hconv.2 (Set.left_mem_Icc.2 zero_le_one) hx1 (show 0 ≤ 1 - μ by linarith) hμ0.le
        (by ring)
      simp only [smul_eq_mul, mul_zero, zero_add] at this
      rw [show μ * x = 1 / q by simp only [μ]; field_simp, hh0, hhq] at this
      have : α ≤ h x := by
        have h1 : μ * α ≤ μ * h x := by nlinarith
        exact le_of_mul_le_mul_left h1 hμ0
      nlinarith
    have := hmono ⟨le_rfl, hq'.2⟩ ⟨htq, ht1⟩ htq
    rw [hF] at this hF0
    simp only at this hF0
    linarith

/-- (13) in the variables `X = |a|`, `Y = |b|`: `φ_q (X, Y) ≥ Y^q − (q − 1)^q X^q` on `[0, ∞)²`,
by homogeneity from `burkholderF_nonneg` on `X + Y = 1`. -/
theorem phiQ_ge {q : ℝ} (hq : 2 ≤ q) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Y ^ q - (q - 1) ^ q * X ^ q ≤ phiQ q X Y := by
  have hq0 : 0 < q := by linarith
  rcases (add_nonneg hX hY).eq_or_lt with hs | hs
  · have hX0 : X = 0 := by linarith
    have hY0 : Y = 0 := by linarith
    simp [phiQ, hX0, hY0, Real.zero_rpow hq0.ne']
  set s := X + Y
  set t := X / s
  have hX' : X = s * t := by simp only [t]; field_simp
  have hY' : Y = s * (1 - t) := by rw [mul_sub, mul_one, ← hX']; simp only [s]; ring
  have ht0 : 0 ≤ t := div_nonneg hX hs.le
  have ht1 : t ≤ 1 := by rw [div_le_one hs]; linarith
  have key := burkholderF_nonneg hq ht0 ht1
  have hps : 0 < s ^ q := Real.rpow_pos_of_pos hs q
  have e : phiQ q X Y - (Y ^ q - (q - 1) ^ q * X ^ q) =
      s ^ q * (alphaQ q * (1 - q * t) - (1 - t) ^ q + (q - 1) ^ q * t ^ q) := by
    have hsq : s ^ (q - 1) * s = s ^ q := by
      rw [Real.rpow_sub_one hs.ne', div_mul_cancel₀ _ hs.ne']
    have hXq : X ^ q = s ^ q * t ^ q := by rw [hX', Real.mul_rpow hs.le ht0]
    have hYq : Y ^ q = s ^ q * (1 - t) ^ q := by
      rw [hY', Real.mul_rpow hs.le (by linarith)]
    rw [hXq, hYq, phiQ, show X + Y = s from rfl, ← hsq, hX', hY']
    ring
  have : 0 ≤ s ^ q * (alphaQ q * (1 - q * t) - (1 - t) ^ q + (q - 1) ^ q * t ^ q) :=
    mul_nonneg hps.le key
  linarith

/-- Burkholder's computation for the exponent `q ≥ 2`: along a curve `t ↦ (X (t), Y (t))` of
positive norms of affine maps, with `X'' = (H − X'²) / X`, `Y'' = (K − Y'²) / Y`, `Y'² ≤ K ≤ H`,
the function `φ_q (X (t), Y (t))` is concave, because, with `S = X + Y`,
`Y (φ_q ∘ (X, Y))'' = −α_q q S^{q−3} ((q − 1) S Y (H − K) + (q − 2) S² (K − Y'²)
  + (q − 1) (q − 2) X Y (X' + Y')²) ≤ 0`. -/
theorem phiQ_concave {q : ℝ} (hq : 2 ≤ q) {x y dx dy ddx ddy : ℝ → ℝ} {H K : ℝ}
    (hx0 : ∀ t, 0 < x t) (hy0 : ∀ t, 0 < y t)
    (hx : ∀ t, HasDerivAt x (dx t) t) (hy : ∀ t, HasDerivAt y (dy t) t)
    (hdx : ∀ t, HasDerivAt dx (ddx t) t) (hdy : ∀ t, HasDerivAt dy (ddy t) t)
    (hddx : ∀ t, ddx t = (H - dx t ^ 2) / x t) (hddy : ∀ t, ddy t = (K - dy t ^ 2) / y t)
    (hKH : K ≤ H) (hdyK : ∀ t, dy t ^ 2 ≤ K) :
    ConcaveOn ℝ Set.univ fun t => phiQ q (x t) (y t) := by
  set α : ℝ := alphaQ q
  have hα : 0 ≤ α := le_trans zero_le_one (one_le_alphaQ hq)
  have hs : ∀ t, 0 < x t + y t := fun t => add_pos (hx0 t) (hy0 t)
  obtain ⟨G', hG'd⟩ : ∃ G' : ℝ → ℝ, G' = fun t => α * ((dy t - (q - 1) * dx t) *
      (x t + y t) ^ (q - 1) + (y t - (q - 1) * x t) * ((dx t + dy t) * (q - 1) *
        (x t + y t) ^ (q - 1 - 1))) := ⟨_, rfl⟩
  obtain ⟨G'', hG''d⟩ : ∃ G'' : ℝ → ℝ, G'' = fun t => α * ((ddy t - (q - 1) * ddx t) *
      (x t + y t) ^ (q - 1) +
    (dy t - (q - 1) * dx t) * ((dx t + dy t) * (q - 1) * (x t + y t) ^ (q - 1 - 1)) +
    ((dy t - (q - 1) * dx t) * ((dx t + dy t) * (q - 1) * (x t + y t) ^ (q - 1 - 1)) +
      (y t - (q - 1) * x t) * ((ddx t + ddy t) * (q - 1) * (x t + y t) ^ (q - 1 - 1) +
        (dx t + dy t) * (q - 1) * ((dx t + dy t) * (q - 1 - 1) *
          (x t + y t) ^ (q - 1 - 1 - 1))))) := ⟨_, rfl⟩
  have hG : ∀ t, HasDerivAt (fun t => phiQ q (x t) (y t)) (G' t) t := fun t => by
    have := (((hy t).fun_sub ((hx t).const_mul (q - 1))).const_mul α).fun_mul
      (((hx t).fun_add (hy t)).rpow_const (p := q - 1) (Or.inl (hs t).ne'))
    rw [hG'd]
    exact this.congr_deriv (by beta_reduce; ring)
  have hG' : ∀ t, HasDerivAt G' (G'' t) t := fun t => by
    have h1 := ((hdy t).fun_sub ((hdx t).const_mul (q - 1))).fun_mul
      (((hx t).fun_add (hy t)).rpow_const (p := q - 1) (Or.inl (hs t).ne'))
    have h2 := ((hy t).fun_sub ((hx t).const_mul (q - 1))).fun_mul
      ((((hdx t).fun_add (hdy t)).mul_const (q - 1)).fun_mul
        (((hx t).fun_add (hy t)).rpow_const (p := q - 1 - 1) (Or.inl (hs t).ne')))
    have := (h1.fun_add h2).const_mul α
    rw [hG'd, hG''d]
    exact this.congr_deriv (by beta_reduce; ring)
  refine concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
    (fun t _ => (hG t).continuousAt.continuousWithinAt)
    (fun t _ => (hG t).hasDerivWithinAt) (fun t _ => (hG' t).hasDerivWithinAt) fun t _ => ?_
  have hx0' := hx0 t
  have hy0' := hy0 t
  have hst := hs t
  obtain ⟨T, hT⟩ : ∃ T, T = (x t + y t) ^ (q - 1 - 1 - 1) := ⟨_, rfl⟩
  have hT0 : 0 < T := hT ▸ Real.rpow_pos_of_pos hst _
  have hS1 : (x t + y t) ^ (q - 1) = T * (x t + y t) ^ 2 := by
    rw [hT, ← Real.rpow_natCast, ← Real.rpow_add hst]; congr 1; push_cast; ring
  have hS2 : (x t + y t) ^ (q - 1 - 1) = T * (x t + y t) := by
    rw [hT, ← Real.rpow_add_one hst.ne']; congr 1; ring
  have hxd : x t * ddx t = H - dx t ^ 2 := by rw [hddx t]; field_simp
  have hyd : y t * ddy t = K - dy t ^ 2 := by rw [hddy t]; field_simp
  have hcert : y t * G'' t = -(α * q * T * ((q - 1) * (x t + y t) * y t * (H - K) +
      (q - 2) * (x t + y t) ^ 2 * (K - dy t ^ 2) +
        (q - 1) * (q - 2) * x t * y t * (dx t + dy t) ^ 2)) := by
    rw [hG''d]
    simp only [hS1, hS2, ← hT]
    linear_combination (-(α * q * (q - 1) * y t * T * (x t + y t))) * hxd +
      (α * T * (x t + y t) * q * (y t - (q - 2) * x t)) * hyd
  have hK := hdyK t
  have hbr : 0 ≤ (q - 1) * (x t + y t) * y t * (H - K) +
      (q - 2) * (x t + y t) ^ 2 * (K - dy t ^ 2) +
        (q - 1) * (q - 2) * x t * y t * (dx t + dy t) ^ 2 := by
    have hq1 : 0 ≤ q - 1 := by linarith
    have hq2 : 0 ≤ q - 2 := by linarith
    have e1 : 0 ≤ (q - 1) * (x t + y t) * y t * (H - K) :=
      mul_nonneg (by positivity) (by linarith)
    have e2 : 0 ≤ (q - 2) * (x t + y t) ^ 2 * (K - dy t ^ 2) :=
      mul_nonneg (by positivity) (by linarith)
    have e3 : 0 ≤ (q - 1) * (q - 2) * x t * y t * (dx t + dy t) ^ 2 := by positivity
    linarith
  have : y t * G'' t ≤ 0 := by
    rw [hcert, neg_nonpos]
    exact mul_nonneg (by positivity) hbr
  by_contra hc
  push Not at hc
  have := mul_pos hy0' hc
  linarith

/-- (14) for the exponent `q ≥ 2` where both lines avoid `0`: `t ↦ u_q (a + t h, b + t k)` is
concave if `|k| ≤ |h|`. -/
theorem uq_concave_generic {q : ℝ} (hq : 2 ≤ q) {a b h k : ℂ} (hk : ‖k‖ ≤ ‖h‖)
    (ha : ∀ t : ℝ, a + t * h ≠ 0) (hb : ∀ t : ℝ, b + t * k ≠ 0) :
    ConcaveOn ℝ Set.univ fun t : ℝ => uq q (a + t * h) (b + t * k) :=
  phiQ_concave hq (H := ‖h‖ ^ 2) (K := ‖k‖ ^ 2)
    (fun t => norm_pos_iff.2 (ha t)) (fun t => norm_pos_iff.2 (hb t))
    (fun t => (norm_line_hasDerivAt ha t).1) (fun t => (norm_line_hasDerivAt hb t).1)
    (fun t => (norm_line_hasDerivAt ha t).2) (fun t => (norm_line_hasDerivAt hb t).2)
    (fun _ => rfl) (fun _ => rfl) (pow_le_pow_left₀ (norm_nonneg _) hk 2)
    (norm_line_deriv_sq_le hb)

/-- `u_q` is `q`-homogeneous: `u_q (t a, t b) = |t|^q u_q (a, b)` for real `t`. -/
theorem uq_smul {q : ℝ} (hq : 1 ≤ q) (t : ℝ) (a b : ℂ) :
    uq q ((t : ℂ) * a) ((t : ℂ) * b) = |t| ^ q * uq q a b := by
  have hn : ∀ z : ℂ, ‖(t : ℂ) * z‖ = |t| * ‖z‖ := fun z => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hpow : |t| ^ q = |t| * |t| ^ (q - 1) := by
    conv_lhs => rw [show q = 1 + (q - 1) by ring]
    rw [Real.rpow_add' (abs_nonneg t) (by ring_nf; linarith), Real.rpow_one]
  simp only [uq, hn]
  rw [show |t| * ‖a‖ + |t| * ‖b‖ = |t| * (‖a‖ + ‖b‖) by ring,
    Real.mul_rpow (abs_nonneg t) (by positivity), hpow]
  ring

theorem continuous_uq {q : ℝ} (hq : 1 ≤ q) : Continuous fun z : ℂ × ℂ => uq q z.1 z.2 := by
  unfold uq
  exact (continuous_const.mul ((continuous_norm.comp continuous_snd).sub
    (continuous_const.mul (continuous_norm.comp continuous_fst)))).mul
    (((continuous_norm.comp continuous_fst).add (continuous_norm.comp continuous_snd)).rpow_const
      fun _ => Or.inr (by linarith))

open Filter Topology in
/-- **Equations (13), (14) for a real exponent `q ≥ 2`** (Remark 4.5): Burkholder's function
`u_q`. (The paper states them for `q = 6`, `scalarFunction_holds`.)

Proof: Burkholder's standard argument (Burkholder 1988, proof of Theorem 1.1; Osękowski 2012,
Section 3.1), as for `q = 6` (`scalarFunction_holds`). (13): by homogeneity it suffices to take
`|a| + |b| = 1`, where the difference is `F (t)`, `t = |a|`, with `F (1/q) = 0` and
`F' = q (h − α_q)` for the convex `h (t) = (1 − t)^{q−1} + (q − 1)^q t^{q−1}`
(`burkholderF_nonneg`, `phiQ_ge`). (14): where both lines avoid `0`, the second derivative of
`φ_q (|a + t h|, |b + t ε h|)` is a sum of nonpositive terms (`phiQ_concave`); in general, `a`
and `b` are limits of points for which the lines avoid `0` (`exists_seq_line_ne_zero`), and
concavity passes to pointwise limits. -/
theorem scalarFunctionQ_holds {q : ℝ} (hq : 2 ≤ q) : ScalarFunctionQ q := by
  refine ⟨fun a b => phiQ_ge hq (norm_nonneg a) (norm_nonneg b), fun a b h ε hε => ?_⟩
  have hk : ‖ε * h‖ ≤ ‖h‖ := by
    rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg h) hε
  have heq : (fun t : ℝ => uq q (a + (t : ℂ) * h) (b + (t : ℂ) * ε * h)) =
      fun t : ℝ => uq q (a + (t : ℂ) * h) (b + (t : ℂ) * (ε * h)) := by
    funext t; rw [mul_assoc]
  rw [heq]
  by_cases hh : h = 0
  · subst hh; simpa using concaveOn_const (c := uq q a b) convex_univ
  obtain ⟨a', ha', ha'0⟩ := exists_seq_line_ne_zero a h
  obtain ⟨b', hb', hb'0⟩ := exists_seq_line_ne_zero b (ε * h)
  refine concaveOn_univ_of_tendsto (F := fun m t => uq q (a' m + t * h) (b' m + t * (ε * h)))
    (fun m => uq_concave_generic hq hk (ha'0 m) (hb'0 m)) fun t => ?_
  exact ((continuous_uq (by linarith)).tendsto _).comp
    ((ha'.add_const ((t : ℂ) * h)).prodMk_nhds (hb'.add_const ((t : ℂ) * (ε * h))))

end External.Burkholder
