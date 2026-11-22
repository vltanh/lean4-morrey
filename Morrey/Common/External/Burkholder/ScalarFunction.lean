module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import BanachProbability.Martingale.Burkholder.Function

/-!
# Burkholder's function for the exponent `6`, and for a real exponent `q ≥ 2`

D. L. Burkholder, *Sharp inequalities for martingales and stochastic integrals*, Colloque Paul
Lévy, Astérisque 157–158 (1988) (read: Numdam), (1.6), (1.10) and Remark 1.2; the paper cites its
proof of Theorem 1.1, "or [V. Vasyunin and A. Volberg 2010] for an alternative proof" (not used).
Cassese uses two properties of `u (a, b) = α (|b| − 5 |a|) (|a| + |b|)^5`, `α = 6 (5/6)^5`, for
complex `a`, `b` (the proof of Proposition 4.2, (13) and (14)): the proposition
`ScalarFunction`, proved by `scalarFunction_holds`. Remark 4.5 extends the argument to
`1 < p < ∞`, `p + 2 < q < ∞`; it needs the same two properties of
`u_q (a, b) = α_q (|b| − (q − 1) |a|) (|a| + |b|)^{q−1}`, `α_q = q (1 − 1/q)^{q−1}`
(`ScalarFunctionQ q`), proved for every real `q ≥ 2` by `scalarFunctionQ_holds`. `uq_six`
identifies `u_6` with `u6`.

Proof: from the package `BanachProbability` (`lean4-banach-probability`,
`Martingale/Burkholder/Function.lean`). For `q ≥ 2`, `p* = q` and `u_q` is the package's
`BanachProbability.Burkholder.burkholderFun q` on the real inner product space `ℂ`
(`uq_eq_burkholderFun`), Burkholder's function in Burkholder's notation (`a` the dominating, `b` the
subordinate position). (13) is `burkholderFun_ge`, `u_q ≥ |b|^q − (q − 1)^q |a|^q`, and (14) is
`burkholderFun_concaveOn_line` with the directions `h` and `ε h`, `|ε h| ≤ |h|`. (13) is
Burkholder's (1.10), proved in the package by his argument: the elementary inequality (1.11) by the
convexity and concavity of `log ((p − 1)^{p−1} / p^{p−2})`, then, by homogeneity on `|a| + |b| = 1`,
the concave and convex pieces of his function `F`. (14) is his Remark 1.2, (1.17), which the paper
states without proof; the package completes it from the paper's own steps: the concavity in the
proof of (1.12), by (1.14) (the sign of the second derivative of `t ↦ u_q (a + t h, b + t k)` on
lines along which neither coordinate vanishes), and, for the other lines, the shift of the proof of
(1.8) by a vector orthogonal to `ℂ` in `ℂ ⊕ ℝ`, letting the shift tend to `0`.
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

/-! ### Burkholder's function for a real exponent `q ≥ 2`

The same two properties for `u_q (a, b) = α_q (|b| − (q − 1) |a|) (|a| + |b|)^{q−1}`,
`α_q = q (1 − 1/q)^{q−1}`, and every real `q ≥ 2` (Burkholder 1988; Remark 4.5 of Cassese
uses them for `q = p + 3`). For `q < 2` the formula is not Burkholder's function (his function for
`1 < q < 2` has the constant `1/(q − 1)` in place of `q − 1`), and (13) fails there:
`u_q (0, b) = α_q |b|^q` with `α_q < 1` for `q` near `1`. -/

/-- `α_q = q (1 − 1/q)^{q−1}`. -/
noncomputable def alphaQ (q : ℝ) : ℝ := q * (1 - 1 / q) ^ (q - 1)

/-- Burkholder's function for the exponent `q`:
`u_q (a, b) = α_q (|b| − (q − 1) |a|) (|a| + |b|)^{q−1}`. -/
noncomputable def uq (q : ℝ) (a b : ℂ) : ℝ :=
  alphaQ q * (‖b‖ - (q - 1) * ‖a‖) * (‖a‖ + ‖b‖) ^ (q - 1)

/-- **Equations (13), (14)** for the exponent `q` (Burkholder 1988, (1.10) and (1.17)):
`u_q (a, b) ≥ |b|^q − (q − 1)^q |a|^q`, and `t ↦ u_q (a + t h, b + t ε h)` is concave for all
complex `a`, `b`, `h` and `|ε| ≤ 1`. Proved for `q ≥ 2` in `scalarFunctionQ_holds`. -/
def ScalarFunctionQ (q : ℝ) : Prop :=
  (∀ a b : ℂ, ‖b‖ ^ q - (q - 1) ^ q * ‖a‖ ^ q ≤ uq q a b) ∧
    ∀ a b h ε : ℂ, ‖ε‖ ≤ 1 →
      ConcaveOn ℝ Set.univ fun t : ℝ => uq q (a + (t : ℂ) * h) (b + (t : ℂ) * ε * h)

/-- For `q = 6`, `u_q` is the function `u6` of Proposition 4.2. -/
theorem uq_six : uq 6 = u6 := by
  funext a b
  have h1 : (1 - 1 / 6 : ℝ) ^ ((6 : ℝ) - 1) = (5 / 6) ^ 5 := by
    rw [show (6 : ℝ) - 1 = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h2 : (‖a‖ + ‖b‖) ^ ((6 : ℝ) - 1) = (‖a‖ + ‖b‖) ^ 5 := by
    rw [show (6 : ℝ) - 1 = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [uq, alphaQ, h1, h2, u6]
  norm_num

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

/-- For `q ≥ 2`, `u_q` is the package's Burkholder function `burkholderFun q` on the real inner
product space `ℂ`: `p* = q` there (`BanachProbability.Burkholder.burkholderFun_of_two_le`). -/
theorem uq_eq_burkholderFun {q : ℝ} (hq : 2 ≤ q) (a b : ℂ) :
    uq q a b = BanachProbability.Burkholder.burkholderFun q a b := by
  rw [BanachProbability.Burkholder.burkholderFun_of_two_le hq, uq, alphaQ]

/-- **Equations (13), (14) for a real exponent `q ≥ 2`** (Remark 4.5): Burkholder's function
`u_q`. (The paper states them for `q = 6`, `scalarFunction_holds`.)

Proof: Burkholder's argument (Burkholder 1988, (1.10); (1.17) completed from (1.14) and the shift
of the proof of (1.8)), in the package: for `q ≥ 2`,
`u_q = burkholderFun q` (`uq_eq_burkholderFun`); (13) is
`BanachProbability.Burkholder.burkholderFun_ge` with `p* = q`, and (14) is
`BanachProbability.Burkholder.burkholderFun_concaveOn_line` for the directions `h` and `ε h`, since
`|ε h| ≤ |h|`. -/
theorem scalarFunctionQ_holds {q : ℝ} (hq : 2 ≤ q) : ScalarFunctionQ q := by
  have hq1 : 1 < q := by linarith
  refine ⟨fun a b => ?_, fun a b h ε hε => ?_⟩
  · have := BanachProbability.Burkholder.burkholderFun_ge hq1 a b
    rwa [BanachProbability.Burkholder.max_div_sub_one_eq_self hq, ← uq_eq_burkholderFun hq] at this
  · have hk : ‖ε * h‖ ≤ ‖h‖ := by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg h) hε
    have e : (fun t : ℝ => uq q (a + (t : ℂ) * h) (b + (t : ℂ) * ε * h)) =
        fun t : ℝ => BanachProbability.Burkholder.burkholderFun q (a + t • h) (b + t • (ε * h)) := by
      funext t
      rw [uq_eq_burkholderFun hq, Complex.real_smul, Complex.real_smul, mul_assoc]
    rw [e]
    exact BanachProbability.Burkholder.burkholderFun_concaveOn_line hq1 a b h (ε * h) hk

/-- **Equations (13), (14)** (`eq:scalar-properties`, `eq:scalar-zigzag`), Burkholder's function
for the exponent `6`.

Proof: the case `q = 6` of `scalarFunctionQ_holds` (Burkholder 1988, (1.10) and (1.17)), with
`u_6 = u6` (`uq_six`). -/
theorem scalarFunction_holds : ScalarFunction := by
  obtain ⟨h13, h14⟩ := scalarFunctionQ_holds (q := 6) (by norm_num)
  rw [uq_six] at h13 h14
  refine ⟨fun a b => ?_, h14⟩
  have := h13 a b
  rwa [show (6 : ℝ) - 1 = 5 by norm_num, Real.rpow_ofNat, Real.rpow_ofNat, Real.rpow_ofNat] at this

end External.Burkholder
