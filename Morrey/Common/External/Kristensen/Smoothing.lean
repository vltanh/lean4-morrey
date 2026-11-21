module

public import Morrey.Common.Basic.CalculusOfVariations.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Kristensen: smoothing a rank-one convex, non-quasiconvex polynomial

J. Kristensen, *On the non-locality of quasiconvexity*, Ann. Inst. H. Poincaré Anal. Non Linéaire
16 (1999), Proposition 2 and its proof; S. Heinz, PhD thesis (2008). Cassese's Corollary 5.2 is
"a standard smoothing argument applied to the polynomial integrand" (TeX lines 2048–2050), with
these citations and no other proof.

It is stated in the narrowest form in which Cassese uses it, not in the generality of the
sources: on `ℝ^{2×m}` with `m ≥ 3`, for homogeneous quartic polynomials (the integrand to which
Corollary 5.2 applies it is the quartic of Theorem 1.3, lifted from `ℝ^{2×3}` to `ℝ^{2×m}` through
the first three columns). Heinz's thesis was not consulted, and the statement of Kristensen's
Proposition 2 was not compared with this one; the proof below follows Kristensen's proof of
Proposition 2 (p. 7), as transcribed for this formalization.

## The proof (`smoothing_holds`)

Kristensen's proof: for a rank-one convex, non-quasiconvex quartic `p` take cut-offs `ζ_s`, `ξ_s`
(`ζ_s = 1` below `s`, `0` above `s + 1`; `ξ_s = 0` below `s - 1`, `t²` above `s + 1`, convex and
nondecreasing); "it is not hard to see" that for suitable `s > 1`, `k > 0` the function
`p ζ_s (|X|) + k ξ_s (|X|)` is rank-one convex and not quasiconvex; then add `ε |X|²` with `ε` so
small that non-quasiconvexity survives, and the uniform Legendre–Hadamard condition with constant
`ε` holds. The "not hard to see" step is supplied here, along Kristensen's lines
(`SmoothingProof.exists_smoothing`):

* *not quasiconvex*: `p` fails quasiconvexity at `0` with a `K`-Lipschitz `φ`, so
  `|∇φ|² ≤ B := 2 m K²` everywhere. The radii are chosen beyond `B`, so `h = p + ε |·|² + K₀` on
  the range of `∇φ`, and `ε := δ / (2 (∫_Q |∇φ|² + 1))`, `δ := p (0) - ∫_Q p (∇φ) > 0`, keeps the
  strict inequality;
* *Legendre–Hadamard*: with `r = |A|²`, `D²h (A) [H, H] = D²(p ζ) (A) [H, H] + Φ'' (r) 4 ⟨A, H⟩² +
  2 Φ' (r) |H|²`, `Φ = k ξ + ε id + K₀`. Where `ζ = 1` (`r < a₀ + 1`) the first term is
  `D²p (A) [H, H] ≥ 0` (rank-one convexity); where `ζ = 0` it vanishes; on the compact annulus
  `a₀ + 1 ≤ r ≤ a₀ + 2` it is `≥ -M |H|²`, `M ≥ 0` a bound of `‖D²(p ζ)‖` on a ball containing
  the annulus, while `ξ' = 1` there, so `k := M / 2` compensates. In all cases
  `D²h (A) [H, H] ≥ 2 ε |H|² ≥ ε |H|²`, and `c := ε`;
* *growth*: `|p ζ| ≤ M'` (`M'` a bound of `|p|` on the support of `ζ`), `0 ≤ ξ (r) ≤ r`, so
  `ε |A|² ≤ h (A) ≤ (2 M' + 1 + k + ε) (1 + |A|²)` with `K₀ := M' + 1`;
* *smoothness*: `ζ`, `ξ` are smooth functions of `|X|²`, a polynomial.

Departures from Kristensen's construction, and their reasons:

* the cut-offs are functions of `r = |X|²` instead of `t = |X|`: `ζ (r) = σ (a₀ + 2 - r)` and
  `ξ (r) = ∫₀^r σ (τ - a₀) dτ` (`σ` = `Real.smoothTransition`), so that their compositions with
  `|·|²` are visibly smooth and `D²(ξ ∘ |·|²) [H, H] = 4 ξ'' ⟨A, H⟩² + 2 ξ' |H|²`. Read as
  functions of `t` (with `s = √(a₀ + 1)`), `ζ` has Kristensen's properties; `ξ` is convex and
  nondecreasing and `0` below `s - 1`, but equals `t² - c` (not `t²`) far out, and its second
  derivative vanishes on the part of `(s - 1, s + 1)` where `ξ = 0`. What the argument uses
  (`ξ'' ≥ 0`, `0 ≤ ξ' ≤ 1`, `ξ' = 1` where `ζ` is not constant) holds. Kristensen does not write
  this step out, so the argument for it is ours;
* the constant `K₀ = M' + 1` is added: the statement requires `c |A|² ≤ h (A)` for every `A`,
  so `h (0) > 0`, whereas Kristensen's `g (0) = p (0) = 0`. Adding a constant changes neither
  second derivatives nor quasiconvexity at `0` on the unit cube, whose volume is `1`;
* `ε` is chosen independently of `s` and `k`: on the range of `∇φ` the function is
  `p + ε |·|² + K₀` whatever `k` is.

Homogeneity of `P` and `m ≥ 3` are not used: `SmoothingProof.exists_smoothing` holds on every
`ℝ^{d×m}` for every smooth rank-one convex integrand that is not quasiconvex at `0`.
-/

@[expose] public section

open MeasureTheory

namespace External.Kristensen

open CalculusOfVariations

/-- The smoothing argument of Kristensen (1999), Proposition 2 and its proof, and Heinz (2008), in
the form Cassese uses for Corollary 5.2 (TeX lines 2048–2065): for `m ≥ 3`, if a homogeneous
quartic polynomial `P : ℝ^{2×m} → ℝ` is rank-one convex and not quasiconvex at `0`, there are a
smooth `h` and `c, C > 0` with `D²h (A) [H, H] ≥ c |H|²` for every `A` and every rank-one `H`,
`c |A|² ≤ h (A) ≤ C (1 + |A|²)`, and `h` not quasiconvex at `0` (`|·|` the Frobenius norm). The
sources were not consulted: this is the statement as Cassese applies it. -/
def Smoothing : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ P : MvPolynomial (Fin 2 × Fin m) ℝ, P.IsHomogeneous 4 →
    RankOneConvex
      (fun A : Matrix (Fin 2) (Fin m) ℝ => MvPolynomial.eval (fun ij => A ij.1 ij.2) P) →
    ¬ QuasiconvexAtOn (unitCube m)
      (fun A : Matrix (Fin 2) (Fin m) ℝ => MvPolynomial.eval (fun ij => A ij.1 ij.2) P) 0 →
    ∃ (h : Matrix (Fin 2) (Fin m) ℝ → ℝ) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X : Fin 2 → Fin m → ℝ => h (Matrix.of X)) ∧
      (∀ A H : Matrix (Fin 2) (Fin m) ℝ, H.rank = 1 →
        c * ∑ i, ∑ j, H i j ^ 2 ≤ iteratedDeriv 2 (fun t : ℝ => h (A + t • H)) 0) ∧
      (∀ A : Matrix (Fin 2) (Fin m) ℝ,
        c * ∑ i, ∑ j, A i j ^ 2 ≤ h A ∧ h A ≤ C * (1 + ∑ i, ∑ j, A i j ^ 2)) ∧
      ¬ QuasiconvexAtOn (unitCube m) h 0

namespace SmoothingProof

open CalculusOfVariations Filter Topology Set
open scoped ContDiff

variable {d m : ℕ}

/-- The squared Frobenius norm `|X|² = ∑ X_{ij}²`. -/
noncomputable def sqNorm (X : Fin d → Fin m → ℝ) : ℝ := ∑ i, ∑ j, X i j ^ 2

/-- The Frobenius inner product `⟨X, Y⟩ = ∑ X_{ij} Y_{ij}`. -/
noncomputable def frob (X Y : Fin d → Fin m → ℝ) : ℝ := ∑ i, ∑ j, X i j * Y i j

theorem sqNorm_nonneg (X : Fin d → Fin m → ℝ) : 0 ≤ sqNorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem contDiff_sqNorm : ContDiff ℝ ∞ (sqNorm : (Fin d → Fin m → ℝ) → ℝ) := by
  unfold sqNorm
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (contDiff_apply_apply ℝ i j).pow 2

theorem sqNorm_line (A H : Fin d → Fin m → ℝ) (t : ℝ) :
    sqNorm (A + t • H) = sqNorm A + 2 * frob A H * t + sqNorm H * t ^ 2 := by
  simp only [sqNorm, frob, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sqNorm_zero : sqNorm (0 : Fin d → Fin m → ℝ) = 0 := by simp [sqNorm]

theorem norm_sq_le_sqNorm (H : Fin d → Fin m → ℝ) : ‖H‖ ^ 2 ≤ sqNorm H := by
  have h0 : 0 ≤ sqNorm H := sqNorm_nonneg H
  have hle : ‖H‖ ≤ Real.sqrt (sqNorm H) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    calc H i j ^ 2 ≤ ∑ j', H i j' ^ 2 :=
          Finset.single_le_sum (f := fun j' => H i j' ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ sqNorm H :=
          Finset.single_le_sum (f := fun i' => ∑ j', H i' j' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖H‖ ^ 2 ≤ Real.sqrt (sqNorm H) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = sqNorm H := Real.sq_sqrt h0

/-- The second derivative of `f` along the line `t ↦ A + t H` at `t = 0` is `D²f (A) [H, H]`. -/
theorem iteratedDeriv_two_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (A H : E) :
    iteratedDeriv 2 (fun t : ℝ => f (A + t • H)) 0 = iteratedFDeriv ℝ 2 f A (fun _ => H) := by
  set L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight H
  have hF : ContDiff ℝ 2 (fun y => f (A + y)) := hf.comp (contDiff_const.add contDiff_id)
  have h1 : (fun t : ℝ => f (A + t • H)) = (fun y => f (A + y)) ∘ L := by
    funext t; simp [L]
  rw [iteratedDeriv_eq_iteratedFDeriv, h1, L.iteratedFDeriv_comp_right hF 0 le_rfl]
  simp [L, iteratedFDeriv_comp_add_left]

/-- A convex `C²` function of one variable has a nonnegative second derivative. -/
theorem iteratedDeriv_two_nonneg_of_convexOn {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : ConvexOn ℝ univ f) (x : ℝ) : 0 ≤ iteratedDeriv 2 f x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hmono : Monotone (deriv f) := fun a b hab =>
    hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ a) (mem_univ b) hab
  exact hmono.deriv_nonneg

/-- The second derivative of `Φ (|A + t H|²)` at `t = 0`. -/
theorem iteratedDeriv_two_comp_sqNorm {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (A H : Fin d → Fin m → ℝ) :
    iteratedDeriv 2 (fun t : ℝ => Φ (sqNorm (A + t • H))) 0 =
      deriv (deriv Φ) (sqNorm A) * (2 * frob A H) ^ 2 + deriv Φ (sqNorm A) * (2 * sqNorm H) := by
  simp_rw [sqNorm_line]
  set r := sqNorm A
  set β := frob A H
  set γ := sqNorm H
  obtain ⟨hd1, hΦ'⟩ := contDiff_infty_iff_deriv.1 hΦ
  have hd2 : Differentiable ℝ (deriv Φ) := (contDiff_infty_iff_deriv.1 hΦ').1
  have hn : ∀ t : ℝ, HasDerivAt (fun t => r + 2 * β * t + γ * t ^ 2) (2 * β + 2 * γ * t) t := by
    intro t
    have := (((hasDerivAt_id t).const_mul (2 * β)).const_add r).add
      ((hasDerivAt_pow 2 t).const_mul γ)
    convert this using 1
    · funext x; simp
    · simp; ring
  have hD1 : ∀ t : ℝ, HasDerivAt (fun t => Φ (r + 2 * β * t + γ * t ^ 2))
      (deriv Φ (r + 2 * β * t + γ * t ^ 2) * (2 * β + 2 * γ * t)) t :=
    fun t => (hd1 _).hasDerivAt.comp t (hn t)
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    show deriv (fun t => Φ (r + 2 * β * t + γ * t ^ 2)) =
      fun t => deriv Φ (r + 2 * β * t + γ * t ^ 2) * (2 * β + 2 * γ * t) from
      funext fun t => (hD1 t).deriv]
  have hD2 := ((hd2 _).hasDerivAt.comp (0 : ℝ) (hn 0)).mul
    (((hasDerivAt_id (0 : ℝ)).const_mul (2 * γ)).const_add (2 * β))
  have hD2' : HasDerivAt (fun t => deriv Φ (r + 2 * β * t + γ * t ^ 2) * (2 * β + 2 * γ * t))
      (deriv (deriv Φ) r * (2 * β) ^ 2 + deriv Φ r * (2 * γ)) 0 := by
    convert hD2 using 1
    · funext t; simp only [Pi.mul_apply, Function.comp_apply, id]
    · simp; ring
  rw [hD2'.deriv]

/-! ### The two profiles -/

/-- The cut-off profile `ζ (r) = σ (b - r)` (`σ` the smooth transition), a function of `r = |X|²`:
`ζ = 1` on `r ≤ b - 1`, `ζ = 0` on `r ≥ b`, `0 ≤ ζ ≤ 1`. -/
noncomputable def cutoff (b r : ℝ) : ℝ := Real.smoothTransition (b - r)

theorem contDiff_cutoff (b : ℝ) : ContDiff ℝ ∞ (cutoff b) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem cutoff_eq_one {b r : ℝ} (h : r ≤ b - 1) : cutoff b r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoff_eq_zero {b r : ℝ} (h : b ≤ r) : cutoff b r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoff_nonneg (b r : ℝ) : 0 ≤ cutoff b r := Real.smoothTransition.nonneg _

theorem cutoff_le_one (b r : ℝ) : cutoff b r ≤ 1 := Real.smoothTransition.le_one _

/-- The convex profile `ξ (r) = ∫₀^r σ (τ - a) dτ`, a function of `r = |X|²`: `ξ' = σ (· - a)` is
nondecreasing with values in `[0, 1]`, `ξ = 0` on `r ≤ a` (for `a ≥ 0`), `ξ' = 1` on `r ≥ a + 1`. -/
noncomputable def ramp (a r : ℝ) : ℝ := ∫ τ in (0 : ℝ)..r, Real.smoothTransition (τ - a)

theorem continuous_ramp_integrand (a : ℝ) :
    Continuous fun τ : ℝ => Real.smoothTransition (τ - a) :=
  Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)

theorem hasDerivAt_ramp (a r : ℝ) : HasDerivAt (ramp a) (Real.smoothTransition (r - a)) r :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_ramp_integrand a).intervalIntegrable _ _)
    ((continuous_ramp_integrand a).stronglyMeasurableAtFilter _ _)
    (continuous_ramp_integrand a).continuousAt

theorem deriv_ramp (a : ℝ) : deriv (ramp a) = fun r => Real.smoothTransition (r - a) :=
  funext fun r => (hasDerivAt_ramp a r).deriv

theorem contDiff_ramp (a : ℝ) : ContDiff ℝ ∞ (ramp a) := by
  rw [contDiff_infty_iff_deriv, deriv_ramp]
  exact ⟨fun r => (hasDerivAt_ramp a r).differentiableAt,
    Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)⟩

theorem ramp_eq_zero {a r : ℝ} (ha : 0 ≤ a) (hr : r ≤ a) : ramp a r = 0 := by
  unfold ramp
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
  intro τ hτ
  apply Real.smoothTransition.zero_of_nonpos
  rcases Set.mem_uIcc.mp hτ with h | h <;> linarith [h.1, h.2]

theorem ramp_nonneg (a : ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ ramp a r :=
  intervalIntegral.integral_nonneg hr fun _ _ => Real.smoothTransition.nonneg _

theorem ramp_le (a : ℝ) {r : ℝ} (hr : 0 ≤ r) : ramp a r ≤ r :=
  calc ramp a r ≤ ∫ _ in (0 : ℝ)..r, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hr
          ((continuous_ramp_integrand a).intervalIntegrable _ _)
          (intervalIntegrable_const (μ := volume) (c := (1 : ℝ)))
          fun τ _ => Real.smoothTransition.le_one (τ - a)
    _ = r := by simp

/-- Polynomials are smooth. -/
theorem contDiff_eval_mvPolynomial {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : MvPolynomial ι ℝ) (f : E → ι → ℝ) (hf : ∀ i, ContDiff ℝ ∞ fun x => f x i) :
    ContDiff ℝ ∞ fun x => MvPolynomial.eval (f x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hf i)

/-! ### The construction -/

/-- **Kristensen's construction** (proof of Proposition 2), with its "not hard to see" step
supplied along his lines, for any smooth rank-one convex `p : ℝ^{d×m} → ℝ` that is not
quasiconvex at `0`. With `φ` a `K`-Lipschitz witness, `B = d m K²` (so `|∇φ|² ≤ B`),
`a₀ = B + 1`, `ζ = cutoff (a₀ + 2)`, `ξ = ramp a₀`, the function is
`h (X) = p (X) ζ (|X|²) + k ξ (|X|²) + ε |X|² + K₀` with `k = max M 0 / 2` (`M` a bound of
`‖D²(p ζ (|·|²))‖` on the ball containing `{|X|² ≤ a₀ + 2}`), `ε = δ / (2 (∫_Q |∇φ|² + 1))`
(`δ = p (0) - ∫_Q p (∇φ) > 0`) and `K₀ = M' + 1` (`M'` a bound of `|p|` on that ball); `c = ε`
and `C = 2 M' + 1 + k + ε`. See the module docstring for the argument and its departures from
Kristensen's. -/
theorem exists_smoothing (p : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (hp : ContDiff ℝ ∞ (fun X : Fin d → Fin m → ℝ => p (Matrix.of X)))
    (hrc : RankOneConvex p) (hnqc : ¬ QuasiconvexAtOn (unitCube m) p 0) :
    ∃ (h : Matrix (Fin d) (Fin m) ℝ → ℝ) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ContDiff ℝ ∞ (fun X : Fin d → Fin m → ℝ => h (Matrix.of X)) ∧
      (∀ A H : Matrix (Fin d) (Fin m) ℝ, H.rank = 1 →
        c * ∑ i, ∑ j, H i j ^ 2 ≤ iteratedDeriv 2 (fun t : ℝ => h (A + t • H)) 0) ∧
      (∀ A : Matrix (Fin d) (Fin m) ℝ,
        c * ∑ i, ∑ j, A i j ^ 2 ≤ h A ∧ h A ≤ C * (1 + ∑ i, ∑ j, A i j ^ 2)) ∧
      ¬ QuasiconvexAtOn (unitCube m) h 0 := by
  -- the test map witnessing that `p` is not quasiconvex at `0`
  unfold QuasiconvexAtOn at hnqc
  push Not at hnqc
  obtain ⟨φ, K, hφ, hφ0, hint, hlt⟩ := hnqc
  simp only [zero_add] at hint hlt
  -- `|∇φ| ≤ K` entrywise, so `|∇φ|² ≤ B`
  have hgrad : ∀ x i j, |grad φ x i j| ≤ K := by
    intro x i j
    have hL : LipschitzWith K (fun y => φ y i) := by
      have := (LipschitzWith.eval i).comp hφ
      rw [one_mul] at this
      exact this
    have hs : ‖(Pi.single j (1 : ℝ) : Fin m → ℝ)‖ = 1 := by simp [Pi.norm_single]
    calc |grad φ x i j| = ‖fderiv ℝ (fun y => φ y i) x (Pi.single j 1)‖ := by simp [grad]
      _ ≤ ‖fderiv ℝ (fun y => φ y i) x‖ * ‖(Pi.single j (1 : ℝ) : Fin m → ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ K := by rw [hs, mul_one]; exact norm_fderiv_le_of_lipschitz ℝ hL
  set B : ℝ := ∑ _i : Fin d, ∑ _j : Fin m, (K : ℝ) ^ 2 with hB_def
  have hB0 : 0 ≤ B := by positivity
  have hB : ∀ x, sqNorm (grad φ x) ≤ B := fun x =>
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hgrad x i j) 2
  -- the radii: `ξ = 0` on `|X|² ≤ a₀`, `ζ = 1` on `|X|² ≤ a₀ + 1`, `ζ = 0` on `|X|² ≥ a₀ + 2`
  set a₀ : ℝ := B + 1 with ha₀_def
  have ha₀0 : 0 ≤ a₀ := by linarith
  set b : ℝ := a₀ + 2 with hb_def
  set R : ℝ := b + 1 with hR_def
  have hmem : ∀ X : Fin d → Fin m → ℝ, sqNorm X ≤ b →
      X ∈ Metric.closedBall (0 : Fin d → Fin m → ℝ) R := by
    intro X hX
    rw [mem_closedBall_zero_iff]
    by_contra hXR
    push Not at hXR
    have h1 : R ^ 2 < ‖X‖ ^ 2 := pow_lt_pow_left₀ hXR (by linarith) (by norm_num)
    have h2 := norm_sq_le_sqNorm X
    nlinarith
  -- the truncated polynomial `q = p ζ (|·|²)` and the bounds on the compact ball
  set pE : (Fin d → Fin m → ℝ) → ℝ := fun X => p (Matrix.of X) with hpE_def
  set q : (Fin d → Fin m → ℝ) → ℝ := fun X => pE X * cutoff b (sqNorm X) with hq_def
  have hq : ContDiff ℝ ∞ q := hp.mul ((contDiff_cutoff b).comp contDiff_sqNorm)
  have hcpt := isCompact_closedBall (0 : Fin d → Fin m → ℝ) R
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn
    ((hq.continuous_iteratedFDeriv (m := 2) (by simp)).continuousOn)
  obtain ⟨M', hM'⟩ := hcpt.exists_bound_of_continuousOn hp.continuous.continuousOn
  have hM'0 : 0 ≤ M' :=
    (norm_nonneg _).trans (hM' 0 (Metric.mem_closedBall_self (by linarith)))
  set M₀ : ℝ := max M 0 with hM₀_def
  have hM₀ : 0 ≤ M₀ := le_max_right _ _
  set k : ℝ := M₀ / 2 with hk_def
  have hk : 0 ≤ k := by positivity
  -- the choice of `ε`
  have hcube : MeasurableSet (unitCube m) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hvol : volume (unitCube m) = 1 := by simp [unitCube, Real.volume_pi_Ioo]
  have hvolR : (volume (unitCube m)).toReal = 1 := by rw [hvol]; simp
  have hmeasN : Measurable fun x => sqNorm (grad φ x) := by
    unfold sqNorm
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    simp only [grad, Matrix.of_apply]
    exact (measurable_fderiv_apply_const ℝ (fun y => φ y i) _).pow_const 2
  have hintN : IntegrableOn (fun x => sqNorm (grad φ x)) (unitCube m) :=
    Measure.integrableOn_of_bounded (M := B) (by rw [hvol]; simp) hmeasN.aestronglyMeasurable
      (Eventually.of_forall fun x => (Real.norm_of_nonneg (sqNorm_nonneg _)).trans_le (hB x))
  set I : ℝ := ∫ x in unitCube m, sqNorm (grad φ x) with hI_def
  have hI0 : 0 ≤ I := setIntegral_nonneg hcube fun x _ => sqNorm_nonneg _
  set δ : ℝ := p 0 - ∫ x in unitCube m, p (grad φ x) with hδ_def
  have hδ : 0 < δ := by rw [hvolR, one_mul] at hlt; linarith
  set ε : ℝ := δ / (2 * (I + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hεI : ε * I < δ := by
    rw [hε_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  -- the radial part `Φ (r) = k ξ (r) + ε r + K₀`
  set Kc : ℝ := M' + 1 with hKc_def
  set Φ : ℝ → ℝ := fun r => k * ramp a₀ r + ε * r + Kc with hΦ_def
  have hΦ : ContDiff ℝ ∞ Φ :=
    ((contDiff_const.mul (contDiff_ramp a₀)).add (contDiff_const.mul contDiff_id)).add
      contDiff_const
  have hdΦ : ∀ r, deriv Φ r = k * Real.smoothTransition (r - a₀) + ε := by
    intro r
    have h1 : HasDerivAt Φ (k * Real.smoothTransition (r - a₀) + ε * 1) r :=
      (((hasDerivAt_ramp a₀ r).const_mul k).add ((hasDerivAt_id r).const_mul ε)).add_const Kc
    rw [h1.deriv, mul_one]
  have hd2Φ : ∀ r, 0 ≤ deriv (deriv Φ) r := by
    intro r
    rw [show deriv Φ = fun r => k * Real.smoothTransition (r - a₀) + ε from funext hdΦ]
    apply Monotone.deriv_nonneg
    intro x y hxy
    have := Real.smoothTransition.monotone (sub_le_sub_right hxy a₀)
    simp only
    nlinarith
  set hE : (Fin d → Fin m → ℝ) → ℝ := fun X => q X + Φ (sqNorm X) with hE_def
  have hEs : ContDiff ℝ ∞ hE := hq.add (hΦ.comp contDiff_sqNorm)
  -- (ii) the uniform Legendre–Hadamard condition
  have hLH : ∀ A H : Fin d → Fin m → ℝ, ConvexOn ℝ univ (fun t : ℝ => pE (A + t • H)) →
      ε * sqNorm H ≤ iteratedDeriv 2 (fun t : ℝ => hE (A + t • H)) 0 := by
    intro A H hcvx
    have hline : ContDiff ℝ ∞ (fun t : ℝ => A + t • H) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hsplit : iteratedDeriv 2 (fun t : ℝ => hE (A + t • H)) 0 =
        iteratedDeriv 2 (fun t : ℝ => q (A + t • H)) 0 +
          iteratedDeriv 2 (fun t : ℝ => Φ (sqNorm (A + t • H))) 0 :=
      iteratedDeriv_fun_add (f := fun t : ℝ => q (A + t • H))
        (g := fun t : ℝ => Φ (sqNorm (A + t • H)))
        ((hq.comp hline).contDiffAt.of_le (by simp))
        ((hΦ.comp (contDiff_sqNorm.comp hline)).contDiffAt.of_le (by simp))
    rw [hsplit, iteratedDeriv_two_comp_sqNorm hΦ]
    have hγ : 0 ≤ sqNorm H := sqNorm_nonneg H
    have e1 : 0 ≤ deriv (deriv Φ) (sqNorm A) * (2 * frob A H) ^ 2 :=
      mul_nonneg (hd2Φ _) (sq_nonneg _)
    rw [hdΦ]
    have hc : Continuous fun t : ℝ => sqNorm (A + t • H) :=
      contDiff_sqNorm.continuous.comp hline.continuous
    by_cases hr : sqNorm A < a₀ + 1
    · -- near `A`, `q = p`, whose second derivative along rank-one lines is `≥ 0`
      have hT : 0 ≤ iteratedDeriv 2 (fun t : ℝ => q (A + t • H)) 0 := by
        have hev : (fun t : ℝ => q (A + t • H)) =ᶠ[𝓝 0] fun t => pE (A + t • H) := by
          filter_upwards [hc.continuousAt.eventually_lt continuousAt_const (by simpa using hr)]
            with t ht
          simp only [q, cutoff_eq_one (show sqNorm (A + t • H) ≤ b - 1 by linarith), mul_one]
        rw [hev.iteratedDeriv_eq 2]
        exact iteratedDeriv_two_nonneg_of_convexOn ((hp.comp hline).of_le (by simp)) hcvx 0
      have hσ := Real.smoothTransition.nonneg (sqNorm A - a₀)
      nlinarith [mul_nonneg (mul_nonneg hk hσ) hγ, mul_nonneg hε.le hγ]
    · push Not at hr
      have hσ1 : Real.smoothTransition (sqNorm A - a₀) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith)
      have hT : -(M₀ * sqNorm H) ≤ iteratedDeriv 2 (fun t : ℝ => q (A + t • H)) 0 := by
        by_cases hrb : sqNorm A ≤ b
        · rw [iteratedDeriv_two_line (hq.of_le (by simp)) A H]
          have h1 := (iteratedFDeriv ℝ 2 q A).le_opNorm (fun _ => H)
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
          have h2 : ‖iteratedFDeriv ℝ 2 q A‖ ≤ M₀ := (hM A (hmem A hrb)).trans (le_max_left _ _)
          have h3 := norm_sq_le_sqNorm H
          have h4 : ‖iteratedFDeriv ℝ 2 q A (fun _ => H)‖ ≤ M₀ * sqNorm H :=
            h1.trans (mul_le_mul h2 h3 (by positivity) hM₀)
          rw [Real.norm_eq_abs] at h4
          linarith [neg_abs_le (iteratedFDeriv ℝ 2 q A (fun _ => H))]
        · push Not at hrb
          have hev : (fun t : ℝ => q (A + t • H)) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
            filter_upwards [continuousAt_const.eventually_lt hc.continuousAt (by simpa using hrb)]
              with t ht
            simp [q, cutoff_eq_zero ht.le]
          rw [hev.iteratedDeriv_eq 2, iteratedDeriv_const]
          simp only [OfNat.ofNat_ne_zero, ite_false, neg_nonpos]
          positivity
      rw [hσ1]
      have e2 : (k * 1 + ε) * (2 * sqNorm H) = M₀ * sqNorm H + 2 * (ε * sqNorm H) := by
        rw [hk_def]; ring
      nlinarith [mul_nonneg hε.le hγ]
  -- (iii) two-sided quadratic growth
  have hgrowth : ∀ A : Fin d → Fin m → ℝ,
      ε * sqNorm A ≤ hE A ∧ hE A ≤ (2 * M' + 1 + k + ε) * (1 + sqNorm A) := by
    intro A
    have hr0 : 0 ≤ sqNorm A := sqNorm_nonneg A
    have hqA : |q A| ≤ M' := by
      by_cases hrb : sqNorm A ≤ b
      · have h1 : |pE A| ≤ M' := by
          have := hM' A (hmem A hrb); rwa [Real.norm_eq_abs] at this
        simp only [q, abs_mul]
        calc |pE A| * |cutoff b (sqNorm A)| ≤ M' * 1 :=
              mul_le_mul h1 (by rw [abs_of_nonneg (cutoff_nonneg _ _)]; exact cutoff_le_one _ _)
                (abs_nonneg _) hM'0
          _ = M' := mul_one _
      · push Not at hrb
        simp [q, cutoff_eq_zero hrb.le, hM'0]
    have h0 := ramp_nonneg a₀ hr0
    have h1 := ramp_le a₀ hr0
    have hqb := abs_le.mp hqA
    simp only [hE, Φ]
    constructor
    · nlinarith [mul_nonneg hk h0]
    · nlinarith [mul_le_mul_of_nonneg_left h1 hk, mul_nonneg hk hr0, mul_nonneg hM'0 hr0,
        mul_nonneg hε.le hr0]
  -- (i) on the range of `∇φ`, `h = p + ε |·|² + K₀`
  have hsmall : ∀ X : Fin d → Fin m → ℝ, sqNorm X ≤ B → hE X = pE X + ε * sqNorm X + Kc := by
    intro X hX
    simp only [hE, q, Φ, cutoff_eq_one (show sqNorm X ≤ b - 1 by linarith),
      ramp_eq_zero ha₀0 (show sqNorm X ≤ a₀ by linarith)]
    ring
  refine ⟨hE, ε, 2 * M' + 1 + k + ε, hε, by positivity, hEs, ?_, ?_, ?_⟩
  · intro A H hH
    exact hLH A H (hrc A H hH)
  · intro A
    exact hgrowth A
  · intro hqc
    have hpt : EqOn (fun x => p (grad φ x) + ε * sqNorm (grad φ x) + Kc)
        (fun x => hE ((0 : Matrix (Fin d) (Fin m) ℝ) + grad φ x)) (unitCube m) := by
      intro x _
      simp only [zero_add]
      exact (hsmall _ (hB x)).symm
    have hint' :
        IntegrableOn (fun x => hE ((0 : Matrix (Fin d) (Fin m) ℝ) + grad φ x)) (unitCube m) :=
      ((hint.add (hintN.const_mul ε)).add (integrableOn_const (C := Kc) (by rw [hvol]; simp)
        (by simp))).congr_fun hpt hcube
    have hle := hqc φ K hφ hφ0 hint'
    have hval : ∫ x in unitCube m, (p (grad φ x) + ε * sqNorm (grad φ x) + Kc) =
        (∫ x in unitCube m, p (grad φ x)) + ε * I + Kc := by
      rw [integral_add (f := fun x => p (grad φ x) + ε * sqNorm (grad φ x)) (g := fun _ => Kc)
          (hint.add (hintN.const_mul ε)) (integrableOn_const (by rw [hvol]; simp) (by simp)),
        integral_add (f := fun x => p (grad φ x)) (g := fun x => ε * sqNorm (grad φ x)) hint
          (hintN.const_mul ε), integral_const_mul, setIntegral_const]
      have hreal : volume.real (unitCube m) = 1 := by simp [Measure.real, hvol]
      rw [hreal, one_smul]
    have h0 : hE (0 : Matrix (Fin d) (Fin m) ℝ) = p 0 + Kc := by
      have h1 := hsmall 0 (by rw [sqNorm_zero]; exact hB0)
      rw [sqNorm_zero, mul_zero, add_zero] at h1
      exact h1
    rw [← setIntegral_congr_fun hcube hpt, hval, h0, hvolR, one_mul] at hle
    linarith

end SmoothingProof

open SmoothingProof in
open scoped ContDiff in
/-- **Kristensen's smoothing argument holds** (`Smoothing`), by Kristensen's proof of
Proposition 2, with its "not hard to see" step supplied along Kristensen's lines (module
docstring): `SmoothingProof.exists_smoothing` applied to the polynomial, which is smooth. -/
theorem smoothing_holds : Smoothing := by
  intro m _ P _ hrc hnqc
  set p : Matrix (Fin 2) (Fin m) ℝ → ℝ := fun A => MvPolynomial.eval (fun ij => A ij.1 ij.2) P
  have hp : ContDiff ℝ ∞ fun X : Fin 2 → Fin m → ℝ => p (Matrix.of X) :=
    contDiff_eval_mvPolynomial P (fun (X : Fin 2 → Fin m → ℝ) (ij : Fin 2 × Fin m) => X ij.1 ij.2)
      fun ij => contDiff_apply_apply ℝ ij.1 ij.2
  exact @exists_smoothing 2 m p hp hrc hnqc

end External.Kristensen
