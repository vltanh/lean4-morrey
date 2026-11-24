module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.Matrix

/-!
# Challenge: rank-one convex, isotropic, positively homogeneous integrands on `2 × 2` matrices

Morrey's problem asks whether rank-one convexity implies quasiconvexity. For integrands on real
`2 × 2` matrices it is open. This file states the results of the paper of this repository,
`docs/HomogeneousIsotropic/paper/main.tex`, which answer it in the class of nonnegative,
isotropic, positively `p`-homogeneous integrands, for every `p > 0`.

## Conventions

* `ℝ^{2×2}` is `Matrix (Fin 2) (Fin 2) ℝ`, `ℝ²` is `Fin 2 → ℝ`, and the gradient of
  `φ : ℝ² → ℝ²` at `x` is `jac φ x` (rows are the components).
* `IsRankOneConvex F`: `t ↦ F (A + t B)` is convex on `ℝ` for every `A` and every `B` of rank
  one.
* `IsQuasiconvex F`: `F (A) ≤ ∫_{(0,1)²} F (A + ∇φ)` for every `A` and every Lipschitz `φ`
  vanishing outside the open unit square `unitSquare`, for which the integral exists.
* `Polyconvex F`: `F (A) = g (A, det A)` for a convex `g` on `ℝ^{2×2} × ℝ`.
* `polyaffine k K c` is `A ↦ k + ⟨K, A⟩ + c det A`, and `HasPolyaffineSupportAt F A₀` says that a
  polyaffine function lies below `F` and equals `F` at `A₀`.
* `IsIsotropic F`: `F (Q A R) = F (A)` for all `Q, R ∈ SO(2)`. `IsPosHomogeneous p F`:
  `F (c A) = c^p F (A)` for `c > 0` (a real power).
* `conformalPart A = z` and `anticonformalPart A = w` are the complex numbers with
  `A ζ = z ζ + w ζ̄` when `ℝ²` is identified with `ℂ`. Then `det A = |z|² − |w|²`
  (`det_eq_norm_sq_sub`), and `|z| + |w|` is the operator norm `|A|` of `A` (not stated here).
* `burkholderType p c₀ m A = (|z| + |w|)^{p−1} (c₀ (|z| + |w|) + m (|z| − |w|))`, that is
  `|A|^{p−2} (c₀ |A|² + m det A)`.
* `burkholder p A = (|z| + |w|)^{p−1} (|z| − (p − 1) |w|)`, the Burkholder function for
  `1 < p ≤ 2`: it is `p/2` times the integrand `(|1 − 2/p| |A|² + det A) |A|^{p−2}` of Guerra and
  Kristensen (Arch. Ration. Mech. Anal. 245 (2022)), and `p − 1` times the function `B_p` of
  arXiv:2609.28311, (2). `reflection` is `J = diag (1, −1)`.
* `multiplier p H m t = min (U, max (L, (p − 1) m))` with `L = ((1 + t) m − p H)/(1 − t)` and
  `U = (p H + (1 − t) m)/(1 + t)`.

## The statements

For `F : ℝ^{2×2} → ℝ` isotropic, positively `p`-homogeneous and rank-one convex:

* `theorem1_1` (`p ≥ 2`, `F ≥ 0`): `F` has a polyaffine support at every matrix, and is
  polyconvex. This answers Question 1.7 of Guerra and Kristensen.
* `theorem1_2` (`p ≥ 2`, `F ≥ 0`): the support at `diag (1, t)`, `|t| < 1`, in closed form. If
  `H = F (diag (1, t)) > 0` and `m` is the slope of a supporting line at `t` of
  `s ↦ F (diag (1, s))` on `[−1, 1]`, then with `c = multiplier p H m t` the polyaffine function
  `c t − (p − 1) H + (p H − t m − c t) a₁₁ + (m − c) a₂₂ + c det A` lies below `F` and equals `F`
  at `diag (1, t)`.
* `theorem1_3_a` (`p > 2`): an isotropic, positively `p`-homogeneous `F` is polyconvex if and
  only if it is rank-one convex and nonnegative. `theorem1_3_b` (`p = 2`): if and only if it is
  rank-one convex.
* `corollary1_4` (`p ≥ 2`, `F ≥ 0` Borel and locally bounded): rank-one convexity,
  quasiconvexity and polyconvexity are equivalent.
* `theorem1_5` (`1 ≤ p < 2`, `F ≥ 0`): at every matrix `A₀` there are `c₀`, `m` with
  `(2 − p) |m| ≤ p c₀` such that `burkholderType p c₀ m` lies below `F` and equals `F` at `A₀`.
  `theorem1_5_identity`: `burkholderType p c₀ m` is the combination of `burkholder p (A)` and
  `burkholder p (J A)` with the coefficients `(p c₀ ± (2 − p) m) / (p (2 − p))`, which are
  nonnegative under that condition.
* `corollary1_6_a` (`1 < p < 2`, `F ≥ 0`): **if the Burkholder function `burkholder p` is
  quasiconvex**, then `F` is quasiconvex. `corollary1_6_b` (`p = 1`): `F` is nonnegative and
  convex (a theorem of Dacorogna, 1995).
* `proposition1_7` (`0 < p < 1`): a positively `p`-homogeneous, rank-one convex `F` is `0`;
  isotropy is not needed.
* `corollary1_8` (`p > 0`, `F ≥ 0`): `F` is quasiconvex, **provided that `burkholder p` is
  quasiconvex when `1 < p < 2`**.

## The assumed result

`corollary1_6_a` and `corollary1_8` take the quasiconvexity of the Burkholder function,
`IsQuasiconvex (burkholder p)` for `1 < p < 2`, as a hypothesis; it is not proved in this
repository. It is stated as Corollary 2 of the preprint arXiv:2609.28311 (Agazzi et al., 2026,
not refereed), for a positive multiple of `burkholder p` and with smooth periodic test maps; the
passage to the test maps used here is not formalized.

The definitions are copied word for word from `Morrey/HomogeneousIsotropic/Defs.lean` by
`scripts/sync_challenge_defs.py`; the theorems are proved in the Solution of the same directory.
-/

@[expose] public section

namespace HomogeneousIsotropic

-- BEGIN SHARED DEFINITIONS

/-- The derivative matrix of `φ : ℝ² → ℝ²` at `x`: the matrix with the entries `∂_k φ_i (x)`
(rows are the components). For a Lipschitz `φ` it is the gradient almost everywhere; an entry is
`0` where `φ_i` is not differentiable. -/
noncomputable def jac (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i k => fderiv ℝ (fun y => φ y i) x (Pi.single k 1)

/-- The open unit square `(0, 1)²`. -/
def unitSquare : Set (Fin 2 → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo 0 1

/-- Rank-one convexity: `t ↦ F (A + t B)` is convex on `ℝ` for every `A` and every `B` of rank
one. -/
def IsRankOneConvex (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, B.rank = 1 → ConvexOn ℝ Set.univ fun t : ℝ => F (A + t • B)

/-- Quasiconvexity at `A`: `F (A) ≤ ∫_{(0,1)²} F (A + ∇φ)` for every Lipschitz `φ` vanishing
outside the unit square for which the integral exists (for a Borel, locally bounded `F` it always
does). -/
def IsQuasiconvexAt (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (K : NNReal), LipschitzWith K φ →
    (∀ x ∉ unitSquare, φ x = 0) →
      MeasureTheory.IntegrableOn (fun x => F (A + jac φ x)) unitSquare →
        F A ≤ ∫ x in unitSquare, F (A + jac φ x)

/-- Quasiconvexity: quasiconvexity at every matrix. -/
def IsQuasiconvex (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ A, IsQuasiconvexAt F A

/-- Isotropy: `F (Q A R) = F (A)` for all `Q, R ∈ SO(2)`. -/
def IsIsotropic (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ Q ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ, ∀ R ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ,
    ∀ A : Matrix (Fin 2) (Fin 2) ℝ, F (Q * A * R) = F A

/-- Positive `p`-homogeneity: `F (c A) = c^p F (A)` for every `c > 0`. -/
def IsPosHomogeneous (p : ℝ) (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ A : Matrix (Fin 2) (Fin 2) ℝ, F (c • A) = c ^ p * F A

/-- The polyaffine function `A ↦ k + ⟨K, A⟩ + c det A` on `ℝ^{2×2}`. -/
noncomputable def polyaffine (k : ℝ) (K : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  k + ∑ i, ∑ j, K i j * A i j + c * A.det

/-- `F` has a polyaffine support at `A₀`: a polyaffine function below `F` that equals `F` at
`A₀`. -/
def HasPolyaffineSupportAt (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (A₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    Prop :=
  ∃ (k : ℝ) (K : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
    (∀ A, polyaffine k K c A ≤ F A) ∧ polyaffine k K c A₀ = F A₀

/-- Polyconvexity on `ℝ^{2×2}`: `F (A) = g (A, det A)` for a convex `g : ℝ^{2×2} × ℝ → ℝ`. -/
def Polyconvex (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∃ g : Matrix (Fin 2) (Fin 2) ℝ × ℝ → ℝ, ConvexOn ℝ Set.univ g ∧ ∀ A, F A = g (A, A.det)

/-- The conformal part `z = ((a₁₁ + a₂₂) + i (a₂₁ − a₁₂)) / 2` of `A`: with `ℝ² = ℂ`,
`A ζ = z ζ + w ζ̄`. -/
noncomputable def conformalPart (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ⟨(A 0 0 + A 1 1) / 2, (A 1 0 - A 0 1) / 2⟩

/-- The anticonformal part `w = ((a₁₁ − a₂₂) + i (a₂₁ + a₁₂)) / 2` of `A`. -/
noncomputable def anticonformalPart (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ⟨(A 0 0 - A 1 1) / 2, (A 1 0 + A 0 1) / 2⟩

/-- The Burkholder-type function `(|z| + |w|)^{p−1} (c₀ (|z| + |w|) + m (|z| − |w|))`, in
conformal coordinates. With `|A| = |z| + |w|`, the operator norm, it is
`|A|^{p−2} (c₀ |A|² + m det A)`. -/
noncomputable def burkholderType (p c₀ m : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
    (c₀ * (‖conformalPart A‖ + ‖anticonformalPart A‖) +
      m * (‖conformalPart A‖ - ‖anticonformalPart A‖))

/-- The Burkholder function `(|z| − (p − 1) |w|) (|z| + |w|)^{p−1}` on `ℝ^{2×2}`, in the form
that is rank-one convex for `1 < p ≤ 2`. In terms of the operator norm `|A|` it is
`((p/2) det A + (1 − p/2) |A|²) |A|^{p−2}`. For `1 < p < 2` it is `p/2` times the Burkholder
integrand `(|1 − 2/p| |A|² + det A) |A|^{p−2}` of Guerra and Kristensen, and `p − 1` times that
of arXiv:2609.28311, (2). For `p > 2` this formula is not the rank-one convex Burkholder
function; the library uses it for `1 ≤ p < 2` only. -/
noncomputable def burkholder (p : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
    (‖conformalPart A‖ - (p - 1) * ‖anticonformalPart A‖)

/-- The reflection `J = diag (1, −1)`. -/
def reflection : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- The determinant multiplier of the support of Theorem 1.2: `(p − 1) m` clamped to the
interval `[L, U]`, `L = ((1 + t) m − p H)/(1 − t)`, `U = (p H + (1 − t) m)/(1 + t)`. -/
noncomputable def multiplier (p H m t : ℝ) : ℝ :=
  min ((p * H + (1 - t) * m) / (1 + t)) (max (((1 + t) * m - p * H) / (1 - t)) ((p - 1) * m))

-- END SHARED DEFINITIONS

end HomogeneousIsotropic

namespace HomogeneousIsotropicChallenge

open HomogeneousIsotropic

/-- **Conformal coordinates.** `det A = |z|² − |w|²`, with `z` the conformal and `w` the
anticonformal part of `A`. -/
theorem det_eq_norm_sq_sub (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = ‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2 := by
  sorry

/-- **Theorem 1.1.** Let `p ≥ 2` and let `F ≥ 0` be isotropic, positively `p`-homogeneous and
rank-one convex. Then `F` has a polyaffine support at every matrix; in particular `F` is
polyconvex. -/
theorem theorem1_1 {p : ℝ} (hp : 2 ≤ p) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (h0 : ∀ A, 0 ≤ F A)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : IsRankOneConvex F) :
    (∀ A₀, HasPolyaffineSupportAt F A₀) ∧ Polyconvex F := by
  sorry

/-- **Theorem 1.2.** Let `p` and `F` be as in Theorem 1.1. Let `|t| < 1`,
`H = F (diag (1, t)) > 0`, and let `m` be the slope of a supporting line at `t` of
`s ↦ F (diag (1, s))` on `[−1, 1]`. With `c = multiplier p H m t`, the polyaffine function
`A ↦ c t − (p − 1) H + (p H − t m − c t) a₁₁ + (m − c) a₂₂ + c det A` lies below `F` and equals
`F` at `diag (1, t)`. -/
theorem theorem1_2 {p : ℝ} (hp : 2 ≤ p) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (h0 : ∀ A, 0 ≤ F A)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : IsRankOneConvex F) {t m H : ℝ}
    (ht : |t| < 1) (hH : F !![1, 0; 0, t] = H) (hHpos : 0 < H)
    (hm : ∀ s : ℝ, -1 ≤ s → s ≤ 1 → H + m * (s - t) ≤ F !![1, 0; 0, s]) :
    (∀ A, polyaffine (multiplier p H m t * t - (p - 1) * H)
        !![p * H - t * m - multiplier p H m t * t, 0; 0, m - multiplier p H m t]
        (multiplier p H m t) A ≤ F A) ∧
      polyaffine (multiplier p H m t * t - (p - 1) * H)
        !![p * H - t * m - multiplier p H m t * t, 0; 0, m - multiplier p H m t]
        (multiplier p H m t) !![1, 0; 0, t] = H := by
  sorry

/-- **Theorem 1.3 (a).** For `p > 2`, an isotropic, positively `p`-homogeneous `F` is polyconvex
if and only if it is rank-one convex and nonnegative. -/
theorem theorem1_3_a {p : ℝ} (hp : 2 < p) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) :
    Polyconvex F ↔ IsRankOneConvex F ∧ ∀ A, 0 ≤ F A := by
  sorry

/-- **Theorem 1.3 (b).** An isotropic, positively `2`-homogeneous `F` is polyconvex if and only
if it is rank-one convex. -/
theorem theorem1_3_b {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous 2 F) : Polyconvex F ↔ IsRankOneConvex F := by
  sorry

/-- **Corollary 1.4.** Let `p ≥ 2` and let `F ≥ 0` be Borel, locally bounded, isotropic and
positively `p`-homogeneous. Then rank-one convexity, quasiconvexity and polyconvexity of `F` are
equivalent. -/
theorem corollary1_4 {p : ℝ} (hp : 2 ≤ p) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hm : Measurable F)
    (hb : ∀ A, ∃ U ∈ nhds A, ∃ C : ℝ, ∀ B ∈ U, |F B| ≤ C) :
    List.TFAE [IsRankOneConvex F, IsQuasiconvex F, Polyconvex F] := by
  sorry

/-- **Theorem 1.5.** Let `1 ≤ p < 2` and let `F ≥ 0` be isotropic, positively `p`-homogeneous
and rank-one convex. At every matrix `A₀` there are `c₀`, `m` with `(2 − p) |m| ≤ p c₀` such that
the Burkholder-type function `burkholderType p c₀ m` lies below `F` and equals `F` at `A₀`. -/
theorem theorem1_5 {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : IsRankOneConvex F) (A₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ c₀ m : ℝ, (2 - p) * |m| ≤ p * c₀ ∧ (∀ A, burkholderType p c₀ m A ≤ F A) ∧
      burkholderType p c₀ m A₀ = F A₀ := by
  sorry

/-- **Theorem 1.5, the identity.** A Burkholder-type function is a combination of the Burkholder
function and its mirror image `A ↦ burkholder p (J A)`; the coefficients are nonnegative when
`(2 − p) |m| ≤ p c₀`. -/
theorem theorem1_5_identity {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) (c₀ m : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderType p c₀ m A =
      (p * c₀ + (2 - p) * m) / (p * (2 - p)) * burkholder p A +
        (p * c₀ - (2 - p) * m) / (p * (2 - p)) * burkholder p (reflection * A) := by
  sorry

/-- **Corollary 1.6 (a).** Let `1 < p < 2` and let `F ≥ 0` be isotropic, positively
`p`-homogeneous and rank-one convex. If the Burkholder function `burkholder p` is quasiconvex,
then `F` is quasiconvex. -/
theorem corollary1_6_a {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : IsRankOneConvex F) (hB : IsQuasiconvex (burkholder p)) : IsQuasiconvex F := by
  sorry

/-- **Corollary 1.6 (b).** An isotropic, positively `1`-homogeneous, rank-one convex `F` is
nonnegative and convex. -/
theorem corollary1_6_b {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous 1 F) (hrc : IsRankOneConvex F) :
    (∀ A, 0 ≤ F A) ∧ ConvexOn ℝ Set.univ F := by
  sorry

/-- **Proposition 1.7.** For `0 < p < 1`, a positively `p`-homogeneous, rank-one convex `F` is
identically `0`. -/
theorem proposition1_7 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hhom : IsPosHomogeneous p F) (hrc : IsRankOneConvex F) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    F A = 0 := by
  sorry

/-- **Corollary 1.8.** Let `p > 0` and let `F ≥ 0` be isotropic, positively `p`-homogeneous and
rank-one convex. Then `F` is quasiconvex, provided that the Burkholder function `burkholder p`
is quasiconvex when `1 < p < 2`. -/
theorem corollary1_8 {p : ℝ} (hp : 0 < p) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : IsRankOneConvex F) (hB : 1 < p → p < 2 → IsQuasiconvex (burkholder p)) :
    IsQuasiconvex F := by
  sorry

end HomogeneousIsotropicChallenge
