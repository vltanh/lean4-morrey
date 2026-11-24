module

public import Morrey.HomogeneousIsotropic.Profile
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrands of any sign: the definitions

The objects of the proof that an isotropic, positively `p`-homogeneous, rank-one convex integrand
on `ℝ^{2×2}` is quasiconvex with no sign condition (`Morrey/HomogeneousIsotropic/Signed/Main.lean`).
Throughout, `p > 1`, `p ≠ 2`, and `e` is the sign of `p − 2`: `e = −1` if `p < 2`, `e = 1` if
`p > 2` (the hypotheses `e = 1 ∨ e = −1` and `0 < e (p − 2)`); `a = e (p − 2)/p = |p − 2|/p`.

* `slice Φ t = Φ ((1 + t)/2, (1 − t)/2)`: the slice of a profile, for `t ∈ [−1, 1]`.
* `supportDet`, `supportMod`, `supportConst`, `restrictedSupport`: at a point of the slice with
  value `H` and supporting slope `m`, the function
  `q (x, y) = α + v r + c (x² − y²)`, where `r = x` if `e = −1` and `r = y` if `e = 1`,
  `c = (e p H + (1 − e t) m)/(1 + e t)`, `v = 2 (p H − 2 t m)/(1 + e t)`, `α = c t − (p − 1) H`.
* `IsHardBase p e Φ t m`: `|t| < 1`, the line of slope `m` through `(t, slice Φ t)` lies below
  the slice, and its value at `−a` is negative.
* `radialProfile e N x y = (x + y + e (x − y)) N (x + y) − 2 ∫₀^{x+y} N`.
* `IsPath p e Φ t₀ m₀ L R T k S`: a path of hard bases with the slopes `m₀ − e ξ`, `ξ ∈ [0, L]`,
  at the points `T ξ` of the slice, along which the scale `S` grows from `1` to `R`.
-/

@[expose] public section

open Set

namespace HomogeneousIsotropic

/-- The slice of a profile, `h (t) = Φ ((1 + t)/2, (1 − t)/2)`; it is used for `t ∈ [−1, 1]`, and
then `Φ (x, y) = (x + y)^p h ((x − y)/(x + y))`. -/
noncomputable def slice (Φ : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  Φ ((1 + t) / 2) ((1 - t) / 2)

/-- The determinant coefficient `c = (e p H + (1 − e t) m)/(1 + e t)` of the restricted
support. -/
noncomputable def supportDet (p e H m t : ℝ) : ℝ :=
  (e * p * H + (1 - e * t) * m) / (1 + e * t)

/-- The coefficient `v = 2 (p H − 2 t m)/(1 + e t)` of the modulus in the restricted support. -/
noncomputable def supportMod (p e H m t : ℝ) : ℝ :=
  2 * (p * H - 2 * t * m) / (1 + e * t)

/-- The constant `α = c t − (p − 1) H` of the restricted support. -/
noncomputable def supportConst (p e H m t : ℝ) : ℝ :=
  supportDet p e H m t * t - (p - 1) * H

/-- The restricted support `q (x, y) = α + v r + c (x² − y²)`, where
`r = ((x + y) − e (x − y))/2` is `x` if `e = −1` and `y` if `e = 1`. -/
noncomputable def restrictedSupport (p e H m t x y : ℝ) : ℝ :=
  supportConst p e H m t + supportMod p e H m t * ((x + y - e * (x - y)) / 2) +
    supportDet p e H m t * (x ^ 2 - y ^ 2)

/-- A hard base: a point `t` of the open interval `(−1, 1)` and a slope `m` such that the line
of slope `m` through `(t, slice Φ t)` lies below the slice (in the form of a Burkholder-type
minorant of `Φ`) and is negative at `−a`, `a = e (p − 2)/p`:
`p (slice Φ t − m t) − e (p − 2) m < 0`. -/
structure IsHardBase (p e : ℝ) (Φ : ℝ → ℝ → ℝ) (t m : ℝ) : Prop where
  /-- The base point is in the open interval `(−1, 1)`. -/
  abs_lt : |t| < 1
  /-- The line of slope `m` through `(t, slice Φ t)` gives a Burkholder-type minorant. -/
  minorant : BurkholderMinorant p (slice Φ t - m * t) m Φ
  /-- The line is negative at `−a`. -/
  neg : p * (slice Φ t - m * t) - e * (p - 2) * m < 0

/-- A path of hard bases. For `ξ ∈ [0, L]` the slope `m₀ − e ξ` is a supporting slope of the slice
at `T ξ`, with intercept `k ξ`, and this is a hard base; `S` is the scale: `S 0 = 1`, `S L = R`,
and `S' = −S (1 + e T)/(p k − e (p − 2) (m₀ − e ξ))` (the denominator is `p` times the value of
the supporting line at `−a`, which is negative). -/
structure IsPath (p e : ℝ) (Φ : ℝ → ℝ → ℝ) (t₀ m₀ L R : ℝ) (T k S : ℝ → ℝ) : Prop where
  /-- The path has a nonnegative length. -/
  length_nonneg : 0 ≤ L
  /-- Every point of the path is a hard base. -/
  hard : ∀ ξ ∈ Icc 0 L, IsHardBase p e Φ (T ξ) (m₀ - e * ξ)
  /-- `k` is the intercept of the supporting line. -/
  intercept : ∀ ξ ∈ Icc 0 L, k ξ = slice Φ (T ξ) - (m₀ - e * ξ) * T ξ
  /-- The path starts at `t₀`. -/
  base_zero : T 0 = t₀
  /-- The base points depend continuously on the parameter. -/
  continuousOn_base : ContinuousOn T (Icc 0 L)
  /-- The derivative of the intercept. -/
  hasDerivAt_intercept : ∀ ξ ∈ Icc 0 L, HasDerivAt k (e * T ξ) ξ
  /-- The scale starts at `1`. -/
  scale_zero : S 0 = 1
  /-- The scale ends at `R`. -/
  scale_length : S L = R
  /-- The scale is positive. -/
  scale_pos : ∀ ξ ∈ Icc 0 L, 0 < S ξ
  /-- The differential equation of the scale. -/
  hasDerivAt_scale : ∀ ξ ∈ Icc 0 L,
    HasDerivAt S (-(S ξ * (1 + e * T ξ)) / (p * k ξ - e * (p - 2) * (m₀ - e * ξ))) ξ

end HomogeneousIsotropic
