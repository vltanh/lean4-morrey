# Basic: general mathematics

Lemmas that say nothing about the paper's objects, filed as Mathlib would file them, so that they
can be contributed. The general theories are in packages of their own:

- the calculus of variations (`grad`, rank-one convexity, quasiconvexity, the quasiconvex
  envelope, separately convex functions, distributions on `ℝ`, mollification) in
  `CalculusOfVariations`;
- torus and Euclidean Fourier analysis (Fourier coefficients of periodic functions, multipliers,
  the Beurling–Ahlfors transform) in `HarmonicAnalysis`.

| Module | Content | Where it could go |
| --- | --- | --- |
| [`Basic.LinearAlgebra.Matrix.RankTwo`](LinearAlgebra/Matrix/RankTwo.lean) | a `2 × 2` matrix over a field has rank at most one exactly when its determinant vanishes; the determinant of the matrix with rows `x`, `y` | `Mathlib/LinearAlgebra/Matrix/Rank.lean` |
| [`Basic.Analysis.Calculus.BumpFunction.Mollify`](Analysis/Calculus/BumpFunction/Mollify.lean) | mollification by a normed bump function, `ρ ⋆ g` (below) | `Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean` |
| [`Basic.Analysis.Convex.Tangent`](Analysis/Convex/Tangent.lean) | a convex function on `ℝ` has a supporting line at every point; if it lies above a function `k` near a point where they agree and `k` is differentiable, the tangent line of `k` supports it; a convex function `g` with `g(t)/t → 0` at `±∞` is constant | `Mathlib/Analysis/Convex/Deriv.lean` |
| [`Basic.Analysis.Convex.Legendre`](Analysis/Convex/Legendre.lean) | for a strictly convex continuous `h` on `[a, b]`: the minimizer `T m` of `h t − m t`, nondecreasing and continuous, and the minimum `k m`, differentiable with derivative `−T m` | `Mathlib/Analysis/Convex/` (a Legendre transform on an interval) |
| [`Basic.Analysis.Convex.Hinge`](Analysis/Convex/Hinge.lean) | a continuous convex function on `[0, R]` is a uniform limit of `N 0 + n₁ r + ∑ wᵢ max (r − ρᵢ) 0` with `wᵢ ≥ 0` | `Mathlib/Analysis/Convex/Piecewise.lean` |
| [`Basic.Topology.Order.SelfImproving`](Topology/Order/SelfImproving.lean) | a continuous `f` on `[a, b]` such that every local oscillation bound `D` improves to `f x − f y ≤ D/2` is nondecreasing | `Mathlib/Topology/Order/` |
| [`Basic.Analysis.Calculus.Deriv.MeanValue`](Analysis/Calculus/Deriv/MeanValue.lean) | a function with a derivative of constant sign at every point of `[a, b]` | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` |
| [`Basic.MeasureTheory.Integral.IntervalIntegral.Primitive`](MeasureTheory/Integral/IntervalIntegral/Primitive.lean) | primitives of functions continuous on an open set; the logarithmic divergence of `exp (∫₀^x ρ)` when `ρ ≥ κ/(b − x)` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean` |

The module `Basic.Analysis.Calculus.BumpFunction.Mollify`, mollification by a normed bump function,
`ρ ⋆ g`:

- smooth, linear, monotone;
- keeps constants, bounds, convexity and concavity, Lipschitz constants and periods;
- its value at `x` depends only on `g` near `x`;
- for Lipschitz `g` its derivative is the mollification of the derivative of `g`;
- pointwise convergence for continuous `g`, almost everywhere convergence of the derivatives for
  Lipschitz `g`;
- used by Šverák's Lemma 1 (the cut-off), Cassese's Proposition 4.2 and Corollary 1.6.
