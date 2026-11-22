# Basic: general mathematics

Lemmas that say nothing about the paper's objects, filed as Mathlib would file them, so that they
can be contributed. The general theories are in packages of their own: the calculus of variations
(`grad`, rank-one convexity, quasiconvexity, the quasiconvex envelope, separately convex functions,
distributions on `ℝ`, mollification) in `CalculusOfVariations`, and torus and Euclidean Fourier
analysis (Fourier coefficients of periodic functions, multipliers, the Beurling–Ahlfors transform)
in `HarmonicAnalysis`.

| Module | Content | Where it could go |
| --- | --- | --- |
| [`Basic.LinearAlgebra.Matrix.RankTwo`](LinearAlgebra/Matrix/RankTwo.lean) | a `2 × 2` matrix over a field has rank at most one exactly when its determinant vanishes; the determinant of the matrix with rows `x`, `y` | `Mathlib/LinearAlgebra/Matrix/Rank.lean` |
| [`Basic.Analysis.Calculus.BumpFunction.Mollify`](Analysis/Calculus/BumpFunction/Mollify.lean) | mollification by a normed bump function, `ρ ⋆ g`: smooth, linear, monotone, keeps constants, bounds, convexity and concavity, Lipschitz constants and periods; its value at `x` depends only on `g` near `x`; for Lipschitz `g` its derivative is the mollification of the derivative of `g`; pointwise convergence for continuous `g`, almost everywhere convergence of the derivatives for Lipschitz `g`; used by Šverák's Lemma 1 (the cut-off), Cassese's Proposition 4.2 and Corollary 1.6 | `Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean` |
