# Basic: general mathematics

Lemmas that say nothing about the paper's objects, filed as Mathlib would file them, so that they
can be contributed.

| Module | Content | Where it could go |
| --- | --- | --- |
| [`Basic.LinearAlgebra.Matrix.RankTwo`](LinearAlgebra/Matrix/RankTwo.lean) | a `2 × 2` matrix over a field has rank at most one exactly when its determinant vanishes; the determinant of the matrix with rows `x`, `y` | `Mathlib/LinearAlgebra/Matrix/Rank.lean` |
| [`Basic.Analysis.Convex.SeparatelyConvex`](Analysis/Convex/SeparatelyConvex.lean) | a function on the real `d × m` matrices that is convex along every line in the direction of a matrix unit is locally Lipschitz (`Matrix.locallyLipschitz_of_convexOn_single`), the argument of Dacorogna's Theorem 2.31; used by Rindler's Lemma 5.6 and by Dacorogna's formula | `Mathlib/Analysis/Convex/Continuous.lean` |
| [`Basic.Analysis.Fourier.TorusLipschitz`](Analysis/Fourier/TorusLipschitz.lean) | Fourier coefficients on the unit cube of `ℤ^ι`-periodic functions: Parseval's identity, the coefficients `2πi ⟨n, v⟩ f̂ (n)` of the derivative of a Lipschitz periodic function, and Fejér means, bounded by `sup ‖g‖` and converging in `L²`; used by Cassese's Proposition 7.2 | `Mathlib/Analysis/Fourier/AddCircleMulti.lean` |
| [`Basic.CalculusOfVariations.Basic`](CalculusOfVariations/Basic.lean) | the textbook notions of the vectorial calculus of variations (Dacorogna, Rindler, Chapter 5): the derivative matrix `grad`, rank-one convexity and affinity, quasiconvexity on a domain and with periodic test maps, local boundedness and the quasiconvex envelope; the cited results of `Morrey/Common/External` are stated with them | a new `Mathlib/Analysis/CalculusOfVariations/` |
