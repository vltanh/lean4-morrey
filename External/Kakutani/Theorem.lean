module

public import FixedPoint.Kakutani.Convex

/-!
# Kakutani's fixed-point theorem

The paper (Theorem 6.2, citing G. V. Smirnov, *Introduction to the Theory of Differential
Inclusions*, AMS Graduate Studies in Mathematics 41, 2002) uses Kakutani's theorem in the form:
a set-valued map `F` of a nonempty compact convex set `A ⊆ ℝ^d` into itself that is upper
semicontinuous, with nonempty convex compact values, has a fixed point `x ∈ F x`.

Upper semicontinuity is the topological notion of set-valued analysis (Smirnov, Section 1.1):
for each `x ∈ A` and each open set `W ⊇ F x`, every point of `A` close enough to `x` is sent into
`W`.

The proof derives the statement from `Kakutani.exists_fixedPoint` of the library
[lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point), which takes a closed graph
instead: an upper semicontinuous map with closed values on a closed set has a closed graph.
-/

@[expose] public section

open Filter Topology

namespace External.Kakutani

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A set-valued map `F` is upper semicontinuous on `A` when, for each `x ∈ A` and each open set
`W ⊇ F x`, every point of `A` close enough to `x` is sent into `W`. -/
def UpperSemicontinuousOn (F : V → Set V) (A : Set V) : Prop :=
  ∀ x ∈ A, ∀ W : Set V, IsOpen W → F x ⊆ W → ∀ᶠ y in 𝓝[A] x, F y ⊆ W

/-- **Kakutani's fixed-point theorem** (the paper's Theorem 6.2; Smirnov 2002): an upper
semicontinuous set-valued map of a nonempty compact convex subset of a finite-dimensional real
normed space into itself, with nonempty convex compact values, has a fixed point. -/
theorem exists_fixedPoint [FiniteDimensional ℝ V] {A : Set V} (hne : A.Nonempty)
    (hcomp : IsCompact A) (hconv : Convex ℝ A) {F : V → Set V} (hmaps : ∀ x ∈ A, F x ⊆ A)
    (husc : UpperSemicontinuousOn F A) (hFne : ∀ x ∈ A, (F x).Nonempty)
    (hFconv : ∀ x ∈ A, Convex ℝ (F x)) (hFcomp : ∀ x ∈ A, IsCompact (F x)) :
    ∃ x ∈ A, x ∈ F x := by
  sorry

end External.Kakutani
