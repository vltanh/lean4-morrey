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

/-- **Kakutani's fixed-point theorem** (the paper's Theorem 6.2, `kakutani`; Smirnov 2002): an upper
semicontinuous set-valued map of a nonempty compact convex subset of a finite-dimensional real
normed space into itself, with nonempty convex compact values, has a fixed point. -/
theorem exists_fixedPoint [FiniteDimensional ℝ V] {A : Set V} (hne : A.Nonempty)
    (hcomp : IsCompact A) (hconv : Convex ℝ A) {F : V → Set V} (hmaps : ∀ x ∈ A, F x ⊆ A)
    (husc : UpperSemicontinuousOn F A) (hFne : ∀ x ∈ A, (F x).Nonempty)
    (hFconv : ∀ x ∈ A, Convex ℝ (F x)) (hFcomp : ∀ x ∈ A, IsCompact (F x)) :
    ∃ x ∈ A, x ∈ F x := by
  -- The graph of `F` over `A` is closed: take `(x, y)` in its closure; then `x ∈ A`, and if
  -- `y ∉ F x`, disjoint open sets `W ⊇ F x` and `U ∋ y` and upper semicontinuity at `x` give a
  -- neighbourhood of `(x, y)` that misses the graph.
  have hgraph : IsClosed {p : V × V | p.1 ∈ A ∧ p.2 ∈ F p.1} := by
    refine isClosed_of_closure_subset fun p hp => ?_
    have hA : p.1 ∈ A :=
      closure_minimal (s := {p : V × V | p.1 ∈ A ∧ p.2 ∈ F p.1}) (t := Prod.fst ⁻¹' A)
        (fun q hq => hq.1) (hcomp.isClosed.preimage continuous_fst) hp
    refine ⟨hA, ?_⟩
    by_contra hy
    obtain ⟨W, U, hW, hU, hFW, hyU, hWU⟩ :=
      SeparatedNhds.of_isCompact_isCompact (hFcomp _ hA) isCompact_singleton
        (Set.disjoint_singleton_right.mpr hy)
    have hN := husc _ hA W hW hFW
    rw [eventually_nhdsWithin_iff] at hN
    have hmem : {z | z ∈ A → F z ⊆ W} ×ˢ U ∈ 𝓝 p :=
      prod_mem_nhds hN (hU.mem_nhds (hyU rfl))
    obtain ⟨q, hqNU, hqG⟩ := mem_closure_iff_nhds.mp hp _ hmem
    exact hWU.ne_of_mem (hqNU.1 hqG.1 hqG.2) hqNU.2 rfl
  exact _root_.Kakutani.exists_fixedPoint hconv hcomp hne hmaps hFne hFconv hgraph

end External.Kakutani
