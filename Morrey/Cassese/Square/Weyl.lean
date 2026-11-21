module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Weyl's monotonicity theorem

For symmetric operators `S ≤ T` (`⟨S v, v⟩ ≤ ⟨T v, v⟩` for all `v`) on an `n`-dimensional real
inner product space, the decreasingly ordered eigenvalues satisfy `λ_k (S) ≤ λ_k (T)` for every
`k` (`square_weyl`). This is the eigenvalue monotonicity behind fact (3) of Section 1.5 of
Cassese (`0 ⪯ A ⪯ B ⇒ ‖A‖_{S_q} ≤ ‖B‖_{S_q}`), proved by the Courant–Fischer argument (Bhatia,
*Matrix analysis*, Corollary III.2.3): the span of the first `k + 1` eigenvectors of `S` meets the
span of the last `n − k` eigenvectors of `T`; on a common unit vector `v`,
`λ_k (S) ≤ ⟨S v, v⟩ ≤ ⟨T v, v⟩ ≤ λ_k (T)`.
-/

@[expose] public section

open Module

namespace Cassese

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- `⟨T v, v⟩ = Σ_i λ_i ⟨b_i, v⟩²` in an orthonormal eigenbasis. -/
theorem square_inner_eq_sum [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hn : finrank ℝ E = n)
    (v : E) :
    inner ℝ (T v) v = ∑ i, hT.eigenvalues hn i * ((hT.eigenvectorBasis hn).repr v i) ^ 2 := by
  set b := hT.eigenvectorBasis hn
  rw [← b.sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm, ← b.repr_apply_apply, ← b.repr_apply_apply,
    hT.eigenvectorBasis_apply_self_apply hn]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

/-- `‖v‖² = Σ_i ⟨b_i, v⟩²`. -/
theorem square_norm_sq_eq_sum (b : OrthonormalBasis (Fin n) ℝ E) (v : E) :
    ‖v‖ ^ 2 = ∑ i, (b.repr v i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm, ← b.repr_apply_apply, sq]

/-- A vector in the span of `b_i`, `i ∈ S`, has no component along `b_j`, `j ∉ S`. -/
theorem square_repr_eq_zero {b : OrthonormalBasis (Fin n) ℝ E} {S : Set (Fin n)} {v : E}
    (hv : v ∈ Submodule.span ℝ (b '' S)) {j : Fin n} (hj : j ∉ S) : b.repr v j = 0 := by
  rw [b.repr_apply_apply]
  have h : Submodule.span ℝ (b '' S) ≤ LinearMap.ker (innerₛₗ ℝ (b j)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply]
    exact b.orthonormal.2 fun h => hj (h ▸ hi)
  exact h hv

/-- The span of the `b_i`, `i ∈ S`, has dimension `|S|`. -/
theorem square_finrank_span (b : OrthonormalBasis (Fin n) ℝ E) (S : Finset (Fin n)) :
    finrank ℝ (Submodule.span ℝ (b '' (S : Set (Fin n)))) = S.card := by
  have hli : LinearIndependent ℝ (fun i : (S : Set (Fin n)) => b i) :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have := finrank_span_eq_card hli
  rw [show Set.range (fun i : (S : Set (Fin n)) => b i) = b '' (S : Set (Fin n)) by
    ext x; simp] at this
  rw [this]
  simp

/-- **Weyl's monotonicity theorem**: `S ≤ T` implies `λ_k (S) ≤ λ_k (T)` for the decreasingly
ordered eigenvalues. -/
theorem square_weyl [FiniteDimensional ℝ E] {S T : E →ₗ[ℝ] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : finrank ℝ E = n) (hST : ∀ v, inner ℝ (S v) v ≤ inner ℝ (T v) v) (k : Fin n) :
    hS.eigenvalues hn k ≤ hT.eigenvalues hn k := by
  set U := Submodule.span ℝ ((hS.eigenvectorBasis hn) ''
    ((Finset.Iic k : Finset (Fin n)) : Set (Fin n)))
  set V := Submodule.span ℝ ((hT.eigenvectorBasis hn) ''
    ((Finset.Ici k : Finset (Fin n)) : Set (Fin n)))
  have hU : finrank ℝ U = k + 1 := by rw [square_finrank_span, Fin.card_Iic]
  have hV : finrank ℝ V = n - k := by rw [square_finrank_span, Fin.card_Ici]
  have hUV : U ⊓ V ≠ ⊥ := by
    intro h
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U V
    rw [h, finrank_bot, add_zero, hU, hV] at h1
    have h2 := Submodule.finrank_le (U ⊔ V)
    rw [hn] at h2
    have hk := k.isLt
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUV
  have hvU := (Submodule.mem_inf.1 hv).1
  have hvV := (Submodule.mem_inf.1 hv).2
  have h1 : hS.eigenvalues hn k * ‖v‖ ^ 2 ≤ inner ℝ (S v) v := by
    rw [square_inner_eq_sum hS hn, square_norm_sq_eq_sum (hS.eigenvectorBasis hn), Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j ≤ k
    · exact mul_le_mul_of_nonneg_right (hS.eigenvalues_antitone hn hj) (sq_nonneg _)
    · have : (hS.eigenvectorBasis hn).repr v j = 0 := square_repr_eq_zero hvU (by simpa using hj)
      simp [this]
  have h2 : inner ℝ (T v) v ≤ hT.eigenvalues hn k * ‖v‖ ^ 2 := by
    rw [square_inner_eq_sum hT hn, square_norm_sq_eq_sum (hT.eigenvectorBasis hn), Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : k ≤ j
    · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hj) (sq_nonneg _)
    · have : (hT.eigenvectorBasis hn).repr v j = 0 := square_repr_eq_zero hvV (by simpa using hj)
      simp [this]
  have hpos : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.2 hv0; positivity
  have := hST v
  nlinarith

end Cassese
