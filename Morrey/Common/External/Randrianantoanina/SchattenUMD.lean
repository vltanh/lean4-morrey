module

public import BanachProbability.Noncommutative.SchattenUMD

/-!
# Schatten classes are UMD, uniformly in the dimension (Randrianantoanina 2002)

N. Randrianantoanina, *Non-commutative martingale transforms*, J. Funct. Anal. 194 (2002)
(arXiv:math/0111264, read in full for §§2–4), which Cassese (arXiv:2608.03488v3) cites as
Proposition 2.7 (2) (Corollary 4.5, TeX lines 832–834): for `q ∈ (1, ∞)`,
`UMD₂ (S_q (ℓ₂ (ℕ))) ≤ C (q* − 1)` with an absolute constant `C`. The source's Corollary 4.5 bounds
the UMD constant of a non-commutative `L^q (M)` at its own exponent,
`C_q (L^q (M)) ≤ C q² / (q − 1)`; the bound at the exponent `2` comes with Pisier's extrapolation
(the source's Remark 4.6 (1), `C₂ (S^q) = O (q)`).

Cassese uses the subspaces `S_q^{d×d}` of real `d × d` matrices, uniformly in `d`; these are the
cases stated (`BanachProbability.SchattenSpace q n n`, real `n × n` matrices with the Schatten
norm):

* `External.Randrianantoanina.corollary4_5`: `UMD_q (S_q^{n×n}) ≤ C q² / (q − 1)`, uniformly in
  `n` and `q ∈ (1, ∞)`;
* `External.Randrianantoanina.remark4_6`: `UMD₂ (S_q^{n×n}) ≤ C (q* − 1)`, uniformly in `n` and
  `q ∈ (1, ∞)`, the form Cassese quotes.

Proof: in the package `BanachProbability` (`lean4-banach-probability`),
`BanachProbability.umdConst_schattenSpace_le` (`UMD_q (S_q) ≤ K q*`, and `q* ≤ q² / (q − 1)`) and
`BanachProbability.umdConst_two_schattenSpace_le`, by the source's argument on the algebra
`L^∞ (Ω) ⊗ M_n (ℝ)` of matrix-valued functions on a filtered probability space, with the conditional
expectations entry by entry: Cuculescu's projections and the weak type `(1, 1)` of martingale
transforms (Theorem 3.1, with a rank count in place of Lemma 3.2's generalized singular values, and
the constant `26` in (3.2), for positive `x`, and `52` in general; the source's value in (3.2) is
`inf {24 α⁻¹ β⁻² + 2 (1 − α)⁻¹ : α, β ∈ (0, 1)}`, printed as `14√3/3 + 28`, a slip for `26 + 8√3`),
Marcinkiewicz interpolation and duality (Theorem 4.3, whose step "by interpolation" is carried out
in three regimes so that the constant stays uniform near `q = 2`), the Hermitian dilation for
non-symmetric matrices, and extrapolation to the exponent `2` (Remark 4.6 (1); HNVW I, Theorem
4.2.7, in place of the theorem of Pisier it quotes).
-/

@[expose] public section

open scoped ENNReal

namespace External.Randrianantoanina

open BanachProbability

/-- **Randrianantoanina (2002), Corollary 4.5**, for real square matrices: there is an absolute
`C > 0` with `UMD_q (S_q^{n×n}) ≤ C q² / (q − 1)` for every `q ∈ (1, ∞)` and every `n`. -/
theorem corollary4_5 : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ →
    ∀ (n : Type) [Fintype n] [DecidableEq n],
      umdConst (SchattenSpace q n n) q.toReal ≤
        ENNReal.ofReal (C * (q.toReal ^ 2 / (q.toReal - 1))) := by
  obtain ⟨K, hK, h⟩ := umdConst_schattenSpace_le
  refine ⟨K, hK, fun q _ hq hqt n _ _ => (h q hq hqt n).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hq1 : 1 < q.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqt).2 hq
  have hq0 : 0 < q.toReal - 1 := by linarith
  gcongr
  -- `q* = max (q, q / (q − 1)) ≤ q² / (q − 1)`
  refine max_le ?_ ?_
  · rw [le_div_iff₀ hq0]; nlinarith
  · exact div_le_div_of_nonneg_right (by nlinarith) hq0.le

/-- **Randrianantoanina (2002), Corollary 4.5 with Remark 4.6 (1)**, the form Cassese quotes in
Proposition 2.7 (2), for real square matrices: there is an absolute `C > 0` with
`UMD₂ (S_q^{n×n}) ≤ C (q* − 1)` for every `q ∈ (1, ∞)` and every `n`. -/
theorem remark4_6 : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ →
    ∀ (n : Type) [Fintype n] [DecidableEq n],
      umdConst (SchattenSpace q n n) 2 ≤ ENNReal.ofReal (C * (pStar q.toReal - 1)) :=
  umdConst_two_schattenSpace_le

end External.Randrianantoanina
