module

public import BanachProbability.UMD.Complex
public import BanachProbability.ZigZag.Basic

/-!
# Complex UMD constants (Yaroslavtsev 2018, Lemma 3.2 and Proposition 3.7)

I. Yaroslavtsev, *Even Fourier multipliers and martingale transforms in infinite dimensions*,
Indag. Math. 29 (2018) (arXiv:1710.04958; §3 read), which Cassese (arXiv:2608.03488v3) cites
for Proposition 2.7 (5) (Lemma 3.2, TeX lines 842–856) and, with HNVW I, Theorem 4.5.6, for the
complex half of Proposition 2.7 (6) (Proposition 3.7, TeX lines 857–869):

* `External.Yaroslavtsev.lemma3_2`: for a complex Banach space `X` and `p ∈ (1, ∞)`,
  `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`, where `UMD_{ℂ,p}` is the best constant for
  transforms by predictable unimodular complex multipliers (`BanachProbability.complexUMDConst`)
  and `UMD_p` that of `X` as a real space;
* `External.Yaroslavtsev.proposition3_7`: if `U` is zig-zag concave in the complex sense
  (`z ↦ U (x + z, y + ε z)` concave for `|ε| ≤ 1`, `ε ∈ ℂ`; `U (0, 0) = 0`;
  `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`), then `UMD_{ℂ,p} (X) ≤ β`;
* `External.Yaroslavtsev.proposition3_7_iff`: the equivalence, `UMD_{ℂ,p} (X) < ∞` if and only if
  such a `U` exists for some `β > 0`.

The predictable multipliers are Cassese's: Yaroslavtsev's constants `β^A_{p,X}` are for
deterministic multipliers with values in a set `A ⊂ 𝕂`, and Lemma 3.2 is `β^{{−1,1}}_{p,X} ≤
β^D_{p,X} = β_{p,X} ≤ (π / 2) β^{{−1,1}}_{p,X}`, `D` the closed unit disc; the two kinds of
multipliers have the same constants (HNVW I, Theorem 4.2.25). Proposition 3.7 is for any `A` and
without `U (0, 0) = 0`, and says that the smallest admissible `β` is `β^A_{p,X}`; the set used is
`A = D`.

Proofs: in the package `BanachProbability` (`lean4-banach-probability`). Lemma 3.2 gives no proof:
it is "proven in" T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume
I* (HNVW I, 2016; read), Proposition 4.2.10 (pp. 285–286), whose argument is followed
(`BanachProbability.umdConst_le_complexUMDConst_le`): real signs are unimodular, and complex numbers
`α_1, …, α_n` of modulus at most one are `(π / 2) Σ_j λ^{(j)} ε^{(j)}` with `ε^{(j)} ∈ {±1}^n` and
`Σ_j |λ^{(j)}| ≤ 1` (Proposition 3.2.14, by Hahn–Banach and `∫₀¹ |cos (2π (s + t))| dt = 2/π`); the
triangle inequality gives the bound for deterministic multipliers, and Theorem 4.2.25 (pp. 300–301)
gives it for predictable ones. The proof of Proposition 3.7 "repeats the one given in" HNVW I,
Theorem 4.5.6, with multipliers in `A` (only the finiteness of `U` is argued anew, for a general
`A`); the package proves Theorem 4.5.6 by the book's argument over `ℝ` and `ℂ` at once, with
multipliers in the closed unit ball (`External.HNVW.theorem4_5_6`).
-/

@[expose] public section

open scoped ENNReal

namespace External.Yaroslavtsev

open BanachProbability

/-- **Yaroslavtsev (2018), Lemma 3.2**: for a complex Banach space `X` and `p ∈ (1, ∞)`,
`UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`. -/
theorem lemma3_2 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ complexUMDConst X p ∧
      complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p :=
  umdConst_le_complexUMDConst_le hp

/-- **Yaroslavtsev (2018), Proposition 3.7** (for the closed unit disc), the bound: for a complex
Banach space `X`, `p ∈ (1, ∞)` and `β > 0`, a function `U` that is zig-zag concave in the complex
sense bounds the complex UMD constant, `UMD_{ℂ,p} (X) ≤ β`. -/
theorem proposition3_7 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {p β : ℝ} (hp : 1 < p) (hβ : 0 < β) {U : X → X → ℝ} (hU : IsComplexZigZagConcave p β U) :
    complexUMDConst X p ≤ ENNReal.ofReal β :=
  complexUMDConst_le_of_isComplexZigZagConcave hp hβ hU

/-- **Yaroslavtsev (2018), Proposition 3.7** (for the closed unit disc), the equivalence: for a
complex Banach space `X` and `p ∈ (1, ∞)`, `UMD_{ℂ,p} (X) < ∞` if and only if there is a function
`U` that is zig-zag concave in the complex sense for some `β > 0`. -/
theorem proposition3_7_iff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {p : ℝ} (hp : 1 < p) :
    complexUMDConst X p < ⊤ ↔
      ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsComplexZigZagConcave p β U :=
  complexUMDConst_lt_top_iff_exists_isComplexZigZagConcave hp

end External.Yaroslavtsev
