module

public import Sverak.Construction

/-!
# Šverák 1992, Lemma 2: the extension is rank-one convex

For each `ε > 0` there is `k = k(ε) > 0` such that
`F (X) = f (P X) + ε |X|² + ε |X|⁴ + k |X − P X|²` (`Morrey.sverakF ε k`) is rank-one convex on
`M^{3×2}`. The paper's proof:

1. eq. (6): `(d²/dt²) F (A + t Y)|₀ = (d²/dt²) f (P A + t P Y)|₀ + 2ε |Y|² + 4ε |A|² |Y|²
   + 8ε ⟨A, Y⟩² + 2k |Y − P Y|²`;
2. since `X ↦ f (P X)` is a homogeneous cubic polynomial, `(d²/dt²) f (P A + t P Y)|₀ ≥ −c |A| |Y|²`
   for some `c > 0`, so (7) and `(*)`: the second derivative is `≥ 0` when `|A| ≥ c / (4ε)`;
3. eq. (8) and a compactness argument on `𝒦 = {(A, Y) : |A| ≤ c/(4ε), rank Y = 1, |Y| = 1}`:
   there is `k₀` with `g (A, Y, k₀) > ε` on `𝒦`, otherwise a limit `(Ā, Ȳ)` would have
   `Ȳ = P Ȳ` (a rank-one direction of `L`) and `(d²/dt²) f (P Ā + t P Ȳ)|₀ ≤ −ε`, against the
   convexity of `f` on rank-one lines of `L` (`sverakf_affine_of_rankOne`);
4. together, `F` is rank-one convex for `k = k₀`.
-/

@[expose] public section

open Morrey

namespace Sverak

/-- **Lemma 2** (`sv-lemma2`). Let `P` be the orthogonal projection onto `L` and `f` the function
`−r s t` on `L`. For each `ε > 0` there exists `k = k(ε) > 0` such that
`F (X) = f (P X) + ε |X|² + ε |X|⁴ + k |X − P X|²` is rank-one convex on `M^{3×2}`. -/
theorem lemma2 {ε : ℝ} (hε : 0 < ε) : ∃ k > 0, RankOneConvex (sverakF ε k) := by
  sorry

end Sverak
