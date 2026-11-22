module

public import Morrey.Cassese.Defs
public import BanachProbability.Schatten.Triangle

/-!
# The triangle inequality for the Schatten norms

The paper takes for granted that `‖·‖_{S_q}`, `q ∈ [1, ∞]`, is a norm on `ℝ^{d×m}` (Section 1.5;
Bhatia, *Matrix analysis*, Chapter IV, which was not accessible). The triangle inequality is the
package `BanachProbability`'s `schattenNorm_add_le`, whose proof follows J.-C. Bourin and
T. Zhang, *Matrix triangle inequalities: past, present, and future*, arXiv:2610.30538 (2026),
Proposition 3.13 by their Remark 3.14: for `q < ∞`, von Neumann's convexity inequality
`Tr g (t X + (1 − t) Y) ≤ t Tr g (X) + (1 − t) Tr g (Y)` (their (1.1), proved there by Peierls's
argument) with `g = |·|^q`, applied to the Hermitian dilations `[[0, A], [Aᵀ, 0]]`,
`[[0, B], [Bᵀ, 0]]` of `A` and `B` normalized to `‖A‖_{S_q} = ‖B‖_{S_q} = 1`, then
homogeneity; for `q = ∞`, the first of Weyl's inequalities, `s_1 (A + B) ≤ s_1 (A) + s_1 (B)`.
The Schatten norms of `Morrey/Cassese/Defs.lean` are the package's by definition
(`schattenNorm_eq_banachProbability`, `rfl`).
-/

@[expose] public section

open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-- The triangle inequality for `‖·‖_{S_q}`, `q ∈ [1, ∞]`: the package's
`BanachProbability.schattenNorm_add_le` (Bourin–Zhang, Proposition 3.13, by Remark 3.14). -/
theorem square_schattenNorm_add_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B :=
  BanachProbability.schattenNorm_add_le hq A B

end Cassese
