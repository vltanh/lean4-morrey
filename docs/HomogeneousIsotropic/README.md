# Homogeneous isotropic integrands on `2 × 2` matrices: Morrey's problem for every exponent

A result of this repository on the open `2 × 2` case of Morrey's problem, proved in Lean 4 with
Mathlib; the [overview](../../README.md) describes the problem and the state of each case.

- The paper: [`paper/main.tex`](paper/main.tex) ([PDF](paper/main.pdf)).
- The statements of record: [`palomar/HomogeneousIsotropic/Challenge.lean`](../../palomar/HomogeneousIsotropic/Challenge.lean).
- How it was made: [CREDITS.md](CREDITS.md).

## What is proved, and from which hypotheses

The integrands are functions `F : ℝ^{2×2} → ℝ`. Four hypotheses occur:

- **H1**, isotropy: `F(QAR) = F(A)` for all rotations `Q, R ∈ SO(2)`;
- **H2**, positive `p`-homogeneity: `F(λA) = λ^p F(A)` for `λ > 0`;
- **H3**, rank-one convexity: `t ↦ F(A + tB)` is convex for every `B` of rank one;
- **N**, the sign condition: `F ≥ 0`.

The Burkholder function is `B_p(A) = (|1 − 2/p| |A|² + det A) |A|^{p−2}`, with the operator norm,
and `J = diag(1, −1)`.

| Exponent | Hypotheses | Conclusion | Lean | Status |
| --- | --- | --- | --- | --- |
| `0 < p < 1` | H2, H3 | `F = 0` | [`eq_zero_of_rankOneConvex_of_lt_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L537) | **proved** |
| `p = 1` | H1, H2, H3 | `F ≥ 0`, and `F` is convex (Dacorogna 1995) | [`convexOn_of_rankOneConvex_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L462) | **proved** |
| `1 < p < 2` | H1, H2, H3, N | at every matrix, a touching minorant `α B_p(A) + β B_p(JA)` with `α, β ≥ 0` | [`exists_burkholderType_le`](../../Morrey/HomogeneousIsotropic/Main.lean#L285) | **proved** |
| `1 < p < 2` | H1, H2, H3, N, and `B_p` quasiconvex | `F` is quasiconvex | [`quasiconvex_of_rankOneConvex_of_burkholder`](../../Morrey/HomogeneousIsotropic/Main.lean#L416) | **proved**, with the quasiconvexity of `B_p` as a hypothesis |
| `p = 2` | H1, H2, H3 | `F` is polyconvex | [`polyconvex_of_rankOneConvex_two`](../../Morrey/HomogeneousIsotropic/Main.lean#L268) | **proved** |
| `p > 2` | H1, H2, H3, N | `F` is polyconvex, with a polyaffine support at every matrix in closed form | [`polyconvex_of_rankOneConvex`](../../Morrey/HomogeneousIsotropic/Main.lean#L68), [`polyaffine_multiplier_le`](../../Morrey/HomogeneousIsotropic/Main.lean#L209) | **proved** |
| `p > 2` | H1, H2, and `F < 0` somewhere | `F` is not polyconvex | [`nonneg_of_polyconvex`](../../Morrey/HomogeneousIsotropic/Main.lean#L93) | **proved** |
| every `p > 0` | H1, H2, H3, N, and `B_p` quasiconvex if `1 < p < 2` | `F` is quasiconvex | [`quasiconvex_of_rankOneConvex_of_pos`](../../Morrey/HomogeneousIsotropic/Main.lean#L580) | **proved**, with that hypothesis |

So rank-one convexity implies quasiconvexity for nonnegative, isotropic, positively
`p`-homogeneous integrands, for every `p > 0`. For `p ≥ 2` this answers Question 1.7 of Guerra
and Kristensen (2022), who proved polyconvexity at the multiples of orthogonal matrices.

**One statement is not proved here.** For `1 < p < 2` the quasiconvexity of `F` rests on the
quasiconvexity of the Burkholder function:

- it is the hypothesis `Quasiconvex (burkholder p)` of the Lean statements, where `burkholder p`
  is `p/2` times `B_p`;
- it is stated as Corollary 2 of the preprint
  [arXiv:2609.28311](https://arxiv.org/abs/2609.28311), which has not been refereed;
- the preprint states it at every matrix, with smooth periodic test maps, for a positive multiple
  of `B_p`. The passage to the test maps used here (Lipschitz maps vanishing outside the unit
  square) is by periodic extension and mollification, and is not formalized.

## Main results

Here `|A|` is the operator norm, `h(s) = F(diag(1, s))`, and quasiconvexity is that of the package
`CalculusOfVariations` (Lipschitz test maps vanishing outside the unit square). The Lean
statements are in conformal coordinates: they have `|z| + |w|` for `|A|`; that this is the
operator norm is not proved in Lean. The numbers are those of the paper, and the Challenge
states each result under the name of its number.

| Result | Lean | Challenge | Statement |
| --- | --- | --- | --- |
| Theorem 1.1 | [`polyconvex_of_rankOneConvex`](../../Morrey/HomogeneousIsotropic/Main.lean#L68), [`hasPolyaffineSupportAt_of_rankOneConvex`](../../Morrey/HomogeneousIsotropic/Main.lean#L58) | [`theorem1_1`](../../palomar/HomogeneousIsotropic/Challenge.lean#L205) | `p ≥ 2`, H1, H2, H3, N: a polyaffine support at every matrix; `F` is polyconvex |
| Theorem 1.2 | [`polyaffine_multiplier_le`](../../Morrey/HomogeneousIsotropic/Main.lean#L209) | [`theorem1_2`](../../palomar/HomogeneousIsotropic/Challenge.lean#L215) | the support at `diag(1, t)` in closed form (below) |
| Theorem 1.3 (a) | [`polyconvex_iff_of_two_lt`](../../Morrey/HomogeneousIsotropic/Main.lean#L190), [`nonneg_of_polyconvex`](../../Morrey/HomogeneousIsotropic/Main.lean#L93) | [`theorem1_3_a`](../../palomar/HomogeneousIsotropic/Challenge.lean#L229) | `p > 2`, H1, H2: polyconvex if and only if rank-one convex and nonnegative |
| Theorem 1.3 (b) | [`polyconvex_iff_two`](../../Morrey/HomogeneousIsotropic/Main.lean#L275) | [`theorem1_3_b`](../../palomar/HomogeneousIsotropic/Challenge.lean#L236) | `p = 2`, H1, H2: polyconvex if and only if rank-one convex |
| Corollary 1.4 | [`tfae_of_two_le`](../../Morrey/HomogeneousIsotropic/Main.lean#L83) | [`corollary1_4`](../../palomar/HomogeneousIsotropic/Challenge.lean#L243) | `p ≥ 2`, H1, H2, N, Borel and locally bounded: rank-one convex, quasiconvex and polyconvex are equivalent |
| Theorem 1.5 | [`exists_burkholderType_le`](../../Morrey/HomogeneousIsotropic/Main.lean#L285), [`burkholderType_eq`](../../Morrey/HomogeneousIsotropic/Main.lean#L371) | [`theorem1_5`](../../palomar/HomogeneousIsotropic/Challenge.lean#L252), [`theorem1_5_identity`](../../palomar/HomogeneousIsotropic/Challenge.lean#L262) | `1 ≤ p < 2`, H1, H2, H3, N: a touching Burkholder-type minorant at every matrix |
| Corollary 1.6 (a) | [`quasiconvex_of_rankOneConvex_of_burkholder`](../../Morrey/HomogeneousIsotropic/Main.lean#L416) | [`corollary1_6_a`](../../palomar/HomogeneousIsotropic/Challenge.lean#L272) | `1 < p < 2`, H1, H2, H3, N: if `B_p` is quasiconvex, `F` is quasiconvex |
| Corollary 1.6 (b) | [`convexOn_of_rankOneConvex_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L462), [`nonneg_of_rankOneConvex_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L428) | [`corollary1_6_b`](../../palomar/HomogeneousIsotropic/Challenge.lean#L279) | `p = 1`, H1, H2, H3: `F` is nonnegative and convex |
| Proposition 1.7 | [`eq_zero_of_rankOneConvex_of_lt_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L537) | [`proposition1_7`](../../palomar/HomogeneousIsotropic/Challenge.lean#L286) | `0 < p < 1`, H2, H3: `F = 0` |
| Corollary 1.8 | [`quasiconvex_of_rankOneConvex_of_pos`](../../Morrey/HomogeneousIsotropic/Main.lean#L580) | [`corollary1_8`](../../palomar/HomogeneousIsotropic/Challenge.lean#L294) | `p > 0`, H1, H2, H3, N: `F` is quasiconvex, if `B_p` is quasiconvex when `1 < p < 2` |

The support of Theorem 1.2: for `|t| < 1`, `H = h(t) > 0` and `m` the slope of a supporting line
of `h` at `t`, let

- `L = ((1 + t) m − p H) / (1 − t)`;
- `U = (p H + (1 − t) m) / (1 + t)`;
- `c = min (U, max (L, (p − 1) m))`, in Lean `multiplier p H m t`.

Then `c t − (p − 1) H + (p H − t m − c t) a₁₁ + (m − c) a₂₂ + c det A ≤ F(A)` for every `A`, with
equality at `diag(1, t)`.

## The proof

Identify `ℝ²` with `ℂ`. A matrix acts as `ζ ↦ zζ + wζ̄`; then `det A = |z|² − |w|²`,
`|A| = |z| + |w|`, an isotropic `F` is a function `Φ` of the moduli of `z` and `w` (its
*profile*), and a line is a rank-one line exactly when `z` and `w` move with the same speed. The
proof uses only two properties of `Φ` ([`IsProfile`](../../Morrey/HomogeneousIsotropic/Defs.lean#L171)): homogeneity, and convexity along the images
of rank-one lines.

| Step | Lean | Content |
| --- | --- | --- |
| Coordinates | [`IsIsotropic.eq_profile`](../../Morrey/HomogeneousIsotropic/Coordinates.lean#L204), [`isProfile_profile`](../../Morrey/HomogeneousIsotropic/Coordinates.lean#L211) | `F(A) = Φ(x, y)` with `x`, `y` the moduli of `z`, `w`, and `Φ` is a profile |
| Supports | [`hasPolyaffineSupportAt_of_profile`](../../Morrey/HomogeneousIsotropic/Coordinates.lean#L258) | a support `k + b x + g y + c (x² − y²)` of `Φ` with `b, g ≥ 0` gives a polyaffine support of `F` |
| | [`polyconvex_of_hasPolyaffineSupportAt`](../../Morrey/HomogeneousIsotropic/Polyaffine.lean#L139) | polyaffine supports at every matrix give polyconvexity |
| | [`HasPolyaffineSupportAt.quasiconvexAtOn`](../../Morrey/HomogeneousIsotropic/Polyaffine.lean#L100) | a polyaffine support gives quasiconvexity at that matrix |
| Minorants | [`IsProfile.exists_burkholderMinorant`](../../Morrey/HomogeneousIsotropic/Profile.lean#L140) | a supporting line of `h` gives a Burkholder-type function below `Φ` that touches it |
| First order | [`IsProfile.tangent`](../../Morrey/HomogeneousIsotropic/Profile.lean#L155) | at a touching point `(x₀, y₀)` with value `H`, the value of `Φ` at the moduli of `(x₀ + τα, y₀ + τβ)` is at least `H + τ (Φ_x Re α + Φ_y Re β)`, along every rank-one line |
| | [`IsProfile.baker_ericksen`](../../Morrey/HomogeneousIsotropic/Profile.lean#L203) | hence `p H − 2 t m ≥ 0` |
| `p ≥ 2`, Case III | [`burkholder_support_le`](../../Morrey/HomogeneousIsotropic/Inequalities.lean#L73), [`BurkholderMinorant.support`](../../Morrey/HomogeneousIsotropic/Supports.lean#L39) | if the supporting line of `h` is nonnegative at `± (p − 2)/p`: the support with `c = (p − 1) m` |
| `p ≥ 2`, Case I | [`IsProfile.support_of_stationary`](../../Morrey/HomogeneousIsotropic/Supports.lean#L150), [`exists_stationary_ge`](../../Morrey/HomogeneousIsotropic/Inequalities.lean#L148), [`IsProfile.support_of_neg`](../../Morrey/HomogeneousIsotropic/Supports.lean#L263) | otherwise: the support with `c = U`, from the first-order inequality along one rank-one line |
| `p ≥ 2`, Case II | [`IsProfile.support_of_neg_aux'`](../../Morrey/HomogeneousIsotropic/Supports.lean#L276) | the mirror image, `c = L` |
| `p ≥ 2`, together | [`IsProfile.support_multiplier`](../../Morrey/HomogeneousIsotropic/Supports.lean#L298), [`IsProfile.exists_support`](../../Morrey/HomogeneousIsotropic/Supports.lean#L523) | the clamped multiplier; a support at every point |
| `1 ≤ p < 2` | [`IsProfile.slice_ge_of_one`](../../Morrey/HomogeneousIsotropic/LowExponent.lean#L32), [`IsProfile.exists_burkholderMinorant_of_lt_two`](../../Morrey/HomogeneousIsotropic/LowExponent.lean#L91) | the supporting lines at `t = ± 1`; the minorant of Theorem 1.5 |
| `0 < p < 1` | [`ConvexOn.eq_of_tendsto_div_zero`](../../Morrey/Common/Basic/Analysis/Convex/Tangent.lean#L72), [`eq_zero_of_rankOneConvex_of_lt_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L537) | a convex function of sublinear growth is constant; `F` is constant along rank-one lines |

In Case I the candidate support is negative at the origin, so by homogeneity it is enough to prove
the inequality where `λ ↦ λ^p q(·/λ)` is stationary. In the coordinates of the modulus of `w` and
`det A` these points form a line, and this line is the image of a rank-one line through the base
point.

## The literature

Checked on 23 November 2026, from the sources (the version of record of Guerra and Kristensen's
paper and Dacorogna's 1995 article were not available; their statements are taken from the
accepted manuscript and from Dacorogna and Haeberly's introduction):

- A. Guerra and J. Kristensen, *Automatic quasiconvexity of homogeneous isotropic rank-one convex
  integrands*, Arch. Ration. Mech. Anal. 245 (2022), 479–500
  ([arXiv:2112.10563](https://arxiv.org/abs/2112.10563)). For nonnegative, isotropic, positively
  `p`-homogeneous, rank-one convex integrands:
  - Theorem 1.3: polyconvexity at the multiples of orthogonal matrices, for `p ≥ 2`;
  - Theorem 1.2: quasiconvexity there, for `p ≥ 2`, and for `p ≤ 2` if the Burkholder function is
    quasiconvex;
  - Theorem 4.2: for `p ≤ 2`, the Burkholder function is the smallest integrand of the class with
    a given value at the identity;
  - Proposition 1.6: the positive part of the Burkholder function is polyconvex for `p ≥ 2`;
  - Remark 1.4: the Burkholder function is not polyconvex for `p > 2`, its positive part is not
    for `p < 2`, and isotropy cannot be dropped;
  - Question 1.7 (the numbering of the accepted version): "When `n = 2`, are the integrands
    satisfying the assumptions of Theorem 1.3 polyconvex everywhere?" Theorem 1.1 here answers
    it.
- B. Dacorogna, *On rank one convex functions which are homogeneous of degree one* (1995): the
  case `p = 1`.
- B. Dacorogna and H. Koshigoe, Ann. Fac. Sci. Toulouse Math. (6) 2 (1993), 163–184, Theorem 2.1:
  an `SO(2) × SO(2)`-invariant function is polyconvex if and only if it has polyaffine supports
  on diagonal matrices. This is the reduction that the proof uses
  ([`hasPolyaffineSupportAt_of_profile`](../../Morrey/HomogeneousIsotropic/Coordinates.lean#L258)).
- The preprints of 2026:
  - [arXiv:2609.28311](https://arxiv.org/abs/2609.28311), Corollary 2: the Burkholder function is
    quasiconvex for `1 < p < ∞`;
  - Bruno and Pasqualotto, [arXiv:2608.06367](https://arxiv.org/abs/2608.06367): for isotropic
    homogeneous quartics on `2 × 2`, rank-one convexity is equivalent to quasiconvexity;
  - Cassese, [arXiv:2608.03488](https://arxiv.org/abs/2608.03488), Conjecture 1: isotropic
    `p`-homogeneous rank-one convex integrands are quasiconvex at `0`.
- No earlier proof of Theorems 1.1, 1.2, 1.3 and 1.5 was found. The search covered arXiv titles
  and abstracts up to 18 November 2026 and the works citing Guerra and Kristensen; it did not
  cover Google Scholar or MathSciNet.

## What is not proved

- The quasiconvexity of the Burkholder function `B_p` for `1 < p < 2`: a hypothesis of
  [`quasiconvex_of_rankOneConvex_of_burkholder`](../../Morrey/HomogeneousIsotropic/Main.lean#L416) and of [`quasiconvex_of_rankOneConvex_of_pos`](../../Morrey/HomogeneousIsotropic/Main.lean#L580).
- Isotropic, positively `p`-homogeneous, rank-one convex integrands with `p > 2` that take
  negative values: they are not polyconvex, and whether they are quasiconvex is not treated.
- Integrands that are not isotropic or not homogeneous: the proof does not apply, and Morrey's
  problem in `2 × 2` stays open.

## Files

| Module | Content |
| --- | --- |
| [`Morrey.HomogeneousIsotropic.Defs`](../../Morrey/HomogeneousIsotropic/Defs.lean) | the definitions; those of the Challenge are in the shared block |
| [`Morrey.HomogeneousIsotropic.Bridges`](../../Morrey/HomogeneousIsotropic/Bridges.lean) | the Challenge's rank-one convexity and quasiconvexity are the package's |
| [`Morrey.HomogeneousIsotropic.Coordinates`](../../Morrey/HomogeneousIsotropic/Coordinates.lean) | conformal coordinates, isotropy, the profile |
| [`Morrey.HomogeneousIsotropic.Polyaffine`](../../Morrey/HomogeneousIsotropic/Polyaffine.lean) | polyaffine supports, polyconvexity and quasiconvexity |
| [`Morrey.HomogeneousIsotropic.Inequalities`](../../Morrey/HomogeneousIsotropic/Inequalities.lean) | the one-variable facts |
| [`Morrey.HomogeneousIsotropic.Profile`](../../Morrey/HomogeneousIsotropic/Profile.lean) | what rank-one convexity gives for the profile |
| [`Morrey.HomogeneousIsotropic.LowExponent`](../../Morrey/HomogeneousIsotropic/LowExponent.lean) | the profile for `1 ≤ p < 2` |
| [`Morrey.HomogeneousIsotropic.Supports`](../../Morrey/HomogeneousIsotropic/Supports.lean) | the supports of the profile for `p ≥ 2` |
| [`Morrey.HomogeneousIsotropic.Main`](../../Morrey/HomogeneousIsotropic/Main.lean) | the theorems for `F`, for every `p > 0` |
| [`Morrey.HomogeneousIsotropic.Example`](../../Morrey/HomogeneousIsotropic/Example.lean) | an integrand that satisfies the hypotheses and is not convex: `(det A)²`, with `p = 4` |
| [`Morrey.Common.Basic.Analysis.Convex.Tangent`](../../Morrey/Common/Basic/Analysis/Convex/Tangent.lean) | supporting lines of convex functions on `ℝ`; convex functions of sublinear growth |

## Palomar

The files of a Palomar submission are in [`palomar/HomogeneousIsotropic/`](../../palomar/HomogeneousIsotropic):

- `Challenge.lean` imports only Mathlib and states the results of the table above, with their
  definitions;
- `Solution.lean` proves them from the library;
- `comparator.json` names the twelve statements that Comparator checks;
- `formalization.yaml` is the metadata. It declares the result as first presented here, and
  the quasiconvexity of the Burkholder function as an assumed result.

Nothing has been submitted, and the preflight workflow has not been run.

## Trust

- `lake build` passes; no `sorry` outside the Challenge, no `axiom`, no `native_decide`.
- The repository's audit, [`scripts/Audit.lean`](../../scripts/Audit.lean), checks that every declaration uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- Comparator accepts the Solution against the Challenge, under Lean's kernel and nanoda.
- The hypotheses are satisfiable by integrands that are not convex: `(det A)²` with `p = 4`
  ([`polyconvex_detSq`](../../Morrey/HomogeneousIsotropic/Example.lean#L71), [`not_convexOn_detSq`](../../Morrey/HomogeneousIsotropic/Example.lean#L63)).
- An independent AI agent compared the Lean statements with the paper, recomputed every identity
  of the paper and tested the supports numerically. It found no error in a theorem or a proof;
  its corrections to the wording are applied. It reviewed the first version of the paper; the
  restructured version and the case `0 < p < 1` were written after its review.
- No person has reviewed the proofs or the paper.
