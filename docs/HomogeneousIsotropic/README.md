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
| `0 < p < 1` | H2, H3 | `F = 0` | [`eq_zero_of_rankOneConvex_of_lt_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L541) | **proved** |
| `p = 1` | H1, H2, H3 | `F ≥ 0`, and `F` is convex (Dacorogna 1995) | [`convexOn_of_rankOneConvex_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L466) | **proved** |
| `1 < p < 2` | H1, H2, H3 | `F` is quasiconvex | [`quasiconvex_of_rankOneConvex_of_isotropic`](../../Morrey/HomogeneousIsotropic/Signed/Main.lean#L355) | **proved** |
| `1 < p < 2` | H1, H2, H3, N | at every matrix `F` has a touching minorant `α B_p(A) + β B_p(JA)` with `α, β ≥ 0` | [`exists_burkholderType_le`](../../Morrey/HomogeneousIsotropic/Burkholder.lean#L147) | **proved** |
| `p = 2` | H1, H2, H3 | `F` is polyconvex | [`polyconvex_of_rankOneConvex_two`](../../Morrey/HomogeneousIsotropic/Main.lean#L272) | **proved** |
| `p > 2` | H1, H2, H3 | `F` is quasiconvex | [`quasiconvex_of_rankOneConvex_of_isotropic`](../../Morrey/HomogeneousIsotropic/Signed/Main.lean#L355) | **proved** |
| `p > 2` | H1, H2, H3, N | `F` is polyconvex, with a polyaffine support at every matrix in closed form | [`polyconvex_of_rankOneConvex`](../../Morrey/HomogeneousIsotropic/Main.lean#L72), [`polyaffine_multiplier_le`](../../Morrey/HomogeneousIsotropic/Main.lean#L213) | **proved** |
| `p > 2` | H1, H2, and `F < 0` somewhere | `F` is not polyconvex | [`nonneg_of_polyconvex`](../../Morrey/HomogeneousIsotropic/Main.lean#L97) | **proved** |
| every `p > 0` | H1, H2, H3 | `F` is quasiconvex (Theorem A) | [`quasiconvex_of_rankOneConvex_of_isotropic`](../../Morrey/HomogeneousIsotropic/Signed/Main.lean#L355) | **proved** |

So rank-one convexity implies quasiconvexity for isotropic, positively `p`-homogeneous
integrands, for every `p > 0`, with no sign condition (Theorem A). The sign condition N is what
polyconvexity needs when `p > 2`. For `p ≥ 2` the polyconvexity of the nonnegative integrands
answers Question 1.7 of Guerra and Kristensen (2022), who proved it at the multiples of
orthogonal matrices.

**The cited result.** One result from outside is used: the quasiconvexity of the truncated
determinant `L`, claimed as Theorem 1 of the preprint of Agazzi et al.,
[arXiv:2609.28311](https://arxiv.org/abs/2609.28311), which we audited with a Lean
formalization, [lean4-iwaniec](https://github.com/vltanh/lean4-iwaniec)
(`Agazzi.quasiconvex_integrandL`). Proposition 6.8 of the paper integrates it over scales. With `N(r) = ±r^{p−1}`
it gives the quasiconvexity of the Burkholder function for every `p > 1`
([`quasiconvex_burkholder_of_one_lt`](../../Morrey/HomogeneousIsotropic/Signed/BurkholderRadial.lean#L185)), claimed as Corollary 2 of the same preprint, which
Corollary 1.6 (a) and the easy bases of Theorem A use. From lean4-iwaniec the library also takes
`Agazzi.opNorm_eq` (`|A| = |z| + |w|`). This repository requires that package, so nothing is
assumed: every statement here is checked by Lean's kernel down to the standard axioms.

## Main results

Here `|A|` is the operator norm, `h(s) = F(diag(1, s))`, and quasiconvexity is that of the package
`CalculusOfVariations` (Lipschitz test maps vanishing outside the unit square). The Lean
statements are those of the paper:

- `opNorm A` is the operator norm, `burkholderType p c₀ m A` is `|A|^{p−2} (c₀ |A|² + m det A)`
  and `burkholder p A` is `B_p(A)`, as the paper defines them;
- the passage to conformal coordinates is proved: [`opNorm_eq`](../../Morrey/HomogeneousIsotropic/Burkholder.lean#L44) (`|A| = |z| + |w|`),
  [`burkholderType_eq_coord`](../../Morrey/HomogeneousIsotropic/Burkholder.lean#L61), [`burkholder_eq_coord`](../../Morrey/HomogeneousIsotropic/Burkholder.lean#L88);
- every numbered statement of the paper has a Lean theorem with the same hypotheses and the same
  conclusion; the paper's Appendix F lists them.

The numbers are those of the paper, and the Challenge states each result under the name of its
number.

| Result | Lean | Challenge | Statement |
| --- | --- | --- | --- |
| Lemma 2.1 (a) | [`det_eq_norm_sq_sub`](../../Morrey/HomogeneousIsotropic/Coordinates.lean#L103), [`opNorm_eq`](../../Morrey/HomogeneousIsotropic/Burkholder.lean#L44) | [`det_eq_norm_sq_sub`](../../Morrey/HomogeneousIsotropic/Coordinates.lean#L103), [`opNorm_eq`](../../Morrey/HomogeneousIsotropic/Burkholder.lean#L44) | `det A = \|z\|² − \|w\|²` and `\|A\| = \|z\| + \|w\|` for the conformal and anticonformal parts `z`, `w` of `A` |
| Theorem 1.1 | [`polyconvex_of_rankOneConvex`](../../Morrey/HomogeneousIsotropic/Main.lean#L72), [`hasPolyaffineSupportAt_of_rankOneConvex`](../../Morrey/HomogeneousIsotropic/Main.lean#L62) | [`theorem1_1`](../../palomar/HomogeneousIsotropic/Challenge.lean#L220) | `p ≥ 2`, H1, H2, H3, N: a polyaffine support at every matrix; `F` is polyconvex |
| Theorem 1.2 | [`polyaffine_multiplier_le`](../../Morrey/HomogeneousIsotropic/Main.lean#L213) | [`theorem1_2`](../../palomar/HomogeneousIsotropic/Challenge.lean#L230) | the support at `diag(1, t)` in closed form (below) |
| Theorem 1.3 (a) | [`polyconvex_iff_of_two_lt`](../../Morrey/HomogeneousIsotropic/Main.lean#L194), [`nonneg_of_polyconvex`](../../Morrey/HomogeneousIsotropic/Main.lean#L97) | [`theorem1_3_a`](../../palomar/HomogeneousIsotropic/Challenge.lean#L244) | `p > 2`, H1, H2: polyconvex if and only if rank-one convex and nonnegative |
| Theorem 1.3 (b) | [`polyconvex_iff_two`](../../Morrey/HomogeneousIsotropic/Main.lean#L279) | [`theorem1_3_b`](../../palomar/HomogeneousIsotropic/Challenge.lean#L251) | `p = 2`, H1, H2: polyconvex if and only if rank-one convex |
| Corollary 1.4 | [`tfae_of_two_le`](../../Morrey/HomogeneousIsotropic/Main.lean#L87) | [`corollary1_4`](../../palomar/HomogeneousIsotropic/Challenge.lean#L258) | `p ≥ 2`, H1, H2, N, Borel and locally bounded: rank-one convex, quasiconvex and polyconvex are equivalent |
| Theorem 1.5 | [`exists_burkholderType_le`](../../Morrey/HomogeneousIsotropic/Burkholder.lean#L147), [`burkholderType_eq`](../../Morrey/HomogeneousIsotropic/Burkholder.lean#L164) | [`theorem1_5`](../../palomar/HomogeneousIsotropic/Challenge.lean#L267), [`theorem1_5_identity`](../../palomar/HomogeneousIsotropic/Challenge.lean#L277) | `1 ≤ p < 2`, H1, H2, H3, N: a touching minorant `G(A) = \|A\|^{p−2} (c₀ \|A\|² + m det A)` at every matrix; for `0 < p < 2`, `G` is a combination of `B_p(A)` and `B_p(JA)` |
| Corollary 1.6 (a) | [`quasiconvex_of_rankOneConvex_of_lt_two`](../../Morrey/HomogeneousIsotropic/Signed/BurkholderRadial.lean#L218), [`quasiconvex_burkholder`](../../Morrey/HomogeneousIsotropic/Signed/BurkholderRadial.lean#L199) | [`corollary1_6_a`](../../palomar/HomogeneousIsotropic/Challenge.lean#L286) | `1 < p < 2`, H1, H2, H3, N: `F` is quasiconvex |
| Corollary 1.6 (b) | [`convexOn_of_rankOneConvex_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L466), [`nonneg_of_rankOneConvex_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L431) | [`corollary1_6_b`](../../palomar/HomogeneousIsotropic/Challenge.lean#L293) | `p = 1`, H1, H2, H3: `F` is nonnegative and convex |
| Proposition 1.7 | [`eq_zero_of_rankOneConvex_of_lt_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L541) | [`proposition1_7`](../../palomar/HomogeneousIsotropic/Challenge.lean#L300) | `0 < p < 1`, H2, H3: `F = 0` |
| Theorem A | [`quasiconvex_of_rankOneConvex_of_isotropic`](../../Morrey/HomogeneousIsotropic/Signed/Main.lean#L355) | [`theoremA`](../../palomar/HomogeneousIsotropic/Challenge.lean#L307) | `p > 0`, H1, H2, H3: `F` is quasiconvex |
| Proposition 6.8 | [`quasiconvex_radial`](../../Morrey/HomogeneousIsotropic/Signed/Radial.lean#L455) | [`proposition6_8`](../../palomar/HomogeneousIsotropic/Challenge.lean#L314) | if `N` is convex on `[0, ∞)`, continuous, `N(0) ≤ 0`, then `X ↦ (\|X\| + e δ) N(\|X\|) − 2 ∫₀^{\|X\|} N` is quasiconvex for `e = ±1` (`δ` is the difference of the moduli of `z` and `w`) |
| Corollary 6.11 | [`quasiconvex_burkholder_of_one_lt`](../../Morrey/HomogeneousIsotropic/Signed/BurkholderRadial.lean#L185), [`radial_rpow_eq_burkholder`](../../Morrey/HomogeneousIsotropic/Signed/BurkholderRadial.lean#L113), [`radial_neg_rpow_eq_burkholder`](../../Morrey/HomogeneousIsotropic/Signed/BurkholderRadial.lean#L131) | | `B_p` is quasiconvex for every `p > 1`: it is the radial function of `N(r) = r^{p−1}` (`p ≥ 2`) or `−r^{p−1}` (`p ≤ 2`) |

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
proof uses only two properties of `Φ` ([`IsProfile`](../../Morrey/HomogeneousIsotropic/Defs.lean#L196)): homogeneity, and convexity along the images
of rank-one lines.

| Step | Lean | Content |
| --- | --- | --- |
| Coordinates | [`IsIsotropic.eq_profile`](../../Morrey/HomogeneousIsotropic/Coordinates.lean#L204), [`isProfile_profile`](../../Morrey/HomogeneousIsotropic/Coordinates.lean#L211) | `F(A) = Φ(x, y)` with `x`, `y` the moduli of `z`, `w`, and `Φ` is a profile |
| Supports | [`hasPolyaffineSupportAt_of_profile`](../../Morrey/HomogeneousIsotropic/Coordinates.lean#L258) | a support `k + b x + g y + c (x² − y²)` of `Φ` with `b, g ≥ 0` gives a polyaffine support of `F` |
| | [`polyconvex_of_hasPolyaffineSupportAt`](../../Morrey/HomogeneousIsotropic/Polyaffine.lean#L139) | polyaffine supports at every matrix give polyconvexity |
| | [`HasPolyaffineSupportAt.quasiconvexAtOn`](../../Morrey/HomogeneousIsotropic/Polyaffine.lean#L100) | a polyaffine support gives quasiconvexity at that matrix |
| Minorants | [`IsProfile.exists_burkholderMinorant`](../../Morrey/HomogeneousIsotropic/Profile.lean#L172) | a supporting line of `h` gives a Burkholder-type function below `Φ` that touches it |
| First order | [`IsProfile.tangent`](../../Morrey/HomogeneousIsotropic/Profile.lean#L197) | at a touching point `(x₀, y₀)` with value `H`, the value of `Φ` at the moduli of `(x₀ + τα, y₀ + τβ)` is at least `H + τ (Φ_x Re α + Φ_y Re β)`, along every rank-one line |
| | [`IsProfile.baker_ericksen`](../../Morrey/HomogeneousIsotropic/Profile.lean#L245) | hence `p H − 2 t m ≥ 0` |
| `p ≥ 2`, Case III | [`burkholder_support_le`](../../Morrey/HomogeneousIsotropic/Inequalities.lean#L73), [`BurkholderMinorant.support`](../../Morrey/HomogeneousIsotropic/Supports.lean#L39) | if the supporting line of `h` is nonnegative at `± (p − 2)/p`: the support with `c = (p − 1) m` |
| `p ≥ 2`, Case I | [`IsProfile.support_of_stationary`](../../Morrey/HomogeneousIsotropic/Supports.lean#L150), [`exists_stationary_ge`](../../Morrey/HomogeneousIsotropic/Inequalities.lean#L148), [`IsProfile.support_of_neg`](../../Morrey/HomogeneousIsotropic/Supports.lean#L263) | otherwise: the support with `c = U`, from the first-order inequality along one rank-one line |
| `p ≥ 2`, Case II | [`IsProfile.support_of_neg_aux'`](../../Morrey/HomogeneousIsotropic/Supports.lean#L276) | the mirror image, `c = L` |
| `p ≥ 2`, together | [`IsProfile.support_multiplier`](../../Morrey/HomogeneousIsotropic/Supports.lean#L298), [`IsProfile.exists_support`](../../Morrey/HomogeneousIsotropic/Supports.lean#L523) | the clamped multiplier; a support at every point |
| `1 ≤ p < 2` | [`IsProfile.slice_ge_of_one`](../../Morrey/HomogeneousIsotropic/LowExponent.lean#L32), [`IsProfile.exists_burkholderMinorant_of_lt_two`](../../Morrey/HomogeneousIsotropic/LowExponent.lean#L91) | the supporting lines at `t = ± 1`; the minorant of Theorem 1.5 |
| `0 < p < 1` | [`ConvexOn.eq_of_tendsto_div_zero`](../../Morrey/Common/Basic/Analysis/Convex/Tangent.lean#L72), [`eq_zero_of_rankOneConvex_of_lt_one`](../../Morrey/HomogeneousIsotropic/Main.lean#L541) | a convex function of sublinear growth is constant; `F` is constant along rank-one lines |

In Case I the candidate support is negative at the origin, so by homogeneity it is enough to prove
the inequality where `λ ↦ λ^p q(·/λ)` is stationary. In the coordinates of the modulus of `w` and
`det A` these points form a line, and this line is the image of a rank-one line through the base
point.

### Integrands that change sign

The argument is due to ChatGPT Chat 6 Extra High (see [CREDITS.md](CREDITS.md)). After a
reflection the negative values of `F` are at negative determinants. At a matrix where the
supporting line of `h` is nonnegative at `−a`, `a = |p − 2|/p`, a multiple of the Burkholder
function plus a convex function supports `F`. At the other matrices (the hard bases):

| Step | Lean | Content |
| --- | --- | --- |
| Restricted supports | [`IsHardBase.restrictedSupport_le_of_lt`](../../Morrey/HomogeneousIsotropic/Signed/RestrictedSupport.lean#L538), [`IsHardBase.restrictedSupport_le_of_nonneg`](../../Morrey/HomogeneousIsotropic/Signed/RestrictedSupport.lean#L568), [`IsHardBase.restrictedSupport_le_of_add_le_one`](../../Morrey/HomogeneousIsotropic/Signed/RestrictedSupport.lean#L784) | a function `α + v r + c det` lies below `F` on the unit ball and on a cone, and touches it at the base |
| Monotonicity | [`IsHardBase.scaled_monotone`](../../Morrey/HomogeneousIsotropic/Signed/RestrictedSupport.lean#L883) | the supporting planes of two hard bases are monotone |
| Radial integration (Proposition 6.8) | [`quasiconvex_radial`](../../Morrey/HomogeneousIsotropic/Signed/Radial.lean#L455) | hinge functions give scaled truncated determinants; convex `N` are limits of their nonnegative combinations |
| The path | [`IsHardBase.exists_isPath`](../../Morrey/HomogeneousIsotropic/Signed/Path.lean#L43) | supporting lines of `h` followed from the base, with the scale given by a quadrature |
| The minorant | [`IsHardBase.exists_convex_minorant`](../../Morrey/HomogeneousIsotropic/Signed/Minorant.lean#L616) | a convex `N` whose radial function lies below `F` on a ball of any radius and touches at the base |
| Assembly | [`quasiconvexAtOn_of_strictConvexOn_slice`](../../Morrey/HomogeneousIsotropic/Signed/Interior.lean#L226), [`quasiconvex_of_rankOneConvex_of_isotropic`](../../Morrey/HomogeneousIsotropic/Signed/Main.lean#L355) | strict convexification, the bases with two nonzero coordinates, the others by continuity |

On the sphere of radius `s ≥ 1` the minorant is `s^p` times a supporting line of `h`; inside the
unit ball it is the restricted support.

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
  - Agazzi et al., [arXiv:2609.28311](https://arxiv.org/abs/2609.28311), Corollary 2, claims
    that the Burkholder function is quasiconvex for `1 < p < ∞`, and that the Beurling–Ahlfors
    transform has norm `p* − 1` on `L^p` (Iwaniec's conjecture). We audited it with a Lean
    formalization, [lean4-iwaniec](https://github.com/vltanh/lean4-iwaniec), which is used here;
  - Bruno and Pasqualotto, [arXiv:2608.06367](https://arxiv.org/abs/2608.06367): for isotropic
    homogeneous quartics on `2 × 2`, rank-one convexity is equivalent to quasiconvexity;
  - Cassese, [arXiv:2608.03488](https://arxiv.org/abs/2608.03488), which claims a negative
    answer to Morrey's problem for maps `ℝ^m → ℝ²`, `m ≥ 3`, and which this repository audited
    with a Lean formalization ([its documents](../Cassese/README.md)). Its Conjecture 1:
    isotropic `p`-homogeneous rank-one convex integrands are quasiconvex at `0`.
- No earlier proof of Theorems 1.1, 1.2, 1.3 and 1.5 was found. The search covered arXiv titles
  and abstracts up to 18 November 2026 and the works citing Guerra and Kristensen; it did not
  cover Google Scholar or MathSciNet.

## What is not proved

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
| [`Morrey.HomogeneousIsotropic.Main`](../../Morrey/HomogeneousIsotropic/Main.lean) | the theorems for `F` that need no package but `CalculusOfVariations`: `p ≥ 2`, `p = 1`, `0 < p < 1`, and `1 ≤ p < 2` in conformal coordinates |
| [`Morrey.HomogeneousIsotropic.Burkholder`](../../Morrey/HomogeneousIsotropic/Burkholder.lean) | the operator norm and the Burkholder function of the paper; Theorem 1.5; the quasiconvexity of the Burkholder function, from lean4-iwaniec; Corollaries 1.6 (a) and 1.8 |
| [`Morrey.HomogeneousIsotropic.Signed.Defs`](../../Morrey/HomogeneousIsotropic/Signed/Defs.lean), `.Basic` | integrands of any sign: the slice, hard bases, the location and sign of a hard base |
| [`Morrey.HomogeneousIsotropic.Signed.RestrictedSupport`](../../Morrey/HomogeneousIsotropic/Signed/RestrictedSupport.lean) | the restricted supports at a hard base and their monotonicity |
| [`Morrey.HomogeneousIsotropic.Signed.Radial`](../../Morrey/HomogeneousIsotropic/Signed/Radial.lean) | Proposition 6.8, radial integration of the truncated determinant |
| [`Morrey.HomogeneousIsotropic.Signed.Path`](../../Morrey/HomogeneousIsotropic/Signed/Path.lean), `.Minorant` | the path of hard bases and the radial minorant along it |
| [`Morrey.HomogeneousIsotropic.Signed.BurkholderRadial`](../../Morrey/HomogeneousIsotropic/Signed/BurkholderRadial.lean) | the Burkholder function from Proposition 6.8 (Corollary 6.11); Corollary 1.6 (a); the nonnegative case of Theorem A |
| [`Morrey.HomogeneousIsotropic.Signed.Interior`](../../Morrey/HomogeneousIsotropic/Signed/Interior.lean), `.Main` | Jensen's inequality at every matrix; Theorem A |
| [`Morrey.HomogeneousIsotropic.Example`](../../Morrey/HomogeneousIsotropic/Example.lean) | an integrand that satisfies the hypotheses and is not convex: `(det A)²`, with `p = 4` |
| [`Morrey.Common.Basic.Analysis.Convex.Tangent`](../../Morrey/Common/Basic/Analysis/Convex/Tangent.lean) | supporting lines of convex functions on `ℝ`; convex functions of sublinear growth |

## Palomar

The files of a Palomar submission are in [`palomar/HomogeneousIsotropic/`](../../palomar/HomogeneousIsotropic):

- `Challenge.lean` imports only Mathlib and states the results of the table above, with their
  definitions;
- `Solution.lean` proves them from the library;
- `comparator.json` names the fourteen statements that Comparator checks;
- `formalization.yaml` is the metadata. It declares the result as first presented here, and
  the quasiconvexity of the truncated determinant as a result claimed in a preprint and taken
  from its Lean formalization, lean4-iwaniec.

Nothing has been submitted, and the preflight workflow has not been run.

## Trust

- `lake build` passes; no `sorry` outside the Challenge, no `axiom`, no `native_decide`.
- The repository's audit, [`scripts/Audit.lean`](../../scripts/Audit.lean), checks that every declaration uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- Comparator accepts the Solution against the Challenge, under Lean's kernel and nanoda.
- The quasiconvexity of the truncated determinant comes from the package lean4-iwaniec. The audit
  here covers its proofs, and that package has its own audit, Challenge and Comparator check.
- The hypotheses are satisfiable by integrands that are not convex: `(det A)²` with `p = 4`
  ([`polyconvex_detSq`](../../Morrey/HomogeneousIsotropic/Example.lean#L71), [`not_convexOn_detSq`](../../Morrey/HomogeneousIsotropic/Example.lean#L63)).
- An independent AI agent compared the Lean statements with the paper, recomputed every identity
  of the paper and tested the supports numerically. It found no error in a theorem or a proof;
  its corrections to the wording are applied. It reviewed the first version of the paper; the
  restructured version, the case `0 < p < 1`, the use of lean4-iwaniec and the theorem for
  integrands that change sign came after its review.
- No person has reviewed the proofs or the paper.
