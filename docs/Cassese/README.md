# Cassese (2026): Morrey's problem in `ℝ^{2×m}`, in Lean (in progress)

One of the papers on Morrey's problem formalized in this repository; the
[overview](../../README.md) describes the problem, the state of each case and how the papers relate.

G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*,
[arXiv:2608.03488v3](https://arxiv.org/abs/2608.03488v3) (16 September 2026), a preprint, claims
rank-one convex integrands on `ℝ^{2×m}` that are not quasiconvex. With Šverák's theorem
([Šverák](../Sverak/README.md)) this would leave `2 × 2` as the only size in which Morrey's problem can
have a positive answer. The paper also answers the homogeneous problem of Kirchheim and Kristensen
negatively: `p`-homogeneous, rank-one convex integrands that are nowhere quasiconvex, at every
exponent `p > 1` in suitable sizes, and at `p = 4` in every size above `2 × 2`.

**Status: every result of the paper is proved; three of the main theorems are conditional.**
Every numbered result of the paper, and the unnumbered claims its argument uses, is stated in Lean,
in the paper's own definitions, and proved, with the standard axioms only. The cited results that
no Lean library has are proved here too (Burkholder's inequalities and scalar functions,
Dacorogna's formula and theorems, Rindler's lemmas, Kristensen's smoothing), except thirteen
results on UMD spaces, non-commutative probability, sharp martingale constants and the
Beurling–Ahlfors transform: each of these is a named hypothesis of the theorems whose proofs use
it, and seven of them are hypotheses of the Challenge's Theorem 1.4 (for general `p`), Theorem 1.5
and Corollary 1.6. The documents of the formalization (report, credits) are not written yet.

## The main theorems and what they assume

| Paper | Lean | Statement | Assumes |
| --- | --- | --- | --- |
| Theorem 1.2 | [`theorem1_2`](../../Morrey/Cassese/Introduction.lean#L2097) ⭐ | every `p > 1`: on `ℝ^{2×m}`, `m ≥ m₀(p)`, a `p`-homogeneous, rank-one convex, nowhere quasiconvex integrand | nothing (the route of Remark 4.5; the paper's proof, [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L2058), assumes Pisier's and Yaroslavtsev's UMD bounds and the HNVW extrapolation) |
| Theorem 1.3 | [`theorem1_3_a`](../../Morrey/Cassese/Introduction.lean#L2113), [`theorem1_3_b`](../../Morrey/Cassese/Introduction.lean#L2138) ⭐ | a quartic homogeneous polynomial on `ℝ^{2×3}`, rank-one convex and nowhere quasiconvex; and for `p` near `4` | nothing |
| Theorem 1.4 | [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2167) ⭐ | every `p > 1`: on `ℝ^{d×d}`, `d ≥ d₀(p)`, a conjugation- and transposition-invariant example | HNVW extrapolation, Randrianantoanina, Cox–Veraar decoupling, Pisier–Xu, Kahane–Khintchine |
| Theorem 1.4, `p = 4` | [`theorem1_4_four`](../../Morrey/Cassese/Square.lean#L3381) ⭐ | the same at `p = 4`, for every `d ≥ 588` | nothing |
| Theorem 1.5 | [`theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2253) ⭐ | every `p ≠ 2`: an example on `ℝ^{4×2}` | transference, Dragičević's lower bound |
| Corollary 1.6 | [`corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2301) ⭐ | a nonnegative 1-homogeneous rank-one convex integrand on `ℝ^{4×4}`, not quasiconvex at a matrix of rank two | as Theorem 1.5 |
| Corollary 5.3 | [`corollary5_3`](../../Morrey/Cassese/TwoByThree/Transpose.lean#L176) ⭐ | the transposed quartic on `ℝ^{3×2}` | nothing |
| Section 1.1, lines 251–254 | [`morrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2327) ⭐ | with Šverák: Morrey's problem fails in every size `d × m` with `d, m ≥ 2` except `2 × 2` | nothing |
| Lines 254–256 | [`homMorrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2355) ⭐ | at `p = 4`, the homogeneous problem fails in every such size except `2 × 2` | nothing |

⭐ in [`Challenge.lean`](../../palomar/Cassese/Challenge.lean), with a check of the definitions
([`projL3_mem`](../../Morrey/Cassese/TwoByThree/Basic.lean#L57)), proved in [`Solution.lean`](../../palomar/Cassese/Solution.lean) and checked by
Comparator. The named hypotheses are defined in [`Defs.lean`](../../Morrey/Cassese/Defs.lean),
each with its source.

## Building

From the repository root, on this branch:

```sh
lake exe cache get && lake build
```


## Credits

- Formalized by Claude (Anthropic), with Claude Code, at the request of The-Anh Vu-Le, following
  the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure,
  independently of the author's own Lean formalization. No person has reviewed the statements.
- License: Apache-2.0 ([`LICENSE`](../../LICENSE)).
