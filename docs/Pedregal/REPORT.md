# Audit of the paper and the formalization

Paper: Pablo Pedregal, *Morrey's conjecture: rank-one convexity implies quasi-convexity for
two-dimensional, two-component maps*, [arXiv:1905.06571v5](https://arxiv.org/abs/1905.06571v5)
(18 June 2026). The audit was made against the arXiv LaTeX source of that version. Section,
result and equation numbers are the paper's (from the compiled source); line numbers refer to
the TeX file `rank-one__quasiconvexity.tex` of the arXiv source.

Status of the formalization:

- **The paper's main results, Theorems 1.1 and 1.2, are neither proved nor refuted.** Theorem 1.1
  (2) and Theorem 1.2 are the `2 × 2` case of Morrey's problem, which is open; Theorem 1.1 (1)
  (every gradient measure of a pair of `ℙ_l` maps is a laminate of finite order) implies it (E16)
  and is open too. They are stated as propositions
  ([`Theorem1_1_part1`](../../Morrey/Pedregal/Introduction.lean#L54), [`Theorem1_1_part2`](../../Morrey/Pedregal/Introduction.lean#L60), [`Theorem1_2`](../../Morrey/Pedregal/Introduction.lean#L65)), not as theorems.
- **Corollary 7.2 and Proposition 7.1 are false** ([`corollary7_2_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L230),
  [`proposition7_1_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L237)), and so is the summary of Step 2 of the proof of Proposition 7.1, with
  Claim 7.5 ([`step2Claim_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L246)). The proof of Theorem 1.1 applies Kakutani's theorem to the map
  `𝐓` of Definition 6.1, and needs every value `𝐓(t)` to be nonempty, which is Corollary 7.2. So
  the paper does not prove Theorem 1.1 (E13).
- Every other numbered result of Sections 3–7 except Claim 7.3 is correct and proved:
  Proposition 3.3, the assertions of Definition 5.1 and eqs. (5.10)–(5.15), Proposition 6.1,
  Subsection 6.1, Proposition 6.3, Claim 7.4, and the reduction
  [`theorem1_1_of_nonempty`](../../Morrey/Pedregal/Reduction.lean#L24): if every `𝐓(t)` is nonempty, then `ν` is a laminate.
- Theorem 1.1 (1) is proved at the level `l = 1` ([`theorem1_1_part1_levelOne`](../../Morrey/Pedregal/LevelOne.lean#L156)), by an explicit
  lamination: the paper's argument fails there too.
- The cited result, Kakutani's fixed-point theorem (Theorem 6.2), is proved in [`External/`](../../Morrey/Common/External) from
  [lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point). Nothing is assumed.
- `lake build` passes with no `sorry` outside [`Challenge.lean`](../../palomar/Pedregal/Challenge.lean), no `axiom`, and every
  declaration depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound)
  ([`scripts/Audit.lean`](../../scripts/Audit.lean)). Comparator accepts [`Solution.lean`](../../palomar/Pedregal/Solution.lean) against [`Challenge.lean`](../../palomar/Pedregal/Challenge.lean).
- No statement of the paper was changed: the false ones are stated as the paper states them and
  refuted.

## 1. Summary

| Kind | Findings |
| --- | --- |
| Errors | E13: Proposition 7.1 and Corollary 7.2 are false, so the proof of Theorem 1.1 fails; E14: the summary of Step 2 (with Claim 7.5) is false |
| Gaps | E15: the proof of Proposition 7.1 (dimension count, positivity, the starting barycenter, the averaging over translates); E16: Theorem 1.1 (2) from (1), "a standard density argument", is not given |
| Missing hypotheses | E4: Theorem 1.2 takes "an arbitrary function", but its integral needs a measurable `ψ` |
| Redundant hypotheses | none in the paper's results |
| Use of cited results | Kakutani's theorem: stated correctly, but its non-emptiness hypothesis fails (E13) |
| Later work | E17: counterexamples claimed in 2026 preprints on `ℝ^{2×3}` and `ℝ^{2×4}` would, if correct, contradict the claim of v1–v2 (2019) for two-component maps in dimension `N ≥ 3` |
| Readings and wording | E7: Proposition 3.3's permutation is unique for ordered molds, as the paper's notation is |
| Misprints and slips | E1–E3, E5, E6, E8–E12, E18 |

## 2. Results from prior work and how the paper uses them

### Proved in `External/`

| Result | Where the paper uses it | Source | Theorem in `External/` |
| --- | --- | --- | --- |
| Kakutani's fixed-point theorem (Theorem 6.2) | Section 8: a fixed point of `𝐓` | Kakutani 1941, cited from Smirnov 2002 | [`External.Kakutani.exists_fixedPoint`](../../Morrey/Common/External/Kakutani/Theorem.lean#L38), from `Kakutani.exists_fixedPoint` of [lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point) |

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| The gradient of a function of `ℙ_l` on a triangle, from its values at the vertices | Sections 4, 5, 7 | [`grad_eq_of_affine`](../../Morrey/Pedregal/Triangulation.lean#L71), [`grad_lower`](../../Morrey/Pedregal/Triangulation.lean#L168), [`grad_upper`](../../Morrey/Pedregal/Triangulation.lean#L192) |
| Across an interface, the jump of the gradient of `w ∈ ℙ_l` is a multiple of the normal | Section 2, Definition 6.1, Proposition 6.1 | [`grad_sides_sub`](../../Morrey/Pedregal/Triangulation.lean#L307) |
| The barycenter of `ν_w` vanishes, by periodicity (5.13), and so the barycenters `𝕎_j` average to `0` (5.15) | Section 5 | [`equation5_13`](../../Morrey/Pedregal/Triangulation.lean#L337), [`equation5_15`](../../Morrey/Pedregal/Map.lean#L238) |
| `Θ_l` is nonempty, convex and compact (Definition 5.1) | Section 6 | [`theta_nonempty`](../../Morrey/Pedregal/Weights.lean#L45), [`convex_theta`](../../Morrey/Pedregal/Weights.lean#L49), [`isCompact_theta`](../../Morrey/Pedregal/Weights.lean#L90), [`theta_subset_simplex`](../../Morrey/Pedregal/Weights.lean#L77) |
| A closed graph into a compact set gives upper semicontinuity | Subsection 6.1 | [`section6_1_usc`](../../Morrey/Pedregal/Map.lean#L346) |
| A rank-one splitting tree gives a laminate | Proposition 6.1 | [`Mold.isLaminate_leafMeasure`](../../Morrey/Pedregal/Hn/Laminate.lean#L139) |
| A `2 × 2` matrix has rank at most one exactly when its determinant vanishes | Definition 6.1, Proposition 6.1 | [`Matrix.rank_le_one_iff_det_eq_zero_of_fin_two`](../../Morrey/Common/Basic/LinearAlgebra/Matrix/RankTwo.lean#L21) |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Kakutani's theorem | Section 8 | stated correctly (Theorem 6.2); its hypotheses are checked correctly except non-emptiness of the values, which is false (E13) |
| Approximation of Lipschitz maps by piecewise affine ones (Ekeland–Temam) | Sections 1, 4 | used for Theorem 1.1 (2) in "a standard density argument" that is not given (E16) |

The other citations give context only: the history of Morrey's problem, examples of rank-one
convex functions, numerical studies.

## 3. Errors and gaps in the paper

### E1. Section 4, eq. (4.4) (line 584): the block `I_3`

The paper writes `I_3 = {2^{2l+2}+1, 2^{2l+2}+2, …, 3^{2l+2}}`; it should be
`{2·2^{2l+2}+1, …, 3·2^{2l+2}}` (the last `2^{2l+2}` of the `3·2^{2l+2}` indices; the case
`l = 2`, eq. (4.1), has it right: `{129, …, 192}`). A misprint; nothing
depends on it. The formalization indexes leaves by `(j, k)` with `j : Fin 3`.

### E2. Definition 3.1 (line 314): "two different indexes `1 ≤ i_p ≤ i_q ≤ k`"

Different indices need `i_p < i_q`. A slip.

### E3. Definition 3.1 (lines 305–311): `μ_k = ∑_i s_i^{(k)} w_i^{(k)}`

The Dirac masses are missing: `μ_k = ∑_i s_i^{(k)} δ_{w_i^{(k)}}`, and likewise for `μ_m`. A
misprint.

### E4. Theorem 1.2 (lines 198–212)

The theorem takes "an arbitrary function" `ψ : 𝕄^{2×2} → ℝ`, but statement (2) integrates
`ψ(F + ∇u)`, which needs `ψ` measurable; the Introduction works with continuous integrands
(lines 124, 136). Statement (1) also writes `Ψ` for `ψ` and does not say `t ∈ [0, 1]`. A
real-valued rank-one convex function is separately convex, hence locally Lipschitz, so the
hypothesis matters only for (2) ⇒ (1). The formalization reads `ψ` continuous ([`Theorem1_2`](../../Morrey/Pedregal/Introduction.lean#L65);
in [`Theorem1_1_part2`](../../Morrey/Pedregal/Introduction.lean#L60) the hypothesis is redundant and harmless). Not proved either way (E13).

### E5. Example 3.2 (line 407)

A stray bracket: `[1, 6], [2, 3], [4, 7], [5, 8]]`. A misprint.

### E6. Section 5, eqs. (5.10), (5.11) and line 679

(5.10) gives the first-level weights `t_k^{(m−1)} = 2^{1−m}` (with `m = 2l + 2` in the dyadic
sub-molds, `2^{−1−2l}`), but (5.5) makes them `3^{−1} 2^{−1−2l}`: a factor `3` is missing. (5.11)
gives `λ_k^{(p)} = 1/2` for `1 ≤ p ≤ m − 2`, and line 679 for "all `0 ≤ p ≤ m − 1`"; the
relative weights are `1/2` for `0 ≤ p ≤ m − 2`, and at `p = m − 1` (the first level) they are
`t_{2k}/t_k^{(m−1)}`, not `1/2`. Slips: the argument only uses that the relative weights above the
first level are `1/2` ([`point_dyadic_theta`](../../Morrey/Pedregal/Weights.lean#L151)).

### E7. Proposition 3.3 (line 411): uniqueness of the permutation (a reading)

"There is always a unique permutation … such that mixtures always take place in the form
`[2i − 1, 2i]`." Unique when the order inside a bracket counts, as it does in the paper's
notation and for the sign of the direction (3.5); for unordered mixtures there would be
`2^{2^m − 1}` such permutations (`[1, 2]` comes from the identity and from `(1 2)`). The
paper's proof is "elementary". The formalization reads molds as ordered trees and proves the
statement ([`proposition3_3`](../../Morrey/Pedregal/Hn/Mold.lean#L171)).

### E8. Definition 4.1 (line 592): "a suitable partition `{𝒞_s}` of the triangles of `τ_l` in which each element occurs six times"

It is a partition of the index set into classes `𝒞_s` of six indices, one class per triangle
(as eq. (4.3) says). A slip of wording. [`TriMold.card_C`](../../Morrey/Pedregal/MoldTau.lean#L355), [`TriMold.card_C_filter`](../../Morrey/Pedregal/MoldTau.lean#L361).

### E9. Duplicate TeX labels

`elementos` labels (3.7) and (5.12), and `pesos` labels Definition 5.1 and (7.2). There is no
`\ref{pesos}`; the three references `\eqref{elementos}` (lines 708, 711, 787) print as (5.12),
which is the intended one there (it repeats the notation of (3.7)). Harmless.

### E10. Definition 6.1 (line 750): "for all `0 ≤ p ≤ m − 2`, `1 ≤ k ≤ 2^p`"

The tri-dyadic mold is not dyadic: level `0` has one mixture, level `1` one mixture and a pair
that passes through, and level `p ≥ 2` has `3 · 2^{p−2}` mixtures (`2^{p−2}` per sub-mold). So
`1 ≤ k ≤ 2^p` is wrong at every level `p ≥ 1` (line 723 has the same slip). The intended condition
is "at every mixture above the first level", which the formalization states ([`Pedregal.T`](../../palomar/Pedregal/Challenge.lean#L224)).

### E11. Eq. (7.12) and line 998

`r = (r_1, …, r_{2l+2})` with `r_{2i} + r_{2i−1} = 2^{−1−2l}`: the vector has `2^{2l+2}` entries
per sub-mold and the pairs add up to `3^{−1} 2^{−1−2l}` in `Θ_l` (5.5); "all weights at the last
level are `2^{−1−2l}`" has the same slip.

### E12. Section 4 (line 532): "for dimension `N = 3`, seven [normals] are necessary"

Kuhn's (Freudenthal's) triangulation of the cube into six simplices `{x_{σ(1)} ≤ x_{σ(2)} ≤
x_{σ(3)}}` tiles `ℝ³` by translations and uses six normals, `e_i` and `e_i − e_j`. The remark is
not used.

### E13. Proposition 7.1 and Corollary 7.2 are false

**What the paper claims.** Proposition 7.1 (line 863): for `u ∈ ℙ_l` and `t ∈ Θ_l`, the measure
`ν_w` of every `w ∈ ℙ_l` admits an `(H_n)`-condition along `𝒮_l` with the decomposition directions
of `u` for `t` and some weights `r ∈ Θ_l`. Corollary 7.2 (line 874): `𝐓(t) ≠ ∅` for all
`u, v ∈ ℙ_l`, `t ∈ Θ_l`. Theorem 1.1 is deduced from Kakutani's theorem, whose hypotheses include
the non-emptiness of the values (Section 8).

**Counterexample.** `l = 1`, the mold `TriMold.canonical 1` (interfaces numbered kind by kind,
cell by cell), `t` the uniform weights `1/48`, and
`u = τ(x₀) − τ(x₁) − τ(x₀ + x₁)`, `v(x₀, x₁) = u(x₁, x₀)`, where `τ(x)` is the distance from `x` to
the nearest integer. Both lie in `ℙ_1`. The first mixture above the first level of the sub-mold
`j = 1` (normals `(1, 0)`, `(0, 1)`) joins the vertical interfaces of the cells `(0, 0)` and
`(0, 1)`. The tangential derivative `∂₂` is continuous across a vertical interface; so the mass
points of the two first-level mixtures, whatever the weights, have second coordinates `∂₂u`
there, and `∂₂v` for `v`:

| Interface | Triangles | `∇u` | `∇v` |
| --- | --- | --- | --- |
| vertical, cell `(0, 0)` | upper `(0,0)`, lower `(1,0)` | `(2, 0)`, `(0, 0)` | `(0, 2)`, `(2, 2)` |
| vertical, cell `(0, 1)` | upper `(0,1)`, lower `(1,1)` | `(0, 0)`, `(−2, 0)` | `(−2, −2)`, `(0, −2)` |

With the weights `t` the mass points of `u` are `(1, 0)` and `(−1, 0)`, so the direction of `u`
is `(2, 0)`. For every weights `r`, the mass points of `v` have second coordinates `2` and `−2`,
so the direction of `v` is `(∗, 4)`, and `det((2, 0), (∗, 4)) = 8 ≠ 0`. No `r` satisfies the
condition of Definition 6.1 at this mixture: `𝐓(t) = ∅`. The same mixture refutes Proposition 7.1
(with `w = v`). Lean: [`T_cex_eq_empty`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L224), [`corollary7_2_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L230), [`proposition7_1_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L237). The
argument does not use the constraints of `Θ_1`. It works for every `t ∈ Θ_1` except those that put
all the weight of the two interfaces on the two triangles where `∇u = 0`, and it survives small
perturbations of `(u, v, t)`: non-emptiness is a closed condition (the conditions are polynomial
in `(u, v, t, r)` and `Θ_l` is compact; [`section6_1_isClosed_graph`](../../Morrey/Pedregal/Map.lean#L303) proves the closedness for fixed
`u, v` only). So the counterexamples meet the dense class `𝒞` to which the proof of
Proposition 7.1 reduces (line 885), and the reduction cannot rescue the claim.

**Which molds.** Lean refutes Corollary 7.2 as a statement about every tri-dyadic mold, which is
how the paper states it ("any such manner of labelling planar interfaces is equally valid",
line 560). That it fails for every mold is checked only numerically, below.

**The failure is generic, and does not depend on the mold.** `𝐓(t)` is cut out of `Θ_l` by linear
equations in `r`: `Θ_l` has dimension `2^{2l+2} + 1` (`17` for `l = 1`), while Definition 6.1
imposes `3(2^{2l+1} − 1) + 2` conditions (`23`). Checked numerically (floating point, not in
Lean; the scripts are in [`numerics/`](numerics)):

- for 40 random `(u, v, t)` with random molds at each of `l = 1` and `l = 2`, the linear system
  defining `𝐓(t)` was inconsistent every time;
- for one generic instance at `l = 1` (integer nodal values, random interior `t`), the system is
  inconsistent for every tri-dyadic mold: all `315³` choices of the three sub-mold shapes
  (orientations and the order of the last mixtures do not matter for it).

**Does Theorem 1.1 still hold?** Unknown: Theorem 1.1 (2) is the `2 × 2` case of Morrey's
problem, and (1) implies it. At `l = 1`
the conclusion of Theorem 1.1 (1) holds ([`theorem1_1_part1_levelOne`](../../Morrey/Pedregal/LevelOne.lean#L156)): `ν` is uniform on the
eight matrices `±C₁ ± C₂ ± C₃` with rank-one `C_i`, which three rank-one splittings reach. So the
failure of Corollary 7.2 is a failure of the method, not evidence against the theorem. For the
counterexample pair itself, `𝐓` even has a fixed point, which Kakutani's theorem cannot provide
here: the weights whose relative weights `λ` (the share of the second leaf, `2i + 1` in Lean,
the paper's `2i`) on the first-level mixtures, in the order of `TriMold.canonical 1`, are
`1, 0, 0, 1, 0, 1, 1, 0` in the sub-mold `j = 1`, `1, 0, 0, 1, ½, ½, ½, ½` in `j = 2` and
`0, 1, 1, 0, ½, ½, ½, ½` in `j = 3` lie in `Θ_1` and in their own image (found numerically,
checked in exact rational arithmetic, [`numerics/fixedpoint_exact.py`](numerics/fixedpoint_exact.py); not in Lean).

### E14. The summary of Step 2 of the proof of Proposition 7.1, with Claim 7.5, is false

The displayed summary after Step 2 (lines 1002–1004) asserts, for each sub-mold `j` separately,
weights `r_j ≥ 0` for which the decomposition directions of `w` are those of `u`, with the
top-to-bottom procedure started from the barycenter `𝕌_j` of `u` (7.6); Claim 7.5 (line 966) is
the positivity part. As the paper states it ([`Step2ClaimPaper`](../../Morrey/Pedregal/NonEmptiness/Statements.lean#L75)), it fails for a trivial reason:
for `w = 0` the barycenter of `w` is `0`, not `𝕌_j ≠ 0`. Without the start from `𝕌_j`
([`Step2Claim`](../../Morrey/Pedregal/NonEmptiness/Statements.lean#L65), weaker), it is still false: the mixture of E13 lies in one sub-mold
([`step2Claim_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L246), [`step2ClaimPaper_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L253)). (For uniform `t` the barycenters `𝕌_j`
vanish, so this trivial failure needs a non-uniform `t`.) Numerically the failure is typical but
not generic: one sub-mold has `2^{2l+1}` relative weights and `2^{2l+1} − 1` parallelism
conditions, so the solutions form a line, which for most random instances misses
`[0, 1]^{2^{2l+1}}` (`l = 1`: 7 of 90 random instances feasible; `l = 2`: none of 90). It does not
miss it for `w` close to `u` when `t` is interior, since `w = u` has the solution `r = t`.

### E15. Gaps in the proof of Proposition 7.1

E13 shows that the statement is false; these are the places where the argument fails.

- Step 2 (lines 964–1008) concludes from "linearity together with this matching of dimensions"
  (line 971)
  that every gradient of `ℙ_l` is reached. In the counterexample, the direction of `u` at the mixture of
  E13 is horizontal, so every `w` that the construction reaches has the same `∂₂w` on the two
  vertical interfaces of that mixture: the image is a proper subspace of `ℙ_1`, which misses `v`. Equal dimensions of a domain and a target do not make
  a linear map onto, and the set of feasible parameters is a polytope (positivity), not a
  subspace: the image of a polytope that contains a neighbourhood of `u` need not be the whole
  space.
- The positivity of Claim 7.5 is derived from "for true gradients of functions in `ℙ_l`,
  averages over planar interfaces are alway legitimate convex combinations" (line 990): those
  are averages with weights `1/2`, not the weights that the construction produces.
- The top-to-bottom procedure for `w` starts from the barycenter `𝕌_j` of `u` (7.6), which
  imposes `3 ∑_k r_k ∇w = 𝕌_j`; the proof never checks it (line 1024: "vectors `𝕌_j` … are the
  same for every `w`").
- Step 3 (lines 1026–1043) averages vectors of weights `r_q` obtained for the translates `w_q`
  of `w`, and appeals to the convexity of `𝐓(t)` (Proposition 6.3). But `r_q` makes the directions
  of `w_q`, not of `w`, parallel to those of `u`: Proposition 6.3 is about one function `v`, and
  says nothing about the average.

### E16. Theorem 1.1 (2) from Theorem 1.1 (1)

The paper gets (2) from (1) "by a standard density argument about approximation by continuous,
piece-wise affine mappings" (line 161) and Section 8. The argument is not given; it needs
Jensen's inequality for laminates and rank-one convex functions, the continuity of rank-one
convex functions, the approximation of periodic Lipschitz maps by `ℙ_l` maps with convergence of
the gradient measures, and the equivalence of the periodic and the `W^{1,∞}_0` definitions of
quasiconvexity. All of it is standard, and all of it is moot while (1) is unproved. Not
formalized.

### E17. Later work: the claim of v1–v2 in higher dimension

Versions v1 and v2 of the paper (2019), titled *Rank-one convexity implies quasiconvexity for
two-component maps*, claimed the equivalence for two-component maps with no restriction on the
dimension of the domain. v3 (29 August 2024) withdrew the paper ("Some of the steps of the proof
require a more transparent and convincing way to be accepted"), and v4 (2025) and v5 restrict
the claim to dimension two and say that the case `N ≥ 3` is open (line 216 of v5). The body of v1 confirms the unrestricted
claim: "rank-one convexity implies quasiconvexity in the case `2 × N`", with `Q ⊂ ℝ^N`. Two preprints of
August 2026, after v5, claim rank-one convex integrands that are not quasiconvex on `ℝ^{2×m}` for
`m` large and on `ℝ^{2×3}` (G. Cassese, [arXiv:2608.03488](https://arxiv.org/abs/2608.03488)), and
on `ℝ^{2×4}` (A. Agazzi, G. Bruno, A. Guerra, F. Pasqualotto,
[arXiv:2608.12298](https://arxiv.org/abs/2608.12298)); in both, `ℝ^{2×m}` is the space of
gradients of maps `ℝ^m → ℝ²`. If they are correct, the claim of v1–v2 is false in dimension
`N ≥ 3`, and the question that v5 leaves open there is settled negatively.

### E18. Misprints

"counter-examble" (line 150), "Brower" (lines 176, 775), "subleties" (line 197), "full collection
of triangle" (line 542), "important for." (line 488), "interfase" (line 620), "point or our
concern" (line 762), "alway" (line 990), and "(in press)" for a 2011 paper (line 1067).

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| Theorem 1.2 | `ψ` measurable (continuous, as in Section 1), needed only for (2) ⇒ (1) | for a non-measurable `ψ` the integral in (2) is undefined | [`Theorem1_2`](../../Morrey/Pedregal/Introduction.lean#L65) takes `Continuous ψ` |

## 5. Redundant hypotheses

None in the paper's results. The proofs of Proposition 6.3 do not use `u, v ∈ ℙ_l`, and the
formalization states them for arbitrary functions `u, v`.

## 6. How the formalization reads the paper

- **Points, matrices.** `ℝ²` is `Fin 2 → ℝ`; the matrix of `(u, v)` has rows `∇u`, `∇v`.
- **`τ_l`, `ℙ_l`.** A triangle is `(a, b, k)`: the cell `(a, b)` of the `2^l × 2^l` grid and
  `k = 0` (lower-left) or `1` (upper-right), cut along the diagonal of normal `(1, 1)`
  (`Tri`, [`triangle`](../../palomar/Pedregal/Challenge.lean#L67)). `ℙ_l` (`PL`) is the set of continuous `1`-periodic functions affine on
  every triangle; the gradient on a triangle is the derivative at its centroid ([`grad`](../../palomar/Pedregal/Challenge.lean#L88)), which is
  the slope of the affine function ([`grad_eq_of_affine`](../../Morrey/Pedregal/Triangulation.lean#L71)).
- **Interfaces.** `Iface l`: the vertical, horizontal and diagonal edge of each cell, with its two
  triangles ([`Iface.sides`](../../palomar/Pedregal/Challenge.lean#L101)), modulo the period; [`sides_adjacent`](../../Morrey/Pedregal/Triangulation.lean#L232) checks that they share an edge
  orthogonal to the normal.
- **Molds** (Definitions 3.1, 3.2) are ordered binary trees, as the paper's bracket notation is
  (E7) ([`Mold`](../../palomar/Pedregal/Challenge.lean#L116)); the bottom-to-top recursion
  (3.3)–(3.6) is [`Mold.weight`](../../palomar/Pedregal/Challenge.lean#L125), [`Mold.point`](../../palomar/Pedregal/Challenge.lean#L135) (with the convention `λ = 1/2` for weight `0`), and the
  direction of `[L, R]` is `L.point − R.point`. The top-to-bottom description is the same object
  read from the root ([`Mold.isLaminate_add_leafMeasure`](../../Morrey/Pedregal/Hn/Laminate.lean#L70)).
- **Tri-dyadic molds for `τ_l`** (Definition 4.1) are `TriMold l`: a numbering of the interfaces
  of each sub-mold, which side gets the first leaf, and the order of the last two mixtures. The
  conditions of Section 4 are proved ([`TriMold.card_C`](../../Morrey/Pedregal/MoldTau.lean#L355), [`TriMold.card_C_filter`](../../Morrey/Pedregal/MoldTau.lean#L361),
  [`TriMold.leafTri_pair`](../../Morrey/Pedregal/MoldTau.lean#L274), [`TriMold.tree_isTriDyadic`](../../Morrey/Pedregal/MoldTau.lean#L243)).
- **Indices.** Leaves are `(j, k)`, both from `0`: the paper's leaf `j · 2^{2l+2} + k + 1`; the
  first-level mixture `i` (from `0`) joins the leaves `2i, 2i + 1`, the paper's `2i + 1, 2i + 2` of
  its interface `i + 1`.
- **Parallel** means linearly dependent (`det = 0`), as rank one requires.
- **`𝐓`** (Definition 6.1): parallelism at every mixture whose two parts are not both leaves,
  which for the tri-dyadic molds is "every level `0 ≤ p ≤ m − 2`" (E10).
- **Laminates** are laminates of finite order ([`IsLaminate`](../../palomar/Pedregal/Challenge.lean#L248)), finitely supported probability
  measures obtained from a Dirac mass by splitting atoms along rank-one segments: the paper's
  "joint `(H_n)`-conditions whose decomposition directions are parallel" (Section 1).
- **Proposition 7.1** ("with the given system of decomposition directions") means directions
  parallel to the given ones: the top-to-bottom step (7.7) splits along `S · 𝐔_k^{(p)}`.
- **Step 2's summary** is stated as [`Step2ClaimPaper`](../../Morrey/Pedregal/NonEmptiness/Statements.lean#L75), for one sub-mold, with nonnegative weights
  adding up to `3^{−1} 2^{−1−2l}` on each first-level mixture and the start from `𝕌_j`, and as
  the weaker [`Step2Claim`](../../Morrey/Pedregal/NonEmptiness/Statements.lean#L65), without the start from `𝕌_j`; both are refuted (E14).
- **Kakutani's theorem** is stated with upper semicontinuity in the topological sense; the paper's
  Subsection 6.1 proves the closed graph property, and [`section6_1_usc`](../../Morrey/Pedregal/Map.lean#L346) derives upper
  semicontinuity from it and the compactness of `Θ_l`, a step the paper leaves implicit.

## 7. Departures from the paper's proofs

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| Theorem 1.1 (1) | a fixed point of `𝐓` by Kakutani's theorem, using Corollary 7.2 | [`theorem1_1_of_nonempty`](../../Morrey/Pedregal/Reduction.lean#L24): the same argument, with the non-emptiness of the values as a hypothesis; [`theorem1_1_part1_levelOne`](../../Morrey/Pedregal/LevelOne.lean#L156): at `l = 1`, an explicit lamination | Corollary 7.2 is false (reason 1: the paper's step is wrong) | E13 |
| Proposition 7.1, Corollary 7.2, Step 2 | proofs of false statements | refutations | the statements are false | E13, E14 |

Every other proof follows the paper's argument. Two steps that the paper leaves implicit are
spelled out, not changed: the closed graph of Subsection 6.1 rests on "the dependence of elements
in (5.12) on `t` is continuous" (the notation of (3.7), E9), which on `Θ_l` is the linearity of
Proposition 6.3 (1); and the
upper semicontinuity that Kakutani's theorem asks for is derived from the closed graph and the
compactness of `Θ_l` ([`section6_1_usc`](../../Morrey/Pedregal/Map.lean#L346)).

## 8. What each result depends on

Generated by [`scripts/Audit.lean`](../../scripts/Audit.lean), which also checks that every declaration of the library uses
only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Prop 3.3 | [`Pedregal.proposition3_3`](../../Morrey/Pedregal/Hn/Mold.lean#L171) | – |
| Def 5.1 (assertions) | [`Pedregal.theta_nonempty`](../../Morrey/Pedregal/Weights.lean#L45) | – |
| Def 5.1 (assertions) | [`Pedregal.convex_theta`](../../Morrey/Pedregal/Weights.lean#L49) | – |
| Def 5.1 (assertions) | [`Pedregal.isCompact_theta`](../../Morrey/Pedregal/Weights.lean#L90) | – |
| Def 5.1 (assertions) | [`Pedregal.theta_subset_simplex`](../../Morrey/Pedregal/Weights.lean#L77) | – |
| Eq. (5.13) | [`Pedregal.equation5_13`](../../Morrey/Pedregal/Triangulation.lean#L337) | – |
| Eq. (5.15) | [`Pedregal.equation5_15`](../../Morrey/Pedregal/Map.lean#L238) | – |
| Prop 6.1 | [`Pedregal.proposition6_1`](../../Morrey/Pedregal/Map.lean#L365) | – |
| Thm 6.2 (Kakutani, cited) | [`External.Kakutani.exists_fixedPoint`](../../Morrey/Common/External/Kakutani/Theorem.lean#L38) | – |
| Subsection 6.1 | [`Pedregal.section6_1_isClosed_graph`](../../Morrey/Pedregal/Map.lean#L303) | – |
| Subsection 6.1 | [`Pedregal.section6_1_isCompact`](../../Morrey/Pedregal/Map.lean#L333) | – |
| Subsection 6.1 | [`Pedregal.section6_1_usc`](../../Morrey/Pedregal/Map.lean#L346) | – |
| Prop 6.3 (1) | [`Pedregal.proposition6_3_point`](../../Morrey/Pedregal/Map.lean#L263) | – |
| Prop 6.3 (1) | [`Pedregal.proposition6_3_dir`](../../Morrey/Pedregal/Map.lean#L276) | – |
| Prop 6.3 (2) | [`Pedregal.proposition6_3`](../../Morrey/Pedregal/Map.lean#L285) | – |
| Prop 7.1 (false) | [`Pedregal.proposition7_1_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L237) | – |
| Cor 7.2 (false) | [`Pedregal.corollary7_2_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L230) | – |
| Cor 7.2 from Prop 7.1 | [`Pedregal.corollary7_2_of_proposition7_1`](../../Morrey/Pedregal/NonEmptiness/Statements.lean#L49) | – |
| Step 2 summary (false) | [`Pedregal.step2Claim_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L246) | – |
| Claim 7.4 | [`Pedregal.claim7_4`](../../Morrey/Pedregal/NonEmptiness/Statements.lean#L107) | – |
| Thm 1.1 (1), up to Cor 7.2 | [`Pedregal.theorem1_1_of_nonempty`](../../Morrey/Pedregal/Reduction.lean#L24) | [`External.Kakutani.exists_fixedPoint`](../../Morrey/Common/External/Kakutani/Theorem.lean#L38) |
| Thm 1.1 (1), l = 1 | [`Pedregal.theorem1_1_part1_levelOne`](../../Morrey/Pedregal/LevelOne.lean#L156) | – |

The route check ([`scripts/route_check.py`](../../scripts/route_check.py)) compares the results that each formal proof uses with
those that the paper's proof cites ([`docs/paper_routes.tsv`](paper_routes.tsv)). Every difference is recorded with its
reason in [`docs/route_differences.tsv`](route_differences.tsv): the refutations do not use the steps of the refuted proofs,
[`theorem1_1_of_nonempty`](../../Morrey/Pedregal/Reduction.lean#L24) takes the conclusion of Corollary 7.2 as a hypothesis, the closed graph of
Subsection 6.1 uses the linearity of Proposition 6.3 (the continuity that the paper invokes), and
the assertions of Definition 5.1 are used without citation throughout.

## 9. Not formalized

- Theorem 1.1 (2) and Theorem 1.2: open (E13), and their reduction to Theorem 1.1 (1) (E16).
- Theorem 1.1 (1) for `l ≥ 2`: open as far as we know.
- Claim 7.3 (the full rank of the map `𝐒 ↦ 𝒰` for a dense set of `(u, t)`, with negligible
  complement): a step of the refuted proof of Proposition 7.1, asserted without proof and used by
  no correct result. The map is injective as soon as every decomposition direction of `u` above
  the first level is nonzero: with relative weights `½`, each mass point is the average of its two
  children, so an `𝐒` in the kernel leaves every mass point at `𝕌_j` and forces `S · 𝐔 = 0`
  at each mixture. That this holds outside a negligible set of `(u, t)` was not checked.
- Section 2 (the strategy), the examples of Section 3, and the remarks on higher dimensions.

## 10. The paper in the literature

Searched on 21 November 2026: arXiv listings and abstracts, the papers that the paper cites, web
search for responses to the paper, and GitHub for formalizations. Preprints are reported as
claimed, not as proved.

### Before the paper

- C. B. Morrey (1952, 1966) proved that weak-∗ lower semicontinuity of `∫ ψ(∇u)` is equivalent to
  quasiconvexity of `ψ`, conjectured that rank-one convexity does not imply quasiconvexity, and
  later stated it as an open problem. J. M. Ball (1977) proved that polyconvexity implies
  quasiconvexity.
- V. Šverák (1992) gave a rank-one convex function on `ℝ^{3×2}` that is not quasiconvex, so the
  implication fails for `m ≥ 3` components; attempts to extend it to two components failed
  (Pedregal 1996; Pedregal–Šverák 1998; Bandeira–Ornelas 2011). Y. Grabovsky (2018) gave other
  examples for `m > 2`, on `ℝ^{8×2}`.
- For two components, partial results: rank-one convexity implies quasiconvexity on diagonal
  matrices (S. Müller 1999) and on some hypersurfaces (Chaudhuri–Müller 2003), and in special
  isotropic and incompressible classes (Martin–Ghiba–Neff 2017; Ghiba–Martin–Neff 2018); Faraco
  and Székelyhidi (2008) localized the quasiconvex hull in `ℝ^{2×2}`. Astala, Iwaniec, Prause and
  Saksman (2012) connected the `2 × 2` problem with Burkholder's functional and the Iwaniec
  conjecture on the Beurling–Ahlfors transform.
- P. Pedregal, *Some evidence in favor of Morrey's conjecture*
  ([arXiv:1406.7199](https://arxiv.org/abs/1406.7199), 2014, since withdrawn), argued in the
  opposite direction: an explicit family of two-component maps whose gradient measures, it
  claimed, cannot be reached by lamination.
- G. Sebestyén and L. Székelyhidi Jr. ([arXiv:1504.06516](https://arxiv.org/abs/1504.06516), J.
  Convex Anal. 24 (2017)) answered it (the withdrawn preprint's comment says so): the gradient
  measures of sums `a_i h(n_i · x + c_i)` of three sawtooth profiles along pairwise non-collinear
  directions `n_i ∈ ℤ²`, with phases (the construction behind Šverák's example), are symmetric
  measures on the vertices `±C₁ ± C₂ ± C₃` of a cube of rank-one matrices, and these are laminates
  (in the sense of Jensen's inequality) in `2 × 2`. The paper says that its case `l = 2` "would
  correspond to the example in" that work (line 537). The case
  `l = 1` of Theorem 1.1 (1) proved here is the simplest such measure, uniform on a cube.
- The dual formulation that the paper uses, laminates against homogeneous gradient Young
  measures, is Pedregal's (*Laminates and microstructure*, 1993; *Parametrized measures and
  variational principles*, 1997), with the `(H_n)`-conditions of Dacorogna (1985).

### The paper's versions

- v1 (16 May 2019) and v2 (27 September 2019), *Rank-one convexity implies quasiconvexity for
  two-component maps*: the claim for two-component maps, with no restriction on the dimension.
- v3 (29 August 2024): withdrawn, with the comment "Some of the steps of the proof require a more
  transparent and convincing way to be accepted".
- v4 (12 May 2025) and v5 (18 June 2026, the version formalized here), *Morrey's conjecture:
  rank-one convexity implies quasi-convexity for two-dimensional, two-component maps*: the claim
  restricted to dimension two.

### Concurrent work

None found: no work on the same question appeared independently within a year of v1 that
claims a solution of the `2 × 2` case.

### Since the paper

- Numerical studies have found no counterexample in `2 × 2`: A. Guerra and R. Teixeira da Costa
  ([arXiv:2006.09063](https://arxiv.org/abs/2006.09063), Rev. Mat. Iberoam. 2022) give numerical
  evidence towards a positive answer, through `N`-wave quasiconvexity (Jensen's inequality for
  sums of `N` sawtooth waves), which they show is quasiconvexity when `N` is arbitrary; `N = 3` in
  `2 × 2` is Sebestyén–Székelyhidi's theorem, and `N ≥ 4` is open; Voss, Martin,
  Sander, Kumar, Kochmann and Neff (J. Nonlinear Sci. 2022) could not show that their candidate
  fails to be quasiconvex; X. Dong and K. Enakoutsa
  ([arXiv:2211.11194](https://arxiv.org/abs/2211.11194)) discuss simulations towards a
  counterexample. R. Awi and V. Šverák (2023) propose a convex-optimization formulation for the
  open case. The paper calls these studies inconclusive (line 154).
- Counterexamples for two-component maps in higher dimension (preprints, after v5): G. Cassese,
  [arXiv:2608.03488](https://arxiv.org/abs/2608.03488) (August–September 2026), rank-one convex
  integrands on `ℝ^{2×m}` that are nowhere quasiconvex for `m` large, and examples on
  `ℝ^{2×3}`; A. Agazzi, G. Bruno, A. Guerra and F. Pasqualotto,
  [arXiv:2608.12298](https://arxiv.org/abs/2608.12298) (August 2026), an explicit example on
  `ℝ^{2×4}`. Both say that the `2 × 2` case remains open. If correct, they contradict the claim of
  v1–v2 in dimension `N ≥ 3` (E17).
- S. Conti, G. Dolzmann and P. Dondl, [arXiv:2610.31886](https://arxiv.org/abs/2610.31886)
  (October 2026): a frame-indifferent rank-one convex function on `ℝ^{3×3}` that is not
  quasiconvex; its introduction says that a proof of the `2 × 2` case "has been proposed",
  citing this paper. Its Lean code, by its README, was written by Claude Opus 5.5 under the
  authors' guidance.
- No published response to the paper's argument, and no erratum, was found.

### Formalizations

- No formalization of the paper, of `(H_n)`-conditions or of laminates was found.
- Conti, Dolzmann and Dondl formalized their `3 × 3` example in Lean 4 with Mathlib
  ([sergioconti/so3-r1c-and-not-qc](https://github.com/sergioconti/so3-r1c-and-not-qc)),
  with definitions of rank-one convexity and quasiconvexity (on the unit cube, with smooth test
  maps and an integrability condition). This work did not use their code; its [`Quasiconvex`](../../Morrey/Pedregal/Introduction.lean#L46)
  follows Theorem 1.2 instead (bounded open domains, Lipschitz test maps).
- Kakutani's theorem comes from [lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point)
  (Brouwer's, Kakutani's and Schauder's theorems), a dependency of this project.

## 11. What's next

Plans for follow-up papers are kept in `NEXT.md`, which is not published.

### Open directions

- **Theorem 1.1 (1) for `l ≥ 2`.** Is the gradient measure of every pair of `ℙ_l` maps a laminate
  of finite order? At `l = 1` it is ([`theorem1_1_part1_levelOne`](../../Morrey/Pedregal/LevelOne.lean#L156)). For all `l`, a positive answer
  gives the `2 × 2` case of Morrey's problem, by the density argument of E16. The maps of `ℙ_l`
  that are sums of three dyadic profiles along `(1, 0)`, `(0, 1)`, `(1, 1)` are `N`-wave maps with
  `N = 3(2^l − 1)`, inside the case `N ≥ 4` that Guerra and Teixeira da Costa leave open.
- **Molds and weights.** The map `𝐓` is defined by more linear conditions than `Θ_l` has
  dimensions (E13), for every tri-dyadic mold. A fixed-point approach would need a smaller set of
  conditions, for instance parallelism only at a fixed point and not on the whole of `Θ_l`, or a
  larger set of weights than `Θ_l`, which forces every triangle to be split into six pieces and
  every interface to be used twice. The lamination at `l = 1` uses each triangle once and only the
  diagonal interfaces at the first level: it is not of the paper's form.

### Simpler proofs

None of the paper's correct proofs could be made simpler for a reader: they are short. One
observation from the formalization: in [`Mold.weight_smul_point`](../../Morrey/Pedregal/Hn/Mold.lean#L107) the identity
`weight · point = ∑ t_i w_i` needs no positivity of the weight, since both sides vanish when it is
zero.

### The formalization

- [`Basic`](../../Morrey/Common/Basic) holds [`Matrix.rank_le_one_iff_det_eq_zero_of_fin_two`](../../Morrey/Common/Basic/LinearAlgebra/Matrix/RankTwo.lean#L21) (for
  `Mathlib/LinearAlgebra/Matrix/Rank.lean`).
- The `(H_n)`-conditions of [`Morrey/Pedregal/Hn/`](../../Morrey/Pedregal/Hn) (molds, their weights and mass points, and the laminate
  of a rank-one mold) are general and could become a small library on laminates, with Jensen's
  inequality for rank-one convex functions, which the reduction of Theorem 1.1 (2) to (1) needs.
- [`External/Kakutani`](../../Morrey/Common/External/Kakutani) derives the upper semicontinuous form of Kakutani's theorem from the
  closed-graph form of lean4-fixed-point; other formalizations that cite Kakutani in that form can
  reuse it.
- The density argument of E16 (Jensen's inequality for laminates, the continuity of rank-one
  convex functions, the approximation of periodic Lipschitz maps by maps of `ℙ_l`) would turn a
  future proof of Theorem 1.1 (1) into Morrey's `2 × 2` case.
