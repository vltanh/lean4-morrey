# Sources, dependencies and priority

Cutoff: 21 November 2026. This page records the primary literature used in the research and the
limits of the prior-work search. It does not certify novelty, community acceptance of a recent
preprint, or an external Lean build. The repository's existing paper-specific reports remain
the detailed sources for the Pedregal and Šverák audits.

## Primary literature and the role it plays

| Source | Relevance and scope in this research |
| --- | --- |
| Pedregal, [arXiv:1905.06571v5](https://arxiv.org/abs/1905.06571v5), 18 June 2026 | The exact version audited. The existing [report](../Pedregal/REPORT.md) explains the false nonemptiness statements and the remaining open main theorem. Older versions had a broader dimensional claim. |
| Šverák, *Rank-one convexity does not imply quasiconvexity* (1992) | Source of the `3 × 2` construction formalized in this repository; see its [report](../Sverak/REPORT.md). Supplies a higher-dimensional control and reusable cutoff infrastructure. |
| Sebestyén–Székelyhidi, [arXiv:1504.06516](https://arxiv.org/abs/1504.06516), published 2017 | Three-wave/cube laminates in `2 × 2`; constrains direct reuse of the three-wave mechanism. The uniform level-one cube is a special case. |
| Guerra–Teixeira da Costa, [arXiv:2006.09063v1](https://arxiv.org/abs/2006.09063v1), published 2022 | Numerical evidence and the N-wave framework. Finite wave/grid searches do not establish the unrestricted implication. |
| Awi–Šverák, *Remarks on Morrey's quasi-convexity* (2023) | Prior convex-optimization formulation, cited in the [global certificate note](../../research/archive/files/morrey_global_certificate_research.md). Conic reformulation itself is not claimed as new here. Exact bibliographic/theorem comparison remains part of a publication review. |
| Dacorogna–Haeberly, [1996 paper](https://doc.rero.ch/record/290415/files/S0308210500023180.pdf), DOI [10.1017/S0308210500023180](https://doi.org/10.1017/S0308210500023180) | Established anisotropic candidate energies and numerical methods. |
| Dacorogna–Haeberly, [1998 paper](https://www.numdam.org/item/M2AN_1998__32_2_153_0.pdf), Example 3 | The eigenvalue criteria used for the degree-one energies in E03; exact parameter checks are saved with the experiments. |
| Aubert, [1988 paper](https://www.numdam.org/item/M2AN_1988__22_1_5_0.pdf), §3 | Comparison against an earlier nonpolyconvex example. The construction there is different from the displayed `Pβ`; this comparison is not a general novelty proof. |
| Bandeira–Pedregal, [2009 paper](https://www.numdam.org/item/10.1016/j.anihpc.2008.08.002.pdf), §3 | The homogeneous-quartic Hessian/generalized-eigenvalue method is prior work. Its displayed examples do not give the exact `Pβ` expression or the `β=2` threshold; broader equivalence/priority remains open. |
| Marcellini, [*Quasiconvex quadratic forms in two dimensions* (1984)](https://people.dimai.unifi.it/marcellini/lavori/reprints/1984_Marcellini_Appl_Math_Optim_Quasiconvex_quadratic_forms_in_two_dimensions.pdf) | Background for quadratic positivity, null-Lagrangian correction and polyconvexity in the planar setting. The larger bivector pullback argument uses the Finsler–Thorpe input pinned below; its scope is rechecked in A06. |
| Bruno–Pasqualotto, [arXiv:2608.06367v1](https://arxiv.org/abs/2608.06367v1) | Quasiconvexity for the Dacorogna–Marcellini energy and the bivariantly rotationally invariant homogeneous quartic class. Used as an **external analytic input** in H16/H18; does not settle arbitrary anisotropic quartics. |
| Cassese, [arXiv:2608.03488v3](https://arxiv.org/abs/2608.03488v3), 16 September 2026 | Explicit homogeneous quartic counterexample in `2 × 3` and broader higher-dimensional results. E04 tests planar pullbacks; the source result is not a `2 × 2` counterexample. Main now includes the unconditional quartic construction and other results with explicitly distinguished hypotheses; see [FORMAL_STATUS.md](FORMAL_STATUS.md). This audit did not rebuild Lean locally. |
| Agazzi–Bruno–Guerra–Pasqualotto, [arXiv:2608.12298](https://arxiv.org/abs/2608.12298) | Higher-dimensional `2 × 4` construction and Grabovsky-derived methods that motivated the pullback investigations. The no-go argument H25 concerns a specified quadratic-bivector-norm planar class, not this entire paper. |
| Guerra–Kristensen, [arXiv:2112.10563](https://arxiv.org/abs/2112.10563), *Automatic quasiconvexity of homogeneous isotropic rank-one convex integrands* (2022) | Theorem 1.2 makes the Morrey implication true at conformal 2 × 2 bases for every nonnegative isotropic rank-one-convex p-homogeneous integrand; the 1<p<2 part was conditional on Burkholder quasiconvexity. The 2026 Iwaniec preprint discharges that condition. Theorem 4.2 further yields an [explicit all-matrix quasiconvex minorant](IWANIEC_MORREY.md#4a-conformal-morrey-for-every-nonnegative-isotropic-homogeneous-integrand). |
| 22 Nov 2026 derived Morrey consequence | [Proposed universal isotropic support-cone proof](IWANIEC_MORREY_UNIVERSAL.md): extending the Guerra–Kristensen/Iwaniec conformal result to every matrix for nonnegative isotropic p-homogeneous rank-one-convex F, 1<p<2. Includes endpoint-slope lemma, exact Burkholder cone supports, a p=2 polyconvex argument, and a p>2 obstruction. **Pending independent review and formal verification; no originality claim.** |
| 22 Nov 2026 hybrid Morrey research | [General support hierarchy](IWANIEC_MORREY_GENERAL.md) uses the 2026 Burkholder global QC claim to produce a canonical QC minorant for every nonnegative isotropic p-homogeneous 2×2 integrand, p>2, plus explicit exact simple-test obstruction and the remaining universal completeness gate. **Hand proof only, not Lean or peer reviewed.** |
| Agazzi et al., [arXiv:2609.28311v2](https://arxiv.org/abs/2609.28311v2), 8 October 2026 | Claims quasiconvexity of a special clipped-determinant integrand L (Theorem 1), of all Burkholder B_p (Corollary 2), and the sharp Beurling–Ahlfors norm. Neither result settles universal 2 × 2 Morrey. The [dedicated connection audit](IWANIEC_MORREY.md) derives the exact nonnegative-defect decomposition, conditional general convex-body calibration and formalization gates. The projection contact lemma and norm bridge were not independently reverified in this research commit. |
| Conti–Dolzmann–Dondl, [arXiv:2610.31886](https://arxiv.org/abs/2610.31886) | Frame-indifferent `3 × 3` example and related [Lean repository](https://github.com/sergioconti/so3-r1c-and-not-qc). Its mention of Pedregal as a proposed proof is not validation of the disputed argument. |
| Powers, [*Rational Certificates of Positivity on Compact Semialgebraic Sets*](https://www.math.emory.edu/~vicki/pub/rationalreps.pdf), author manuscript, Theorem 6 | Rational Putinar input for A03. The sphere constraints include an explicit redundant ball generator. Homogenization and gap-preserving strictification are proved in [GLOBAL_CERTIFICATES.md](GLOBAL_CERTIFICATES.md). This is an application of established positivity, not a novelty claim. |
| Magron, [*Convergence rates for polynomial optimization on set products*, arXiv:2505.18580v4](https://arxiv.org/abs/2505.18580v4), 3 June 2026 | Prior work on SOS hierarchies on products of spheres. Its rates are not needed for A03 and do not bound the unknown Morrey witness degree or mesh. |
| Bettiol–Krishnan, [*Ricci flow does not preserve positive sectional curvature in dimension four*](https://link.springer.com/article/10.1007/s00526-022-02335-z), Calc. Var. 62, 13 (2023), §2.2, Proposition 2.2 | Precise non-strict Finsler–Thorpe statement used in H25. The [structural audit](STRUCTURAL_AUDIT.md) explains the Bianchi-component bridge from an arbitrary quadratic form on bivectors. |
| [lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point) | Source dependency behind the repository's Kakutani formalization. It does not fix the failed nonemptiness hypothesis. |

The versioned abstracts for Bruno–Pasqualotto, Cassese, Guerra–Teixeira da Costa and Agazzi et al.
were rechecked during this consolidation. Other entries preserve the primary-source comparisons
recorded in the existing reports and recovered research. The completion audit additionally checked the Powers, Magron and Bettiol–Krishnan primary
sources above. This is not a new systematic literature review of every lemma.

## What the prior-work search establishes

The original Pedregal audit records searches of arXiv, cited papers, responses to the proposed
proof and GitHub formalizations. The subsequent research compared established candidate families,
homogeneous-quartic methods, the new higher-dimensional constructions and selected exact formulas.
See the [Pedregal literature report](../Pedregal/REPORT.md), the
[Pβ comparison](../../research/experiments/2026-11-21/work_pb/README.md), and the
[DH comparison](../../research/experiments/2026-11-21/work_lit/README.md).

These searches did not establish priority. In particular:

- Cubic rigidity, quadratic quasiconvexity, finite-dimensional separation and Carathéodory
  bounds are established tools or straightforward consequences; no novelty is claimed.
- An exact coefficient formula not found in the papers inspected may occur under a linear
  change of variables, a different normalization or an older theorem. The `Pβ` threshold,
  flat-line support and quartic cone observations require theorem-specific review.
- H16/H18 depend on an external analytic theorem. Exact polynomial identities and rational
  stability constants do not independently verify that theorem.
- H22 uses Hilbert's ternary-quartic theorem; H25 uses a Finsler–Thorpe/equality-S-lemma result.
  A06 pins the latter reference and its hypotheses. Hilbert's theorem and all external inputs still need precise citations in any publication or Lean translation.
- The original report's “no earlier formalization found” is a dated search result, not a claim
  that no such work exists. This research ledger does not repeat it as a novelty guarantee.

## Publication gate

Before treating an entry as a publishable new theorem, freeze its statement and parameter range,
search its mathematical invariants as well as its displayed formula, compare the closest primary
results, and obtain independent mathematical review. Record exact versions and the final scope of
the claim.
