# Historical research archive

These 53 files preserve the earlier research payloads byte-for-byte. Start with the current
[ledger](../../docs/research/LEDGER.md), not an archived conclusion. Old notes may contain stale
paths, superseded targets, different gap signs and preliminary claims. Their inclusion does not
make them Lean proofs or verified new literature.

The [source manifest](../source_manifest.json) maps every standalone file and ZIP member from
the 36 recovered source artifacts to its repository path and SHA256. Identical payloads have one
copy. ZIP containers are identified by checksums; their members are retained as readable files.
The latest 86-file search package is separate under [experiments](../experiments/2026-11-21).

## Reading guide

| Topic | Original note | Current ledger entries |
| --- | --- | --- |
| Universal level-one mold and reversal of B/B₁ | [Level-one mold](files/morrey_l1_mold_counterexample.md) | H01, H29 |
| Uniform-weight and single-use tree obstructions | [Level-two repair status](files/morrey_level2_repair_status.md), [all-level checker](files/morrey_all_levels_uniform_obstruction.py) | H02–H05 |
| Rational polynomial and dyadic reduction | [Polynomial reduction](files/morrey_polynomial_reduction.md) | H07–H09 |
| Splitting-cone reformulation and heat flow | [Global reorientation](files/morrey_global_reorientation.md) | H10, H12, H24 |
| Finite-degree Hessian duality and moment witnesses | [Global certificate note](files/morrey_global_certificate_research.md) | H11–H12, H15, H26 |
| One exact 32-atom quartic certificate | [Certificate note](files/morrey_quartic_l2_readme.md), [data](files/morrey_quartic_l2_dual_certificate.json) | H13–H14 |
| Quartic orbit and harmonic decomposition | [Orbit note](files/morrey_global_quartic_orbit_note.md) | H16–H17 |
| Quantitative quasiconvex coefficient neighborhood | [Open neighborhood](files/morrey_global_quartic_open_ball.md) | H18 |
| Flat rank-one lines | [Support note](files/morrey_flat_rankone_support.md) | H19 |
| Rank-one-null rigidity and singular bases | [Rigidity](files/morrey_rankone_null_rigidity.md), [singular support](files/morrey_singular_base_support.md) | H20–H21 |
| Rank-one-zero quartic SOS | [SOS note](files/morrey_rankone_zero_sos.md) | H22 |
| Failure of the proposed quartic generator cone | [Cone obstruction](files/morrey_quartic_cone_no_go.md) | H23 |
| Planar pullbacks and rejected curvature-sampled candidates | [Counterexample reorientation](files/morrey_counterexample_reorientation.md) | H25, H27–H28 |

The original bundle index [README_morrey_bundle.md](files/README_morrey_bundle.md) is retained as
historical context. The current overview and roadmap supersede its next-step checklist.

## Reproduction cautions

Some historical scripts expect sibling data, optional solvers or scratch candidate files that
were not retained. Some write output files beside their inputs. Use a temporary working copy.
The supported verification commands and their recorded results are in the
[reproduction guide](../../docs/research/REPRODUCING.md). Exploratory scripts remain available for
inspection; their presence is not a promise that every original search can be replayed without
reconstructing missing intermediate state.

Do not automatically run files whose names contain `probe`, `search`, `exchange`, or
`exact_roconvex` as a quick verification suite. They may launch optimization or costly adaptive
subdivision. Positive sampled curvature values are not global rank-one-convexity certificates.

Do not edit archived payloads to correct their conclusions. Record a correction in the ledger
and add a new versioned result with its own evidence. This keeps the provenance check meaningful.
