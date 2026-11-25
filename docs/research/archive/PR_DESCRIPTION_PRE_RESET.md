# Original PR #1 description before the 24 November research reset

Historical metadata, not current status. Consult [current research README](../README.md) and [formal status](../FORMAL_STATUS.md).

---

## 23 Nov 2026 update — signed homogeneous isotropic theorem (candidate hand proof)

**Verified baseline:** the [homogeneous-isotropic branch at f70d7e9](https://github.com/vltanh/lean4-morrey/tree/f70d7e9253ecf59ea6c862893d1fdd3fb60cffa9) formalizes the nonnegative theorem for all p>0, signed p=2, p=1, and 0<p<1. Its [Lean CI including axiom audit](https://github.com/vltanh/lean4-morrey/actions/runs/45323677832) passed. Its pinned lean4-iwaniec dependency proves the quasiconvexity of L and Burkholder.

**New:** [characteristic integration of truncated determinants](https://github.com/vltanh/lean4-morrey/blob/b0cc8f705384f8750e78877e26ca788ba208b453/docs/research/IWANIEC_MORREY_SIGNED_CHARACTERISTICS.md) gives a candidate complete hand proof that **every finite-valued signed isotropic positively p-homogeneous rank-one convex planar integrand is quasiconvex for every p>0**. Evolve a supporting slope of the profile with a scalar ODE; monotonicity of restricted supporting planes makes the scale-integration weight nonnegative, giving a global touching quasiconvex minorant. Fourteen exact symbolic identities and two exact kink controls passed. The new signed argument still needs independent review and Lean formalization.

**Unrestricted planar Morrey remains open.** Removing homogeneity and isotropy cannot be done by demanding polyconvexity; the earlier [nonhomogeneity](https://github.com/vltanh/lean4-morrey/blob/research/ledger-roadmap-2026-11-21/docs/research/IWANIEC_MORREY_NONHOMOG_PC_NOGO.md) and [anisotropy](https://github.com/vltanh/lean4-morrey/blob/research/ledger-roadmap-2026-11-21/docs/research/IWANIEC_MORREY_P2_SIGNED.md) counterexamples remain valid. See the [current roadmap](https://github.com/vltanh/lean4-morrey/blob/research/ledger-roadmap-2026-11-21/docs/research/ROADMAP.md).

---

## Why

The follow-up research was spread across notes, certificates, scripts and numerical bundles. Some early conjectures were later refuted, and upstream has now incorporated Cassese's formalization. This PR preserves the research record, gives each claim an evidence level, and identifies the remaining global completion gates.

**The unrestricted 2 × 2 Morrey problem remains unresolved here. No planar counterexample or completed proof is claimed.**

## Start reviewing here

- [Completion audit](https://github.com/vltanh/lean4-morrey/blob/785f33455a974e47f6fc7197795a15070a1fac43/docs/research/COMPLETION_AUDIT.md): findings ranked by their effect on the next step.
- [Research ledger](https://github.com/vltanh/lean4-morrey/blob/785f33455a974e47f6fc7197795a15070a1fac43/docs/research/LEDGER.md) and [roadmap](https://github.com/vltanh/lean4-morrey/blob/785f33455a974e47f6fc7197795a15070a1fac43/docs/research/ROADMAP.md).
- [Global certificate proofs](https://github.com/vltanh/lean4-morrey/blob/785f33455a974e47f6fc7197795a15070a1fac43/docs/research/GLOBAL_CERTIFICATES.md): norm-multiplier completeness, explicit local-to-global stabilization, and the corrected positive compactness argument.
- [Pipeline audit](https://github.com/vltanh/lean4-morrey/blob/785f33455a974e47f6fc7197795a15070a1fac43/docs/research/PIPELINE_AUDIT.md) and [exact checkers](https://github.com/vltanh/lean4-morrey/blob/785f33455a974e47f6fc7197795a15070a1fac43/research/audit/README.md).
- [Formal status](https://github.com/vltanh/lean4-morrey/blob/785f33455a974e47f6fc7197795a15070a1fac43/docs/research/FORMAL_STATUS.md): current main, including unconditional and conditional Cassese results and reusable Lipschitz/domain bridges.
- [Structural audit](https://github.com/vltanh/lean4-morrey/blob/785f33455a974e47f6fc7197795a15070a1fac43/docs/research/STRUCTURAL_AUDIT.md), [experiments](https://github.com/vltanh/lean4-morrey/blob/785f33455a974e47f6fc7197795a15070a1fac43/docs/research/EXPERIMENTS.md), [reproduction](https://github.com/vltanh/lean4-morrey/blob/785f33455a974e47f6fc7197795a15070a1fac43/docs/research/REPRODUCING.md), and [sources](https://github.com/vltanh/lean4-morrey/blob/785f33455a974e47f6fc7197795a15070a1fac43/docs/research/SOURCES.md).

## New audit findings

- Three archived base minimizers use eigenvalue cutoffs without a complete range/kernel check. New exact quadratic controls demonstrate an omitted minimum of −99 and an unbounded direction. These are regression controls; no saved missed planar counterexample is asserted.
- An exact ten-square identity puts the sharp P₂ endpoint inside direct LH-SOS. Its flat directions exclude a strictly positive Gram in the existing full basis. The separate Pβ searches included β=2; the diagnosis concerns the general fixed-margin SOS search.
- A hand proof using rational Putinar certificates shows that norm multipliers give a complete certificate hierarchy for some negative witness after a gap-preserving strict perturbation. No degree, mesh, order or runtime bound follows.
- Exact positive Hessian quadratures at every degree automatically admit a common compactly supported limit by radial-moment bounds. This corrects H12; universal feasibility remains unproved.
- Added exact rational verifiers for two global LH certificate formats and actual periodic PL witnesses, plus exact base diagnostics and P₂ algebra checks. Weighted-Gram discovery, rational extraction and optimizer integration remain to implement.
- Rechecked H19–H25 within their stated hypotheses and reduced the full Pβ family to an explicit all-field endpoint inequality, which remains open.

## Preserved research

All 36 recovered source artifacts remain as 139 byte-identical deduplicated payloads: 53 historical files and the 86-file latest search package. The ledger retains failed routes, superseded B/B₁ conjectures, invalid candidates, the missing older discovery input and the exact **3 × 2** control. Python checks and hand arguments are not presented as Lean theorems or independent human review.

The branch integrates upstream `cde348ba320b65d902c9f0f782f392e932ba507c`. The follow-up formalization audit integrates main `764256f7910b00551419fe71c35809e6b52d7ddd` and adds universal Jensen and planar-definition bridge modules. Existing theorem statements, proof bodies and CI workflows are preserved. The added modules are awaiting this branch's Lean CI.

## Validation

- All 139 original payload hashes match.
- Six new exact verification commands passed; both valid LH formats and six corrupted-certificate rejection cases were exercised. Regenerated outputs match saved bytes. Logs: `research/verification/completion_audit/`.
- The earlier consolidation's 18 checks remain recorded separately: 14 exact and four floating/high-precision checks. They were not all rerun in this audit.
- Curated Markdown tables: zero broken rows. All 225 checked relative link targets exist. New Python syntax and curated whitespace checks pass.
- Published tree checked against all 335 expected file hashes/modes; all 140 non-README upstream files match the pinned main.
- Upstream's pinned Lean CI passed. No local Lean build, axiom/route audit, Comparator run or new optimization campaign is claimed.

Research cutoff: 21 November 2026. Formalization audit in progress: 22 November 2026. The archive preserves historical evidence; the ledger gives its current interpretation.
