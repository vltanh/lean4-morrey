# Reset audit — 24 November 2026

## Snapshots and scope

- Pre-reset research head: [d198628ecccb10fb1f2ded5ecd99f37e55c55e16](https://github.com/vltanh/lean4-morrey/tree/d198628ecccb10fb1f2ded5ecd99f37e55c55e16), 143 PR commits and 371 changed files reported before the reset.
- Verified current main: [a7a9a583ad05f36ca7b6db2ac22f9f4434e4ee6f](https://github.com/vltanh/lean4-morrey/tree/a7a9a583ad05f36ca7b6db2ac22f9f4434e4ee6f), successful CI at that exact revision.
- The pre-reset tree contains 510 blobs, including 102 research notes/index files and 263 research files (archive payloads, experiments, exact scripts, logs and manifests). Git tree enumeration returned no truncation. The new [catalog](CATALOG.md) classifies every pre-reset note.
- Scope of this audit: inspect current formal theorem declarations and CI/failed build logs; compare trees; review core old reductions, negative results and recent notes; consolidate remaining notes from the existing index/ledger and topic-specific records. This is not a line-by-line independent verification of all 102 hand proofs or a rerun of the 263 research files, nor a new priority/literature clearance.

## Findings ranked by impact

| Finding | Corrective action |
| --- | --- |
| The old PR summary and formal-status documents still describe the signed theorem as candidate or conditional on proof work. | Replace with the actual signed all-p theorem and the successful pinned-main CI evidence. |
| The branch is behind current main; divergent files are README and scripts/Audit.lean (relative to the previous formal baseline). | Reconcile by taking current main's formal tree and CI intact, plus all existing research files. Root README gets only a research entry link. No force push or proof-body modifications. |
| Old PR build failed at the unverified LegendreHadamard bridge, line 62:4, before axioms/routes/checks. | Archive the four PR-only bridge modules byte-for-byte outside active Lean source. Keep them for later repair; no claim they compile. |
| The roadmap treats a new proof of an already known result as a newly closed geometry. | Deduplicate the trap results: [TRAP_COMPATIBILITY](IWANIEC_MORREY_TRAP_COMPATIBILITY.md) already excludes both traps, quantitatively, and cites classical prior art. [UNRESTRICTED_CONDITIONAL_GATE](IWANIEC_MORREY_UNRESTRICTED_CONDITIONAL_GATE.md) adds an alternative L detector and contraction formulation, not a new bounded classification. |
| The proposed unrestricted split route has an explicit earlier incompatibility obstruction. | [TRAP_COMPATIBILITY §6](IWANIEC_MORREY_TRAP_COMPATIBILITY.md) constructs a real smooth gradient law and an exact rank-one minor-preserving split with a non-gradient trap branch. [DELTA_NOGO](IWANIEC_MORREY_DELTA_NOGO.md) refutes the stronger Delta-only splitting principle. Both are prominent in the negative ledger. |
| The conditional contraction criterion is necessary existentially if Morrey holds, hence equivalent, not a strict complexity reduction. | Retain it as an optional interface. Require a new uniform constructive operation with spatial compatibility to count progress. |
| Several “finite” reductions only bound support cardinality or positive-accuracy optimization. | Record the 1993 prior-art correction, exact vs positive tolerance, unresolved mesh/degree/wave/depth cutoff; no finite exhaustive unrestricted classification. |
| Earlier non-PC witnesses, cone failures, heat-flow counterexamples and invalid three-ridge proof are sometimes interleaved with positive claims. | Explicit N/X entries and no-reopen rules. None is an RC/non-QC planar witness. |
| Sampled/angular optimization has exact rejections; globally repaired control has positive gap. Latest note refers to external conversation attachment. | Preserve experiment notes and all existing arrays/checkers; full 24 Nov discovery bundle is not present in the inspected Git tree. Record missing replayability and demand saved reproducible certificates. |
| Supremal QC, convexified/exponential energy and constant-determinant results do not imply ordinary unrestricted Jensen. | Separate established restricted results from reductions; no speciality ladder is an active gate. |

## Preservation and organization

The original 102 note versions and 263 research blobs are all preserved in the immutable pre-reset commit (also reachable through this reset's history). Original detailed note paths remain on the working branch, avoiding broken citations to prior work. Only the four high-level summaries (README, LEDGER, ROADMAP, FORMAL_STATUS) are replaced by short current versions. HANDOFF, CATALOG, RESET_AUDIT and the archive guide are new. Existing detailed evidence and source files are not rewritten, with their historical statuses overridden by the new ledger when needed.

The current formal tree is synchronized to verified main. The PR-only sources that failed CI are archived with their original bytes under research/archive/reset-2026-11-24/unverified-lean. This is a scope decision, not a claim the mathematical interfaces are false. No active proof from current main is removed. The old PR head is a parent of the reset commit, so the complete pre-reset project state and old README/CI are retrievable.

## Remaining checks

Check the combined branch's CI after the reset, and repair archived bridges only when needed. There was no local Lean build, no rerun of all exact Python checks, no new numerical campaign, no independent human mathematical review and no claim of a resolution. Main's green run is not a green run for the combined branch. Use [FORMAL_STATUS](FORMAL_STATUS.md) for exact CI and source evidence.
