# Formal status — 24 November 2026

## Verified baseline

Current main inspected: [a7a9a58](https://github.com/vltanh/lean4-morrey/tree/a7a9a583ad05f36ca7b6db2ac22f9f4434e4ee6f). The [Lean Action CI run 45495704012](https://github.com/vltanh/lean4-morrey/actions/runs/45495704012) completed successfully at this exact SHA. Its job 138805486135 reports successful build, exhaustive audit-import coverage, axiom/dependency audit, all three paper-route checks, Challenge definition synchronization, code-link check and Markdown table check. The four Palomar preflight workflows at main e0ccdbf939ce39584db1f1bfd41b65ebe092e4d4 also report success; this is prior-commit preflight evidence, not a new registry review.

| Result | Formal source | Scope |
| --- | --- | --- |
| Signed homogeneous isotropic QC, every p>0 | [Signed/Main.lean](../../Morrey/HomogeneousIsotropic/Signed/Main.lean) and [Challenge solution](../../palomar/HomogeneousIsotropic/Solution.lean) | All bases, finite real-valued F, positive homogeneity and both proper rotation groups. |
| Nonnegative homogeneous isotropic PC, p≥2 | [Main.lean](../../Morrey/HomogeneousIsotropic/Main.lean) | The sign condition is essential for p>2. |
| Signed isotropic degree two PC; degree one convex | [Main.lean](../../Morrey/HomogeneousIsotropic/Main.lean) | Isotropy retained. |
| 0<p<1 implies zero | [Main.lean](../../Morrey/HomogeneousIsotropic/Main.lean) | No isotropy. |
| Truncated determinant, radial/Burkholder kernels | [Signed/Radial.lean](../../Morrey/HomogeneousIsotropic/Signed/Radial.lean), [BurkholderRadial.lean](../../Morrey/HomogeneousIsotropic/Signed/BurkholderRadial.lean) | External L proof in lean4-iwaniec; no universal-generation claim. |
| Pedregal false nonemptiness and conditional reduction; level-one theorem | [Counterexample](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean), [Reduction](../../Morrey/Pedregal/Reduction.lean), [LevelOne](../../Morrey/Pedregal/LevelOne.lean) | Refutes the proposed proof, not Morrey. The endpoints in [Introduction](../../Morrey/Pedregal/Introduction.lean) are proposition definitions. |
| Šverák and Cassese nonplanar counterexamples | [Šverák report](../Sverak/REPORT.md), [Cassese report](../Cassese/REPORT.md) | Current main formalizes the nonplanar landscape including 3×2 and 2×3; no automatic planar restriction or transpose. |
| Reusable analytic infrastructure | [Rindler re-exports](../../Morrey/Common/External/Rindler/Lemmas.lean), pinned [dependency manifest](../../lake-manifest.json) | Use existing definitions, Lipschitz regularity and domain/periodic bridges; recheck exact statement when instantiating. |

Main pins lean4-iwaniec to [e4922fa6bfdadbe5fe22231c91b69044dac89bab](https://github.com/vltanh/lean4-iwaniec/tree/e4922fa6bfdadbe5fe22231c91b69044dac89bab) and mathlib to 9d581dfff2e41de989072ea63abf3daf69311520 (v4.36.0-rc2), as checked in [lake-manifest](../../lake-manifest.json). The complete homogeneous theorem is no longer a hand-proof candidate. The paper [overview](../HomogeneousIsotropic/README.md) lists its exact symbols and hypotheses; use those instead of the old research summaries.

## PR-only bridge modules — archived, not certified

The old PR is based on 764256f7910b00551419fe71c35809e6b52d7ddd. Its completed [CI run 45497494928](https://github.com/vltanh/lean4-morrey/actions/runs/45497494928/job/138811746229) failed in LegendreHadamard.lean at line 62:4: the simplified one-dimensional iterated derivative did not match the expected iterated Fréchet derivative. All later audit steps were skipped. Earlier runs also failed; successful older runs predate the added modules. The old head's newer CI was in progress at audit time.

To reset without modifying any verified proof, the four PR-only modules (LegendreHadamard, Pedregal.Bridges, CounterexampleCertificate, Jensen) are archived byte-for-byte under [unverified Lean sources](../../research/archive/reset-2026-11-24/unverified-lean/README.md), not placed in the active Lean library. The updated branch uses the current main's Lean sources, dependencies, CI and audit script unchanged. Port the archived interfaces only when needed for a final proof and verify them with CI. Do not count their statements as verified.

No local Lean build or new kernel audit was executed in this research reset. The cited green run belongs to pinned main, not the combined reset commit. Check the latter's CI independently before claiming the whole PR passes. No post-main hand theorem is promoted to Lean verified by this reorganization.

## Post-reset CI follow-up

The [reset-tree CI run 45500655053](https://github.com/vltanh/lean4-morrey/actions/runs/45500655053) at 8ef4d2f completed with the Lean build, exhaustive audit-import coverage, axiom/dependency audit, all three route checks, and all Challenge definition checks successful. It failed only at the documentation link check (`docs/HomogeneousIsotropic/CREDITS.md`); the Markdown-table step was skipped. The new research files made four previously plain-code note paths resolvable, so the current branch linkifies those four spans without changing the credits' prose or any formal proof. Fresh complete CI is still needed to confirm that the repaired documentation passes. The post-reset parametric and flat-contact notes are hand proofs, not new Lean theorems.

## Reset CI completed

Both [run 45507443979](https://github.com/vltanh/lean4-morrey/actions/runs/45507443979) and [run 45507435211](https://github.com/vltanh/lean4-morrey/actions/runs/45507435211) completed successfully at exact commit e3981e34d5dafa04948cf4736cc6a881a3309cfa after the credits-link repair. The subsequent signed-trace proof and exact controls are research-only, not newly Lean-certified. The formal baseline is unchanged.
