# Planar Morrey research — clean reset (24 November 2026)

**Unrestricted finite-valued 2 × 2 Morrey remains OPEN.** No certified planar counterexample is in this repository. The formalized signed homogeneous bi-isotropic theorem on main is complete, for every positive exponent. Do not confuse that theorem with removing either continuous symmetry or homogeneity.

This reset separates the formal baseline, positive results, disproved methods, unproved reductions and experiments. It intentionally does not appoint another special-class program as the main problem.

| Start here | Purpose |
| --- | --- |
| [HANDOFF](HANDOFF.md) | Fresh-eye statement of the problem, allowed tools and success conditions. Read first. |
| [LEDGER](LEDGER.md) | Current positive / negative / open / experimental results, deduplicated by mathematical outcome. |
| [FORMAL_STATUS](FORMAL_STATUS.md) | Pinned verified main, CI, exact scopes and unverified archived modules. |
| [ROADMAP](ROADMAP.md) | New unrestricted agenda, gates, falsification and stop rules. |
| [RESET_AUDIT](RESET_AUDIT.md) | Audit findings, limitations, corrections, and archival policy. |
| [CATALOG](CATALOG.md) | Complete index of the 102 pre-reset notes by topic, evidence and disposition. |
| [Archive](archive/README.md) | Immutable pre-reset snapshot and original computational materials. |

**Post-reset research:** [unrestricted compactification](IWANIEC_MORREY_PARAMETRIC_COMPACTIFICATION.md) gives a fixed compact integrand domain, exact finite-accuracy polynomial test families and a positive-stress criterion covering arbitrary matrix energies. The [flat-region resolution](IWANIEC_MORREY_FLAT_CONTACT_RESOLUTION.md) closes the E2 benchmark and identifies the inverse-chart folding issue for E. Both are hand proofs/reductions, not Lean certification or unrestricted closure.

The earlier detailed notes remain at their original paths for link stability, but are **historical references**, not active roadmap items. The long previous README, ledger, roadmap and formal-status summary are available byte-for-byte in the [pre-reset snapshot](https://github.com/vltanh/lean4-morrey/tree/d198628ecccb10fb1f2ded5ecd99f37e55c55e16/docs/research). The research/checker/experiment files have not been erased or silently reinterpreted as proofs.

Current conventions: RC = rank-one convexity, QC = quasiconvexity, PC = polyconvexity. A negative result for PC or for a proof method does not imply non-QC. The Jensen gap is average F(A+Dphi) minus F(A). Strictly negative is the counterexample direction. A finite-order laminate, a laminate (all RC Jensen tests), a correct-minors abstract law, and an actual gradient law are different notions.
