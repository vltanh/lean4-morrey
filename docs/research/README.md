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

**Post-reset research:** [unrestricted compactification](IWANIEC_MORREY_PARAMETRIC_COMPACTIFICATION.md) gives a fixed compact integrand domain, exact finite-accuracy polynomial test families and a positive-stress criterion covering arbitrary matrix energies. The [Signed trace and folding-safe extension](IWANIEC_MORREY_SIGNED_TRACE_FOLD_TRANSFER.md) handles folded charts for the canonical bounded-deficit extension, proves commuting envelopes and reduces the unrestricted problem to one fixed compact normalized class. It closes both flat-region benchmarks E and E2. These are hand proofs/reductions, not Lean certification or unrestricted closure.

**Law-side continuation:** [Integer fillings and BV trace](IWANIEC_MORREY_INTEGER_FILLINGS.md) retains the BV singular derivative at vertical faces, establishes equivalence with degree-one integer fillings, and provides an exact integer-chain certificate plus a finite MILP discovery driver. Relaxing multiplicity is invalid (explicit 1/10 benchmark gap). The unrestricted lower bound remains open.

**Degree-free continuation:** [Positive fillings and degree-free finite optimization](IWANIEC_MORREY_DEGREE_FREE_FINITE_FILLINGS.md) turns positive integer fillings into binary graph selections and proves an explicit finite rational optimization over all normalized RC integrands at any prescribed positive accuracy for fixed geometry. Exact finite controls passed; the universal geometry cutoff remains open.

**Uniform finite-accuracy breakthrough (hand reduction):** [Uniform geometric cutoff](IWANIEC_MORREY_UNIFORM_GEOMETRY_CUTOFF.md) now bounds both the integrand and geometric complexity at each prescribed positive accuracy, with an explicit finite certificate alternative for the unrestricted normalized problem. The bound is far too large for direct enumeration and no accuracy-independent cutoff is proved. Exact zero remains open.

**Exact-zero continuation:** [Global C¹,¹ relative localization](IWANIEC_MORREY_C11_OPTIMAL_MARGIN.md) proves a uniform all-amplitude relative mesh theorem and a computable universal optimal relative margin in a fixed C¹,¹ normalization. A finite condition-number alternative can certify exact strong QC or a genuine softened-energy counterexample. Zero of the universal margin is still open; the explicit finite bounds remain theoretical.

**Exact cofactor symmetry:** [Cofactor shear duality and universal margin bound](IWANIEC_MORREY_COFACTOR_DUALITY.md) preserves RC/QC and their finite envelopes and exposes a critical-state rigidity target with compatible gradients and cofactor stresses. The universal margin is bounded below by −99/200, not yet zero. These are hand proofs, not a new Lean theorem or a complete Morrey proof.

**Higher-dimensional transfer route:** [Joint 4×2 Hamiltonian flow](IWANIEC_MORREY_JOINT_HAMILTONIAN_FLOW.md) gives a short-time RC-preserving evolution with a 4×2 Hamiltonian, QC preservation, and an exact finite jet test for transferring a negative higher-dimensional gap on a gradient-stress graph into a planar counterexample. No qualifying negative joint field or exact-zero proof has been found.

**Full stationary lift:** [Full stationary lift and local repair](IWANIEC_MORREY_FULL_STATIONARY_LIFT.md) adds the inner-variation energy-momentum block and an explicit local quadratic curvature repair for higher-dimensional RC tests. Direct embedding tests on the known negative mechanisms clarify the surviving nonlinear transfer gate. No negative planar witness or exact-zero proof.

**Current critical-state gate:** [Quadratic-tail critical states and exact clipping](IWANIEC_MORREY_QUADRATIC_TAIL_CRITICAL.md) uses the pinned scalar projection theorem to obtain bounded-base, bounded-amplitude near-equality gradients for one fixed smooth critical H and bounded actual six-row lifts, with all errors relative to variance. Relative second variation adds an energy-based stability constraint. High-amplitude concentration is removed; exact rigidity and Morrey remain open.

**Maximum-defect continuation:** [Maximum-defect contact laws and inner-stress shear](IWANIEC_MORREY_INNER_STRESS_SHEAR.md) produces exact support-separated compact shifted six-row laws and an exact local domain-coordinate amplification D↦D/(1−tD). This bypasses absolute-variance dilution in the new setup. The regular chart and normalization cannot yet be continued to a fixed fraction of the pole, and the unrestricted problem remains open.

**Combined shear continuation:** [Combined shear continuation](IWANIEC_MORREY_COMBINED_SHEAR_CONTINUATION.md) proves determinant-weighted projective transfer of a compact stacked gradient Young measure when its projection block is uniformly positive on the support, even for folded generating maps. An exact combined-shear Hessian pencil and degree certificate separate matrix chart regularity from spatial folding. No uniform amplification or exact-zero theorem yet.

The earlier detailed notes remain at their original paths for link stability, but are **historical references**, not active roadmap items. The long previous README, ledger, roadmap and formal-status summary are available byte-for-byte in the [pre-reset snapshot](https://github.com/vltanh/lean4-morrey/tree/d198628ecccb10fb1f2ded5ecd99f37e55c55e16/docs/research). The research/checker/experiment files have not been erased or silently reinterpreted as proofs.

Current conventions: RC = rank-one convexity, QC = quasiconvexity, PC = polyconvexity. A negative result for PC or for a proof method does not imply non-QC. The Jensen gap is average F(A+Dphi) minus F(A). Strictly negative is the counterexample direction. A finite-order laminate, a laminate (all RC Jensen tests), a correct-minors abstract law, and an actual gradient law are different notions.
