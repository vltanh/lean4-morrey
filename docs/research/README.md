# Planar Morrey research

**Open:** unrestricted finite-valued planar rank-one convexity implies quasiconvexity. No certified planar counterexample or complete unrestricted proof is recorded. The sole positive target is [beta_* = 0](ROADMAP.md#target).

The signed positively homogeneous bi-isotropic theorem for every p>0, and the stated nonnegative p≥2 polyconvexity theorem, are already Lean-verified on main. They are not active research gates. See [formal status](FORMAL_STATUS.md) for exact hypotheses and CI evidence.

## Start here

| Document | Purpose |
| --- | --- |
| [ROADMAP](ROADMAP.md) | The exact unrestricted target, current obstruction, acceptable completion mechanisms and stop rules. |
| [LEDGER](LEDGER.md) | Authoritative positive, negative, conditional and experimental results; stable P/R/N/E identifiers. |
| [FORMAL_STATUS](FORMAL_STATUS.md) | Verified baseline, archived unverified modules and limits of the certification. |
| [CATALOG](CATALOG.md) | Topic-indexed detailed arguments before and after the November 24 reset. |
| [GLOBAL_CERTIFICATES](GLOBAL_CERTIFICATES.md) | Complete strict-negative certificate hierarchy; no uniform exact decision cutoff. |
| [REPRODUCING](REPRODUCING.md) | Saved evidence, exact checkers and reproduction instructions. |
| [SOURCES](SOURCES.md) | Literature references and source scope. |
| [Archive](archive/README.md) | Pinned historical snapshots, deduplication policy and preserved evidence. |

## Problem and reliable starting facts

For every finite-valued rank-one convex (RC) F on real 2×2 matrices, arbitrary base A and every periodic Lipschitz two-component map u, prove

    J_F(A,u) = integral [F(A+Du) - F(A)] >= 0.

A strict negative value with a globally RC F and an actual compatible gradient disproves the conjecture. Translation absorbs A, but need not preserve homogeneity. Finite RC implies local Lipschitz regularity; smooth approximation and periodic/affine-boundary bridges allow bounded test ranges for strict counterexamples. Rank-one convex quadratics are QC, and affine functions and the determinant are null Lagrangians.

Gradient laws obey the mean and determinant identities, but those identities alone do not establish gradient realizability or laminate status. Conditioning, Carathéodory reduction and abstract moment constraints need independent compatibility justification. Polyconvexity (PC) is not a necessary premise for this program. Pedregal's false universal nonemptiness premise refutes the proposed argument, not the conjecture.

## Status at consolidation (25 November 2026)

- R15/R16 record hand reductions to explicit finite positive-accuracy tests for unrestricted integrands and compatible gradients. The computed bounds are theoretical; the exact-zero gate is open.
- P15/P16 record the strongest current hand bound, −1/8 < beta_* ≤ 0, with a conservative explicit strictness gain. Neither the bound nor the global reduction is newly Lean-verified.
- N20–N24 reject specific heat-jet, fixed-degree, finite-moment, Legendre and quadratic Hamiltonian contraction mechanisms. P17 is a useful quantitative rigidity result, not unrestricted QC-to-PC or a zero certificate.
- All existing detailed mathematical notes, exact checker sources, certificate inputs and distinct numerical evidence are retained. Historical agendas and the pre-squash history remain available through the archive. The ledger, not the older notes, determines the current evidence level.

RC = rank-one convexity; QC = quasiconvexity; PC = polyconvexity. A negative result about PC or a particular proof method is not a planar non-QC witness. No new mathematical result is claimed by this consolidation.
