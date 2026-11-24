# Fresh-eye handoff — the actual mathematical problem

**Read this before browsing the old research.** No previous proposed completion strategy is assumed to work. The goal is unrestricted planar Morrey, not another class of integrands.

## Target

For every finite-valued rank-one convex F on R^(2×2), every base A and every periodic Lipschitz two-component map phi on the unit two-torus, prove

    J(F,A,phi) = integral F(A+Dphi) - F(A) >= 0,

or exhibit one globally RC F and one actual compatible map giving a rigorously strict negative gap. Translation of F absorbs A, but do not accidentally retain homogeneity after translating. Finite RC implies local Lipschitz continuity. Smooth approximation and the periodic/affine-boundary bridges allow working on bounded test ranges without losing a strict violation.

## Safe starting facts

1. Rank-one convex quadratic forms are quasiconvex (indeed PC); affine functions and the determinant are null Lagrangians. A smooth integrand is RC iff its Hessian is nonnegative on all rank-one directions.
2. The repository's current main proves the signed positively homogeneous SO(2)×SO(2)-invariant theorem at every base for every p>0, including PC in the stated nonnegative p≥2 range. The pinned lean4-iwaniec supplies the QC truncated determinant L; see [formal status](FORMAL_STATUS.md).
3. Pedregal's original universal nonemptiness premise is formally false; the unrestricted theorem is not proved or refuted by that audit.
4. A gradient law has the mean matrix and determinant moments, but these moments alone do not imply laminate status or gradient realizability.
5. A valid counterexample may be sought among smooth positive strongly RC integrands; rational polynomial approximation with a global tail and a rational periodic piecewise-affine witness gives a complete strict-negative certificate hierarchy. Completeness is not a finite cutoff.

## Guardrails

Do not assume PC for arbitrary RC functions: it is already false outside the proved isotropic homogeneous scope. Do not infer QC from sublevel hulls, numerical non-detection, nonnegative sampled LH tests, or failed constructions of a particular laminate tree. Do not treat a conditional law obtained by conditioning a gradient as another gradient law. Several attractive relaxations and decompositions fail for exactly that reason.

The only success is a global theorem (all compatible gradients/all integrands) or a certified genuine negative pair. A reduction to a *finite number of configurations* must actually prove a uniform finite cutoff or a terminating induction with strict progress; an unbounded hierarchy or a bounded number of continuous parameters is not that. A new equivalent variational formulation is useful infrastructure, but not a solved gate.

## Working method

First develop one genuinely new unrestricted mechanism from the problem and safe facts, and state exactly the universal claim it would need. Then cross-check [negative ledger](LEDGER.md#negative-results-and-invalid-inferences) and [catalog](CATALOG.md) to avoid rediscovery. Do not run extensive numerical campaigns unless the mechanism predicts a discriminating test. If no global mechanism works, use the complete certificate framework as a disciplined counterexample route. Keep the verified homogeneous result separate and intact.

See [ROADMAP](ROADMAP.md) for acceptance rules, not a commitment to the previous martingale or stress approach.
