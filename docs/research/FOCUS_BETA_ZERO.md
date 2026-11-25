# Active research directive — prove beta_* = 0

24 November 2026. This directive supersedes earlier priorities and proposed next gates. The user explicitly requests focus on the universal relative margin itself, not another restricted theorem.

## Sole positive target

Let C consist of all globally C^{1,1}, rank-one-convex energies F on real 2x2 matrices, normalized by F(0)=DF(0)=0 and Lip DF<=1. Define

    beta_* = inf_{F in C, A, u, E(u)>0} J_F(A,u)/E(u),
    J_F(A,u) = integral [F(A+Du)-F(A)],
    E(u) = integral |Du|²,

with arbitrary periodic W^{1,2} two-component maps u and arbitrary bases A. By R16, beta_*=0 is equivalent to unrestricted finite-valued planar Morrey. The current hand-proof bound is -1/8<beta_*<=0 (P15/P16); this bound and the R16 reduction require analytic/formal verification before use in a final proof.

The objective is **beta_*=0**, without a restriction to polyconvexity, isotropy, homogeneity, a fixed amplitude, a fixed number of waves or a fixed support size. A genuine certified negative planar pair would also resolve the original question.

## Prioritize a finite exact completion mechanism

1. **Self-contraction:** prove a universal inequality beta_* >= theta beta_* for an explicit 0<=theta<1. This forces beta_*=0 because beta_*<=0. Seek a finite exact LP/SOS, interval, or real-algebraic certificate with a justified reduction from ALL actual compatible gradients and ALL normalized RC energies.
2. **Gap separation:** prove an explicit epsilon>0 such that beta_* is either zero or <=-epsilon. Then certify beta_*>-epsilon, using a sound finite computation. R16 gives a theoretical positive-accuracy reduction but no gap separation or practical exact-zero cutoff.
3. A different direct universal proof is welcome if it establishes the same exact target. Do not make either of the above sufficient strategies an extra assumption of the theorem.

In the b=-beta_*>0 contradiction setup, H=F+b|.|² is QC and strongly RC, but need not be PC. A certificate excluding arbitrarily small stabilized residual j at each fixed positive b, e.g. j>=c b^N for fixed c>0 and finite N, would settle the target. Such a certificate must hold for the actual unrestricted near-extremizers, including concentration. Merely finding a finite set of necessary constraints or a finite positive-accuracy approximation is not an exact-zero certificate.

## Stop the drift

- The polyconvex-stabilization branch (P17, Section 4) is **historical/restricted**, not the active gate. Do not try to establish PC of general H, nor impose PC reweighting inequalities on a QC energy.
- The earlier contact-law contractions, shear continuation, local collapses, and heat-jet/finite-test relaxations are references, not independent goals. Reuse them only if they furnish a rigorous step in the beta_* proof. In particular, N18–N23 document failures that must not be assumed away.
- Do not start a new hierarchy of atom counts, polynomial degrees, frequencies, mesh sizes, integrand subclasses, or increasingly local cases without a proved uniform stopping bound.
- A smaller negative bound, another necessary condition, or another equivalent formulation is not exact-zero progress by itself. It may be recorded as an auxiliary result, but must not displace the active target. Explain precisely how it enables a contraction, gap separation, or complete direct proof before prioritizing more work on it.
- Do not report a numerical relaxation's infeasibility as a proof unless every unrestricted candidate is rigorously represented and all solver outputs are certified exactly. Do not infer gradient compatibility from determinant moments, arbitrary conditioning, or Caratheodory reduction.

Before a substantial computational campaign, state the exact global implication and certificate to be checked, why its domain includes every actual unrestricted candidate, and the smallest meaningful falsification test. Use exact rational/algebraic checks for final certificates. Record failed mechanisms in the ledger; stop rather than repeatedly tune a falsified relaxation.

**Acceptance:** a rigorous proof of beta_*=0, a justified finite exhaustive proof with all cases certified, or a genuine globally RC negative compatible-gradient witness. No claim of closure or proximity without one of these. The verified homogeneous isotropic theorem is unchanged.

**Most recent direct attempt (N23):** [Direct product-metric Legendre test](IWANIEC_MORREY_BETA_LEGENDRE_TEST.md) tests the universal beta inequality on exactly normalized anisotropic Legendre duals. The optimized quadratic Fenchel comparison still admits a positive-b isotropic formal state. No self-contraction resulted. Do not optimize this same comparison further or replace the active target with its auxiliary covariance inequality.
