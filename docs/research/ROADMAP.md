# Unrestricted planar Morrey — exact-zero roadmap

This is the single active research plan. It replaces the overlapping reset handoff, chronology and exact-zero directive. For mathematical details and stable result IDs use the [ledger](LEDGER.md); the [catalog](CATALOG.md) is a reference index, not a list of tasks.

## Target

Let C be all globally C^{1,1} rank-one convex energies F on real 2×2 matrices with F(0)=DF(0)=0 and Lip DF≤1. For arbitrary bases A and periodic W^{1,2} two-component u of positive energy set

    E(u) = integral |Du|²
    J_F(A,u) = integral [F(A+Du)-F(A)]
    beta_* = inf_{F in C, A, u, E(u)>0} J_F(A,u)/E(u).

**Prove beta_*=0.** R16 records a hand reduction making this equivalent to the unrestricted finite-valued planar problem. P15/P16 record −1/8 < beta_* ≤ 0. Both need analytic/formal verification before final assembly. Do not assume an optimizer, polyconvexity, isotropy, homogeneity, bounded amplitudes, fixed support or fixed wave count.

## G0 — baseline and current evidence

The signed homogeneous bi-isotropic QC theorem for every p>0 and nonnegative homogeneous bi-isotropic PC for p≥2 are verified on main; the active library is unchanged. The false Pedregal nonemptiness premise is already formalized. See [FORMAL_STATUS](FORMAL_STATUS.md). This does not close unrestricted planar Morrey.

The normalized compactification and relative mesh reductions R11–R16 cover both integrand and geometry at any fixed positive accuracy; they do not give a uniform finite exact cutoff. R16 is the most directly relevant normalization. P15/P16 are the strongest recorded bounds, not a self-contraction.

## G1 — exact unrestricted proof (OPEN)

Choose a mechanism with a quantified implication valid for every normalized RC energy and every actual compatible gradient. The following are sufficient alternatives, not additional assumptions of Morrey:

1. **Self-contraction:** prove beta_* ≥ theta beta_* for an explicit 0≤theta<1. Since beta_*≤0, this forces equality. A computer-assisted proof needs a sound universal reduction and an exact LP/SOS/interval/algebraic certificate, not merely a finite collection of necessary tests.
2. **Gap separation:** prove beta_*=0 or beta_*≤−epsilon for an explicit epsilon>0, then certify beta_*>−epsilon using a justified finite computation or an analytic bound. R16 supplies positive-accuracy enclosures, not the separation.
3. **Direct rigidity:** for b=−beta_*>0, H=F+b|.|² is QC and strongly RC, not necessarily PC. Uniformly exclude vanishing relative stabilized residual at fixed b (for example, a valid j≥c b^N with positive c and finite N). Include all genuine near-extremizers, including concentration or vanishing absolute energy. A different direct global Jensen proof is equally acceptable.

### Do not repeat these failed mechanisms

| Result | What is established | What remains missing |
| --- | --- | --- |
| N18/N19 | Local pair/T4 collapses and fixed-contact flattening fail in the stated generality. | Compatible change of the law or a different rigidity mechanism. |
| N20 | Quadratic covariance and constant-target heat identities admit artificial negative jets. | Common-energy and spatial constraints beyond the rejected relaxation. |
| N21 | Fixed-degree polynomial Jensen and abstract copy/graft closure admit diluted incompatible countermodels. | Sound genuinely spatial or nonpolynomial constraints, not a degree ladder. |
| N22/P17 | Finite fixed tests fail; adaptive tests and an all-affine hyperboloid certificate are useful but not sufficient. The bounded-amplitude PC branch is restricted. | Universal QC-compatible test selection and concentration control; do not impose PC reweighting on QC. |
| N23 | Optimized quadratic Fenchel comparison for normalized product-metric Legendre duals admits positive-b formal states. | A genuinely stronger comparison or new mechanism. |
| N24 | All quadratic norm-preserving Hamiltonian generators fail on balanced controls. Nonlinear normalized families reject these controls and add necessary tests. | A universal choice of nonlinear descent generator for actual near-extremizers, or a different proof. |

The most recent direct attempt is [N24](IWANIEC_MORREY_BETA_NORMALIZED_HAMILTONIAN_TEST.md). Reuse the earlier stress/duality, compatible recursion, filling and envelope tools only when they establish a missing implication above. R17–R24 describe their precise strengths and limits. In particular, an abstract moment state is not a gradient witness; arbitrary determinant-neutral conditioning does not preserve compatible children.

**Exit:** prove an unrestricted exact-zero inequality, or supply a sound uniform finite exhaustive reduction and certify all its cases. A new negative bound or necessary condition alone is not gate closure.

## G2 — exact counterexample alternative (OPEN)

The [global certificate hierarchy](GLOBAL_CERTIFICATES.md) is complete for strict negative witnesses but does not terminate in the positive case. Search only where a new structural prediction makes a discriminating test worthwhile.

- Verify the corrected base-minimizer range/kernel condition and known planar-positive and higher-dimensional-negative controls.
- Save a single globally RC energy (exact LH/Gram or other global certificate), a compatible rational periodic PL field or equivalent affine-boundary test, and a rigorously negative integral with all errors included. Save input data, code, settings, repair and exact rejection reason.
- Never interpret a non-PC energy, a sampled LH pass, a failed laminate construction or finite non-detection as a counterexample or as proof of the conjecture.

**Exit:** one certified genuine planar negative pair.

## G3 — verification and formal assembly (PENDING)

Independently audit the actual successful global mathematical proof or negative witness. Connect it to the unrestricted formal endpoint in the existing Lean library; only port archived bridges when necessary. Require fresh successful CI and an assumption audit. Hand proofs and exact finite controls remain distinct from kernel certification.

## Stop rules

Before any substantial computation, state the exact global implication, why every unrestricted candidate is covered, and the smallest test that could refute the proposed mechanism. No atom-, frequency-, mesh-, degree-, exponent- or subclass ladder without a proved stopping bound. A finite parameterization or arbitrarily accurate finite approximation is not an exact decision procedure. Record negative approaches once in the ledger; reopen only with a changed, testable hypothesis.

Success means a proof of beta_*=0, a justified finite exact proof with every case certified, or a certified negative planar witness. No claim of closure or proximity without one of those.
