# Rank-one-curvature compactness, effective minimum-set rigidity, and optimal fixed-contact repair

24 November 2026. Continuation of [envelope pinching](IWANIEC_MORREY_ENVELOPE_PINCHING.md), addressing loss of Hessian regularity and curvature in the proposed contraction. The objective is an exact proof, not enumeration of increasingly large witness meshes.

**New hand results.**
* Upper and lower rank-one curvature bounds alone imply local compactness modulo affine functions and a determinant gauge, with an explicit interpolation estimate and local C^1 compactness. Neither a common full-Hessian bound nor equicontinuity of Hessians is needed. For nonnegative energies with bounded average on a fixed bounded range, even the affine/determinant gauges are bounded.
* For prescribed positive lower rank-one margin, upper rank-one curvature, amplitude bound and positive absolute variance, the planar minimum-set rigidity used in R23 is uniform over this entire class. In particular the secondary gap QF-PF at bounded minimizing laws with a fixed positive defect is separated from zero. Using the previous C11 relative mesh theorem and the classical gradient Young-measure characterization, there is a terminating, albeit extremely expensive, exact finite-certificate procedure giving a positive rational lower bound on this separation. This is a computability proof; the full procedure was not run.
* Envelope subtraction preserves the upper **rank-one** curvature bound exactly. Thus the compactness requirement of the preceding rigidity result survives loss of full-Hessian bounds, as long as lower rank-one curvature, amplitude and a positive defect stay controlled. This removes the earlier C2 obstruction at a nonzero maximum defect, not at arbitrary vanishing defects.
* A maximal strongly rank-one convex envelope of the upper quadratic supports of contracted contact jets solves the fixed-contact curvature-repair problem exactly, including a prescribed QC lower barrier. It preserves a specified full-Hessian bound. The feasible contraction/amplification parameters form a closed convex region described by affine inequalities from finite rank-one trees. There is a positive admissible contraction when the original curvature bounds have slack. Conversely a nontrivial laminate in the support gives a strict positive lower bound on the stress-contraction factor for EVERY such repair with fixed lower curvature. Thus unlimited contraction with one fixed contact law cannot finish the proof, even with an optimal nonlinear repair.

**Limits.** The general lower-curvature-preserving contraction remains unsolved. In fact the last result identifies a genuine barrier to keeping the original support and contracting all its jets to a common minimum. We must change the contact law or prove rigidity by a different spatial mechanism. No new negative planar pair or unrestricted Morrey proof. The earlier exact-zero localization theorem R16 is a hand-proof dependency of the effective (not qualitative) assertion. The published planar compactness theorem and generalized Young-measure characterization are external inputs, not new Lean formalizations. No independent review or novelty claim.

## 1. Compactness using rank-one curvature alone

Write Q(X)=|X|_F²/2. Say that a finite continuous energy f is in the curvature sandwich (m,M), 0<=m<=M, if both f-m Q and M Q-f are rank-one convex. This is the directional definition, including nonsmooth Hessians. In particular for every rank-one H,
    m |H|² <= f(X+H)+f(X-H)-2f(X) <= M |H|².
The upper bound is preserved under all the affine and determinant gauges. It does not imply a uniform bound on every matrix-space Hessian direction, so we avoid making that inference.

**Lemma 1.** On every centered coordinate cube C_r=[-r,r]^4 there exists a rank-one affine polynomial l_r(X)=a_r+B_r:X+c_r det X such that
$$
\sup_{C_r}|f-l_r|\le 48 M r^2.                             (1)
$$
The same conclusion applies to a translated cube, with its affine/determinant polynomial written in the translated variables.

Proof. Scale to r=1 by dividing the energy by r². Let P be the multiaffine interpolant of the sixteen corner values, with variables (a,b,c,d) in row-major order, and coefficients c_S for monomials indexed by subsets S of {1,2,3,4}. Coordinate interpolation is positive and its error on each separately convex line is between 0 and M/2, by the upper rank-one curvature bound. Composing the four interpolations and telescoping gives
    0<=P-f<=2M
on the whole cube.

For each pair of entries sharing a row or column, let those coordinates be zero, let the other two coordinates take values ±1, and take the centered second difference in the direction with a one at both sharing entries. This direction is rank one, of squared norm two. The second difference of f is in [0,2M], and that of P-f is in [-4M,4M]. Half the second difference of P is precisely the coefficient of the sharing pair as a multiaffine polynomial of the other two entries. It is bounded in absolute value by 3M at all their corners. Walsh inversion on those four corners bounds each coefficient involving that sharing pair by 3M. All nine monomials of degree >=2 other than ad and bc contain a sharing pair.

At zero use the all-ones matrix, which is rank one of squared norm four. The absolute second difference of P is <=8M, so the sum of its even-degree coefficients of positive degree is bounded by 4M. Subtract the four sharing quadratic coefficients and the quartic coefficient; we obtain |c_ad+c_bc|<=19M. Subtract the affine part of P and ((c_ad-c_bc)/2) det X. The remaining coefficient sum is <=9*3M+19M=46M; include the interpolation error 2M. This proves (1).

**Lemma 2.** A family in the curvature sandwich (m,M) is locally precompact in C^1 modulo a rank-one affine gauge, with a common local C^{1,1/2} bound. For nonnegative members h, if some Y in a fixed bounded cube has h(Y)<=1, the h themselves are locally precompact, without subtracting any gauge.

To prove the first assertion, choose l_1 by (1) and subtract it. For r>=1 compare l_r with l_1 on C_1: the difference is bounded by 48M(r²+1). Since affine and determinant coefficients are Walsh coefficients on those corners, each is bounded by that same constant. Hence on C_r,
    |f-l_1|<=48M r²+48M(r²+1)(1+4r+2r²).
Separate convexity gives a uniform local Lipschitz bound from the bound on a cube enlarged by one in each coordinate. Each coordinate-line restriction is C11 with derivative Lipschitz constant at most M, by the two curvature inequalities. To compare partial derivatives at two nearby points, approximate each partial by a forward difference of length t. Its error is at most Mt/2. The difference of the two forward quotients is bounded by 2L|X-Y|/t when L is the local Frobenius Lipschitz constant. Choose t=sqrt(|X-Y|) for |X-Y|<=1 on a slightly smaller cube. This proves local uniform Holder-1/2 continuity of each partial derivative, and thus the C^1 compactness. The sandwich passes to the limit by the rank-one segment inequalities.

For the nonnegative assertion, center at the point Y and apply (1) to its unit cube. The one-dimensional descent estimate on each coordinate line gives |partial_i h(Y)|²<=2M h(Y)<=2M. Thus h(Y±e_i)<=1+sqrt(2M)+M/2. From the approximation (1), the absolute constant and linear coefficients of l_1 are bounded by C1=2+50M. Evaluating nonnegativity at diag(1,1) and diag(1,-1) relative to Y bounds |c_1|<=3C1+48M. This bounds the entire gauge. The preceding comparison on larger cubes then bounds the energy itself. For example if Y is in [-R,R]^4, R>=1, a deliberately loose rational bound is
    0<=h(X)<=B(k):=2000(1+M)(k+R+2)^4 on [-k,k]^4, k>=1.
For the centered cube of radius r>=1 the gauge bound is <=646(1+M)r², and the comparison and interpolation errors are <=672M r^4+48M r². This verifies the displayed bound after accounting for the shift Y. A common entrywise-1-norm Lipschitz constant on C_k is B(k+1), by separate convexity and coordinate slopes to points a unit distance outside. No Hessian continuity was used.

## 2. Uniform rigidity at fixed nonzero variance

We use Faraco and Székelyhidi, *Tartar's conjecture and localization of the quasiconvex hull in R2x2*, Acta Math. 200 (2008), 279–305, [DOI](https://doi.org/10.1007/s11511-008-0028-1), Theorem 6 and Corollary 2. In particular a compact set without rank-one connections or T4 configurations supports no non-Dirac homogeneous gradient Young measure. Equivalently, for the minimum-set application, the rank-one convex hull of a gradient law's support is connected, and a connected compact rank-one-free set supports only Dirac gradient laws. This is specifically planar.

Fix m>0, M>=m, R>=1, e>0. Consider every globally nonnegative h in the sandwich (m,M), and every compact homogeneous gradient Young measure nu supported in C_R with Var(nu)>=e.

**Theorem A.** There is epsilon(m,M,R,e)>0, independent of h and nu, such that
$$
\int h\,d\nu\ge\epsilon(m,M,R,e).                         (2)
$$
In particular no C2 modulus or full-Hessian bound enters this constant.

Proof. If a sequence violated every positive lower bound, eventually its average energy would be <=1, so each h_j would have a point in C_R with value <=1. Lemma 2 gives a locally uniformly convergent subsequence to a globally nonnegative h in the same sandwich. Bounded homogeneous gradient laws are weak-* closed on a fixed compact range (by their QC Jensen characterization), so a subsequential weak limit nu is a homogeneous gradient law. It has variance >=e. The limit energy integral is zero, hence supp nu is in {h=0}. By strong RC, any compact laminate on those zeros has zero variance: apply its Jensen inequality to h-m Q. Thus the rank-one convex hull of any compact subset of these zeros is itself, no two zeros are rank-one connected, and no T4 can be supported there. Apply the cited planar rigidity. This contradicts the positive variance and proves (2).

This proof deliberately assumes a positive lower bound on absolute variance. It does not replace the transition-layer argument of R23 for vanishing variance, which required stronger regularity.

### 2.1 Consequence for envelope subtraction

Let f be in the sandwich (m,M), with finite QC and PC envelopes q,p and an actual compact minimizing gradient Young measure nu at A. Suppose supp nu subset C_R and f(A)-q(A)>=D0>0. Assume a supporting global polyaffine minorant l touching p at A exists; for the positive quadratic-tail class this was proved in R23. Use (1) at radius 2R and note that f-l_(2R) has entrywise-1-norm Lipschitz constant <=384 MR on C_R by separate convexity. Its Frobenius Lipschitz constant is <=768 MR. Since the determinant and affine gauges integrate to their base values,
    D0<=f(A)-int f dnu<=768 MR sqrt(Var(nu)).
Apply Theorem A to h=f-l. Subtracting l leaves the rank-one curvature sandwich unchanged. With e=(D0/(768 MR))² we obtain
$$
\boxed{Qf(A)-Pf(A)\ge\epsilon(m,M,R,e)>0.}                 (3)
$$
This gives uniform pinching away from zero defect under **rank-one-only** curvature control.

For finite q, the cell-infimum formula proves that q inherits the same UPPER rank-one curvature bound M: after subtracting M Q, every translated cell integral is concave on every rank-one line; their infimum is concave there. Also q is RC. Thus, while f_theta=f-theta q has lower LH margin at least m-theta M, its upper LH curvature remains at most M exactly. Indeed M Q-f_theta=(M Q-f)+theta q is RC. In the quadratic-tail class the exact envelope identities of R23 still hold. The full Hessian need not remain bounded by the original M, and no C2 compactness is needed for (3). The remaining loss is the positive lower LH margin (and the range/defect bounds if the law is changed).

## 3. A terminating finite certificate of the separation in (2)

This subsection is an effective refinement, dependent on the [previous global C11 relative mesh estimate](IWANIEC_MORREY_C11_OPTIMAL_MARGIN.md), R16, in addition to the published minimum-set theorem. We establish termination of a rational algorithm for prescribed rational m,M,R,e; we do not provide practical complexity or run the enormous finite tests. The algorithm does not decide beta_*=0.

### 3.1 Effectively enumerable complete QC tests for compact laws

Enumerate rational C2 semialgebraic energies with exactly quadratic exterior, of the form rational quadratic/affine polynomial plus a rational polynomial times a fixed C2 piecewise-polynomial radial cutoff with rational radii. Use ordinary cutoffs in |X|². Derivative bounds on the compact cutoff region by coefficient sums and on the exterior give a rational global bound B on Lip DF. For each candidate and each positive rational eta, use R16 to compute a periodic PL mesh size n=n(B,eta). The condition
    J_F(A,u)>=2 eta int |Du|²
for every real base and every periodic nodal assignment on this fixed mesh is a real-algebraic universal sentence. Its evaluation is semialgebraic, and areas and slopes are rational linear formulas in the nodal variables. Exact real quantifier elimination decides it. If true, R16 proves J_F>=eta E globally. Dovetail this process over candidates and eta. Every output is globally strongly QC, and every strongly QC member of the enumerated family is eventually output (choose eta less than half its positive margin). There are infinitely many outputs, including rational positive quadratics. No floating solver is used for this certification.

These outputs are dense on every fixed compact cube in the restrictions of finite continuous QC energies of linear growth. Here are the required approximation details:
1. Such a QC energy k is RC, and its coordinate-line convex restrictions and global linear-growth bound imply a global Lipschitz bound by secant slopes at infinity. Smooth by convolution and add an arbitrarily small positive quadratic epsilon Q. The resulting smooth function is strongly QC and approximates k on the target cube.
2. Use a GLOBAL smooth convex maximum with a higher positive quadratic barrier, shifted downward to be inactive on the target cube. The smoothed k has linear growth, so the quadratic barrier is active outside a sufficiently large ball. Smooth maximum is convex, nondecreasing in its two arguments and translation-equivariant; subtract a common smaller positive quadratic from both arguments to see that strong QC is preserved by Jensen. This is not the invalid claim that a locally glued QC function is automatically globally QC.
3. The resulting smooth energy differs from its exterior quadratic by a smooth compactly supported function. Approximate that difference and its first two derivatives uniformly on a larger cube by polynomials (for example multivariate Bernstein approximation of a smooth function in C2), then multiply by a fixed rational C2 cutoff which is one on the old compact support. Approximate coefficients by rationals, including the exterior quadratic coefficients. This gives global Hessian error as small as desired, since the compact perturbation is zero outside its support and the cutoff has fixed bounded derivatives. Choose the error smaller than the positive QC margin; the Taylor estimate on the difference of energies then preserves strong QC. Values are arbitrarily close on the target cube. Such an approximation is in the enumerated family.

For compact probability laws, Jensen for all the QC tests of linear growth suffices for membership in the homogeneous gradient Young-measure class. One standard justification uses Kristensen–Rindler, *Characterization of generalized gradient Young measures generated by sequences in W1,1 and BV*, Arch. Ration. Mech. Anal. 197 (2010), 539–598, [DOI](https://doi.org/10.1007/s00205-009-0287-9), characterization theorem and Remark 6.10 (classical case with zero concentration). A constant law nu with affine barycenter and zero concentration has only the ordinary Jensen conditions for QC linear-growth tests. Its generator can be taken with no L1 concentration. Since nu is compactly supported, the L1 derivative mass above any sufficiently large fixed radius tends to zero. The weak-L1 maximal-function estimate, Sobolev pointwise Lipschitz bound and componentwise Lipschitz extension then give uniformly Lipschitz generating maps, changing the derivatives only on sets of measure tending to zero. On the cube subtract constants, use uniform compactness and the barycenter to get affine limit, and cut off to the affine boundary on shrinking collars (chosen slower than uniform map convergence). The gradient bound stays fixed and the law is unchanged. This is also the usual bounded-support truncation principle. Thus the enumerated strong QC tests characterize compact homogeneous gradient laws. This uses the published Young-measure theorem; it does not claim that finite moment conditions alone characterize such laws.

### 3.2 A finite decision at each stage, with proved termination

Use the explicit B(k) in Lemma 2. At stage n, take an increasing finite set of rational samples containing the current finite uniform grid of C_R, zero, and the first n triples of an exhaustive enumeration of rational centered rank-one second differences (and rational dense points in all of R4). Variables w_s are scalar energy data. Impose nonnegativity, the bound B(k) on samples in C_k, all pairwise Lipschitz constraints with constant B(k+1) on C_k, and the two rational second-difference inequalities of the sandwich on the first n triples. Rational rank-one directions are dense in the rank-one cone by approximation of their two factors. No limit energy reconstruction from arbitrary single-stage data is asserted.

Let sigma_n be the rational coordinate rounding error on the grid of C_R, tending to zero. Introduce probability weights on these grid points. Their variance is a quadratic expression in the weights; require it >=e-16R sigma_n. The rounding error estimate follows by bounding |X|,|X'|<=2R and |X-X'|<=2 sigma_n both for second moments and for the mean squared norm. Require the sampled energy average <=2^(-n)+4 B(ceil(R)+1) sigma_n.

For the first n certified QC energies k_i impose
    sum w_i^law k_l(grid_i) >= k_l(mean) - 8 L_l sigma_n,
where L_l is a rational entrywise-1-norm Lipschitz bound on C_R (obtainable from the polynomial pieces). Rounding changes average and base evaluations by at most 4 L_l sigma_n each. All these constraints form one finite real-algebraic feasibility problem. Polynomial pieces in k_l(mean) can be expressed by their semialgebraic graphs. Decide exactly by quantifier elimination. If infeasible, return epsilon=2^(-n) as the positive lower bound in (2).

Indeed every true pair with average <=2^(-n)<=1 has the uniform energy sample bounds proved above, and its rounded law and energy values satisfy the finite constraints. Hence an infeasible stage is a valid certificate.

If every stage were feasible, use diagonal compactness of the bounded sample values and the pairwise Lipschitz constraints to obtain a locally uniformly continuous limit energy on the dense rational set, then extend it continuously. It is nonnegative and in the sandwich, by the exhaustive second differences and density. The grid probability laws have a subsequential weak limit on C_R. Their variance is >=e in the limit. Along that subsequence the sampled energies converge uniformly on C_R to the limit function, by the pairwise Lipschitz inequalities and density of the fixed samples. Hence the limiting energy integral is zero. Every fixed enumerated QC test passes to the limit in its rounded Jensen inequality; by Section 3.1 the limiting law is a homogeneous gradient Young measure. This contradicts Theorem A. Therefore the algorithm MUST halt after finitely many stages for each prescribed positive rational input m,M,R,e.

No computable bound independent of e or of the lower curvature m is supplied. The procedure uses effective finite-accuracy QC certification, not a decision of exact QC on arbitrary energies. In particular the proof of termination depends on the published planar minimum-set rigidity, rather than assuming termination of Morrey search. We have not implemented the full algorithm or computed its very large constants. This is a concrete theoretical finite certificate for the uniform strict separation needed in (3).

## 4. Exact optimal repair with prescribed curvature and contracted contact jets

Here use the original bounded contact law from [maximum-defect setup](IWANIEC_MORREY_INNER_STRESS_SHEAR.md). Recenter f(0)=Df(0)=0. Let D>0 be the maximum QC-envelope defect, q=Qf, p_env=Pf, S=q(0)-p_env(0)>0. Let nu be its minimizing compact homogeneous gradient law with support K disjoint from zero, mean zero, variance E>0, and
    int f=-D, f=q on K,
    int Df=0, int T=-D I,
    T=f I-X^T Df.
The full six-row graph is compatible in the shifted mean sense of R21. Let l be a global polyaffine minorant with l(0)=p_env(0) (positive quadratic-tail class).

We will allow a general stress scale a in [0,1] and target absolute deficit d>=0. Require a repaired energy g to have
    g(0)=0, Dg(0)=0,
    g(X)=v_(a,d)(X):=a(f(X)+D)-d on K,
    Dg(X)=p_(a,d)(X):=a Df(X) on K,
    g(Y)>=L_(a,d)(Y):=a(q(Y)+D)-d for ALL Y.
The last barrier is QC. Fix curvature targets 0<kappa<m_f, M1>M_f, where f is strongly RC with margin m_f and Lip Df<=M_f. Seek g globally kappa-strong RC, with Lip Dg<=M1.

For any such repair the full lift on K is a constant affine row transform of the original one:
    T_g=a T+(aD-d)I,
    T_g+dI=a(T+D I).
The law remains genuine and its mean third block is -d J. The witness and barrier give the exact base envelope value Qg(0)=-d. Also g>=a l+aD-d, giving Pg(0)>=-d-aS. Thus
    g(0)-Qg(0)=d,
    0<=Qg(0)-Pg(0)<=a S.
This simultaneously contracts the centered stress and the secondary envelope gap while allowing the primary defect to increase. The law remains the minimizing law at zero, but we do not assert that zero maximizes the new defect or that the entire QC envelope is the barrier.

**Theorem B (optimal repair).** Define K0=K union {0}, with jet values v(0)=0,p(0)=0 and the above prescribed jets on K. Set
$$
U_{a,d}(Y)=\min_{X\in K_0}
    [v_{a,d}(X)+p_{a,d}(X):(Y-X)+(M_1/2)|Y-X|^2],
$$
$$
G_{a,d}=\kappa Q+R[U_{a,d}-\kappa Q],                   (4)
$$
where R is the usual rank-one convex envelope. Then G_(a,d) is globally kappa-strong RC, globally C11 with Lip DG<=M1. A repair with the stated bounds exists IF AND ONLY IF
    G_(a,d)(X)=v_(a,d)(X) for every X in K0,
    G_(a,d)>=L_(a,d) globally.
When feasible, G_(a,d) is the pointwise largest such repair.

Proof. Any g with Lip Dg<=M1 and the prescribed jets lies below every upper paraboloid in (4) by Taylor. If it is kappa-strong RC, g<=G by the RC envelope property. The obstacle is M1-semiconcave (subtract M1 Q to get an infimum of affine functions) and U-kappa Q has a finite lower constant since M1>kappa and the jets range in a compact set. Thus the envelope is finite, and the standard finite-laminate infimum representation gives strong RC of G. Each translate-average of U-kappa Q is (M1-kappa)-semiconcave, so its infimum is too; adding kappa Q gives M1-semiconcavity of G. Mollify and use orthogonal rank-one decomposition R+S of any direction: the sum of the Hessian quadratic forms on R+S and R-S is at least 2kappa|R+S|². The upper bound M1 gives the lower Hessian bound 2kappa-M1. Hence the mollifications and G have derivative Lipschitz constant <=M1. If a repair exists, G>=g, while G<=U<=v at each prescribed point. Therefore G has the correct values and lower barrier. Conversely equality at each jet means that G touches its corresponding smooth upper paraboloid from below, hence has its prescribed derivative. This proves feasibility and maximality.

The feasible (a,d) region is closed and convex. Indeed the conditions in Theorem B are equivalently all affine inequalities obtained as follows:
take any finite rank-one splitting tree with leaf weights w_i and leaf matrices Y_i, root B, and select ANY X_i in K0 for each leaf. Require
    sum_i w_i [v_(a,d)(X_i)+p_(a,d)(X_i):(Y_i-X_i)
                            +M1 |Y_i-X_i|²/2]
           -kappa Var(tree)/2
        >= L_(a,d)(B)
and, if B is a prescribed point, also >=v_(a,d)(B).
The minimum over X_i and the infimum over trees are exactly (4) at the root. Thus each failure has a strict finite tree witness, although there is no uniform bound on its size. This is a genuine optimal two-parameter curvature-repair formulation, not a claim that sampling tree inequalities proves exact feasibility.

The region contains (1,D) by f itself. It contains positive contractions at d=D: take g=f-theta q-theta D with a=1-theta, for theta>0 small enough that m_f-theta M_f>=kappa and (1+theta) M_f<=M1. It also contains amplifications at a=1 and d=(1+eta)D for small eta>0: use g=f+eta(f-q)-eta D. The maximum-defect identity ensures the prescribed base jet, and the old contact set gives the required jets. Its lower barrier is q-eta D, and the two curvature estimates follow from Lip Dq<=M_f, RC of q and the original margin of f. Thus this is a nonempty actual repair problem with a positive admissible change under strict curvature slack. The maximal envelope can do better than these elementary small changes.

### 4.1 A structural bound on all fixed-law contractions

A limit a->0 while keeping the fixed nontrivial contact law and positive kappa cannot be feasible, regardless of the chosen nonlinear repair, even without an upper Hessian constraint. There is a quantitative reason on this very support. The cited planar compactness theorem implies that K contains a rank-one connected pair or a T4 configuration: otherwise it cannot support the nontrivial nu. Such a pair supplies a two-atom laminate; a T4 supplies a nontrivial laminate on its four endpoint matrices by the usual repeated rank-one cycle. Equivalently existence of some nontrivial compact laminate mu supported in K follows immediately from the connected-rank-one-hull proof of Corollary 2: if every laminate on K were Dirac, K would equal its rank-one hull and be rank-one-free, forcing nu Dirac. Use any one such mu, with barycenter B and positive variance E_mu.

Every admissible g must satisfy
    int g dmu >= g(B)+kappa E_mu/2 >= L_(a,d)(B)+kappa E_mu/2.
On its support the prescribed values give int g=a(int f dmu+D)-d. Cancel the constants to obtain
$$
\boxed{\quad a\ge
\frac{\kappa\,E_\mu}{2(\int f\,d\mu-q(B))}>0.\quad}        (5)
$$
The denominator is positive since f is strongly RC, q<=f, and E_mu>0. The bound is independent of d and M1. It involves one actual laminate on the support, not an unjustified replacement of part of nu by that laminate. For rational finite well data this kind of witness can be tested directly; no actual hypothetical counterexample support is available here.

The new uniform rigidity estimate gives another bound when M1,R are controlled: h=g-(a l+aD-d)>=0 has average aS on the fixed nontrivial gradient law. Therefore aS>=epsilon(kappa,M1,R,E) from Theorem A. The algorithm of Section 3 supplies a computable positive lower bound from these fixed inputs, if they are specified rationally (one can use rational outer bounds and a rational positive lower variance). This rules out a uniform fixed-support repair even if one drops all C2 regularity. The feasible region at fixed M1 is compact, since d<=M1 E/2 by Taylor at zero and a is in [0,1]. By (5) its maximum d/a is finite and attained. Thus no sequence of these normalized fixed-contact repairs can give unlimited defect-to-stress amplification. This is a mathematical obstruction to that specific continuation mechanism, not merely a failure of the initial quadratic estimate.

## 5. Disposition and verification

The weak curvature normalization and uniform finite certificate solve the full-Hessian/C2 compactness issue at a nonzero bounded maximum defect. The optimal repair preserves the normalization as stipulated and tells us exactly when changing the two contact parameters is possible. But (5) shows that a complete proof cannot result simply from indefinitely contracting the same law's stress and secondary gap at a fixed positive rank-one margin. Some other operation must change the law/support or derive rigidity from it; allowing kappa to tend to zero loses the minimum-set rigidity input. This is not an argument that unrestricted Morrey is false or that all possible moving-law amplifiers fail.

The useful next attack is to exploit the unavoidable rank-one pair or T4 within the contact support in an ACTUAL minimizing gradient law: seek an energy-decreasing or variance-resolving replacement that preserves compatibility, or a new contradiction with contact optimality. The previous N09 conditioning obstruction means that one cannot simply subtract a laminate from a gradient measure and assume the result is compatible. Neither a finite-size bound on all contact supports nor such a replacement has been proved. Avoid another chart or fixed-contact contraction ladder.

The companion lh_jet_repair_exact.py was executed in the working container. It passed 40 rational multiaffine interpolation controls, the coefficient/growth budget identities, 36 rational stress/energy parameter controls, and the two-point obstruction and eight rational curvature-budget controls. SHA-256 319e1c30c91059bbe91b85d5c9dad192fb4592d66ead26f73c2efc40705c38b4. These check algebra, not the published rigidity theorem or the analytic effective-enumeration proof. No full quantifier-elimination stage, hypothetical contact-law computation, Lean validation or unrestricted proof was completed.
