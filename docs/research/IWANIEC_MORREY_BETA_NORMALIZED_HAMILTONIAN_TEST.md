# Direct beta_* test: exact normalized Hamiltonian perturbations

24 November 2026. This tests a self-contraction mechanism under the active [exact-zero directive](README.md#target). Unlike earlier Hamiltonian perturbations, the transformations below preserve the full unit Hessian bound, rather than paying for growth of the bound with the unknown beta_*.

**Outcome.** We characterize all constant quadratic Hamiltonian generators preserving the normalized RC Hessian cone. They give new necessary moment inequalities at universal near-extremizers, including int det DF(X)->0. An exact calculation (and twelve executed LP controls) shows that this entire first-order quadratic-generator family cannot force a strict descent on the balanced zero-stabilized-stress moment state. This limitation persists for artificial states with a common globally C11 QC/RC integrand and the all-affine detector (P17). A nonlinear normalized Hamiltonian family does reject those states; an explicit rational-cost regression check is given below. No universal choice of a negative nonlinear generator, contraction, gap separation, stronger universal numerical bound, genuine negative gradient witness, or unrestricted proof was obtained. This is a direct proof-mechanism test, not a new restricted completion target. The analytic arguments are hand proofs, not independently reviewed or Lean-verified.

## 1. The exact normalization and the relevant tangent cone

Use Frobenius coordinates on R4, with C the symmetric cofactor involution, C²=I, det X=X:C X/2. Let E_+, E_- be its two-dimensional eigenspaces. A nonzero R is rank one iff R:C R=0. Write

    K={H symmetric: -I<=H<=I, R:H R>=0 for every rank-one R}.

The normalized C11 RC energies have a.e. Hessians in K. Two elementary active-boundary facts are useful.

* At an LH null direction, R:H R=0 with R unit rank one, the derivative of the nonnegative quadratic form along the smooth rank-one cone vanishes. Its normal there is C R; hence H R=c C R with |c|<=1.
* If H v=-v for unit v, H<=I-2 v tensor v. Thus |v:R|²<=1/2 for every unit rank-one R. The maximum of this squared inner product is the squared larger singular value of v. Its Frobenius norm is one, so both singular values equal 1/sqrt(2). Therefore v belongs to E_+ or E_-.

Both kinds of active directions are realizable: H=c C for |c|<=1, and H=+I at the upper spectral boundary.

Consider the quadratic Hamiltonian

    k(X,p)=X:A X/2+X:B p+p:D p/2,

where A,D are symmetric and B is arbitrary. Its characteristic equations for the Hamilton-Jacobi evolution partial_t F_t=k(X,DF_t(X)) are

    dot X=-B^T X-D p,   dot p=A X+B p,
    dot H=A+B H+H B^T+H D H.

**Theorem A.** The following conditions characterize preservation of K by the Riccati flow for small nonnegative time, for every H initially in K:

    A+D+B+B^T <= 0;
    v:(A+D-B-B^T)v >=0 for v in E_+ or E_-;
    R:[A+c(B C+C B^T)+c² C D C]R>=0
       for all unit rank-one R and -1<=c<=1.              (1)

Necessity follows by the active-direction realizations above. Sufficiency follows by testing each active defining inequality of K, using the two boundary facts. For a detailed invariance justification, perturb the Riccati vector field by epsilon(I/2-H) and start at (1-delta)H+delta I/2. At a first boundary hit the active linear inequality has a strictly inward derivative: the perturbation has a uniform positive inward margin because I/2 satisfies all normalized defining inequalities strictly. A differentiable slack cannot first reach zero from positive values with strictly positive derivative. Thus the perturbed path stays in the compact K. Continuous dependence on the vector field and initial data gives invariance for the unperturbed flow as epsilon,delta->0. The finite-dimensional cone conditions (1) are semialgebraic (the last is a universal polynomial inequality on a compact parameter set).

For completeness, this is also an energy transformation, not only an ODE on arbitrary Hessians. The linear characteristic flow in (X,p) is symplectic. If its block matrix is S_t, the independent-coordinate map X->Y=S11 X+S12 DF(X) is a globally bi-Lipschitz perturbation of identity for a uniform small time depending only on the generator and Lip DF<=1. Define the transformed energy by

    F_t(Y)=F(X)+(Y:p_t-X:p)/2.

The symplectic identity preserves X:dp-p:dX and gives dF_t=p_t:dY. Differentiating at fixed Y gives the stated Hamilton-Jacobi equation. Its a.e. Hessian is the Riccati solution; thus RC and Lip DF_t<=1 hold exactly by (1). This proof first applies to smooth F; mollification preserving K, subtracting the affine tangent, and passage to the local limits of the uniform bi-Lipschitz formulas give the globally C11 case. The origin with zero derivative is fixed, as k is homogeneous quadratic. No amplitude restriction enters.

A simple example is the cofactor-normalized shear. With |s|<1 let Y=X+s C p and

    F_s(Y)=(1-s²)(F(X)+s det p)+s det Y.

Its Hessian is H_s=(H+s C)(I+s C H)^(-1). Rank-one convexity follows from R17's cofactor shear (or Theorem A after using the characteristic time artanh(s) and simultaneous scalar rescaling). The exact identity

    (I+s H C)(I-H_s²)(I+s C H)=(1-s²)(I-H²)

proves the FULL norm bound one, not the earlier growth bound. All identities have been checked symbolically. This transform is available for both signs.

## 2. Use the original universal beta inequality

Suppose beta_*=-b<0. Normalize near-extremizers F_j and actual compatible X_j as in R16, with mean zero, E=int|X_j|²=1, int F_j(X_j)->-b. Put m=2b and p_j=DF_j(X_j). For H_j=F_j+b|.|², QC follows directly from the universal beta definition. Hilbert-space descent for the nonnegative affine-compatible gap functional gives

    int (p_j+m X_j)->0,    ||P(p_j+m X_j)||_2->0,

where P is the mean-zero gradient projection. In particular int X_j:p_j->-m. We do not assume attainment of beta_*, polyconvexity, or uniform amplitude bounds.

Every generator satisfying (1) gives a new normalized energy and hence

    liminf_j int k(X_j,p_j)>=0.                         (2)

Indeed the transformed energy at the same fixed X has the uniform expansion F_t(X)=F(X)+t k(X,DF(X))+O(t²|X|²). The uniform error follows from the linear characteristic map, its inverse being I+O(t) in Lipschitz norm, |DF(X)|<=|X|, and the quadratic bound on k. Integrate, use beta_* for F_t on the ORIGINAL compatible X_j, first take j->infinity at fixed t>0 and then t->0. This is a direct use of the universal margin without a normalization loss. Taking A=C,D=-C,B=0 and its negative in (1) yields

    int det p_j -> 0,                                   (3)

because int det X_j=0. Thus also int det(X_j +/- C p_j)->-/+m. The determinant identity here is exact in W1,2 by approximation.

## 3. Exact limit of quadratic first-order descent

The following subproblem is a test of sufficiency, not a claimed reduction of all actual near-extremizers. Consider the formal zero-stabilized-stress state p=-m X, with centered correct-minor law, covariance S=int vec(X) tensor vec(X), trace S=1, tr(C S)=0. For every 0<m<1, **absence of a strictly negative expected quadratic generator in (1) is equivalent to**

    S-m C S C >=0.                                     (4)

Proof. From (1) at c=0, A is RC as a quadratic form; averaging c=1 and c=-1 gives D+C A C RC as well. Set U=-(A+D+B+B^T)>=0. The exact integrated identity is

    2 int k(X,-mX)
      =(1+m) A:(S-m C S C)
       +m(1+m)(D+C A C):S +m U:S.

A PSD matrix with zero C trace is a sum of rank-one outer squares of determinant-zero vectors: write it as L L^T and take an orthonormal basis with zero diagonal for the traceless symmetric L^T C L. Such a basis follows inductively by a zero quadratic-form direction and restriction to its orthogonal complement. Thus if (4) holds, all three terms are nonnegative. Conversely, if v:(S-m C S C)v<0, take

    A=v tensor v, D=-C A C, B=-(A-C A C)/2.

These satisfy (1): upper inequality is equality, lower compressions to E_± vanish, and the LH expression equals (1-c²)R:A R. The expected cost is strictly negative. This proves (4), for the ENTIRE quadratic generator family, not only samples.

The twelve executed LPs optimize a necessary outer relaxation of (1) at diagonal covariances. With cofactor partner i'=5-i, diagonal coefficients a_i,d_i,b_i must satisfy a_i>=0, a_i'+d_i>=0, -a_i-d_i-2b_i>=0. For w_i=S_ii and sum w_i=1 the cost has the exact dual decomposition

    sum_i w_i(a_i-2m b_i+m²d_i)
      =(1+m)sum_i(w_i-m w_i')a_i
       +m(1+m)sum_i w_i(a_i'+d_i)
       +m sum_i w_i(-a_i-d_i-2b_i).

When w_i>=m w_i', the zero generator attains the LP optimum zero, and this displayed rational identity certifies the lower bound. Otherwise the explicit A,D,B above gives a genuine admissible negative generator. Nine LPs had certified optimum zero; three had exact negative admissible generators. Parameters were m=1/4,1/10,1/1000, and full isotropic, balanced diagonal, threshold, and unbalanced covariance controls. The negative cases are not purported actual universal extremizers.

In particular S=I/4 satisfies every quadratic first-order test, for any m in (0,1). This is the same balanced moment state surviving the concurrent [Legendre comparison N23](IWANIEC_MORREY_BETA_LEGENDRE_TEST.md). Neither that comparison nor these quadratic moment perturbations can alone establish the desired contraction.

### 3.1 Stronger common-integrand regression, also passing P17

The previous conclusion does not merely depend on arbitrary incompatible Hessian jets. Here is an existence construction of an artificial exact critical law with a common globally C11 QC (thus RC) F, p=-m X, S=I/4, and the all-affine detector P17 satisfied. This does NOT claim the law passes all possible QC tests or the true universal beta inequalities for every other integrand.

Use the pinned verified truncated determinant L (R06/R17). It has global Frobenius Lipschitz bound 4, because RC gives convex coordinate restrictions and its linear growth bounds each coordinate slope by 2. Smooth by a radial compactly supported convolution of radius delta=1/1000, obtaining L_delta. It is QC, rotationally invariant under SO(2)×SO(2), globally C11, and equals det on |X|<=1/2 (convolution of det with the radial kernel leaves it unchanged). A correct-minor mean-zero law on symmetric signs of 2I and diag(1,-1)/4 has relative L gap -1/16: positive determinant mass is weighted to balance the negative. The strict sign survives convolution, since the negative atom remains in the det patch and the positive value changes by <=4 delta.

Take a convex nondecreasing smooth maximum of L_delta and |X|²/2-100, with smoothing width 1/4. This gives a globally C11 QC rotationally invariant F_0, equal to L_delta on B4, exactly the quadratic barrier outside a sufficiently large radius R. The smooth maximum preserves QC by Jensen; the transition Hessian is bounded on its compact region. It has F_0=det near zero and still has the strict negative abstract minors gap.

For nonzero X put r=det X/|X|², w=F_0(X)/|X|². In minimizing w over convex combinations with mean r=0, it suffices to use a compact annulus 1/2<=|X|<=R: smaller radii give w=r, realized at radius 1/2 with the same angle, and larger radii give w=1/2-100/|X|², no better than at radius R with the same angle. The compact convex hull of the pairs has strictly negative lower boundary -b0 at r=0. Since 0 is interior to the r interval, it has a finite supporting slope c there. Therefore

    h_0(X)=F_0(X)+b0 |X|²-c det X >=0

globally and there are contact matrices X_+,X_- with opposite nonzero determinant signs: any contact at r=0 would contradict rank-one nonnegativity F_0(X)>=0 on the rank-one cone. Choose the two from the supporting face, with energy-weighted probabilities balancing r, then convert to ordinary probabilities by dividing their weights by |X|² and renormalizing. Average over the finite independent quarter-turn orbits in conformal and anticonformal coordinates. These rotations are realized by SO(2) left/right rotations, so the contact values and determinants are unchanged. The result has zero mean and determinant mean zero, positive variance and no nonzero energy h_0 on its support. h_0 is differentiable and nonnegative, so Dh_0 vanishes there. Normalize variance to one by simultaneous amplitude rescaling and quadratic rescaling of the energy. Its covariance is now S=I/4 (the two C eigenspaces have equal trace from the determinant mean, and each quarter-turn average is isotropic on its subspace). Its weighted lifted covariance

    Gamma=int (vec X,det X) tensor (vec X,det X)/(1+|X|²)

is positive definite: the four-by-four block is positive definite, the determinant entry positive and the cross terms zero by sign symmetry. All ranges here are finite.

Inflate only the global Hessian bound of the energy, by adding K (|X|-R')_+²/2 to both F_0-c det and h_0, where R' exceeds all contact norms and K can be arbitrarily large. This convex C11 function vanishes with derivative on the entire tested range. Divide by a global derivative-Lipschitz bound M tending to infinity with K. Now F is normalized globally C11 QC and RC; its rank-one lower curvature infimum is zero by the det patch at the origin. With b=b0/M>0, h=F+b|.|² is globally QC, strongly RC and nonnegative, and h=Dh=0 on the artificial law. Thus j=0 and p=-mX (m=2b). The candidate b tends to zero while the law, S and Gamma remain fixed.

The all-affine P17 moment inequalities also hold at j=0 for sufficiently small b. Write lambda=lambda_min(Gamma)>0 and kappa=m/(1+m). For any invertible left/right matrices P,Q put s=||P||op ||Q||op, d=cond(P)cond(Q)>=1. The pullback curvature ratio used in P17 is kappa_T=kappa/d². Its affine residual coefficient a(P,Q) has last coordinate det P det Q of modulus s²/d. Therefore

    B(kappa_T) sqrt(2 a^T Gamma a)
         >= (16/kappa²) sqrt(2 lambda) d³ s².

The left side E_Y of P17 is at most s², because E=1. For kappa sufficiently small the displayed bound alone dominates E_Y for ALL invertible P,Q, and the skew term is nonnegative. The same proof applies to the looser Frobenius pullback bounds. This makes (4) and P17 together insufficient, even with a common globally normalized energy and exact zero stabilized stress. It also passes the N23 quadratic Legendre comparison by its balanced covariance. It need NOT pass an arbitrary additional adaptive QC test (in fact it fails the next one), or the true extremality requirement for all normalized RC tests on that law. This is a precise regression state for the stated relaxations, not a counterexample to Morrey.

## 4. A nonlinear family with exact norm preservation

The quadratic limitation is not an obstruction to all normalized perturbations. Let phi be any globally C11 RC function with zero tangent at zero that is concave in the E_+ variables and convex in the E_- variables (holding the complementary variables fixed). Consider

    k(X,p)=phi(X+C p).

This is a legitimate normalized nonlinear generator. Along a characteristic Y=X+C p is CONSTANT, since

    dot X=-C Dphi(Y),    dot p=Dphi(Y).

Thus for a uniform small t the independent-coordinate map X_t=X-t C Dphi(X+C DF(X)) is globally bi-Lipschitz (its perturbation has Lipschitz constant <=2t Lip Dphi<1). The exact action is

    F_t(X_t)=F(X)+t[phi(Y)-p:C Dphi(Y)]
                    -t² Dphi(Y):C Dphi(Y)/2.

Differentiation gives DF_t(X_t)=p+t Dphi(Y) and partial_t F_t at fixed coordinate equals k. At a smooth Hessian the Riccati equation along the characteristic is

    dot H=(I+H C) D²phi(Y)(I+C H).

At an upper spectral active direction H R=R the tested variation (I+C H)R=2 R_+ lies in E_+, so the derivative is nonpositive. At a lower direction H R=-R the variation lies in E_-, so the derivative is nonnegative. At an LH null HR=c CR the variation is (1+c)R, rank one, giving nonnegative derivative by RC of phi. The same inward perturbation proof as Section 1 preserves K. Smooth convolution and uniform small-time formulas extend to C11 F and phi. There is NO Hessian-norm growth factor. The version k=phi(X-C p) uses concavity on E_- and convexity on E_+ instead.

In particular for any globally C11 RC K with zero tangent at zero and Lip DK<=N, the function phi=K-N det satisfies the required concavity/convexity (and retains RC since det is null). The opposite-sign case uses phi=K+N det. The uniform fixed-coordinate expansion in Section 2 now holds with constant depending on N, since the maps are Lipschitz-close to identity and phi has quadratic growth. Equations (2),(3) and int X:p->-m give the necessary nonlinear inequalities

    liminf_j int K(X_j+C p_j) >= -m N,
    liminf_j int K(X_j-C p_j) >= -m N.                    (5)

More generally the ungauged phi generators as just described must each have nonnegative limiting first-order cost. These are tests on the actual universal near-extremizers. They are not asserted Jensen inequalities for compatible laws of X±C p_j.

The stronger fake of Section 3.1 fails the nonlinear test: choose K=F_0 (rescaled to the variance-normalized law, before inflating its Hessian bound). It has int K=-b0<0 and fixed finite N. At p=-mX, X+C p=(I-m C)X, det average=-m. The expected generator K(X+C p)-N det(X+C p) tends to -b0 as m->0. Thus for all sufficiently small positive m the same common-energy family that passes P17 and all quadratic tests has a strictly negative normalized nonlinear generator. This shows a strict increase in what the no-normalization-loss test detects. It does not yet supply a universal negative generator for a TRUE near-extremizer.

A fully rational moment-only control checks the same distinction numerically without reconstructing the contact-minimizing energy. Give total mass 1/16 to the four conformal matrices ±2I,±2J, total mass 1/4 to the four anticonformal matrices ±diag(1,-1),±[[0,1],[1,0]], and remaining mass 11/16 to zero, equal weights within each orbit. Then E=1, correct means/minors, S=I/4, Gamma eigenvalues 1/36 (twice),1/12 (twice),7/36. Hence it passes (4) and all P17 affine inequalities at j=0 for every admissible kappa<=1. Its raw L average is -1/16. Smooth L by the radial compact polynomial density proportional to (1-|X|²/delta²)_+² with delta=1/1000. The derivative L1 norm of this kernel is 192/(35 delta), so Lip D L_delta<=4*192/(35 delta)<32000. Its tangent at zero is zero. Take m=10^(-7) and the normalized generator phi=L_delta-32000 det. Its cost at p=-mX is bounded above by

    -1/16+4 delta+(4+32000)m = -138249/2500000 <0.

The errors use Lip L<=4, |X| mean <=1, and the exact determinant moment of (I-m C)X. The script verifies every rational moment and cost. This is only a moment control, distinct from the common-energy existence construction in Section 3.1.

## 5. Decision, reproducibility and limitations

A direct contraction would need a justified universal choice of an admissible generator with strictly negative expected first-order cost at hypothetical true b>0, or another exact finite proof. We did not obtain that choice. In particular simply taking K=F_j in (5) incurs a determinant budget m=2b, which does not cancel the original b defect with a strict gain; no contraction follows. The exact quadratic descent criterion (4) is a stop rule for further tuning quadratic first-order perturbations alone. The nonlinear mechanism legitimately adds stronger tests, but their universal sufficiency is open. Do not make them a new independent target or claim progress toward exact zero based solely on this regression.

Executed research/audit/beta_quadratic_tangent_exact.py (Python 3, SciPy 1.17.0, SymPy 1.14.0). Exact symbolic tangent/cofactor identities, twelve LPs with exact dual nonnegativity or admissible negative generators, full-covariance Gamma identities, negative minors seed and mollifier budgets, and the strict nonlinear rational-cost control passed. SHA-256 9a2f0d43359144a2a6562b5c3e2ef5b481a5d6f1e61f1626cbef5543760d291c; Git blob e29fd410e2893d2310134beebbb36e426434a10b. The analytic flow and common-energy existence proofs are not certified just by these calculations. No full unrestricted feasibility solver, actual negative compatible-gradient pair, new Lean declaration or proof of beta_*=0.

## 6. 25 November: exact normalized joint Hamiltonians and a quantitative descent certificate

This extends the nonlinear test from Section 4 and the unrestricted joint lift R18. The only objective is still beta_*=0. The new statements are hand results, not independent or Lean verification.

### 6.1 Joint normalized generators

Write C for the cofactor involution and Q for the set of symmetric four-dimensional Hessians satisfying -I<=H<=I and LH>=0. For any globally C11 rank-one convex energy K on 4x2 matrices (written as two 2x2 row blocks X,Y), normalize K(0,0)=DK(0,0)=0 and let N be a global bound for Lip DK. Define the directional normalization budget

    gamma = (1/2) max{0,
        ess sup_(X,Y), |v|=1 D²K(X,Y)[(v,Cv),(v,Cv)],
        ess sup_(X,Y), |v|=1 -D²K(X,Y)[(v,-Cv),(v,-Cv)]}.

Equivalently, take a uniform upper bound for the first directional curvature and a uniform lower bound for the second in the line-second-difference formulation. Any larger nonnegative gamma also works. Since the two joint directions have squared norm 2, gamma<=N for the minimal budget. Then

    k(X,p)=K(X,Cp)-gamma X:p                                  (6)

generates a short-time Hamilton-Jacobi flow preserving EXACTLY the whole unit-Hessian RC normalization. No assumption of QC or PC of K or F enters.

Proof for smooth energies. The characteristic equations are dot X=-k_p and dot p=k_X. The Hessian graph satisfies the Riccati equation, with quadratic form

    v:dot H v = D²k(X,p)[(v,Hv),(v,Hv)].

At an active rank-one direction R, H R=c C R, |c|<=1 (Section 1). The argument of the Hessian of K becomes the stacked rank-one direction (R,c R). Its contribution is nonnegative and the bilinear gauge contributes -2 gamma R:H R=0. At the upper spectral boundary H v=v the contribution of K is at most 2 gamma |v|², and the gauge contributes -2 gamma |v|². At the lower boundary H v=-v the contribution of K is at least -2 gamma |v|² and the gauge contributes +2 gamma |v|². These signs test every active linear inequality of the compact convex Hessian cone. The inward-perturbation/first-exit proof of Section 1 applies to the time-dependent Riccati ODE along each characteristic. Thus the Hessian remains in Q. There is no bound-growth term to pay. Both the joint rank-one curvature and the two directional curvature bounds pass through ordinary positive convolution, so smooth approximation of F and K, subtracting their affine tangents at zero, proves the C11 version by the uniform graph estimates below.

### 6.2 Uniform finite-time error and the actual beta test

Let L>0 bound Lip Dk (one can take N+gamma if nonzero). The characteristic vector field on the pair (X,p) is L-Lipschitz and vanishes at zero. For 0<=tau<=1/(8L), the characteristic displacement is at most (exp(L tau)-1) times the initial pair norm. The Lipschitz constant of the displacement of the graph's first coordinate is at most sqrt(2)(exp(L tau)-1)<=3L tau, because Lip DF<=1. The first-coordinate map is therefore globally invertible by contraction. At a fixed matrix x the initial matrix x0 has |x0|<=2|x|, |x0-x|<=6 L tau |x|. Also

    |DF_tau(x)-DF(x)|<=12 L tau |x|.

The origin with zero derivative stays fixed; set F_tau(0)=0. The Hamilton-Jacobi equation and the preserved unit norm give

    |k(x,DF_tau(x))-k(x,DF(x))|<=24 L² tau |x|²,

so integration in time proves

    |F_tau(x)-F(x)-tau k(x,DF(x))|<=12 L² tau² |x|².           (7)

These estimates are uniform under the smooth approximations just used. The graph-flow formula supplies the energy and its derivative; no need to integrate a numerical trajectory for a certificate.

For hypothetical beta_*=-b<0, take F_j in the normalized class and actual centered compatible gradients X_j with int |X_j|²=1, int F_j(X_j)->-b. Write m=2b and p_j=DF_j(X_j). The Hilbert descent argument in Section 2 gives int X_j:p_j->-m. Apply beta_* to the transformed energy on the ORIGINAL compatible field X_j, not to a claimed compatible constitutive pushforward. By (7), for every family K_j satisfying the joint RC conditions with a common global derivative-Lipschitz bound and bounded budgets gamma_j,

    liminf_j [int K_j(X_j,Cp_j)+m gamma_j]>=0.                 (8)

The generators are allowed to depend on the energy and the field; the uniform bounds are essential to take first j->infinity, then tau->0. This is an amplitude-free family of tests using the exact original beta normalization.

Moreover, suppose an actual input field of energy one has a generator (6) with int k(X,p)<=-d<0. Since |k(X,p)|<=L |X|², d<=L. Taking tau=d/(24 L²) in (7) gives an admissible normalized energy on that SAME field with gap smaller by at least

    d²/(48 L²).                                               (9)

Thus finding a uniform strict violation of (8) for genuine universal near-extremizers, at any fixed hypothetical b>0, would give a quantitative contradiction, rather than merely a finite-moment obstruction. The search for such a K is still open.

### 6.3 A saturated direct comparison without the earlier factor-two budget

Let J=[[0,-1],[1,0]], so C p=J p J^T and J C p=p J. For any normalized planar RC energy G, real t, and orthogonal two-dimensional matrix O, take

    K(X,Y)=G((X+t JY)O).

This is globally RC on 4x2: a stacked rank-one increment (a tensor n, b tensor n) maps to (a+t Jb) tensor (O^T n). Its Hessian bound is at most 1+t². On both normalization-boundary directions (v,+/- C v) its linear argument has squared norm (1+t²)|v|², since right multiplication by J is skew and orthogonal in Frobenius coordinates. Thus one can use gamma=(1+t²)/2, rather than the generic gamma=N. Equation (8) gives

    liminf_j [int G_j((X_j+t p_j J)O)+b(1+t²)]>=0.             (10)

Here G_j may be ANY sequence of unit-Hessian RC energies, including F_j itself. Bounded adaptive t,O are also permitted with the same argument. At t=0, O=I, G_j=F_j the inequality is exactly saturated, unlike the earlier estimate with budget 2b in (5). This opens a direct nonlinear joint comparison at the correct constant. It does not show that a strict improvement is possible. The first variation in t for G=F, O=I vanishes pointwise, since p:(p J)=0. The next attack needs a different adaptive joint test or genuine spatial/constitutive information at second or higher order. Do not optimize t alone without such a mechanism.

For comparison, the self-Cayley generator of Section 4 can be built from F if Lip DF<1. Put Y=X+C p and g(Y)=F(X)+det p. This is the R17 cofactor shear at unit parameter, invertible under the strict bound, with Dg=p and RC preserved. Writing S=D²g, the exact identity

    (I-CS)^T (I-H²)(I-CS)= I-CS-SC

shows that S<=I/2 on the conformal block and S>=-I/2 on the anticonformal block (the signs follow by evaluating on the corresponding eigenspaces of C). Therefore phi=g-det/2 is a legitimate saddle RC generator in Section 4. Its cost is exactly

    phi(X+C p)=F(X)-(X:p)/2+(det p-det X)/2.

This is zero at the formal universal critical budget of Section 2, not negative. The derivative bound of phi may diverge as Lip DF approaches one; do not assume uniform invertibility in a universal near-extremizer limit. This observation explains why the most immediate self-generated nonlinear test does not itself close the problem.

## 7. A global positive stress-rigidity theorem for the complete fixed-energy critical route

The preceding joint tests must use actual stress compatibility, not just formal moment data. Here we prove an independent coercivity theorem which works without nonnegativity of the energy, QC or PC, and does not merely exclude a fixed finite support. It extends the minimum-set rigidity of R23 to entire constant-stress level sets. The hypothesis of a fixed smooth energy is available without restricting possible counterexamples by R20.

### 7.1 Constant-stress sets are incompatible

Let H be C² and uniformly strongly RC, meaning H-(m/2)|.|² is RC for m>0. For any q the set of X with DH(X)=q contains no distinct rank-one-connected pair: along such a segment strong rank-one monotonicity of DH gives a strictly positive derivative difference.

There is also no T4 configuration in a constant-stress set. Subtract the affine function q:X and suppose the four points X_i=P_i+kappa_i R_i, kappa_i>1, with rank-one increments R_i, P_(i+1)=P_i+R_i, P_5=P_1, satisfy DH(X_i)=0 for the subtracted energy. For f_i(t)=H(P_i+t R_i) (with H now affine-normalized), f_i'(kappa_i)=0 and f_i''>=m |R_i|². Thus for 0<=t<=1,

    f_i'(t)<=-m(kappa_i-t)|R_i|²,

and hence

    H(P_(i+1))-H(P_i)<=-m(kappa_i-1/2)|R_i|².

Summing around the nontrivial cycle contradicts telescoping. This is an exclusion of T4s in a derivative-level set even if its points have different energy values.

Use the planar result of Faraco–Székelyhidi, *Tartar's conjecture and localization of the quasiconvex hull in R2x2*, Acta Math. 200 (2008), 279–305, [DOI](https://doi.org/10.1007/s11511-008-0028-1), Corollary 2 and its proof: a compact set with neither rank-one connections nor T4 has rank-one convex hull equal to itself and supports only Dirac homogeneous gradient Young measures. Every compact subset of a constant-stress set has these properties. For any disjoint compact partition of such a subset, the two individual hulls and their union hull are the original sets. The planar incompatibility theorem of Kirchheim–Székelyhidi (as in R23) then gives incompatibility for nonhomogeneous gradient Young measures as well. We use Ball–James, *Incompatible sets of gradients and metastability*, Arch. Ration. Mech. Anal. 218 (2015), 1363–1416, [DOI](https://doi.org/10.1007/s00205-015-0883-9), Theorem 14: on the unit cube, the integral of 1+|Dy|² on a fixed sufficiently small transition neighborhood's complement is at least a positive constant times the smaller of the two phase measures. These are the same published planar rigidity and transition-layer inputs as R23, but applied to derivative-level rather than minimum sets.

### 7.2 Relative stress coercivity, including vanishing variance and determinant gauges

**Theorem.** Fix a C² globally strongly RC energy H with m>0 and global Hessian bound M, and a radius R>0. There exists c(H,R)>0 such that for EVERY compatible affine-periodic field X=A+Du with |X|<=R almost everywhere and every q in R^(2x2), lambda in R,

    int |DH(X)-q-lambda C X|² >= c(H,R) int |Du|².            (11)

The constant is independent of q, lambda, the field, its number of values, the oscillation scale and the absolute variance. No positivity, QC or PC hypothesis is needed.

Proof. Write E=int |X-A|². If E=0 the claim is immediate. Suppose a countersequence X_j=A_j+U_j, E_j>0 has ratio tending to zero for q_j,lambda_j. Centering the residual and using Lip DH<=M gives

    ||DH(X_j)-mean DH(X_j)||_2<=M sqrt(E_j),
    ||DH(X_j)-q_j-lambda_j C X_j||_2
        >= (|lambda_j|-M)_+ sqrt(E_j).

Thus lambda_j is bounded. Replace q_j by the optimal mean of DH(X_j)-lambda_j C X_j, which is bounded since the range is fixed. Put h_j=H-lambda_j det-q_j:X; subtracting these null/affine terms leaves the strong RC margin. Pass to a subsequence with q_j,lambda_j convergent, so h_j converges in C² on compact sets to h. Write r_j=Dh_j(X_j); then ||r_j||²=o(E_j).

The spatial laws of the bounded compatible gradients have a weak-* limit nu, a homogeneous gradient Young measure by periodic replication and closedness on compact supports (as in R23). Since E_j<=R², the residual integrals tend to zero. Uniform convergence of Dh_j implies support(nu) is in the compact set K={Dh=0} intersect closed B_R. Section 7.1 makes nu a Dirac mass at A_*. Hence A_j->A_*, X_j->A_* in L², E_j->0, and Dh(A_*)=0. Absolute compactness alone is not enough; we must keep the following estimates relative to E_j.

The planar Finsler lemma from R17 applied to D²h(A_*) yields a constant nonzero eta and a kappa>0 with D²h(A_*)+eta C>=2 kappa I (if eta initially vanishes, take a small nonzero perturbation and decrease kappa). By C² convergence and continuity there is rho>0 so the same bound with kappa I holds for D²h_j+eta C near A_* on B_(3rho), and for h. For sufficiently large j, on the local set |U_j|<=rho, integration of this Hessian along the segment from A_j to X_j gives

    (Dh_j(X_j)-Dh_j(A_j)):U_j+2 eta det U_j
        >= kappa |U_j|².                                     (12)

In particular every distinct Y in K near A_* satisfies 2 eta det(Y-A_*)>=kappa |Y-A_*|². For other Y in K, det(Y-A_*) cannot vanish by the rank-one exclusion. Partition K into K_+ consisting of A_* and the points with eta det(Y-A_*)>0, and K_- with eta det(Y-A_*)<0. The near-point inequality keeps K_- separated from A_*, so both sets are compact and disjoint. If nonempty, they are incompatible by Section 7.1.

Take sufficiently small fixed epsilon neighborhoods of these sets, with epsilon also chosen for the Ball–James estimate. The transition region within B_R has a positive lower bound for |Dh| off both neighborhoods. Since Dh_j converges uniformly there, its measure is o(E_j). The K_+ phase tends to measure one by X_j->A_*. The transition-layer estimate and bounded amplitudes imply the K_- phase has measure o(E_j) as well. If K_- is empty, the transition estimate by positive |Dh| off K_+ alone suffices.

On the remote good set |U_j|>rho near K_+, compactness of the part of K_+ a positive distance from A_* ensures 2 eta det U_j>=kappa_1 |U_j|² for some fixed kappa_1>0; shrink epsilon first if needed. The remote bad set has measure o(E_j), bounded determinant, and variance o(E_j).

Integrate (12) on the local set. The integral of r_j:U_j there is o(E_j) by Cauchy-Schwarz. Also Dh_j(A_j)->0 and, because int U_j=0,

    |int_(local) U_j|=|int_(remote) U_j|<=E_j/rho.

Thus the local integral of Dh_j(A_j):U_j is o(E_j), without a required rate of C² convergence. Integrating the remote estimates and using the exact periodic determinant identity int det U_j=0 now yields

    0 >= min(kappa,kappa_1) E_j-o(E_j),

a contradiction. This proves (11).

### 7.3 Remove amplitude and base restrictions for the ungauged quadratic-tail class

Suppose additionally that H equals (a/2)|X|² plus a constant outside a ball B_r, with a>0. Write DH(X)=a X+v(X) where v is bounded, supported in B_r, and B=Sup |v|. Then there exists c(H)>0 such that for EVERY affine base A and periodic W1,2 gradient,

    int |DH(A+Du)-mean DH(A+Du)|² >= c(H) int |Du|².         (13)

For a large base |A|>r, v(A+U) can be nonzero only where |U|>=|A|-r. Hence its centered L² norm is at most B sqrt(E)/(|A|-r). The centered linear stress aU has norm a sqrt(E), so (13) with c=a²/4 holds when |A|-r>=2B/a (increase the base cutoff slightly if B=0).

For bases in a fixed bounded ball, suppose a countersequence has centered stress norm squared o(E). Put q=mean DH(X)=a A+mean v(X), which is uniformly bounded. For a fixed sufficiently large R_0, outside B_(R_0) the residual DH(X)-q=a X-q has norm at least (a/2)|X|. Thus int_(|X|>R_0)|X|²=o(E).

Apply ordinary periodic Lipschitz truncation to U=Du at a fixed sufficiently large threshold T (take T/2>R_0+sup |A|). We give the relative estimate explicitly. The set where the Hardy–Littlewood maximal function of |U| exceeds T has measure <=C/T² times int_(|U|>T/2)|U|²: split the input into the part bounded by T/2 and its complement and apply the L² maximal estimate. On the good set the Sobolev pointwise Lipschitz estimate bounds u's Lipschitz constant by C T. Coordinatewise Lipschitz extension on the torus preserves u and its derivative on that set and gives a periodic Lipschitz u_T with ||Du_T||_infty<=C T. If the good set is empty, choose a constant extension. On the bad set the squared error is bounded by the integral of |U|² there plus C T² times the set measure. Splitting |U| at T/2 bounds this by C int_(|U|>T/2)|U|². Consequently ||Du_T-Du||²=o(E). The high-gradient tail estimate just established justifies the last equality.

The truncated field X_T=A+Du_T has a uniform amplitude bound, its variance is (1+o(1))E, and by Lipschitz continuity of DH its residual from the same q still has norm squared o(E). This contradicts (11) at lambda=0. Thus (13) holds globally. Equation (11) includes arbitrary determinant gauges on bounded ranges; (13) makes no assertion for determinant gauges at unbounded amplitudes where the quadratic tail after gauging may be singular.

### 7.4 Consequence for the unrestricted critical-state problem

By R20, any strict finite-valued planar Morrey counterexample would give ONE fixed smooth QC uniformly strongly RC H with positive quadratic exterior, bounded-base bounded-amplitude actual fields X_j=A_j+U_j, E_j>0, and J_H/E_j->0. In particular R20's outer-stress argument for s_j=DH(X_j)-DH(A_j) gives

    ||P_grad s_j||_2+|mean s_j|=o(sqrt(E_j)),

while (11) gives

    inf_lambda ||s_j-lambda C U_j||_2² >= c(H,R) E_j.

Let V_j=C P_sol s_j, where P_sol is the zero-mean rowwise solenoidal Fourier projection. Then V_j is an ACTUAL compatible mean-zero planar gradient, and ||V_j-C s_j||_2=o(sqrt(E_j)). Therefore, eventually,

    inf_lambda ||V_j-lambda U_j||² >= c(H,R) E_j/4.

Also ||V_j||²<=M² E_j. The 2x2 Gram matrix of U_j,V_j as Hilbert-space fields, divided by E_j, has determinant at least c(H,R)/4 and trace at most 1+M². Consequently for every real alpha,beta,

    ||alpha U_j+beta V_j||² >= [c(H,R)/(4(1+M²))]
                               (alpha²+beta²) E_j.            (14)

This is a nondegeneracy estimate on a genuinely compatible gradient/stress pair, including vanishing absolute variance, no PC premise and no restriction of the original counterexample class. A pure determinant stress (or zero stabilized stress) is impossible in the entire fixed-energy critical regime. It controls scalar mixing of the two planar fields, not all row remixes or chart regularity.

One exact sufficient remaining statement for the fixed-energy route is that every such QC critical near-equality sequence must asymptotically collapse to a constant plus a determinant stress, in the relative L² norm. This would contradict (11) and prove Morrey by R20. No such collapse theorem is proved here. Alternatively, exploit the nondegenerate compatible stress in a strict normalized Hamiltonian descent or a different universal rigidity proof. Equations (8)–(10) concern universal beta near-extremizers with possibly changing normalized energies. The constants of (11)–(14) depend on a fixed H (and R where indicated); do NOT silently transfer them to arbitrary varying C11 universal near-extremizers. Bridging those regimes or proving a direct all-energy contraction is still open.

## 8. Verification and disposition of the 25 November extension

Five exact SymPy symbolic checks were executed for J C p=p J, the (1+t²) squared directional norm, det(X+C p)=det X+X:p+det p, the self-Cayley cost identity, and the finite-time gain d²/(48L²). No numerical search or full finite certificate was executed. These checks do not establish the analytic characteristic, compactness, transition-layer or truncation arguments independently. The positive results are the full joint normalization-preserving test (P18) and fixed-energy stress coercivity (P19), not a new stronger beta numerical bound, uniform finite exact cutoff, genuine planar counterexample, or proof of beta_*=0. No Lean files or formal assumptions changed. No priority claim is made.

