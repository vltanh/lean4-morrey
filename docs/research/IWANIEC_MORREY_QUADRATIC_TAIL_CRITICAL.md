# Quadratic-tail critical states: remove amplitude concentration by verified scalar projections

24 November 2026. Attack the concentration gate preceding the [full stationary lift](IWANIEC_MORREY_FULL_STATIONARY_LIFT.md), not another tolerance or vertex-count ladder.

**Principal result.** Any hypothetical unrestricted planar Morrey counterexample yields ONE fixed smooth, globally QC, uniformly strongly RC energy H with an exactly quadratic exterior, and a sequence of genuine bounded-amplitude periodic gradients at bounded bases, whose relative Jensen gaps tend to zero. The rank-one ellipticity margin and the amplitude bounds are fixed across the sequence. Both the planar gradients and their full six-row stationary lifts can be represented by actual uniformly bounded gradients up to an L2 error o(sqrt(variance)). All lifted minors and smooth normalized QC tests therefore pass to the relative limit, with no uncontrolled fourth-moment concentration. This follows from the already verified Iwaniec scalar projection theorem, not an assumed vector-valued projection theorem.

This closes the HIGH-AMPLITUDE concentration issue for the full-lift approach, in the relative sense needed for Jensen margins. It does NOT prove that the absolute variance of a bounded near-equality sequence stays bounded away from zero. In particular, do not subsequently divide the matrix argument by sqrt(variance) and assume the same amplitude bound. The argument instead keeps all error estimates relative to variance, including the inner-stress projection. The exact remaining gate is rigidity of these bounded critical sequences. No unrestricted proof, negative planar pair, new Lean theorem, independent mathematical review, or publication-priority claim. The exact arithmetic companion was actually executed.

## 1. Reduce any strict counterexample to one fixed critical energy

Let F be a finite globally RC function on real 2x2 matrices with a strict negative Jensen gap on a bounded periodic Lipschitz gradient at some affine base. Smooth by positive convolution in matrix space; on the bounded witness range the functions converge uniformly, so a sufficiently small smoothing retains the strict gap. Choose radii 0<r<R containing that range and the base strictly inside B_r. Shift the smoothed energy by a constant to make it >=2 on B_R.

Inside B_R take its smooth convex maximum with the barrier
    a(|X|²-r²), a>0,
and outside B_R use only the barrier. Here a smooth maximum is (s+t+chi(s-t))/2, where chi is the convolution of absolute value with a smooth even probability kernel supported in (-1,1). It is smooth, convex and nondecreasing in each argument, agrees with max(s,t) when |s-t|>=1, and preserves rank-one line convexity. Choose a so large that the barrier strictly dominates the shifted smooth energy by more than one on the outer sphere. The gluing therefore agrees on a collar, and is smooth and globally RC. On B_r it equals the shifted original smooth energy exactly. Thus we obtain a smooth globally RC F0 with a strict negative witness and the form
    F0(X)=lambda0 |X|²/2 + c0 + V(X),
where lambda0>0 and V is smooth compactly supported. In particular Lip DF0 is finite. This is an exact witness-preserving reduction; no statement of density at an unknown negative margin is needed.

For any globally C11 energy define
    beta(F0)=inf J_F0(A,u)/E(u),
    E(u)=int |Du|²>0,
over all affine bases and nonconstant periodic Lipschitz test maps on the area-one torus. The Hessian bound and mean-zero gradient imply beta(F0) is finite. By the strict witness beta(F0)=-b<0. Set
    H=F0+b|X|².
Then H is globally QC by the definition of beta(F0), and H-(m/2)|X|² is RC with m=2b>0. H is smooth and globally Hessian bounded, with exactly the same compact perturbation V, exterior coefficient lambda=lambda0+2b, and
    inf J_H(A,u)/E(u)=0.
Choose a sequence A_j,u_j with E_j>0 and j_j=J_H(A_j,u_j) satisfying j_j/E_j->0. This is a near-minimizing sequence for ONE fixed H, not a sequence of energies whose smoothness modulus must be controlled uniformly.

Conversely if Morrey holds then every such H with LH margin m satisfies J_H>=m E/2, by applying Morrey to H-(m/2)|X|². Thus proving strong QC of every smooth QC, uniformly strongly RC energy with a quadratic exterior would solve unrestricted planar Morrey. A bound depending on H individually suffices. The remaining analysis can be done with that fixed H.

## 2. Exact quantitative clipping theorem

Let Q be the area-one square torus, X=A+Du for a periodic Lipschitz u with affine base A, and let
    F(X)=lambda |X|²/2 + c + V(X),
    lambda>0, supp V subset B_r, |V|<=B.
The following argument does not need RC or QC of F.

Choose R>r with each Euclidean row norm of A <=R and B/(R-r)²<=lambda/4. Apply the pinned verified [Agazzi.lemma4 and lemma4_exists](https://github.com/vltanh/lean4-iwaniec/blob/e4922fa6bfdadbe5fe22231c91b69044dac89bab/Agazzi/Proof/ScalarProjection/Main.lean) separately to each of the two scalar components, with K the closed Euclidean disk of radius R and p the corresponding affine row. The output Y is a genuine Lipschitz periodic gradient with the SAME affine base. The lemma gives for each row i:
    |Y_i|<=R,
    Y_i=X_i or |Y_i|=R a.e.,
    int Y_i·(X_i-Y_i)>=0.
These are properties of the scalar projection in potential space; we do not assume that the pointwise radial clipping of a gradient is compatible.

Summing the signs and expanding the quadratic norm yields
    int |Y|² <= int |X|² - int |Y-X|².                      (1)
On the set D where the matrices differ, at least one output row is on the circle, so |Y|>=R and V(Y)=0. If V(X) is nonzero there, |X|<=r, and hence |Y-X|>=R-r. Thus everywhere,
    V(Y)-V(X) <= B |Y-X|²/(R-r)².
It is important that we account for changes of rows of SMALL original norm: the projection theorem does not assert that it changes only rows exceeding R. The positive penalty for changes inside the compact nonlinear core is paid by (1).

**Theorem A (fixed-radius energy-improving compatible clipping).**
$$
\boxed{
\int F(Y)-F(A)
 \le \int F(X)-F(A)-\frac{\lambda}{4}\|Y-X\|_2^2 .
}
\tag{2}
$$
Indeed the quadratic cost decreases by at least lambda/2 times the squared error, and the possible core cost increases by at most lambda/4 times that error. Also
    E_Y<=E_X-||Y-X||²,
because both mean matrices are A. QED.

**First consequence: exact amplitude cutoff for negative relative margins of a fixed energy.** If J_F(A,u)<0, the clipped witness still has negative gap, nonzero variance, and no larger relative Jensen gap (negative numerator has decreased, positive denominator has not increased). The original magnitude of the negative gap is irrelevant to the chosen R. Bases are bounded as well. At a base outside B_r, if |A|-r>=sqrt(4B/lambda)>0, then
    J_F(A,u)>= [lambda/2-B/(|A|-r)²] E_X>=lambda E_X/4,
since a nonzero V(X) requires |X-A|>=|A|-r. If B=0 the energy is quadratic and has no negative witnesses. Choose a slightly larger base radius to avoid equality at the boundary. Thus for any negative beta(F), its exact infimum is unchanged by imposing a fixed explicit bound on base and all gradient amplitudes, depending only on lambda,r,B. This is not a bound on oscillation complexity.

**Second consequence: bounded critical sequences for H of Section 1.** The same base estimate applies to H. Eventually all A_j belong to a fixed compact ball. Choose R once so that it contains all those affine row norms and satisfies the condition of Theorem A. Since H is QC, the output gap is nonnegative. Consequently, with j_j=J_H(X_j),
    ||Y_j-X_j||² <=4 j_j/lambda,
    ||(Y_j-A_j)-(X_j-A_j)||_2/sqrt(E_j)->0.
The new variance E'_j satisfies E'_j/E_j->1, by the triangle inequality, and the new gap j'_j is in [0,j_j]. Thus E'_j>0 eventually and j'_j/E'_j->0. Every Y_j is an actual gradient, with |Y_j|<=sqrt(2)R. All these constants are fixed independently of j. This proves the bounded critical-state assertion, conditional only on existence of a strict Morrey counterexample.

We henceforth rename the clipped perturbation gradient U_j=Y_j-A_j, its variance E_j, and its gap j_j. Write L for a common finite bound on |U_j|, delta_j=j_j/E_j->0, and M=Sup ||D²H||. In particular E_j<=L². All higher moments have the RELATIVE bound
    int |U_j|^p <= L^(p-2) E_j, p>=2.
There is no high-amplitude concentration of |U_j|^p relative to variance. Absolute E_j may tend to zero, for example after dilution of a near-optimal test. We do not assume otherwise.

## 3. Relative stationarity for the fixed bounded critical sequence

Recenter H separately at A_j, without changing any curvature bound:
    h_j(U)=H(A_j+U)-H(A_j)-DH(A_j):U,
    p_j=Dh_j(U_j),
    T_j=h_j(U_j)I-U_j^T p_j.
Then h_j(0)=Dh_j(0)=0, h_j is globally QC and has the same strong LH margin m; |p_j|<=M |U_j|, |T_j|<=2M |U_j|². In particular
    ||p_j||_2<=M sqrt(E_j), ||T_j||_2<=2ML sqrt(E_j),
    ||T_j||_infty<=2ML².

Use P0, P, Q for the orthogonal L2 projections onto constants, zero-mean compatible gradients, and zero-mean rowwise solenoidal fields. These are the Fourier projections already used in [cofactor duality](IWANIEC_MORREY_COFACTOR_DUALITY.md). For a matrix with two rows, C denotes cofactor, and J=[[0,-1],[1,0]]. C Q is compatible and Q T times J is compatible. We use Q here only as a projection symbol in the rest of this note.

### 3.1 Outer stress

The functional Z -> int h_j(Z)-h_j(mean Z) on the Hilbert space of all affine-base compatible L2 fields is nonnegative by QC and quadratic-growth approximation. Its gradient has Lipschitz constant at most 2M. Apply the Hilbert descent lemma at U_j: the squared gradient norm is at most 4M j_j. The two orthogonal components of that gradient are P p_j and P0 p_j, since the affine base is zero. Thus
    ||P p_j||²+|mean p_j|²<=4M j_j.
In particular the difference from the compatible stress lift C Q p_j is O(sqrt(delta_j E_j)) in L2.

### 3.2 Inner stress and mean

The domain-variation bound of [full stationary lift](IWANIEC_MORREY_FULL_STATIONARY_LIFT.md), Section 4, holds for h_j:
    |int T_j:Dxi|<=12 sqrt(M E_j j_j) ||Dxi||_infty
for every smooth periodic vector xi (using a Frobenius derivative norm only enlarges the bound). Briefly, transport by x->x+t xi(x), normalize ||Dxi||_infty<=1, and use QC nonnegativity for |t|<=1/4. The change-of-variables formula has first derivative int T_j:Dxi and second derivative bounded by 64 M E_j. Taylor in both signs and t=sqrt(j_j/(32 M E_j))<=1/8 gives the result; zero gap follows by a limit. This does not require a bound on derivatives of U_j.

Also int h_j(U_j B)>=0 for every constant matrix B (domain-linear transform for invertible B, then continuity). Its gradient as a function of B has Lipschitz constant <=M E_j. Descent at B=I gives
    |int U_j^T p_j|²<=2 M E_j j_j,
    |mean T_j|<=sqrt(2) j_j+sqrt(2 M E_j j_j).
In particular |mean T_j|/sqrt(E_j)->0 because E_j is bounded above. This mean estimate has the extra variance factor needed when E_j is small.

### 3.3 Relative projection estimate without assuming a lower variance bound

We strengthen the absolute inner-stress projection argument in the previous note. For any periodic vector xi with ||Dxi||_2<=sqrt(E_j) and lambda_cut>=1, ordinary Lipschitz truncation gives a periodic Lipschitz xi_cut satisfying
    ||Dxi_cut||_infty<=C lambda_cut,
    ||Dxi-Dxi_cut||_1<=C E_j/lambda_cut.
Here and below C may depend on the dimension or fixed H and L, but not on j or E_j. To verify the second bound with the correct scaling, take the bad set where the maximal function of |Dxi| exceeds lambda_cut. Its measure is <=C E_j/lambda_cut² by the maximal-function L2 estimate. The Sobolev pointwise Lipschitz estimate on the good set and coordinatewise McShane extension give the bounded-gradient truncation, with derivatives unchanged a.e. on the good set. Cauchy-Schwarz bounds the integral of the original derivative on the bad set by C E_j/lambda_cut; the bounded extension contributes the same bound. If the good set is empty choose a constant extension, using the same bound on the bad-set measure. This argument works on the periodic torus. Smooth periodic convolution permits application of the inner variation estimate to xi_cut.

It follows by the uniform bound on T_j that
    |int T_j:Dxi|
       <= C[lambda_cut sqrt(M E_j j_j)+||T_j||_infty E_j/lambda_cut].
Take the supremum over these xi, divide by E_j and choose lambda_cut=delta_j^(-1/4) when 0<delta_j<=1. For delta_j=0 take lambda_cut->infty. We obtain
$$
\boxed{\frac{\|P T_j\|_2}{\sqrt{E_j}}\le C(H,L)\delta_j^{1/4}.}
\tag{3}
$$
No positive lower bound on E_j was used. Together with the mean estimate, (3) gives the full lift
    W_j=[U_j; C p_j; T_j J]
and an actual zero-mean compatible six-row gradient
    W_j^c=[U_j; C Q p_j; (Q T_j) J]
with
    ||W_j-W_j^c||_2<=C(H,L) delta_j^(1/4) sqrt(E_j)
eventually (for delta_j<=1). The first block U_j is kept exactly. The squared norm of W_j, and that of W_j^c, are bounded by C E_j. This proves the relative full-stationary compatibility statement, including the previously missing energy-momentum block.

## 4. Make the compatible stress lift itself uniformly bounded

The orthogonal Fourier projection of a bounded field is not automatically bounded. This is another place where the verified scalar projection can be used, without an unjustified L-infinity estimate.

**Lemma B (compatible bounded replacement near a bounded field).** Let f be a scalar-row vector field bounded in norm by B1, and let v be a zero-mean compatible scalar gradient in L2 with ||v-f||_2<=e. Then for any R1>=2B1 with R1>0 there exists a zero-mean compatible Lipschitz gradient w with |w|<=R1 and ||w-f||_2<=3e+epsilon for every epsilon>0.

Proof: first approximate v by smooth periodic gradients in L2 with error arbitrarily small. Apply the verified disk projection to that smooth row (denoted v again). Let D be where w differs from v. On D, |w|=R1. The global sign in the lemma gives
    R1² |D| + ||w-v||² <= ||v||_(L2(D))².
Since |f|<=R1/2,
    R1 sqrt(|D|)<=||v||_(L2(D))<= (R1/2)sqrt(|D|)+||v-f||_2.
Thus R1 sqrt(|D|)<=2||v-f||_2, and ||v||_(L2(D))<=2||v-f||_2. Hence ||w-v||_2<=2||v-f||_2 and the triangle inequality gives ||w-f||_2<=3||v-f||_2. The arbitrarily small smoothing error accounts for epsilon. If e=0 and f=v is already a bounded compatible row, its periodic potential is Lipschitz and can be retained. QED.

Apply this independently to the four stress rows of W_j^c, targeting the corresponding bounded rows of W_j. Keep U_j unchanged. The fixed row radius R1 can be twice the largest pointwise row bound of the stresses (or larger). Choose the smoothing errors o(sqrt(E_j)), for instance <=sqrt(E_j) delta_j^(1/4) when delta_j>0, and retain exact compatible rows when the error is zero. We obtain a genuine compatible six-row gradient Z_j with all rows uniformly bounded and
$$
\boxed{
\|Z_j-W_j\|_2=o(\sqrt{E_j}),\qquad
\|Z_j\|_2+\|W_j\|_2\le C(H,L)\sqrt{E_j}.
}
\tag{4}
$$
This is stronger than merely distributional stationarity of the lift. It controls all six rows simultaneously by actual uniformly bounded compatible potentials.

In particular every 2x2 minor of W_j has mean o(E_j): the corresponding minor of Z_j has mean zero by the null Lagrangian, and the determinant bilinear difference is controlled by the two L2 norms times their difference. In matrix form the consequences include
    int det p_j = o(E_j),
    int U_j T_j^T = o(E_j),
    int [h_j(U_j) C p_j - det(p_j) U_j] = o(E_j),
    int det T_j = o(E_j).
For the third identity use C p p^T=(det p) I. The mixed minors with T_j J equal, up to a sign, the inner products of the corresponding rows. These identities are consequences of the actual simultaneous field construction, not independent moment assumptions.

For every C² QC K on 6x2, write k0(Z)=K(Z)-K(0)-DK(0):Z. On the fixed compact lifted range its Hessian is bounded, so
    |int k0(W_j)-int k0(Z_j)|=o(E_j)
by (4) and the C11 remainder estimate on that range. Since Z_j is an actual compatible zero-mean gradient, int k0(Z_j)>=0. Thus the full lifted relative Bregman gap has nonnegative liminf for EVERY such higher-dimensional QC test K. The same conclusion holds uniformly over tests with a common local Hessian bound. For merely continuous tests do not divide a fixed uniform approximation error by a possibly vanishing E_j. We do not assert the corresponding inequality for every RC K; this would need another argument.

## 5. Exclude amplitude collapse to zero and obtain a fixed compact weighted critical state

There is also a nontrivial lower-amplitude conclusion, even if E_j tends to zero. Because H is a FIXED smooth energy and the A_j stay in a compact set, its Hessian is uniformly continuous on the relevant matrix range. Choose r0>0 so that for every such A and |U|<=r0,
    |h_A(U)-D²H(A)[U,U]/2|<=m|U|²/8,
where h_A is the recentered energy. Globally that remainder difference is bounded by M |U|². For every compatible periodic U, the constant quadratic form D²H(A) has rank-one lower bound m and hence, by Parseval,
    int D²H(A)[U,U]/2 >= m E/2.
It follows that
    j_j >= (3m/8) E_j - M int_(|U_j|>r0) |U_j|².
For j_j/E_j<=m/8 this gives
$$
\boxed{
\frac{\int_{|U_j|>r_0}|U_j|^2}{E_j}\ \ge\ \frac{m}{4M}>0.
}
\tag{5}
$$
Together with the fixed upper amplitude bound, a definite fraction of the relative variance belongs to a fixed compact annulus. It cannot all migrate to arbitrarily small or arbitrarily large matrix amplitudes.

One can retain all the relative information on a fixed compact polar state space: define probability measures
    mu_j=(r=|U_j|, theta=U_j/|U_j|)# [(|U_j|²/E_j) dx]
on [0,L] x S³, omitting zero-weight points. Pass to a subsequence with A_j->A* and mu_j weak-* convergent to mu. By (5) its mass on the closed annulus r>=r0 is at least m/(4M). Define
    h_A(r theta)/r²,
    W_A(r,theta)=[theta; C(Dh_A(r theta)/r); (T_A(r theta)/r)J],
    T_A(U)=h_A(U)I-U^T Dh_A(U).
These functions extend continuously to r=0, with the first given by D²H(A)[theta,theta]/2 and the last two lifted blocks by C(D²H(A) theta) and zero, respectively. Uniform continuity follows from the fixed smooth H on a compact base/range set. Hence the limit mu has:
- integral of h_A*(r theta)/r² equal to zero;
- integral of every 2x2 minor of W_A* equal to zero, by (4);
- nonnegative integral of k0(r W_A*)/r² for every C² QC K, with the natural quadratic limit at r=0.

This is an exact compact record of a necessary critical-state structure, not a claim that arbitrary probability measures satisfying those constraints come from compatible gradients. Replacing the actual sequences by unconstrained moment laws would lose the spatial compatibility that is central to the problem. In particular the old minor-only nonlaminate obstructions are not bypassed by declaring a weighted law compatible.

The fixed annulus and fixed H are useful for the next rigidity attack, which can use all lifted gradients without an uncontrolled amplitude tail. The open possibility of vanishing absolute variance has been handled in the estimates, not excluded.

## 6. Independent optional linear-projection route

There is also a more elementary smoothing of the outer stress equation, useful if one wants moment estimates without applying the disk clipping. Write DH(X)=lambda X+g(X), g=DV bounded and Lipschitz. The outer stationarity estimate implies that
    U_j^lin=-lambda^(-1) P [g(A_j+U_j)-g(A_j)]
differs from U_j in L2 by O(sqrt(j_j)), even before clipping. It is an actual compatible gradient, preserves the relative gap up to o(E_j) by the common Hessian bound, and has all finite relative higher moments. For clarity the explicit projection bound follows from the pinned verified torus Beurling bound [NormTorus.lean](https://github.com/vltanh/lean4-iwaniec/blob/e4922fa6bfdadbe5fe22231c91b69044dac89bab/Agazzi/Corollary2/NormTorus.lean), torusBeurlingPowNorm_one_le. On a nonzero Fourier frequency k, the row Helmholtz projection is (identity plus reflection across k)/2. In complex coordinates the reflection is multiplication by (k1+i k2)^2/|k|² after complex conjugation; this is the inverse Beurling operator applied to the conjugated function. Subtract the mean and use the torus bound p-1 for p>=2 and ||v-mean v||p<=2||v||p. Each scalar-row projection has norm <=p, and the two-row matrix projection has norm <=2p.

If |g|<=B1 and Lip g<=L1, then
    int |U_j^lin|^p <= (2p/lambda)^p (2B1)^(p-2) L1² E_j.
When B1>0, write D=4B1/lambda and C1=L1²/(4B1²). The right side is C1 E_j (Dp)^p. Expanding exp(|U|/(4D))-1-|U|/(4D) and using k!>=(k/e)^k and e<3 gives a bounded exponential moment relative to E_j. When B1=0 the energy is convex quadratic and the critical sequence cannot exist. This route gives relative higher moments but not L-infinity bounds; Sections 2 and 4 give the stronger bounded result via the scalar projection.


## 6.1 First genuinely energy-based restriction after the concentration gate

The preceding compatibility identities alone use only near stationarity. We can now impose a stronger stability condition using QC near equality itself, with no derivative bounds on the spatial gradients.

**Theorem C (relative second variation).** Let H and the bounded critical sequences from Sections 1--4 be fixed. Suppose V_j is any zero-mean compatible periodic gradient with a common L-infinity bound B1 and ||V_j||_2²<=B2 E_j. Write delta_j=j_j/E_j. Then
$
\boxed{
\int D²H(A_j+U_j)[V_j,V_j]\ \ge\ -C(H,B_1,B_2)\delta_j^{1/3} E_j
}
\tag{6}
$
eventually when delta_j<=1. For zero gap the right side is zero. No stationary solution or exact attainment is assumed.

Indeed, QC of h_j gives
    int h_j(U_j+t V_j)>=0,   int h_j(U_j-t V_j)>=0
for every real t. Add both Taylor expansions about U_j. The linear terms cancel. With T0=Sup ||D³H|| finite by the quadratic exterior (or a local bound on the common compact range for |t|<=1), the two remainders have combined absolute value at most
    (T0/3)|t|³ int |V_j|³ <= (T0/3) B1 B2 |t|³ E_j.
It follows that
    int D²H(A_j+U_j)[V_j,V_j]/E_j >= -2 delta_j/t² -(T0/3) B1 B2 |t|.
Choose t=delta_j^(1/3) when delta_j>0; otherwise let t->0. This proves (6).

Apply (6) simultaneously to every constant row map D:R^6->R², with V_j=D Z_j, using the genuine bounded compatible lift from (4). For row maps of operator norm at most one the constants B1,B2 are uniform. Replacing Z_j by W_j changes the second variation by at most
    M ||D||² (||Z_j||_2+||W_j||_2)||Z_j-W_j||_2=o(E_j).
Consequently every compact weighted critical state mu of Section 5 must satisfy
$
\boxed{
\int D²H(A_*+r\theta)[D W_{A_*}(r,\theta),D W_{A_*}(r,\theta)]\,d\mu
\ \ge0\quad\text{for all }D\in\mathbb R^{2\times6}.
}
\tag{7}
$
In particular one common symmetric 12 by 12 quadratic matrix is positive semidefinite: its entries are obtained by taking the twelve elementary row maps as a basis in the left side of (7). Unlike individual pointwise LH tests this is a spatially derived second-variation restriction with all cross-row stress correlations. The conclusion does not depend on the number of active gradient values or on the original mesh.

There is also a whole nonlinear row-variation restriction for the fixed H: for every constant base B and row map D,
    liminf_j J_H(B,D Z_j)/E_j>=0.
Replacing D Z_j by D W_j in the Bregman integrand at B changes the relative integral by o(1), using the fixed compact range and (4). At the original base and row map selecting the first two rows the limit is zero. Thus the weighted critical state gives a nonnegative function of (B,D) with an exact zero at (A_*,D_first). This is a family of actual QC competitors, not an assumed extra rank-one Jensen inequality on arbitrary stress matrices.

The next rigidity argument should use (7), the nonzero annulus mass (5), the energy equality, and the actual compatibility from (4) together. At present no universal contradiction to (7) has been established. In particular do not infer that a finite-dimensional matrix positivity test on moment data decides unrestricted rigidity. The value of the new condition is as a necessary quantitative constraint arising from energy near-minimality, not a standalone sufficient test for gradient compatibility.

## 7. Status and next exact gate

The unrestricted problem is now reduced, for the critical-state route, to this single rigidity statement:

> For each fixed smooth globally QC, uniformly strongly RC H with a positive quadratic exterior, there are no bounded-base, uniformly bounded compatible gradients of nonzero variance whose relative Jensen gap tends to zero.

The reduction is exact in both directions; the preceding proofs remove the high-amplitude concentration obstacle and establish a quantitative bounded compatible six-row lift for any hypothetical violating sequence. The rigidity statement itself has NOT been proved. Stationarity alone cannot be assumed to force affine fields; the literature on stationary differential inclusions includes nontrivial Lipschitz solutions even for strongly quasiconvex systems (see https://doi.org/10.1007/s00526-021-01981-z). A successful next argument must exploit near equality of the QC energy as well as the compatibility and fixed curvature bounds. No additional exponent or mesh-size enumeration is needed to establish amplitude control.

Executed companion [quadratic_tail_exact.py](../../research/audit/quadratic_tail_exact.py), SHA-256 861d597854a9d6b657ebdbdda5f5a85d32eb7ca1ba7927f6b2bc005c413f21eb, checks an exact compatible clipping algebra control including changes inside the nonlinear core (energy decrease 49/2, squared error 17), 80 rational Fourier projection and row-rotation identities, and the relative error, annulus and exponential budgets. The clipping control checks the two projection properties and algebra, not a numerical implementation of the potential-space projection. The analytic scalar lemma is the pinned verified external theorem. No numerical critical sequence, proof of rigidity, new Lean validation or strict counterexample was constructed.
