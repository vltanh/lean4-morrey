# Finite beta-certificate test: common-integrand false critical laws and adaptive detectors

24 November 2026. Computer-assisted exact-zero attack, distinct from the independent-copy polynomial-degree countermodel in N21. The goal was a finite polynomial feasibility certificate involving the unknown universal margin itself.

**Results.** A sound finite semialgebraic outer relaxation of universal near-extremizers retains selected moments of ACTUAL gradient laws, common-energy jet interpolation, and critical stress inequalities. Its baseline has at most 28 atoms, or 43 with the lifted determinant covariance. No uniform amplitude cutoff is imposed. The reduced atomic law is NOT asserted to be a gradient law.

A fixed-test obstruction holds even with ONE common globally C11 RC energy. For any finite list of fixed C1 RC tests (hence in particular QC tests), there are correct-minor artificial critical laws with positive candidate b, normalized Hessian bound one, exact stabilized PC equality and zero stabilized stress, passing those tests. An adaptive covariance/scale test rejects the first trap family but fails on a second. Small rank-one contamination also passes the nonblocked covariance condition at the SAME positive candidate b with critical residual tending to zero. Thus this finite baseline is insufficient. Determinant-regression adaptation rejects the controls, but no sufficient adaptive selection for arbitrary critical laws is known.

**Limits.** No universal contraction, positive gap separation for beta_*, improved bound on beta_*, true gradient counterexample, or finite infeasibility certificate was obtained. These results refute a specified proof mechanism, not computer-assisted proof in general. The proof is at hand level; exact rational controls were executed, but not full SDP/QE, Lean verification or independent review.

## 1. A finite near-extremizer certificate interface

Suppose b=-beta_*>0 is the TRUE unknown margin. Use the P15 bound 0<b<=1/8. Normalize F globally C11 RC with F(0)=DF(0)=0, Lip DF<=1, and an actual smooth periodic gradient X=Du to mean zero and E=int|X|²=1. Bounded witnesses suffice to approximate the universal infimum by R16. Set H=F+b|.|², L=1+2b<=5/4, p=DF(X), q=DH(X)=p+2bX, j=int H(X)=t². By the definition of beta_*, H is globally QC. At this fixed b the residual j can tend to zero; restrict to t²<b/2.

On the affine-compatible Hilbert space the functional I(Z)=int H(Z)-H(mean Z) is nonnegative and has derivative Lipschitz constant <=2L. The quadratic descent estimate at X gives
    ||Pq||²+|mean q|² <=4L j<=5t²,
where P is the mean-zero compatible projection. For the mean-zero rowwise solenoidal projection Q, ||q-Qq||_2<=sqrt(5)t. The cofactor involution C takes rowwise solenoidal fields to compatible fields. Consequently W=(X,Cq) differs from the actual compatible mean-zero Wc=(X,CQq) in L2 by <=sqrt(5)t, and both L2 norms are <=2. In particular
    |mean q|²<=5t²,
    |int any two-row minor of W|<=10t,
    int det X=0.
The minor error follows from the quadratic determinant bound and Cauchy-Schwarz.

For any fixed bases A and constant 2x2 row maps L1,L2 of operator norm <=1, one can also impose
    int [H(A+Y)-H(A)-DH(A):Y]>=-20t,
    Y=L1 X+L2 Cq.
The field Yc obtained using Qq is compatible and mean-zero, and its Bregman gap is nonnegative by QC. The error estimate follows from ||Y||_2,||Yc||_2<=1+L, ||Y-Yc||_2<=sqrt(5)t, and the Taylor remainder difference bound L(|Y|+|Yc|)|Y-Yc|. Additional fixed C11 QC tests on approximate compatible blocks admit analogous explicit errors. This is where actual compatibility is used BEFORE finite reduction.

### 1.1 One adaptive anisotropy/scale test

Write R=int XX^T, S=int X^T X. Both have trace one. The orthogonal singular-value decomposition into rank-one summands and RC tangent inequality give F(X)>=-|det X|; hence int |det X|>=b-j>=b/2. In an eigenbasis for R, use the product of row lengths to bound determinant and then Cauchy-Schwarz; do the same for S by columns. This proves R,S >= (b²/4)I.

Choose orthogonal eigenbases U,V of R,S, with descending eigenvalues. If the eigenvalues of R are r1>=r2, let d=sqrt(r2/r1), and set
    Z=diag(1,1/d) U^T X V,
    m2=int |Z|², m4=int |Z|⁴,
    rho²=(4/17)m4/m2, Y=Z/rho.
The scale coefficient is chosen for the first example below, not claimed canonical. These are constant matrix transformations for the given law, hence legitimate for gradient Jensen tests (right multiplication uses the affine-domain formulation). For each of the four diagonal sign matrices D we have
    int K_4(-3I-DY)>=0,                                 (1)
where K_r(A)=(s-r)_+(r-det A/s), s=||A||op, with value zero for s<=r. QC of K_r follows from the verified truncated determinant by scaling and subtracting det; see R06. Its value at the base -3I is zero. At repeated eigenvalues any selected eigenbasis is valid. All four tests and their defining statistics have semialgebraic descriptions.

### 1.2 Exact finite support reduction

For a bounded actual law first compute the adaptive parameters. Preserve the vector of scalar expectations
    X,q (8), F(X) (1), R,S (6),
    two-row minors of W (6), m2,m4 (2), four tests (4).
These are 27 continuous functions of X on a compact range. Caratheodory gives a law on at most 28 points of that range with EXACTLY those expectations. Keep the chosen eigenbases, which remain valid. Additional finitely many test functions cost at most one atom each. The atom coordinates need not be bounded uniformly across inputs. This step preserves moments, not gradient realizability.

For every pair of sampled arguments X_i,X_k require the exact necessary C11 interpolation constraints for values f_i, derivatives p_i:
    |f_i-f_k-(p_i+p_k):(X_i-X_k)/2|
        <= (|X_i-X_k|²-|p_i-p_k|²)/4.                   (2)
Indeed apply the convex 2-Lipschitz-gradient interpolation inequality to both |X|²/2+F and |X|²/2-F, and combine. That interpolation inequality follows by descent applied to the tangent-subtracted nonnegative function. At determinant-zero differences also require f_i>=f_k+p_k:(X_i-X_k) by rank-one convexity. Include the base zero jet. Extra finite nodes, e.g. rowwise cross-corners or rank-one summands, can be introduced with the same inequalities. Every actual F supplies all these jets. We do not claim finite RC constraints suffice for global RC extension.

For semialgebraic tests, this is a finite quantified real-algebraic problem; square roots, eigenbases and operator norm in (1) have polynomial descriptions. A certificate j>=c b^N, c>0, finite N (or simply a positive lower bound on j at each fixed b>0), would contradict near-extremization at the TRUE positive b. This is a sound interface independent of mesh/tolerance. Sufficiency of the listed baseline is FALSE, as shown next.

## 2. A common-integrand obstruction for arbitrary finite fixed C1 tests

**Rank-one-flat lemma.** If a globally C1 RC f has f(0)=Df(0)=0 and f vanishes on the rank-one cone, it has a global determinant support at zero: f(A)>=c det A for some c.

At nonzero rank-one R the derivative is Df(R)=lambda_R C R, since f is identically zero on the smooth rank-one manifold. Given X,Y of opposite nonzero determinant signs, there is n with CX n,CY n independent. Otherwise (CX)^(-1)CY would send each vector to a multiple of itself, hence be a scalar identity, contrary to opposite determinant signs. Solve (CX n) dot a=det X, (CY n) dot a=det Y. Then R=a tensor n is nonzero rank one and det(X-R)=det(Y-R)=0. The rank-one tangent inequalities at R give f(X)>=lambda_R det X and f(Y)>=lambda_R det Y. Hence every positive-det ratio dominates every negative-det ratio. A coefficient between their infimum and supremum works everywhere, including rank-one matrices.

For a finite list of fixed C1 RC tests subtract their tangents at zero. Flat tests have nonnegative gaps on all correct-minor laws by the lemma. For each nonflat test g_k choose n_k such that a->g_k(a tensor n_k) is a nonzero nonnegative convex function. For a nonnegative convex function with value zero at zero, the directions where it vanishes along the entire real line form a linear subspace (use the convexity inequality at t(x+y) between 2tx,2ty). Thus the flat a directions at n_k form a proper subspace. Choose unit a outside the finite union; then for this a choose unit n outside the corresponding finitely many proper flat subspaces in n. On the single rank-one line t a tensor n every nonflat test is positive somewhere and positive further along that ray. Any mean-zero law charging both positive and negative multiples of that direction, when sufficiently dilated, therefore has STRICT positive Jensen gap for all nonflat tests. This includes restrictions of fixed C1 QC tests on stacked fields to (X,0,...,0), and any preselected translations or affine left/right transforms. It does NOT include an entire adaptive parameter family.

## 3. Explicit common globally C11 RC energy with false critical law

Use diagonal coordinates (x,y) and the trap
    (-1,1/2), (1/2,-1), (2,2), weights 4/9,4/9,1/9.
Mean and determinant mean are zero; each coordinate variance is one and xy=x+y on support. This is not a gradient law. Construct a single globally C11 PC uniformly strongly RC energy h vanishing with derivative at zero and all atoms.

For X=[[x,u],[v,y]] put q0=|X|²/2, B=u²+v², s=det X-tr X, and let phi be the convex C11 Huber function s² for |s|<=1 and 2|s|-1 otherwise. Take four branches
    h0=phi(s)+B,
    h1=q0+1026 phi(s)-5,
    h2=q0+1026 B-5,
    h3=10000 q0-40002.
Define h by sequential binary smooth maxima of h0,h1,h2,h3 with width sigma=1/4: smax(a,b)=(a+b+chi(a-b))/2, chi(z)=|z| for |z|>=sigma, (z²+sigma²)/(2sigma) otherwise. This is convex, nondecreasing in both arguments, and between max and max+sigma/4. The branches are convex in (X,det X), so h is PC. At zero and the three atoms h0=0, all other branches <=-1. Thus h=Dh=0 there and h>=0 globally.

**LH margin.** Whenever h0 has positive final derivative weight, the smooth maxima imply h_i<=h0+1 (allowance at most 7sigma/2). Adding the first two comparisons gives phi(s)+B<=12/1024<1/64; the third gives q0<5, hence |X|<4. Now |s|<=1/8, B<=1/64, |(x-1)(y-1)|=|1+s+uv|>3/4, and each factor magnitude >1/8 since the other is <=5. For a unit rank-one R of offdiagonal norm t, the LH curvature of h0 is 2[(CX-I):R]²+2t², since phi''=2 and det is affine on rank-one lines. If t>=1/64 this is >=1/2048. Otherwise one diagonal component has magnitude >=1/2, the other <=t² by det R=0; then |(CX-I):R|>=1/16-5t²-t/8>1/32. All other branches have LH margin >=1. The smooth maximum Hessian is a convex weighted average plus PSD terms. Thus h has global LH margin m=1/2048, using the a.e. Hessian inequality and C11 regularity (or convolution to pass to all lines).

**Hessian bound.** Because phi(s)<=2|s|<=2q0+3|X|, outside B4 the branch h3 dominates all other branches by >1, so h=h3 there. On B4, |Ds|<=6, ||D²phi(s)||<=74, branch derivative norms <=40000. Largest branch Hessian plus three smoothing terms is at most 75925+3*2*(80000)² < M_h=4*10^10. These bounds establish global C11. The rational comparisons are checked in the companion script.

Complete a,n from Section 2 to orthogonal U,V. Transform by T(X)=r U diag(1,d) X V^T with r>=1, 0<d<1. Let h_T=h composed with T inverse, kappa=m/(2r²), M_f=(M_h+1)/(r²d²). Then
    F=(h_T-kappa |.|²/2)/M_f,
    b=kappa/(2M_f)=m d²/[4(M_h+1)]>0.
The LH margin of h_T is >=m/r², so F is globally RC; Lip DF<=1, F(0)=DF(0)=0. Its critical stabilization H=F+b|.|²=h_T/M_f is exactly PC and nonnegative. The transformed law has correct mean and minors and H=DH=0 on support. Mix in zero to normalize its variance r²(1+d²) to one. Then int F=-b, all stabilized stress blocks q=DH and H I-X^Tq vanish, and every stabilized Jensen test of a constant row transformation and translation holds by PC. Actual common F supplies exact interpolation, including any additional sample nodes.

Choose r large enough for strict positivity of each nonflat fixed test on the limiting rank-one law as in Section 2. Choose d>0 small enough that positivity persists by continuity; zero dilution multiplies the gap by a positive mass. Flat tests stay nonnegative by the determinant support lemma. This proves the obstruction for any finite fixed smooth tests, with positive candidate b arbitrarily small. This b need not equal the true -beta_*.

## 4. Adaptive test success and failure, exactly

For the first trap E|X|⁴=17/2, E|X|²=2. On its transformed/diluted family the covariance normalizer undoes anisotropy and recovers r exactly because m4/m2=(17/4)r². One sign choice returns the original trap plus zero. K_4(-3I-X) has values (0,0,-1) and zero at the base, so the adaptive gap is minus trap mass/9. The verified K_r excludes the entire family.

However take the second trap
    (-5,5/6), (5/6,-5), (2,2), weights 12/49,12/49,25/49.
It also has correct mean/minors, xy=x+y, equal coordinate variances, and (4/17)E|X|⁴/E|X|²=769/153>4. After the scale normalization each atom has at least one diagonal coordinate of magnitude <1. Thus every sign-transformed -3I-DY has smaller singular value <=4, so K_4 is nonnegative. All four tests PASS, also after the anisotropic transformation/dilution family. For a common h of the same form replace (1026,5,10000,40002) by (2050,14,50000,700000). The active bounds phi+B<1/64, |X|<8 follow by the same comparisons; |x-1|,|y-1|>=3/[4(8+1)]. Use t0=1/[16(8+1)²] for the small-offdiagonal argument to obtain margin >=2t0². The quadratic tail dominates outside B8 and the compact branch derivatives yield a finite global Hessian bound. Thus F,b and the fixed-test proof extend to the second law.

## 5. Lifted covariance and near-critical nonclosedness

Add the 15 scalar moments of Sigma=int Z0 tensor Z0, Z0=(vec X,det X), giving <=43 atoms in the baseline. The earlier adaptive-martingale one-step criterion is
    Sigma c=(vec R,0) for some c, det R=0, |R|²=1.       (3)
It characterizes a determinant-neutral binary observation with distinct rank-one-connected child means: reweight by 1±epsilon c dot Z0 for small epsilon. Conversely such a split gives a rank-one direction in the range of Sigma, equal to the lifted span. The blocked classification and verified L detector in R06 show every non-Dirac bounded actual gradient law satisfies (3). This is therefore a sound additional semialgebraic necessary test, not an assertion that the child laws are compatible.

An exact correct-minor equality law of strongly RC PC H cannot satisfy (3): each child Jensen inequality holds by PC, and strong RC at their two separated rank-one means forces strict excess. So (3) excludes the exact PC fakes, but not near-critical sequences.

Take the transformed second law above at fixed r,d, with its common F and b>0. Mix in mass epsilon of a symmetric unit-variance rank-one law on ±a tensor n. Mean, minors, variance remain correct. The covariance range now contains (vec(a tensor n),0), so (3) holds for every epsilon>0. The second law's strict small-coordinate property persists in the covariance-scale test for sufficiently small epsilon: distinct covariance eigenaxes remain unchanged and scale statistic varies continuously. Rank-one added atoms also have a zero diagonal coordinate. Fixed tests on X pass by the construction and rank-one Jensen. The SAME H remains globally PC and nonnegative. Now j=epsilon times the H average on the added atoms tends to zero at the SAME positive b. Descent for nonnegative H gives |DH|²<=2L H, hence squared stress norm <=2Lj. All the stated approximate stress/minor/stabilized-test inequalities follow by comparison to (X,0), whose minor means vanish, and by PC of H on row transformations of X. Fixed additional C11 QC tests on the approximate lift likewise hold with the corresponding quadratic-remainder error when their restriction to (X,0) was included among the fixed tests. The common F meets all global RC interpolation requirements. No claim is made that (X,0) itself is a gradient law; the finite baseline has only the listed necessary conditions. This disproves j>=c b^N for that baseline, even with the adaptive covariance-scale and nonblocked tests.

### 5.1 Determinant-relation adaptive normalization

The exact blocked detector can be recovered from these finitely many covariance moments: if (3) fails, the lifted span is a graph det X=ell(X) on L=span supp X, with Lorentzian determinant signature up to sign. Solve the linear regression on the covariance range, recover C0 in L by (CX):C0=ell(X) (polarization), and use the known classification and normalization in R06. This gives det(X-C0)=det C0, invertible C0, and a similarity sending (X-C0)(-C0)^(-1) to symmetric determinant-one matrices of mean I. They charge both definite sheets. A radius exceeding the normalized support gives the exact K_r(Z-rI) gap minus the negative sheet mass. All normalization choices arise from the span and relation, apart from the radius which can depend on the original bounded support. This uses the prior blocked theorem, not a new classification.

For the diagonal perturbed controls, regress det X on the two diagonal entries with coefficients alpha,gamma. Gamma=1, alpha tends to the anisotropy d in the checked r=1 family. Use Z=I-X diag(gamma,alpha)^(-1); a fixed sufficiently large r in K_r(Z-rI) yields a negative gap continuously through these perturbations. Four rational perturbations, including 10^-8, were checked. This defeats the demonstrated false near-critical sequence, but no uniform regression rule for all approximately blocked laws with changing span or amplitude, and no rigidity for general QC critical H, is proved.

One cannot impose ALL affine L tests on the reduced 28- or 43-atom law without a preservation theorem: Caratheodory preserves finitely many specified functions, not an infinite family of adaptive values. Tests selected from preserved statistics before reduction are valid, and a finite approximation/selection theorem would also be valid if it controlled the exact critical budget. This remains missing.

## 6. Verification and stop rule

Executed research/audit/beta_adaptive_detector_exact.py using standard-library rational arithmetic. SHA-256 b06e2c225ac70e7e8067588243754f1697fdbc810fea6129d8e028afc55aa31a, Git blob cefe11f3eb981a4c198411c77ccfcb75fde193fa. All base trap moment/contact/LH and Hessian budgets, 12 anisotropy/dilution controls, second trap scale-detector failure, blocked regression and four near-critical controls passed, with regression-adaptive detection. The arbitrary finite fixed-test theorem follows from the analytic proof, not enumeration.

Do not run large SDP/QE on this refuted baseline hoping for exact zero. The finite interface is sound for any justified adaptive selection, but sufficiency of stronger finite constraints remains unknown. No improved beta_* bound, self-contraction, genuine counterexample, or unrestricted proof was found.
