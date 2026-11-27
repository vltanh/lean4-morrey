# Cofactor shear duality, envelope commutation and a strict universal margin bound

24 November 2026. Exact-zero attack following [the C11 optimal-margin reduction](IWANIEC_MORREY_C11_OPTIMAL_MARGIN.md). No extra isotropy, matrix homogeneity, finite-gradient cardinality, or amplitude hypothesis is imposed.

**Main results (hand proofs).**

1. A globally invertible nonlinear cofactor shear is an exact symmetry of both RC and QC on the entire globally C^{1,1} class. It preserves strong RC (with an explicit margin), commutes with the RC and QC envelopes when they are finite, and transports their contact sets. The QC argument uses the spatial Helmholtz projection and a quantitative near-stationarity estimate. It does NOT assume existence of minimizing gradients or assume that every constitutive change of variables maps an arbitrary gradient to a gradient.
2. If the universal optimal relative margin is negative, there are normalized near-equality sequences for globally QC, uniformly strongly RC energies, with simultaneously compatible gradients and asymptotically solenoidal constitutive stresses. Cofactor shears preserve these near-equality sequences. This supplies a new exact geometric operation at the critical threshold. It is not in itself the missing rigidity theorem.
3. The earlier all-base logarithmic determinant transport estimate (a consequence of the already formalized truncated determinant) gives a new **all-integrand, all-gradient** quantitative consequence: the universal normalized relative margin satisfies beta_* >= -99/200, strictly improving the elementary -1/2. For any strong LH margin m and Hessian bound M, J_F >= (199m-99M)/200 times the gradient variance. In particular m/M >=99/199 implies QC without any mesh enumeration. This is a modest bound, not a bootstrap to zero.

**Limit and provenance.** No proof that beta_*=0, gap amplification with a uniform nonzero threshold, or strict planar counterexample. The exact envelope symmetry also preserves the sup-norm envelope gap, so cannot amplify that gap by itself. The old logarithmic transport theorem is explicitly credited; it is not rediscovered as new progress. The cited searches did not establish priority of the new cofactor transformation. The arguments below are hand proofs, not Lean-certified or independently reviewed. The exact script at the end was actually executed on algebra and constant controls, not an unrestricted proof.

## 1. Planar cofactor geometry

Use the Frobenius inner product and norm, identifying real 2x2 matrices with R^4 in row-major coordinates. Define the symmetric orthogonal involution

    C X = cof X = [[X22,-X21],[-X12,X11]],
    q(X)=det X=(1/2) X:C X.

Its eigenspaces have dimensions (2,2), and a nonzero matrix R has rank one precisely when R:C R=0. In particular C preserves the rank-one cone.

On the area-one two-torus let G be the closed L2 subspace of zero-mean compatible gradients, P its orthogonal projection, and Q the orthogonal projection onto zero-mean rowwise divergence-free fields. Let P0 be the mean projection. Fourier expansion gives the mutually orthogonal decomposition L2=P0 L2 + G + Q L2 and

    C G = Q L2,    C Q L2 = G.

Indeed for a nonzero spatial frequency k, gradient modes have matrix amplitude a tensor k; the cofactor sends this to (J a) tensor (J k), where J is rotation through pi/2. The determinant has zero integral on either of the two zero-mean subspaces. For any p in L2, with p0=mean p,

    int q(p)=q(p0)+int (Qp):C(Pp).                          (1)

These are spatial compatibility identities, not just assumptions on a probability law.

## 2. The nonlinear shear T_t

Let F be globally C^{1,1} on matrix space and M>=Lip DF. For any t in R with |t|M<1 put

    Y=Psi_t^F(X)=X+t C(DF(X)),
    T_t F(Y)=F(X)+t q(DF(X)).                              (2)

The map Psi_t is onto, injective and globally bi-Lipschitz: for fixed Y solve X=Y-t C DF(X) by contraction. Bounds on its Lipschitz constant and that of its inverse are 1+|t|M and 1/(1-|t|M).

**Theorem A.** T_t F is globally C^{1,1}; if p=DF(X), then

    D(T_t F)(Y)=p,
    Lip D(T_t F)<=M/(1-|t|M).                              (3)

The transforms have the additive group rule T_s(T_t F)=T_(s+t)F whenever the indicated charts are invertible. Translation/recentering and the quadratic rescaling F(A+a X)/a^2 commute with the transform after shifting the base to Psi_t(A) and subtracting the appropriate affine tangent.

Proof of (3) without C² assumptions: for X'=X+h and p'=p+k, use the exact determinant expansion
    q(p+k)-q(p)=(C p):k+q(k).
Subtract p:(Y'-Y) from the difference of the right sides of (2). The result is
    F(X+h)-F(X)-p:h + t q(k),
which is O(|h|²), hence O(|Y'-Y|²). This proves the gradient formula. The derivative is Lipschitz by the inverse-map bound. In the group rule the gradient stays p and the independent shifts t C p and s C p add; their determinant-energy corrections add as well. For the affine recentering, q(p_A+k)=q(p_A)+(C p_A):k+q(k) cancels the linear tangent at the transformed base. Quadratic scaling then gives exactly the same t. QED.

### 2.1 Rank-one convexity and ellipticity

At a.e. differentiability point of DF write H=D²F(X). At the image of this point the Hessian of T_t F is

    H_t=H(I+t C H)^(-1).                                    (4)

Here C also denotes the symmetric 4x4 cofactor matrix; the expression is symmetric. Bi-Lipschitz changes preserve null sets and differentiation can be performed at a.e. point. Use the planar quadratic Finsler lemma: if H is nonnegative on the C-null cone, then H=c C+K with K positive semidefinite. More generally if H[R,R]>=m|R|² for rank-one R, write H=m I+c C+K, K>=0. For clarity the elementary non-strict lemma follows by separating the closed convex cone PSD+R C. Its dual consists of Z>=0 with tr(C Z)=0. Such a Z is a sum of h_i h_i^T with h_i:C h_i=0: the symmetric matrix Z^(1/2) C Z^(1/2) of trace zero has an orthonormal basis with zero diagonal, obtained by choosing one zero-quadratic unit vector and inducting on its orthogonal complement. This proves the dual assertion, and hence the Finsler lemma. The sum cone is closed since evaluation on the positive and negative eigenspaces of C bounds the scalar c for every convergent sequence.

If ||H||<=M and 0<=m<=M, then |c|<=M-m by evaluation of H-m I-c C on the two eigenspaces. The path H(u)=m I+c C+u K for 0<=u<=1 has operator norm <=M. The matrix map T_t on Hessians is monotone on such paths:

    d H_t(u)/du = (I+t H(u) C)^(-1) K (I+t C H(u))^(-1) >=0.

This is a congruence of K. At u=0 direct inversion gives

    (m I+c C)_t
      = [m I+(c+t(c²-m²)) C]/[(1+tc)²-t²m²].

Its rank-one curvature is m/[(1+tc)²-t²m²] >= m/(1+|t|M)². This proves:

**Theorem B.** If F is RC, T_t F is RC, and a global strong LH margin m for F gives the strong LH margin

    m_t >= m/(1+|t|M)²                                    (5)

for T_t F. Conversely RC of T_t F implies RC of F.

To pass the a.e. Hessian condition to the line inequalities, mollify the transformed C^{1,1} function, integrate the nonnegative rank-one Hessian along lines, then pass to locally uniform limits. For the converse use T_-t on sufficiently small increments of the path from 0 to t. Specifically along that path the derivative Lipschitz bound is at most M/(1-|t|M), so choose a finite partition with step length times this bound <1/4. Each reverse step is then covered by the forward argument. This avoids assuming that the crude inverse Lipschitz bound at the final endpoint automatically satisfies the smallness condition.

## 3. Quasiconvexity is preserved in both directions

For any globally C^{1,1} energy H define its global relative margin

    beta(H)=inf_(A,u,E>0) [int H(A+Du)-H(A)]/E,
    E=int |Du|²,

where u ranges over periodic W^{1,2} maps. It is finite between -Lip DH/2 and Lip DH/2, by Taylor's bound and the gradient mean. QC is equivalent to beta(H)>=0: the usual bounded-gradient tests imply the W^{1,2} tests by smoothing and quadratic-growth continuity. No assertion of attainment of this infimum is used.

**Theorem C.** For every F as in Section 2 and |t|M<1,

    F is QC iff T_t F is QC.                               (6)

We first prove the direction F QC => G=T_t F QC when |t|M<1/2. Put N=M/(1-|t|M). Suppose beta(G)=-b<0, so 0<b<=N/2. Take a near-minimizing sequence, recentering at its base and rescaling the matrix argument and energy quadratically to make the mean-zero compatible field Y_j have ||Y_j||_2=1. Recenter the corresponding F's at the inverse-image bases, using Theorem A. Denote the new integrands F_j,G_j; they still satisfy G_j=T_t F_j, F_j(0)=G_j(0)=0, DF_j(0)=DG_j(0)=0 and the bounds M,N. Their relative margins are unchanged. We have int G_j(Y_j)->-b.

Set H_j=G_j+b|Y|², so H_j is globally QC by the definition of beta(G). Define the nonnegative functional on the Hilbert subspace of all affine-base gradient fields A=P0 L2 + G by

    I_j(Z)=int H_j(Z)-H_j(mean Z) >=0.

Its gradient in this Hilbert space has Lipschitz constant at most 2(N+2b), uniformly in j, by the Nemytskii derivative estimate and orthogonal projections. The usual descent lemma for a nonnegative C^{1,1} functional on a Hilbert space gives
    ||grad_A I_j(Y_j)||_2² <= 4(N+2b) I_j(Y_j).
Indeed evaluate the Taylor upper estimate at the point reached by subtracting its gradient divided by the Lipschitz constant. Now I_j(Y_j)->0. If p_j=DG_j(Y_j), the exact Hilbert gradient identity, using the affine normalization and mean zero, gives

    mean p_j -> 0,       P p_j + 2b Y_j -> 0 in L2.         (7)

This is the key approximate stationarity, including the mean-stress condition. It cannot in general be replaced by an unproved existence of a smooth or Lipschitz minimizer.

Take the pointwise inverse image X_j=Y_j-t C p_j and its actual compatible part X_j^c=P X_j. Formula (1) and the cofactor exchange imply

    X_j^c-X_j=t C(p0_j+P p_j),
    int p_j:(X_j^c-X_j)=t[2q(p0_j)+int (Qp_j):C(Pp_j)].

Taylor's bound for F_j, using DF_j(X_j)=p_j, gives

    int F_j(X_j^c)
      <= int G_j(Y_j)+t q(p0_j)
               + (M t²/2)(|p0_j|²+||Pp_j||_2²).

Use (7) to obtain

    limsup_j int F_j(X_j^c) <= -b+2M t² b² <0.              (8)

The strict inequality follows from 2M t² b<=M t² N=(|t|M)²/(1-|t|M)<1. This is a genuine negative compatible-gradient test for some F_j, hence for F. The argument proves more generally a quantitative transfer of a negative optimal margin:
    beta(F) <= (-b+2M t² b²)/(1+|t|N)²,
under the same smallness condition. For this bound use ||X_j^c||_2<=1+|t|N and the eventual strictly negative numerator. No arbitrary projection of a gradient law has been asserted to preserve compatibility of the uncorrected pointwise inverse; the energy loss of the orthogonal correction is accounted for in (8).

For the two-way equivalence use small steps |delta t| M_s<1/4, where M_s bounds the derivative of the current energy. Then the inverse step also obeys the one-way smallness condition, because the derivative bound after the step is <=M_s/(1-|delta t|M_s). Along the complete path |s|<=|t| the common bound is M/(1-|t|M). A finite partition therefore proves (6) for the full invertible interval. QED.

## 4. Exact envelope commutation and contact geometry

These results concern a globally C^{1,1} F with a finite QC minorant (for example any bounded-below F); this ensures both global envelopes are finite. The finite-valued RC and QC envelopes RF,QF are the largest RC and QC minorants, respectively.

First, if Lip DF<=M, then

    Lip D(RF)<=M,      Lip D(QF)<=M.                       (9)

For RF use the infimum over all finite rank-one splitting trees centered at the base. This infimum is finite by the lower minorant; grafting trees proves RC, and Jensen for any RC minorant proves equality to RF. Translation of a centered tree gives the same set of averaging operators at every base. Subtracting M|A|²/2 from each averaged F gives a concave function, so the infimum is M-semiconcave.

For QF the identical argument uses the cell infimum
    qcell(A)=inf_u int F(A+Du)
over bounded periodic gradient perturbations. It is finite by the QC lower minorant, and M-semiconcave by translation of the test. A finite semiconcave function is continuous. To verify QC of the infimum, first take a periodic PL test with finitely many triangles. In the interiors of its constant-gradient cells insert small-scale bounded periodic approximate minimizers for the corresponding bases, cut off to zero near each cell boundary. The high-frequency limit gives the desired averaged costs in the interiors; the cutoff terms are bounded for each fixed test and its fixed collar, and the collars can be taken of arbitrarily small measure. This is the standard patching argument, using only bounded-gradient correctors and local boundedness of F. Thus the cell infimum has the Jensen inequality on PL tests. Smooth periodic approximation followed by PL interpolation with a common gradient bound extends it to all Lipschitz tests. Every QC minorant is below this infimum by Jensen, so it equals QF.

To obtain (9) for either finite envelope, use mollification of the RC, M-semiconcave function. The mollified Hessian has upper bound M I. For any matrix R+S in a singular-value decomposition into orthogonal rank-one summands, the reflected direction R-S has the same norm and
    H[R+S,R+S]+H[R-S,R-S]=2H[R,R]+2H[S,S]>=0.
Hence H has lower bound -M I. This proves a common C11 bound for mollified functions; local uniform convergence and Arzela-Ascoli for their derivatives gives (9). This planar quadratic argument does not suppose the envelope is convex or C².

**Order property.** For F0,F1 of common global derivative Lipschitz bound M and |t|M<1, one has

    F0<=F1  =>  T_t F0<=T_t F1.                             (10)

In fact, set F_s=(1-s)F0+sF1, X_s=(Psi_t^(F_s))^(-1)(Y) at a fixed Y. Contraction shows X_s depends Lipschitz continuously on s on [0,1], and remains bounded. Differentiation of (2) at fixed Y, or a first-order finite-difference expansion as in Section 2, cancels the X_s derivative against the determinant term, giving
    d/ds T_t F_s(Y) = (F1-F0)(X_s).
For t=0 the same identity is immediate. Integration proves (10) and the exact comparison formula.

**Theorem D.** For all invertible t of Section 2 and F with a finite QC minorant,

    R(T_t F)=T_t(RF),       Q(T_t F)=T_t(QF).               (11)

For sufficiently small |t|M<=1/4, (9), (10) and the RC/QC symmetry give T_t(QF)<=Q(T_t F), with analogous RC inequality. In particular the new energy has a finite QC minorant, so its envelopes are finite and their derivative bound is <=N=M/(1-|t|M). By inverse monotonicity and QC invariance, T_-t(Q(T_tF))<=QF. Transform forward once more, using the bound N/(1-|t|N)<=M/(1-2|t|M) on the inverse envelope, to obtain the reverse inequality. The forward smallness condition holds for this common bound since |t|M<=1/4. The RC argument is identical. Partition a general safe path into finitely many such steps, with the common derivative bound M/(1-|t|M). This proves (11).

There are two further exact consequences, not merely estimates:

- The contact set {F=QF} is mapped bijectively by Psi_t^F onto {T_tF=Q(T_tF)}; likewise for RF. For QF apply the comparison formula with F0=QF,F1=F. The gap equals int_0^1 (F-QF)(X_s) ds. Its zero requires the nonnegative continuous integrand of this integral to vanish for all s. At contact F and QF have equal derivatives (both C11), so their shears coincide. Conversely that equality at a contact point proves zero transformed gap.
- The global sup-norm envelope gap is invariant:
      sup (T_t F-Q(T_t F))=sup(F-QF),
  including the value +infinity, and likewise for RF. Constants commute with T_t. If F<=QF+D, monotonicity proves the upper bound by D; inverse monotonicity on the same small-step partition proves the reverse implication. This is also a precise no-amplification result for this particular measure of the defect. It does NOT assert invariance of the Hessian-normalized relative margin, which has a different normalization.

The transformation enlarges the exact set of compatible operations and supplies a genuine new structural attack on critical equality cases. It does not identify the QC and RC contact sets with each other.

## 5. A critical-state reduction for the remaining exact-zero problem

Let beta_* be the universal infimum over globally RC F with Lip DF<=1, as in [C11 margin](IWANIEC_MORREY_C11_OPTIMAL_MARGIN.md). Assume for contradiction beta_*=-b<0. Choose normalized near-extremizers F_j and compatible mean-zero X_j with
    F_j(0)=DF_j(0)=0, ||X_j||_2=1, int F_j(X_j)->-b.
The critical energies H_j=F_j+b|X|² are globally QC by definition of beta_*, uniformly strongly RC with margin 2b, and Lip DH_j<=1+2b. Their nonnegative Jensen gaps on X_j tend to zero. By the Hilbert gradient estimate of Section 3, their stresses p_j=DH_j(X_j) obey
    mean p_j->0, ||P p_j||_2->0.
The sequence C p_j is therefore asymptotically compatible in L². In particular int q(p_j)->0 by (1) and the uniform L² bound on p_j. Both the constitutive relation and this spatial compatibility are required; stationarity of a matrix-law surrogate alone is not sufficient.

For any |t|(1+2b)<1 put
    Y_j^c=P(X_j+t C p_j).
Its difference in L² from the pointwise shear tends to zero. By (2), the determinant identity and the uniform C11 bounds of Theorem A,
    int T_t H_j(Y_j^c)->0.
These are again actual compatible near-equality sequences for globally QC uniformly strongly RC integrands, with their derivative stresses asymptotically equal to p_j. One can apply all existing verified planar inequalities to every constant linear combination of the two asymptotically compatible fields X_j and C p_j, or to their constant row combinations. This supplies simultaneous genuine spatial information, not merely determinant moments of each marginal.

Consequently an exact rigidity theorem excluding these nonvanishing normalized near-equality sequences at any fixed positive ellipticity margin would prove Morrey. Such a rigidity theorem has NOT been established here. It must exploit energy near-equality as well as stationarity: nontrivial weak stationary solutions can occur even for strongly quasiconvex planar systems (see e.g. Muller and Sverak's convex integration results; https://www.mathunion.org/fileadmin/ICM/Proceedings/ICM1998.2/ICM.1998.2.ocr.pdf, Theorem 4.2). Do not infer uniqueness of stationary solutions from rank-one ellipticity. The present critical-state reduction is equivalent in force to the unresolved problem if the needed rigidity is simply postulated.

## 6. A strict universal lower bound using the verified truncated determinant

We now obtain an unconditional all-integrand improvement on the elementary beta_*>=-1/2, using the already Lean-verified truncated-determinant inequality in the repository's pinned lean4-iwaniec dependency. The logarithmic transport bound itself is the earlier [weighted spectral transport theorem](IWANIEC_MORREY_WEIGHTED_SPECTRAL_TRANSPORT.md); we give a short self-contained derivation at zero and a new anisotropic use of it.

### 6.1 Logarithmic transport

Take any bounded compatible mean-zero planar gradient X. Write s=||X||op, d=det X, delta=d/s (zero at zero), and put
    S=int s², E=int |X|_F², S<=E<=2S.
We have int d=0. The verified QC integrand at radius r>0 has the formula
    L_r(X)=d if s<=r,
           r(s+delta)-r² if s>r.
Reflection of one row is also QC and replaces d,delta by their negatives. Apply both Jensen inequalities at zero to get
    |B(r)|<=K(r), where
    B(r)=int_{s<=r} d+int_{s>r} (r/s)d,
    K(r)=int_{s>r} r(s-r).
Integration gives int_0^infty K(r) dr/r=S/2.

Let mu_+,mu_- be the pushforwards of d_+ and d_- weighted gradient measures under log s. Their common mass is m=(1/2)int |d|. Terms at s=0 have zero mass; first log moments are finite for bounded gradients. For a unit mean exponential random variable Z, the difference of CDFs of the two log-radius measures shifted by -Z is B(exp(t)): indeed conditional on log radius u the CDF at t is min(1,exp(t-u)). Therefore their unnormalized W1 transport cost is at most S/2, by the one-dimensional cumulative-distribution formula. Shift both smeared measures by log 2, which leaves this cost unchanged. The coupling from each original measure to its smearing has cost at most m E|log 2-Z|=m log 2 (the integral is log 2-1+2 exp(-log 2)). The triangle inequality gives precisely the zero-base case of the old transport estimate:

    W1(mu_+,mu_-) <= S/2+2m log 2.                         (12)

It applies to actual bounded gradients; approximate arbitrary W^{1,2} gradients by smooth periodic convolutions when passing the final quadratic energy estimate to the limit. No unbounded logarithmic moment assumption is needed.

### 6.2 A two-matrix estimate for arbitrary anisotropic RC energies

Let F be globally RC, Lip DF<=1, and subtract its affine tangent at zero. Put g(X)=F(X)+|X|_F²/2. This is a nonnegative convex function with g(0)=Dg(0)=0: monotonicity of Dg follows by Cauchy-Schwarz from the global derivative bound. For any rank-one R, F(R)>=0. For a singular decomposition X=R+S' with R,S' rank-one, the rank-one supporting line inequality gives
    F(X)>=F(R)+DF(R):S'>=-|R||S'|=-|det X|.
Write the conformal coordinates of a planar linear map as z,w in C, so s=|z|+|w|, d=|z|²-|w|², |X|²=2(|z|²+|w|²). Consequently

    g(X)>=2 min(|z|²,|w|²).                                (13)

At a rank-one matrix, g(X)>=s²/2.

**Pair inequality.** For X with d(X)>0 and Y with d(Y)<0, write a=s(X), b=s(Y), R=max(a,b)/min(a,b), and e=g(X)/a²+g(Y)/b². Then

    e >= 1/[2(1+sqrt(R))²].                               (14)

If e>=1/2 the inequality is immediate. Otherwise by (13) the minority modulus of either matrix is at most kappa=sqrt(e/2)<1/2 times its own radius, and the majority modulus is at least (1-kappa) times its radius. There is a point Z=tX+(1-t)Y on their segment where the determinant vanishes. Set alpha=t a, beta=(1-t)b. If alpha>=beta, its conformal modulus is at least (1-kappa)alpha-kappa beta>=(1-2kappa)alpha. If beta>=alpha use its anticonformal modulus instead. At this rank-one point the moduli coincide, so
    s(Z)>=(1-2kappa)(alpha+beta)>0.
By convexity of g and its lower rank-one bound,
    (1-2kappa)² (alpha+beta)²/2
       <=g(Z)<=alpha a (g(X)/a²)+beta b (g(Y)/b²)
       <=max(a,b)(alpha+beta)e.
Since alpha+beta>=min(a,b), this proves 2e R >= (1-sqrt(2e))², hence (14). This argument requires no ability to rotate the original matrices without changing their energy. In particular it applies to completely anisotropic F.

### 6.3 Integrate the pair estimate with the actual compatibility budget

Let G=int g(X). If G<S/100, (13) and Cauchy-Schwarz imply

    S-2m=int(s²-|d|)<=sqrt(2 S G),
    m/S>(1-1/sqrt(50))/2>3/7.

Lift a monotone optimal coupling of the two log-radius measures to a coupling pi of the determinant-weighted matrix measures, by disintegration on their logarithmic radii. This uses ordinary coupling of measures only to evaluate the pair inequality, not to declare the resulting pairs compatible gradients. The function
    k(t)=1/[2(1+exp(t/2))²], t>=0
is decreasing and convex (its second derivative is exp(t/2)(2 exp(t/2)-1)/(4(1+exp(t/2))^4)). By (14), |d|<=s² and Jensen on the probability coupling pi/m,

    G >= int [g(X)/s(X)²+g(Y)/s(Y)²] d pi
      >= m k(W1(mu_+,mu_-)/m).

By (12), W1/m<=S/(2m)+2 log 2<7/6+2 log 2. The elementary exact rational estimate exp(7/12)<9/5 follows by summing the first four Taylor terms and bounding the remaining positive tail by a geometric series; the resulting upper bound is 3938881/2198016<9/5. Hence
    exp((7/6+2 log 2)/2)<18/5,
    G>(3/7) S * 25/1058=(75/7406) S>S/100,
a contradiction. Thus G>=S/100>=E/200. Rescale back to an arbitrary base and Hessian bound M, using translation and affine subtraction. For M=0 the energy is affine and the result is immediate.

**Theorem E.** For every globally RC C^{1,1} integrand with Lip DF<=M and every planar periodic W^{1,2} test,
$$
J_F(A,u)\ge -\frac{99}{200}M\int |Du|^2.
$$
In particular beta_*>=-99/200>-1/2. The proof uses actual compatibility through (12) and does not follow from the determinant moment alone.

If F has known strong LH margin m, subtract (m/2)|X|². Its Hessian is bounded in operator norm by M-m, not M+m: the rank-one decomposition and reflection argument of Section 4 gives D²F>=(2m-M)I. Consequently
$$
J_F(A,u)\ge \frac{199m-99M}{200}\int |Du|^2.
$$
Thus m/M>=99/199 suffices for QC, and a strict inequality gives strong QC. One may optimize M over constant determinant gauges, since they change neither LH nor Jensen gaps. The conclusion modestly improves the automatic convexity range m/M>=1/2 and the universal trivial margin. It gives no condition-ratio reduction for arbitrary possible counterexamples. The transport budget does not vanish as the normalized deficit tends to zero.

## 7. Exact remaining gate and verification

The cofactor shear is a new exact spatially justified symmetry, not a universal proof. It preserves the sup envelope gap; the relative gap may change with normalization, but no uniform amplifier to a fixed positive magnitude follows from the ellipticity estimate (5). In particular a proof that the critical near-equality sequences in Section 5 cannot exist still needs a new energy-rigidity mechanism. The bound in Theorem E is a direct universal improvement but does not iterate to zero by itself. No finite exact vertex bound, huge finite optimization, or strict negative witness is claimed.

The executed companion [cofactor_duality_exact.py](../../research/audit/cofactor_duality_exact.py) checks exact rational transformed quadratic gradient/inverse formulas, PSD monotonicity and order for three shear parameters, six Fourier cofactor-mode controls, and the rational exponential and margin constants. Git blob 0f5bb5cc68ab462befdd5ce5b68597277b1b8fba; SHA-256 4267157a0c3a138d33a1202cf5b21f7b47fc01657ebb23252fe5a1d8ae6d322d. All these controls actually passed. They do not independently establish the global Hilbert-space, envelope, or transport proofs. No new Lean statement or human review. Unrestricted Morrey remains open.
