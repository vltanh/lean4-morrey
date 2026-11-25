# Global C^{1,1} relative localization and a computable optimal Morrey margin

24 November 2026. Exact-zero attack after [the uniform geometric cutoff](IWANIEC_MORREY_UNIFORM_GEOMETRY_CUTOFF.md). We strengthen the quantitative framework rather than enumerate more small meshes.

**New results (hand proofs).**
1. The relative finite-mesh theorem now needs only a global Lipschitz bound on the gradient of the energy (a C^{1,1} bound). It applies to every periodic W^{1,2} gradient, at every base and every amplitude, with a single mesh depending only on the prescribed relative error and the Hessian bound. No third derivative, amplitude cutoff, or unknown integrand-dependent continuity modulus.
2. Define the universal normalized optimal relative Jensen margin beta_* by taking the infimum over all globally C^{1,1} RC functions of gradient-Lipschitz constant at most one, and all nonconstant compatible gradients. The margin is zero iff unrestricted planar Morrey is true. The new localization, combined with a Hessian-normalization-preserving finite-data repair, gives explicit rational intervals of arbitrary prescribed width enclosing beta_* itself. This is a two-sided approximation in the SAME normalization, not a certificate alternative with an attenuated gap.
3. For an input globally uniformly strongly RC energy with known bounds m>0 and M, one finite mesh gives an **exact alternative**: prove global strong QC of the input, or obtain a genuine counterexample to Morrey for the input minus a specified quadratic that preserves strong RC. This alternative does not depend on the size of an unknown violation of the input. For semialgebraic evaluation formulas it is a finite real-algebraic decision.

**Limit:** the remaining exact-zero gate is not closed. The condition number m/M in result 3 is not uniformly bounded below for all potential counterexamples. The universal scalar in result 2 is computable to positive accuracy, but zero of a computable real is not in general finitely decidable. No positive lower bound on a possible nonzero defect, universal gap amplifier, negative planar witness, or practical enormous-mesh computation is supplied. Exact constants were checked locally. No Lean verification, independent mathematical review, or novelty claim.

## 1. Uniform relative theorem without a third derivative

Use normalized integrals on the flat two-torus. All matrix norms below are Frobenius norms, and Lip DF is the global Euclidean Lipschitz constant of the derivative. For F globally C^{1,1}, Lip DF<=M, put

    J_F(A,u)=int [F(A+Du)-F(A)],
    E(u)=int |Du|^2,
    beta(F)=inf_(A,u,E(u)>0) J_F(A,u)/E(u),

where u ranges over all periodic W^{1,2} two-component maps. Write beta_n(F) for the same infimum over the periodic n by n square mesh with a common diagonal. Base and nodal values in beta_n are unrestricted. The zero mean of Du and the C^{1,1} Taylor estimate imply -M/2<=beta(F)<=beta_n(F)<=M/2.

**Theorem 1.** For every M>=0 and eta>0 there is a computable n=n(M,eta) such that, simultaneously for every F with Lip DF<=M,

    beta_n(F)-eta <= beta(F) <= beta_n(F).

Equivalently J_F(A,u)>=(beta_n(F)-eta) E(u) for ALL W^{1,2} periodic maps. RC is not needed in this estimate.

### 1.1 Relative low/high-band freezing

We use the exact Fourier partition of the earlier note, Sections 3--5: P_i is the product two-dimensional de la Vallee Poussin multiplier based on 2^i, D_i=P_i-P_(i-1) (D_0=P_0). The D_i are nonnegative and sum to identity on Fourier coefficients. Approximate the input gradient X=Du by its Fejer convolutions; it suffices to consider finite Fourier fields. There is no need for a uniform bound on |X|. The quadratic-growth estimate for F ensures energy continuity under strong L2 convergence.

Keep K consecutive indices and discard g consecutive indices periodically with every possible offset. Set alpha=g/(K+g). For a given offset let Y be the discarded gradient, G_j=Dw_j the retained consecutive blocks, E_j=||G_j||_2^2, L_j=sum_(i<j)G_i. As before, write lambda=2^(-s), g=2s+1, ell_j and u_j for the lower and upper frequency bounds. Then successive retained blocks have disjoint supports,
    E_ret=sum E_j=||X-Y||_2^2<=E=||X||_2^2,
    ||w_j||_2<=sqrt(E_j)/(2pi ell_j),
    ||DG_j||_2<=16 u_j sqrt(E_j),
    u_i/ell_j<=lambda^2 2^(-(j-1-i)) for i<j.
The first block has u_1<=2^(K+g). Empty blocks may be retained in the ordering. As in the earlier proof the linear part of the telescope obeys

    sum_j |int DF(A+L_j):G_j|<=4 M lambda^2 E_ret.

Indeed project DF(A+L_j) onto frequencies >=ell_j, use the Lipschitz chain rule in W^{1,2}, Parseval and the geometrically decaying ratios. The first term vanishes by the zero mean. No bound on the absolute values of the partial sums is used.

For R(B,H)=F(B+H)-F(B)-DF(B):H, the C^{1,1} estimate gives

    |R(B,H)|<=M |H|^2/2,
    |R(B,H)-R(B,K')|<=M(|H|+|K'|)|H-K'|,
    |R(B,H)-R(B',H)|<=2M |B-B'| |H|.

The last estimate is the key change. It follows by writing R as the integral of [DF(B+tH)-DF(B)]:H over t in [0,1], using Lip DF on both terms. We do not need pointwise control of the third derivative.

For j>1 partition into m_j by m_j squares, m_j=lambda ell_j as before. On each square C freeze at B_C=A+average_C L_j rather than the center value. The L2 Poincare inequality for square cells gives

    ||A+L_j-B_C||_(L2, all cells)
       <= m_j^(-1)||DL_j||_2
       <= 16 lambda sum_(i<j) 2^(-(j-1-i)) sqrt(E_i).

The first inequality follows, for example, from the one-dimensional Poincare inequality along each coordinate (the square constant 1 suffices). Hence the sum over bands of the base-freezing errors is at most

    32 M lambda sum_(i<j) 2^(-(j-1-i)) sqrt(E_i E_j)
       <=64 M lambda E_ret.

This bound is relative to total gradient energy and depends neither on an L-infinity bound on X nor on D^3 F. It is uniform for all F with the stated Hessian bound. The cell partitions and their shifts can be selected independently of F.

### 1.2 Boundary localization and improved mesh interpolation

Use boundary width theta as in the previous theorem, with 0<theta<1/4 and lambda<=theta/16. A translated square grid ensures that at most 4 theta E_j of the G_j squared energy lies in the boundary layers, by averaging translations. On each cell the actual localized potential chi w_j has gradient H_j=chi G_j+w_j tensor Dchi; take the product smoothstep cutoff with |Dchi|<=16 m_j/theta, |D²chi|<=64 m_j²/theta².

The aggregate L2 norm of H_j is <=2 sqrt(E_j), its squared norm on boundary layers is <=(8 theta+512 lambda²/theta²) E_j, and its difference from G_j in L2 is at most (2 sqrt(theta)+16 lambda/theta) sqrt(E_j). Therefore the change of Taylor remainder after base freezing is bounded by M(6 theta+256 lambda²/theta²) E_j. On scaling each cell to unit size, with scaled potential U_C whose gradient is unchanged, the weighted aggregate H² seminorm is <=H0 sqrt(E_j), where

    H0=16*2^(K+g+2)/lambda +32/theta+64/theta².

The first block uses its original periodic potential, with no localization or base freezing, and obeys the same bound. These conclusions follow by the product rule and the Fourier bounds in Section 1.1; they are the estimates in Sections 4--5 of the earlier note with the new L2 base freezing.

We also improve the earlier 1/sqrt(n) finite-element interpolation bound to 8/n. Let h=1/n, n>=4. For any periodic W^{2,2} map U convolve with the normalized square box kernel of radius h in each coordinate, producing U_h. Then ||DU_h-DU||_2<=sqrt(2)h||D²U||_2. On a mesh square C the Hessian sup norm of U_h is bounded by ||D²U||_(L2,C+[-h,h]^2)/(2h), by Cauchy-Schwarz. The convolved derivatives are continuous by L2 translation continuity. Interpolate U_h at the nodes. Each gradient column on a triangle is the difference quotient on one horizontal or vertical edge. Comparing with DU_h on the triangle via the mean-value integral gives pointwise Frobenius error at most 2h times the preceding local Hessian sup norm. Each enlarged square has overlap at most 16 almost everywhere on the periodic torus. Summing the squared errors gives ||D I_n U_h-DU_h||_2<=4h||D²U||_2. Consequently

    ||D I_n U_h-DU||_2<=8/n ||D²U||_2.

Choose n with 8H0/n<=zeta<=1. The weighted aggregate mesh approximation error in each band is <=zeta sqrt(E_j), and the aggregate gradient norm after interpolation is <=(2+zeta)sqrt(E_j). Thus the R-error is <=M(4+zeta)zeta E_j. Both the compact-boundary localization and the periodic interpolant are actual compatible maps.

### 1.3 Complete budget

Use the following notation:

    gamma=2 sqrt(theta)+16 lambda/theta+zeta,
    e_loc=4M lambda²+64M lambda
             +M(6theta+256lambda²/theta²)+M(4+zeta)zeta.

For every offset the total retained-field gap differs from the weighted sum of local periodic mesh gaps by <=e_loc E_ret. The weighted squared gradient energy S_mesh satisfies

    |S_mesh-E_ret|<=(2 gamma+gamma²) E_ret.

This is obtained by comparing the L2 norms in each band using the cutoff and interpolation errors, and summing. Since every local mesh gap is >= beta_n(F) times its own energy, even at its frozen base, we conclude

    J_F(A,X-Y)>= beta_n(F) E_ret
                 -[e_loc+(M/2)(2gamma+gamma²)] E_ret.

Here J_F(A,X-Y) denotes the integral at the compatible retained gradient. Average over offsets. The discarded multiplier satisfies avg Y=alpha X and avg ||Y||²<=alpha E. Also avg E_ret>=(1-2alpha)E. Taylor expansion about A+X, with int X=0, gives

    avg J_F(A,X-Y)<=J_F(A,X)+(3/2) M alpha E,

since |int DF(A+X):X|<=M E. Using |beta_n(F)|<=M/2 in the lower bound for the average yields

    J_F(A,X)>=
      [beta_n(F)-(5/2)M alpha-e_loc-(M/2)(2gamma+gamma²)] E.       (1)

This estimate has no amplitude or regularity parameter beyond Lip DF.

For explicit parameters take

    rho=min(1/16, eta/[1024(M+1)]),
    theta=rho², zeta=rho,
    s=ceil(log2(16/rho³)), lambda=2^(-s), g=2s+1,
    K=max(1,ceil(64g(M+1)/eta)).

For rational M and eta the logarithmic ceilings can be computed by rational power-of-two comparisons. Then alpha<=eta/[64(M+1)], gamma<=4rho, and the total error in (1) is <eta. For example the respective contributions to e_loc are bounded by M rho, M rho, 7M rho², and 5M rho; (M/2)(2gamma+gamma²)<= (9/2) M rho. Combined with the alpha term the sum is strictly less than eta. These constants deliberately overestimate the actual error.

An explicit integer mesh side is n=2^(L+Z+3), with

    D=ceil(log2(1/theta)), Z=ceil(log2(1/zeta)),
    L=max(K+g+s+6,5+D,6+2D)+2.

Each summand of H0 is <=2^(L-2); hence H0<=2^L and 8H0/n<=2^(-Z)<=zeta. Passing to the original W^{1,2} map by strong Fejer approximation gives (1). This proves Theorem 1.

## 2. Normalize the entire exact relative-margin problem

Let C be the class of all globally C^{1,1} RC F satisfying

    F(0)=0, DF(0)=0, Lip DF<=1.

It is invariant under translation/recentering and quadratic rescaling of the matrix argument:

    F_(A,a)(X)=[F(A+aX)-F(A)-a DF(A):X]/a², a>0.

For any nonconstant gradient choose a=sqrt(E(u)), use u/a and F_(A,a). This preserves the relative margin, puts the base at zero and the gradient energy at one, and preserves RC and the global Hessian bound. Define

    beta_* = inf_(F in C) beta(F),    beta_n^* = inf_(F in C) beta_n(F).

Both belong to [-1/2,0] (zero energy F is admissible). Theorem 1 gives

    beta_n^* - eta <= beta_* <= beta_n^*,                        (2)

with one n=n(1,eta) for the whole class. Unlike the previous absolute-gap extraction, (2) preserves the relative deficit and the energy normalization.

**Exact equivalence.** beta_*=0 iff unrestricted finite-valued planar Morrey is true. In the negative direction, a strict W^{1,2} witness for any F in C can be smoothed periodically in W^{1,2}; quadratic growth preserves its negative sign. In the converse direction use the earlier [bounded-deficit normalization](IWANIEC_MORREY_SIGNED_TRACE_FOLD_TRANSFER.md): any unrestricted strict Lipschitz witness survives replacing the integrand on a large ball by its maximum with a steep convex radial linear-tail barrier and gluing to the barrier outside. The resulting globally RC energy is globally Lipschitz (coordinate convexity and fixed asymptotic slopes). Mollify in matrix space at sufficiently small scale; the negative sign survives, the mollified energy is smooth RC with finite globally Lipschitz derivative. Subtract its affine tangent and divide by a positive Hessian bound. The resulting F belongs to C and has a strictly negative relative gap. No uniform positive size of that gap is claimed.

## 3. Hessian-normalization-preserving finite data repair

The earlier [degree-free repair](IWANIEC_MORREY_DEGREE_FREE_FINITE_FILLINGS.md) normalized the Lipschitz constant of the energy. For (2) we need to preserve instead the Lipschitz constant of the derivative. The following construction uses both upper and lower midpoint data and a logarithmically slow cutoff, rather than a steep linear tail.

Fix rational 0<tau<=1, radius r>=1, and a finite rational set S0 in the Frobenius ball B_r including 0. Set

    mu=tau/128, k=ceil(256/mu), R=r*2^k,
    L0=4(R+4), delta=tau/(1024 L0),
    t=min(1,mu delta²/(256 L0)),
    h=min(1/4,mu t²/(256 L0)).

Choose all bases Y in h Z^4 within [-R-delta-h,R+delta+h]^4. Choose all general directions H' in h Z^4 within [-1-h,1+h]^4, and all rank-one directions H'=u' tensor v' with u',v' from the analogous two-coordinate grid. Include Y and Y±tH' in a finite set S together with S0. Use the following finite rational LP constraints on the scalar sample values w:

    w_0=0, |w_s|<=|s|²/2,
    |w_s-w_q|<=L0 |s-q|_1    (all sample pairs),
    |w_(Y+tH')+w_(Y-tH')-2w_Y|<=t² |H'|²    (general directions),
    w_(Y+tH')+w_(Y-tH')-2w_Y>=0            (rank-one directions).

Every F in C restricts to feasible data. The values and derivative normalization give |F(s)|<=|s|²/2. Every segment connecting sample points lies in the coordinate cube of radius R+4, where the Lipschitz constant in entrywise 1-norm is <=2(R+4). The second difference upper/lower bound follows from Lip DF<=1. If a rounded rank-one direction is also included in the general direction grid the repeated inequalities cause no problem.

**Theorem 2 (relative repair).** Any feasible w extends up to the following controlled error to a function F in C. For every finite law of slopes supported in S0 with mean zero, and squared energy E in [1/2,2],

    |J_F/E - (sum_X p_X w_X)/E| <= tau/8.                       (3)

The same F works for every such law supported in S0. We do not assert pointwise exact extension of the samples.

**Proof.** Use the McShane extension f0(X)=min_(s in S) (w_s+L0|X-s|_1), which is globally L0-Lipschitz in this norm and matches the data. For unit H and X in the cube of radius R+delta, round the base and direction to the grids with coordinate error <=h. A general rounded direction has |H'|²<=1+5h; a rank-one direction is rounded by rounding each of its two unit vector factors, giving entrywise direction error <=12h. Comparing the midpoint data with the exact base and direction gives general second-difference absolute upper bound t²(1+5h)+40 L0 h and rank-one lower bound -40 L0 h. These follow from |X-Y|_1<=4h, t<=1, and the two endpoint plus twice midpoint Lipschitz errors.

Smooth f0 with the four-coordinate product probability kernel
    rho_delta(s)=15/(16 delta)(1-(s/delta)²)² for |s|<=delta, zero otherwise.
Then g=f0*rho satisfies |g-f0|<=4L0 delta. As in the earlier midpoint repair, the directional third derivative of g has absolute bound 128 L0/delta²: combine the L-infinity bound 2L0 on weak directional derivatives of f0 with the L1 bound 64/delta² on second directional derivatives of the product kernel. Differentiation of the convolution gives continuous derivatives by L1 translation continuity. Averaging the midpoint bounds and applying Taylor to the smoothed second differences yields on [-R,R]^4

    ||D²g||op<=1+5h+40 L0 h/t²+43 L0 t/delta²<=1+mu,
    D²g[H,H]>=-mu for all unit rank-one H.

The parameter choice gives the first error <=(5+40+43)mu/256. Subtract g(0)+Dg(0):X and denote the result by gbar. On B_R, |Dgbar(X)|<=(1+mu)|X| and |gbar(X)|<=(1+mu)|X|²/2.

A slowly varying radial cutoff prevents the normalization from being lost when globalizing. For r<|X|<R put

    chi(X)=p(log(|X|/r)/S), S=log(R/r),
    p(v)=1-10v³+15v⁴-6v⁵.

Set chi=1 on B_r and zero outside B_R. The polynomial is nonincreasing from one to zero; its first and second derivatives vanish at the endpoints. Since |p'|<=2, |p''|<=60 and S=k log 2>=128/mu, the Euclidean radial estimates on the annulus are

    |Dchi|<=mu/(64 |X|),
    ||D²chi||op<=mu/(32 |X|²).

In particular 2/S+60/S²<=mu/32 for mu<=1. The product-rule error in D²(chi gbar), relative to chi D²gbar, has operator norm <=(1+mu)mu(1/32+1/64)<mu. Hence the compactly supported product has Hessian bound 1+2mu and rank-one Hessian lower bound -2mu globally. At the endpoints of the annulus, C² gluing follows from the vanishing cutoff derivatives. Thus

    F(X)=[chi(X) gbar(X)+mu |X|²]/(1+4mu)

is globally C^{1,1}, RC, of derivative-Lipschitz constant <=1, and F(0)=DF(0)=0. It belongs to C. On S0 the cutoff is identically one. The affine recentering integrates out by the zero mean of each law. Since the sample absolute values satisfy |w_X|<=|X|²/2, its normalized sampled gap has modulus <=1/2. The smoothing error in J is <=8 L0 delta. Thus, using E>=1/2 and dividing by 1+4mu,

    |J_F/E - sum p_X w_X/E| <=16 L0 delta+3mu<=tau/8.

This is (3), with the Hessian normalization preserved exactly. QED.

## 4. Explicit finite rational intervals for beta_* itself

Given any rational 0<tau<=1, choose n=n(1,tau/4) from Theorem 1. By quadratic rescaling it suffices at this mesh to take base zero and E=1. Each constant mesh gradient has Frobenius norm <=sqrt(2)n, since each triangle has area 1/(2n²). After subtracting the value at one fixed vertex, all nodal values have magnitude <=2n by integrating this Lipschitz bound along paths in the unit square.

Set d_u=tau/128 and h_u=tau/(512n). Round the two nodal coordinates independently to h_u Z, periodically and keeping that vertex at zero. Every gradient changes by Frobenius norm <=4nh_u=d_u; its new L2 energy is in [1/2,2]. For F in C, the difference in its two gaps is at most 3d_u by the C^{1,1} remainder estimate and Cauchy-Schwarz, and the difference in squared energies is also <=3d_u. Since the original gap has absolute value <=1/2, the relative margin changes by at most 10d_u<=tau/8 (the denominator is at least 1/2).

Take the finite family of all periodic mesh nodal assignments from h_u Z intersect [-2n-1,2n+1], the fixed vertex zero, and squared gradient energy in [1/2,2]. There are finitely many rational slopes, each of Frobenius norm <=2n by the energy upper bound. Take their union with zero as S0, use r=2n+1 and Theorem 2. For each nodal assignment minimize the relative sampled gap, a rational linear functional of the common finite LP data variables. Take the minimum m_grid of these finite rational optima. The bounded polytope is nonempty (zero sample data are feasible); every retained nodal map is a genuine gradient and has rational positive energy. No floating solution is trusted in this definition.

Let m_nodal be the infimum over the retained finite nodal assignments and true F in C. The restriction and repair give

    m_grid<=m_nodal<=m_grid+tau/8.

Nodal rounding and normalization give

    beta_n^*<=m_nodal<=beta_n^*+tau/8.

Using (2) with eta=tau/4 gives the explicit interval

    m_grid - 3tau/8 <= beta_* <= m_grid + tau/8.                 (4)

Its width is tau/2, and it may be intersected with [-1/2,0]. This proves the claimed uniform finite approximation to the universal optimal relative margin, with no additional amplitude change or attenuation of a negative relative gap. The finite LP can also produce an actual negative witness via Theorem 2 whenever m_grid+tau/8<0. The original problem is equivalent to beta_*=0; (4) does NOT decide that equality in a finite number of tolerance levels.

## 5. An exact condition-number alternative, and the remaining amplification gate

Suppose a particular globally C^{1,1} F has Lip DF<=M and is uniformly strongly RC with known margin m>0, meaning F-(m/2)|X|² is RC. Choose n=n(M,m/8). Exactly one of the following conditions holds:

(a) beta_n(F)>=m/4. Then Theorem 1 proves global strong QC,
    J_F(A,u)>=(m/8) E(u)
for all compatible W^{1,2} gradients and all bases.

(b) beta_n(F)<m/4. Then some actual finite mesh gradient has relative gap <m/4. The same witness gives a strict negative gap for the globally strongly RC energy F-(m/4)|X|², whose rank-one curvature margin is still m/2. This is a genuine planar Morrey counterexample, even if F itself happened to be QC.

In particular for semialgebraic F with certified global m,M, the branch inequality is a finite real-algebraic universal inequality: quantify over all real nodal values and the base and express the evaluation formula by its semialgebraic graph. The negative branch has an explicit finite mesh witness by the negation of that sentence. This alternative depends only on the *known* condition bounds, not on the unknown gap of the input F. It is not a decision procedure for whether F itself is QC in branch (b).

One can also test the whole uniform-condition class C with margin m>=kappa>0 using the normalized sampled-data variant (subtract the known quadratic and use the repair or a semialgebraic family); a positive verified lower margin on the selected mesh suffices for an exact all-gradient inequality. We have not carried out that computation.

We tried amplification by scaling the matrix argument and the energy, or adding a common quadratic to improve ellipticity. There is an exact obstruction to claiming that these operations alone close the uniform gate. The recentering in Section 2 preserves both the relative gap and the Hessian bound. More generally F -> c F(A+aX) changes both by the factor c a², so the normalized relative gap does not increase. Adding (q/2)|X|² shifts both beta(F) and the rank-one curvature lower bound divided by two by q/2, leaving their difference unchanged. It may increase the condition ratio but can erase the negative Jensen sign. Subtracting that quadratic restores the original gap and the original ratio. Taking a fixed-ratio approximation of every RC energy is also unjustified: for a sequence with a common positive fraction kappa of the global Hessian upper bound as LH lower bound, the midpoint curvature along any coordinate rank-one line is at least kappa times the upper midpoint curvature on any other equal-length line. This condition passes to local uniform limits, and fails for the convex function X_11² (compare the E11 and E22 lines). This example refutes a universal fixed-condition-ratio density assertion, not the possibility of a different gap amplifier or an additive decomposition into QC and well-conditioned terms.

**Principal exact gate:** either establish beta_*=0 by a genuine universal mechanism, or prove that any nonzero beta_* has a computable positive separation from zero by a new amplifier, and then solve the corresponding finite problem. The new relative approximation and condition-number alternative show what such a separation would buy; neither establishes that separation. No mathematical reason to declare that the remaining problem is nearly solved follows from effective approximation of beta_*.

## 6. Verification

The companion c11_cutoff_constants.py was actually run locally. Its SHA-256 is e25b917a9bbfa0fb18ca664a0a69e390ca762fe4bff4970e555cb2becfd1e6c0. It checked 16 exact relative localization parameter budgets and five exact normalized-repair/rounding budgets; all passed. Largest checked localization error divided by tolerance was about 0.046803. For M=1 and relative tolerances 1, 1/10, 1/100, the base-two logarithms of the explicit mesh side are respectively 9734, 121768, 1472201. These are theoretical bounds, still far beyond practical enumeration. The interval (4) has not been numerically evaluated. The arithmetic checks do not independently establish the analytic localization, convolution, or extension theorems. No Lean statements were added.
