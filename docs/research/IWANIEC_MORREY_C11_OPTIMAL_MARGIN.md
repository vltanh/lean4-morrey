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

## 7. 25 November continuation: exact optimal martingale dilation into laminates

**Outcome.** An attained primal-dual formula identifies the original unit-C11 RC deficit on EVERY centered square-integrable law with half the minimum extra variance of a martingale dilation into a laminate. No PC, isotropy, homogeneity, amplitude bound or support-size assumption is needed. For rational finite laws, rational finite splitting trees and rational martingale couplings give a complete convergent upper-certificate LP hierarchy. Optimality supplies an exact common gradient/stress coupling for every hypothetical universal near-extremizer (using P18 for the joint laminate lift). This is an exact geometric formulation of G1, not a proof of zero or an accuracy-independent finite cutoff.

### 7.1 Measures, growth, and finite laminates

Use Frobenius coordinates on real 2x2 matrices, Q(X)=|X|²/2, C the cofactor involution. For a centered probability law nu with E=int |X|² dnu<infinity, put

    d(nu)=sup_(F in normalized C11 RC class C) [-int F dnu].

The class C is exactly the one in Section 2: F(0)=DF(0)=0, Lip DF<=1. In particular |F|<=Q, and the supremum is attained by local C1 compactness of C and dominated convergence on the fixed law. The quantity d is nonnegative. Write L2 for centered square-integrable laws mu satisfying int f dmu>=f(0) for all globally Lipschitz RC f. This definition includes noncompact laws, not just classical compact laminates.

**Growth observation.** The same Jensen inequality holds for every finite RC f satisfying |f(X)|<=K(1+|X|²). To see this, on B_(2r), r>=1, take max(f, l_r) with the convex radial function l_r(X)=10(K+1)(r+1)(|X|-r)-K(1+r²)-1. On B_r the maximum equals f; at radius 2r the barrier strictly dominates f. Extend by l_r outside B_(2r), using the overlap collar. Local rank-one convexity on overlapping domains implies global RC along every rank-one line. This function has global linear growth and hence is globally Lipschitz by coordinate convexity and the asymptotic coordinate slope bounds. The functions equal f on B_r and satisfy a common bound C_K(1+|X|²): outside B_r the slope is O_K(r+1) and the offset O_K(r²+1), both controlled by |X| there. Dominated convergence proves the observation. In particular det and every F in C are legitimate tests of L2.

The L2 laws with a common second-moment bound form a convex compact set in W1: the second-moment bound ensures uniform integrability of first moments and tightness, the mean and globally Lipschitz RC tests pass to the limit, and the second moment is lower semicontinuous. Convexity uses the common barycenter zero.

**Density observation.** Every mu in L2 is a W2 limit of finite rank-one splitting trees rooted at zero, allowing finite mixtures at that same root (or a degenerate zero split). Here is a proof that controls the second moment, not just weak convergence. On signed measures of finite quadratic weighted variation take the locally convex weak topology induced by continuous functions g with |g(X)|<=K_g(1+|X|²). If mu were outside the closed convex hull of these finite trees, Hahn–Banach separation would give such a g with int g dmu < inf_tree int g. The infimum is the rank-one convex envelope Rg(0), by the splitting-tree formula: taking a first rank-one split then independent finite subtrees gives RC of the infimum, and Jensen gives maximality among RC minorants. The strict separation would require Rg(0)>-infinity. Then Rg(X) is finite at every X and has at most quadratic growth. Indeed, split zero along the first-row subspace into plus/minus the first row of X; from the positive branch split along the second row into the two matrices with that first row and plus/minus the second row. One leaf is X with mass 1/4 and all other leaves have norm at most |X|. Replace that leaf by any tree rooted at X. It follows that

    Rg(X)>=4 Rg(0)-3 K_g(1+|X|²),    Rg(X)<=g(X).

Thus Rg is finite continuous RC with quadratic growth. The growth observation gives int g dmu>=int Rg dmu>=Rg(0), a contradiction. Closure in the topology just used yields a sequence of finite trees converging weakly and in second moments: use increasingly many compactly supported continuous tests from a countable convergence-determining family, plus |X|². This is W2 convergence. The same proof works with rank-one matrices in any fixed matrix dimension, using sequential row splitting to reach an arbitrary leaf.

### 7.2 Exact primal-dual formula, including unbounded laws

A martingale coupling (X,Y) means Law(X)=nu, E[Y|X]=X; require Law(Y)=mu in L2. The cost is half the extra variance, since

    E|Y-X|²=E|Y|²-E|X|².

Such couplings always exist. For example choose one of the two rows independently with equal probabilities and retain that row of X doubled while setting the other to zero. The target law is a mean-zero mixture of row-subspace laws, hence a laminate, and E|Y|²=2E. More sharply, a measurable singular-value decomposition X=sigma1 R1+sigma2 R2 with orthonormal rank-one R_i gives a rank-one target Y=(sigma1+sigma2)R_i with conditional probability sigma_i/(sigma1+sigma2), and Y=0 if X=0. The centered target is supported on the rank-one cone and is a laminate: any smooth RC test is above its tangent at zero on each rank-one ray, so integrate; mollify to handle Lipschitz RC tests. Its second moment is E+2 int |det X|. This supplies an elementary exact check of feasibility and of the cost scale.

**Theorem (attained martingale-dilation duality).**

    d(nu) = min_(martingale couplings X,Y, Law(Y) in L2) E|Y-X|²/2.       (10)

Proof of the easy inequality. For F in C, G=Q-F is convex. The laminate Jensen inequality and conditional convex Jensen give

    0<=E F(Y)=E Q(Y)-E G(Y)
             <=E Q(Y)-E G(X)
             =E F(X)+E|Y-X|²/2.

Take sup over F and inf over couplings.

For the reverse inequality, equivalently minimize int Q dmu over mu in L2 dominating nu in convex order. We use Strassen's classical martingale-coupling theorem, [The existence of probability measures with given marginals, Ann. Math. Statist. 36 (1965), 423–439, Theorem 8](https://doi.org/10.1214/aoms/1177700153): for probability measures on finite-dimensional Euclidean space with finite first moments, convex order is equivalent to existence of a coupling with the stated conditional mean. Convex order can be tested by globally Lipschitz convex g: an arbitrary finite convex function is the increasing supremum of finite maxima of its supporting affine functions, each maximum Lipschitz, so apply monotone convergence after subtracting a common affine lower bound. Thus the domination constraints are W1 closed. Compactness of cost sublevels established above gives attainment of the minimum l of int Q dmu.

Fix any 0<=r<l. The compact cost sublevel r fails the full family of convex-order tests. By the finite intersection property, some finite list g_1,...,g_k of convex Lipschitz tests suffices to exclude that sublevel. Form the finite-dimensional convex set

    S={(a,t): exists mu in L2 with
              a_i<=int g_i dmu-int g_i dnu for every i,
              t>=int Q dmu}.

This set is closed: for any convergent sequence of its points the witnesses have a bounded second moment, so take a W1-converging subsequence and use lower semicontinuity of the cost. The point (0,r) lies outside S. Strict separation, using downward closure in each a and upward closure in t, gives coefficients c>=0 and lambda_i>=0 with

    inf_(mu in L2) [c int Q dmu - sum_i lambda_i(int g_i dmu-int g_i dnu)] > c r.

In fact c>0: a feasible convex-order dominating law would give a nonpositive value if c=0. Divide by c and let g=sum_i (lambda_i/c) g_i, a convex globally Lipschitz function. Then

    int g dnu + inf_(mu in L2) int (Q-g) dmu > r.

Set f=R(Q-g). Since Q-g is bounded below, f is finite RC. It is 1-semiconcave: each finite splitting tree translated to base B gives a function of B equal to an average of translates of Q-g, minus Q(B) this is concave, and an infimum of concave functions is concave. Taking the infimum over all such trees proves f-Q concave. The full unit derivative bound follows from this upper bound plus rank-one convexity in 2x2, not from an assumed lower Hessian estimate. Mollify, and write any matrix direction V=R+S as a sum of two orthogonal rank-one directions using its singular-value decomposition. For the smooth Hessian H of the mollification,

    H[V,V]+H[R-S,R-S]=2H[R,R]+2H[S,S]>=0,
    H[R-S,R-S]<=|R-S|²=|V|².

Hence -I<=H<=I. Passage to the locally uniform limit gives a globally C11 f with Lip Df<=1 (local gradient convergence follows from the common Taylor bounds and uniform function convergence). Subtract the affine tangent at zero to get a member of C. Also inf_(mu in L2) int(Q-g) dmu=f(0): the lower bound follows by Jensen for f (quadratic-growth test), the upper bound by the finite splitting-tree formula. Consequently

    d(nu)>= f(0)-int f dnu
          >= f(0)-int(Q-g) dnu > r-E/2.

Let r increase to l; the l=0 case follows from the easy inequality and d>=0. This proves (10) with both optima attained. The affine/mean-zero reduction treats arbitrary barycenters by translation.

An elementary calibration, useful for checking the new optimization, is

    |int det X dnu| <= d(nu) <= int |det X| dnu.

The lower bound uses F=+/-det, the upper bound the singular-value dilation above. Thus the cost is known exactly for determinant-one-sign laws. Such nonzero determinant examples are NOT planar gradient witnesses. Actual centered periodic gradients have determinant mean zero.

For actual centered periodic W1,2 gradients X, the supremum of d(Law(X))/E is EXACTLY b=-beta_* by the definitions (and the equivalence with unrestricted finite-valued Morrey is Section 2). Therefore (10) is the original G1 in primal geometry: construct a cheaper laminate dilation, with zero extra variance as the desired endpoint. The current P15/P16 hand bound implies that every actual gradient law admits a laminate dilation of variance at most 5E/4 (in fact strictly below it for E>0). This numerical constant is inherited, NOT a newly improved universal bound.

### 7.3 Complete finite rational upper certificates for a fixed rational law

Let nu be finite with rational atoms x_i and rational probabilities a_i, mean zero. The infimum in (10) is unchanged if one restricts Y to a rational finite rank-one splitting tree (allowing finite mixtures) with a rational martingale coupling to nu. Proof:

Take an optimal mu from (10), and finite trees mu_n -> mu in W2 from Section 7.1. Approximate the splitting weights and the two factors of each rank-one increment by rationals, keeping the root zero and defining child matrices as parent+(1-w)R and parent-wR. This preserves the rank-one barycentric split exactly. For each fixed finite tree the resulting laws converge in W2 as the parameters converge. Choose the rational approximations sufficiently close to retain mu_n -> mu in W2.

Glue an optimal W2 coupling of mu to mu_n to the optimal martingale coupling (X,Y) from nu to mu, conditioning on Y, to obtain Y_n of law mu_n and

    || E[Y_n|X]-X ||_2 <= W2(mu_n,mu)->0.

Since the marginals nu and mu_n are rational finite laws, approximate the X,Y_n transport matrix by a rational matrix with exactly the same two marginals: rational points are dense in a nonempty rational transportation polytope (e.g. convex combinations of its rational vertices). Choose approximation errors small enough that the conditional-mean error e_n(X)=E[Y_n|X]-X still tends to zero in L2. It is now rational on every atom and has mean zero. If the error vanishes, the coupling already works.

Otherwise choose rational delta_n>0 tending to zero with ||e_n||_2/delta_n bounded, e.g. delta_n tending to zero more slowly than the error. Define the centered rational finite law of

    Z_n = X - [(1-delta_n)/delta_n] e_n(X).

Conditionally on X, mix the law of Y_n with weight 1-delta_n and the simple row-doubling dilation of Z_n with weight delta_n. Its mean given X is exactly X. Its marginal is a mixture of the rational finite tree mu_n and the row-doubling target of Z_n. Each row-doubling target restricted to that row has mean zero, and every finite probability law in a row subspace is obtained by finite binary rank-one splits: successively split off one atom from the mean of the remaining atoms. All probabilities and matrices are rational. Hence the new target is a rational finite tree mixture. Its second moment tends to int |Y|² because the row-doubling second moment is 2||Z_n||²_2, uniformly bounded. This proves the assertion. No compactness bound on the number of leaves or a finite optimum at cost zero is claimed.

It gives a genuine finite LP upper certificate mechanism. Enumerate rational finite splitting trees T with leaves y_(T,l) and weights w_(T,l). For any finite tree library, take mixture variables alpha_T>=0 and transport variables pi_(i,T,l)>=0. Impose

    sum_T alpha_T=1;
    sum_(T,l) pi_(i,T,l)=a_i;
    sum_i pi_(i,T,l)=alpha_T w_(T,l);
    sum_(T,l) pi_(i,T,l) y_(T,l)=a_i x_i.

Minimize the rational linear objective

    (1/2) sum_(i,T,l) pi_(i,T,l) |y_(T,l)-x_i|².

Every exact feasible solution is a valid upper bound on the maximum unit-Hessian RC Jensen deficit for this input law. An increasing exhaustive library has optima decreasing to d(nu), by the preceding proof; infeasible stages mean only that the current library is insufficient. The finite-data repair in Section 3 provides the opposite finite-accuracy enclosure for a rational slope law (rescale to the required variance interval). Thus this is a complete positive-accuracy *upper* proof hierarchy using explicit finite trees and martingale couplings, not a hierarchy of sampled RC constraints mistaken for sufficiency. The finite-mesh normalization in Section 4 can use such certificates on its finite rounded laws. There is still no uniform exact-zero stopping bound. The certificate of cost zero requires an actual zero-cost finite-tree representation; a laminate need not admit such a finite representation.

### 7.4 Exact common constitutive lift, not a stand-alone moment relaxation

For any fixed nu choose an optimizer F in C and an optimal martingale coupling X,Y. Let p=DF, R=Y-X, G=Q-F. The proof of (10) splits into two nonnegative slacks:

    E F(X) + E|R|²/2
      = E F(Y) + E [G(Y)-G(X)-DG(X):R] = 0.

Both vanish. Convex differentiability gives

    E F(Y)=0,    DG(Y)=DG(X) a.s.,
    p(Y)=p(X)+R,   E[R|X]=0,   E|R|²=2 d(nu).                (11)

This is an exact common-energy contact constraint on a whole martingale coupling, including its conditional distribution, not simply covariance constraints. Along the entire segment from X to Y, G is affine and F has the upper quadratic curvature with equality. The determinant identity for mu and the martingale condition give E det R=-E det X.

For a general approximately optimal energy F in C, write e=E F(X)+d(nu)>=0 and keep an optimal dilation. Each slack above is <=e. Since Lip DG<=2, the convex smooth Bregman lower bound gives

    E|p(Y)-p(X)-R|² <= 4 e.

For completeness, apply the ordinary descent estimate to the convex nonnegative function G(Z)-G(X)-DG(X):(Z-X), which has minimum zero at X and derivative-Lipschitz constant two. Its value at Y is at least |DG(Y)-DG(X)|²/4. This bound does not require compact support.

At exact equality, the joint law of (Y,C p(Y)) is a centered square-integrable laminate on 4x2 matrices, using the existing hand normalized joint-flow theorem P18. Here are the unbounded-law details. Since mu is a laminate, translating it shows E F(Y+h)-F(h)>=0 for all h with equality at zero, hence E p(Y)=0 by differentiation under the integral. Scaling the law by t, or applying arbitrary fixed left/right linear changes, retains laminate Jensen; first differentiation at the identity yields E Y:p(Y)=0, E Y p(Y)^T=0 and E Y^T p(Y)=0. Quadratic growth and the unit derivative bound justify all differentiations. For any globally C11 RC K on 4x2 with zero tangent at zero, P18 supplies normalized RC F_t with F_t(0)=0 and first-order change K(Y,Cp(Y))-gamma Y:p(Y), with an O(t² |Y|²) error uniformly in Y. Laminate Jensen for F_t, E F(Y)=0 and E Y:p(Y)=0 imply E K(Y,Cp(Y))>=0. By mollification and affine normalization of all globally Lipschitz RC K, the joint law is a laminate in the same L2 sense. The growth observation also applies in 4x2, using separate coordinate convexity, so all its quadratic null minors are legitimate tests. This step is dependent on P18, not new independent verification of that hand theorem.

In particular E det p(Y)=0, so (11) and E[R|X]=0 imply the exact identities for EVERY fixed-law optimal F,

    E X:p(X)=-2d(nu),
    E det p(X)=E det X,
    E X p(X)^T=-E R R^T,
    E X^T p(X)=-E R^T R.                                    (12)

For actual gradient laws the determinant on the right is zero. More strongly,

    (X,Cp(X)) -> (Y,Cp(Y))=(X,Cp(X))+(R,CR)

is an exact joint martingale dilation into a centered 4x2 laminate; its extra variance is 4d(nu), and every displacement lies in the single linear graph {(R,CR)}. This strengthens the independent necessary-generator inequalities of P18 by requiring ONE common equality laminate and ONE common martingale coupling. It does NOT assert that the input joint law, the residual R, or the spatial conditional coupling is a compatible gradient law.

For a hypothetical universal negative b>0, choose actual gradient laws nu_j with E=1 and d(nu_j)->b; replace each energy by a fixed-law optimizer F_j from (10), without weakening the limit. Then all of (11)–(12) hold EXACTLY for each j, not just in the extremizing limit. The stabilized energies F_j+b|.|² are QC by the universal definition, so their stationarity gives the actual compatible projection V_j=C P_sol(DF_j(X_j)+2b X_j) with

    ||V_j-C(DF_j(X_j)+2b X_j)||_2 ->0.

Thus the joint coupling and the actual compatible-stress constraints can now be used together, without choosing a common amplitude bound or losing the optimum under stress interpolation. The laws and couplings may still vary with j; this does not transfer the fixed-energy constants of P19 to all F_j.

### 7.5 The new exact-zero target and what optimality forbids

The coupling exhibits a precise obstruction to the simplest contraction. For 0<=t<=1 let nu_t be the law of X+tR. It is centered, convex-order dominated by mu (convexity of every test on the segment plus convex order of nu and mu), and its variance is E+2t²d(nu). Its F-integral is exactly -(1-t²)d(nu), since G is affine on each coupling segment and the linear conditional term vanishes. The upper bound (10) using mu and the matching lower bound using F prove

    d(nu_t)=(1-t²)d(nu).                                    (13)

So if d(nu)>0 no nontrivial conditional compression of an optimal coupling is already a laminate. The actual compatibility of nu must be used to construct a DIFFERENT coupling or laminate, or to prove that a nonzero common residual in (11) is impossible for gradients.

The most direct positive attack is now a primal variance contraction: for actual compatible gradient laws with d(nu)/E approaching b, construct a new laminate dilation with extra variance <=2 theta d(nu) for some theta<1, or derive contradiction from the exact equality laminate and conditional-flat identities (11)–(12) using actual stabilized stress compatibility. This would close G1. The conditional-flat structure is an exact additional restriction; merely imposing a finite sample of its moments or enumerating ever larger tree libraries is not closure. No such cheaper dilation is established here. In particular Strassen's coupling alone does not make the residual a gradient; do not apply beta_* to R or to arbitrary conditional sublaws without a separate compatibility theorem. No theorem of joint gradient realization is claimed.

### 7.6 Executed checks, limits and provenance

Actual Python standard-library Fraction and SymPy checks: 12 two-atom determinant-sign controls with exact conditional mean, determinant calibration, stress equality, cost and four interpolation parameters each; four rational mean-repair controls at scales 1/10, 1/100, 1/1000, 1/10000, giving costs decreasing to the analytic value 2; and the scalar interpolation cost identity. Actual SciPy/HiGHS LPs for two finite tree libraries: the artificial two-atom law +/-diag(2,1) gave exact rational feasible cost 2 (lower bound from det); the genuine independent two-row periodic sawtooth gradient law on diag(+/-2,+/-1) gave cost 0 (one two-level splitting tree). All LP equality constraints and objectives were replayed with Fraction after rational reconstruction. These are controls of the algebra and the finite certificate format, not tests over the unrestricted family. No full hierarchy or large search was executed; no new script file was necessary. The analytic duality uses standard Strassen and Hahn–Banach, and the joint lift uses P18. No independent review, Lean verification, novelty clearance, improved numerical beta_* bound or proof of beta_*=0 is claimed.

## 8. 25 November: exact nearest-laminate projection and a finite occupation-flow LP

**Outcome.** There is a second attained optimization which complements (10) without any Hamiltonian-flow assumption: the ordinary squared Wasserstein distance to laminates equals the optimal sum of squared *smaller* singular values of adaptive martingale increments, plus unresolved variance. Every closest laminate has a complementary laminate on the SAME probability space, and the stacked cofactor lift is itself a laminate. This gives a purely primal proof of the joint-laminate conclusion of P21, an exact Hilbert-space formulation of beta_*, and a uniform exponential tail bound for the optimal dilation of every bounded input law. Separately, an occupation-measure LP handles ALL splitting depths and cyclic splitting networks on any finite rational matrix grid. The finite LP detects exactly zero for both the four-well cycle and the N18 six-well example, neither of which has a finite splitting tree on its terminal support. There is no claim of a uniform exact-zero grid cutoff or a proof of the missing spatial inequality.

### 8.1 Ordinary distance to laminates is an exact adaptive projection cost

For a centered square-integrable matrix variable S, define

    D2(S)=inf E|S-Y|²,

where Y has a centered L2 laminate law, with arbitrary coupling to S. This is an ordinary Wasserstein optimization; unlike (10) it has no constraint E[Y|S]=S. A minimizer exists: a minimizing sequence has uniformly bounded second moments, tight joint laws, fixed first marginal, and centered laminate second marginal closed under weak convergence with bounded second moments by the Lipschitz test characterization in Section 7.1. Use lower semicontinuity of the nonnegative quadratic cost.

Allow arbitrary auxiliary randomness and finite binary filtrations starting at the trivial sigma algebra; write M_j=E[S|F_j], M_0=0. No terminal revelation assumption is needed. Let sigma1>=sigma2 denote the two singular values of a planar matrix. Then

    D2(S)=inf_F E[|S-M_n|² + sum_j sigma2(Delta M_j)²].       (14)

Indeed, at a binary split the two possible increments of M are proportional to a single matrix. Choose its leading right singular unit vector n_j, measurable at the parent node, and put P_j=n_j n_j^T. The martingale A with increments Delta M_j P_j is a finite rank-one splitting tree. Orthogonality of martingale differences and of the two right projections gives

    E|S-A_n|²=E|S-M_n|²+E sum_j |Delta M_j(I-P_j)|².

This proves the upper bound in (14). For the reverse, approximate any coupled laminate Y in W2 by finite splitting trees Y_l rooted at zero (Section 7.1). Couple these approximants to the original pair S,Y through Y. On each tree let Y_j be the node values and M_j=E[S|F_j]. Each tree increment of Y is rank one with a fixed right direction n_j at the parent node (choose arbitrarily if the split is degenerate). Since Delta Y_j=Delta Y_j P_j,

    E|S-Y_l|²
      = U_l + E sum_j |Delta M_j(I-P_j)|² + V_l,
    U_l=E|S-M_n|²,
    V_l=E sum_j |Delta M_j P_j-Delta Y_j|².                 (15)

The middle term is at least E sum sigma2². This proves the reverse inequality by W2 approximation. In particular (14) differs from the earlier determinant-defect objective D in R04: it is the exact squared Wasserstein distance, not a sufficient determinant penalty.

### 8.2 Every closest laminate has a complementary laminate, jointly

Let Y be ANY minimizing coupling in (14). Choose the preceding finite tree approximants so e_l=E|S-Y_l|²-D2(S) tends to zero. Improve the tree by taking the projected increments Delta M_j P_j. Append finite binary refinements revealing S in L2 to arbitrary accuracy, using leading right singular directions for those extra increments. At least half of the newly revealed variance is captured because sigma1²>=|Delta M|²/2. Since D2 is a global infimum, (15) gives

    V_l + U_l/2 <= e_l.                                     (16)

This inequality follows by taking the terminal refinement accuracy to zero for each fixed l; no uniform depth or rate of the original laminate approximation is presumed. Also the sum of the losses sigma1(Delta M_j)²-|Delta M_j P_j|² tends to zero: replacing the original directions by leading singular directions is another admissible tree.

On the original finite tree set

    A_n=sum_j Delta M_j P_j,
    B_n=sum_j Delta M_j(I-P_j).

Both are finite rank-one martingales. Their stacked pair (A_n,C B_n) is a finite rank-one splitting tree in 4x2: if Delta A=a tensor n, Delta B=b tensor Jn, then Delta(C B) has right direction n (up to sign). Formula (16) gives

    ||A_n-Y||_2 ->0,    ||B_n-(S-Y)||_2 ->0

under the coupled approximations, because ||A_n-Y_l||²=V_l and M_n=A_n+B_n. Therefore the common law

    (Y,C(S-Y)) is an L2 laminate on 4x2 matrices.             (17)

Here closure uses the growth-controlled characterization in Section 7.1, including its stated extension to 4x2. In particular S-Y is itself a laminate after cofactor transformation, and E Y:(S-Y)=0 (also follows by optimizing scalar multiples of Y). This result does not require S to be a gradient, bounded, or a constitutive stress. It holds for every closest coupling, not just an example chosen by the construction.

### 8.3 Apply the projection to the actual universal beta problem

Define on centered square-integrable fields

    N(X)=sqrt(E|X|²+2d(Law(X))).

This is a norm, equivalent to the Hilbert norm: ||X||_2<=N(X)<=sqrt(2)||X||_2 by (10) and row doubling. Indeed N²/2 is sup_F E[Q(X)-F(X)], a convex functional because Q-F is convex for every F in C; scalar homogeneity of the class gives absolute degree-two homogeneity, so its unit sublevel is the balanced convex unit ball of the stated norm. Let N* be the polar norm on the same centered Hilbert space.

The dual norm has the exact expression

    N*(S)=sup E S:Y,   Law(Y) laminate, ||Y||_2<=1,          (18)

allowing extensions of the probability space. For the upper bound in the duality, if Y is coupled on an extension, set X=E[Y|original spatial variable]. Then E[Y|X]=X and N(X)<=||Y||_2 by (10), and E S:Y=E S:X. For the converse use the attained dilation of any X in the dual-norm test, glue it conditionally on X to S, and use E[Y|X]=X and ||Y||_2=N(X). Optimizing scalar multiples of laminate fields in (18) gives

    N*(S)²=||S||_2²-D2(S)=sup_F E sum_j sigma1(Delta M_j)².   (19)

The F under the last supremum denotes adaptive binary filtrations, not energies. The distinction is important: (19) involves only a spatial field S and conditional mean operations, and no unknown rank-one convex integrand.

On the spatial unit torus let P be the orthogonal projection in centered L2 onto rowwise compatible gradients. By Hilbert duality and (18),

    1+2b = sup_{X=P X, X!=0} N(X)²/||X||_2²
         = sup_{S!=0} ||P S||_2²/N*(S)²,       b=-beta_*.     (20)

To see the second equality take sup over Hilbert-unit gradients X of N(X)=sup_{N*(S)<=1} E X:S, interchange the two suprema, and use the definition of orthogonal projection. Thus the precise remaining spatial inequality is

    sup_F E sum_j sigma1(Delta E[S|F_j])² >= ||P S||_2²
      for EVERY centered spatial S.                          (21)

It is equivalent to unrestricted Morrey, not a stronger assumption of a common input-independent filtration. Existing P15 bounds the left side below by (4/5)||P S||², with the strict P16 improvement inherited; the exact coefficient 1 is open. An input-adaptive projection proof, or a direct contraction of the ratio in (20), would close G1.

There is a useful bridge to the P21 constitutive optimality. Let X,Y be any optimal martingale pair of (10), F an optimal energy, p=DF, G=Q-F and S=DG(X). Equation (11) gives S=Y-p(Y). Even without using P18, translating/scaling the equality laminate Y yields E p(Y)=0 and E Y:p(Y)=0. Thus E X:p(X)=-2d, E S:X=N(X)², E G(X)=N(X)²/2. For any coupled laminate Z, convexity of G and its laminate upper bound give

    E S:Z <= [||Z||²+N(X)²]/2.

Apply this also to scalar multiples of Z to obtain N*(S)<=N(X). But E S:Y=E S:X=N(X)² and ||Y||²=N(X)², so equality holds. Consequently Y is an ordinary closest laminate to S by (19). The joint conclusion of (17) now gives (Y,Cp(Y)) laminate (change the sign of the lower row block). This supplies an independent purely primal proof of the joint-laminate part of P21; the normalized Hamiltonian-flow theorem P18 is no longer required for that part.

For the universal near-extremizing sequence of Section 7.4, ||X||²=1, S=X-DF(X), d->b and P S=(1+2b)X+o(L2). Equations (19)-(20) and the exact P21 optimality give N*(S)²=1+2d, hence the hypothetical spatial capture shortfall converges to (1+2b)2b>0. It is this specific shortfall, not an arbitrary artificial moment law, that a contraction must eliminate. The complementary projection decomposition is exact; it does not say the martingale filtration is the spatial Fourier filtration or that its residual is a gradient.

### 8.4 Uniform tail and approximate support radius for optimal dilation

Suppose ||S||_infty<=B, B>0. In the projected tree proof of (17), M_j is bounded in norm by B, its jumps by 2B, and A is a martingale transform by orthogonal projections. For any stopping node tau, the conditional expected remaining squared increment sum of A is at most

    E[|S-M_tau|² | F_tau] <= B².

By the conditional maximal inequality for the squared norm, the probability of any subsequent displacement from A_tau of at least 2B is at most 1/4. One can prove this directly by stopping at the first such displacement, using orthogonality and conditional expected remaining variance; no estimate on the number of splits is required. Each crossing overshoots the threshold by at most 2B. Iteratively stop at the first displacement of at least 2B from the last stopping point. The probability of at least k crossings is at most 4^(-k). If fewer than k crossings occur, the entire path stays inside radius 4kB. The same argument holds for the complementary transform B_n (here B_n denotes the matrix martingale, not the scalar bound B).

For ANY closest laminate Y to S, pass through the L2 convergence of A_n in Section 8.2. This proves the uniform terminal bound

    P(|Y|>4kB) <= 4^(-k),     k=1,2,...,                      (22)

and likewise for S-Y. For the optimal martingale dilation of a bounded input |X|<=R, take S=DG(X), so B=2R by the unit Hessian bound and zero affine tangent. In particular every optimal target Y has tails bounded by (22) with B=2R, and P(|Y-X|>(8k+1)R)<=4^(-k). These estimates apply to the global optimizer, not merely some convenient finite tree, and are uniform in the input law and energy.

There is an explicit approximate radius consequence. Given eta>0, stop the projected approximating tree at first |A|>=4kB, or its terminal step if no crossing. Its terminal norm is at most (4k+2)B. The squared stopping error is at most B²4^(-k), using conditional remaining variance and the above maximal bound. Choose k>=1 with B 2^(-k)<=eta/2 and then a sufficiently close original tree approximant from Section 8.2. We obtain a bounded finite splitting-tree Y' coupled to Y with ||Y'-Y||_2<=eta and radius L=(4k+2)B.

To restore the original martingale constraint for X, couple through Y and set e(X)=E[Y'|X]-X; ||e||_2<=eta and |e|<=L+R. For 0<eta<=R/2 set delta=eta/R, Z=X-[(1-delta)/delta]e. Use the same mean-repair mixture as R25: with conditional probability 1-delta use Y', otherwise the row-doubling dilation of Z. The resulting marginal is a laminate and its mean given X is exactly X. Its support radius is at most

    max{L, 2[R+(L+R)/delta]}.

Its extra second moment above that of the optimum is at most 12R eta: use ||Y||<=sqrt(2)R, ||Y'||<=||Y||+eta, ||Z||<=2R, and the bound (1-delta)||Y'||²+2delta||Z||². Thus its half-variance cost is <=d+6R eta. This gives an explicit target-radius cutoff for positive ADDITIVE accuracy over the whole bounded input class; it is not an exact radius cutoff or a uniform relative bound for vanishing input variance. Rational finite trees and couplings can subsequently be approximated and corrected as in Section 7.3, with arbitrarily small additional accuracy/radius slack. No tree-depth or grid-resolution bound is asserted by this radius estimate.

### 8.5 One finite LP over all depths on a rational matrix grid

Let G be any finite rational matrix grid (a finite subset of matrix space, not necessarily a Cartesian grid) containing the origin. List every nontrivial admissible split s from parent v_s to distinct children a_s,b_s in G satisfying

    v_s=w_s a_s+(1-w_s)b_s,  0<w_s<1,
    rank(a_s-b_s)=1.

All w_s are rational and are determined by the points. For a rational centered finite input law on x_i with weights alpha_i, use variables z_s>=0 (expected split occupation), pi_(i,v)>=0 (martingale transport masses), and m_v=sum_i pi_(i,v) (terminal mass). The single finite rational LP is

    minimize sum_(i,v) pi_(i,v) |v-x_i|²/2

    m_v + sum_(s:parent=v) z_s
       = 1_(v=0) + sum_s [w_s 1_(a_s=v)+(1-w_s)1_(b_s=v)] z_s;
    sum_v pi_(i,v)=alpha_i;
    sum_v pi_(i,v) v=alpha_i x_i.

There is no bound on splitting depth in this LP. The number of split variables is at most |G|³, and the number of transport variables is input-atom-count times |G|. All finite splitting trees and mixtures on G give feasible occupation variables by aggregation, and the LP allows cycles.

**Exact converse.** For any feasible occupation solution, summing the balance proves sum m_v=1. Multiplying by |v|² and summing proves

    sum_v m_v |v|² = sum_s z_s w_s(1-w_s)|a_s-b_s|².         (23)

Every nontrivial split has a strictly positive variance increment. In particular if there are any splits the total occupation is bounded by max_G |v|² divided by the smallest positive split variance. At a state v put t_v=m_v+sum_(s:parent=v)z_s; if t_v>0, stop with probability m_v/t_v, otherwise choose split s with probability z_s/t_v and select the child with the corresponding split weight. At any unreachable state with t_v=0 choose immediate stopping. Starting from 0 this Markov process has expected visit counts <=t, by iterating the balance equations for the nonnegative transition matrix before absorption. Since sum t is finite, it stops almost surely with finite expected number of splits. Its terminal mass at each v is <=m_v, and hence equals m_v because both total masses are one. Every finite stopping truncation is a rank-one martingale on the fixed compact grid (random choice between splits with the same mean is allowed). Thus the absorbed law is a laminate by bounded convergence. The transport constraints now give a true martingale dilation. This establishes soundness and exactness of the finite-state occupation formulation, including cycles and stochastic stopping. No positivity conclusion can be drawn if a particular grid is infeasible.

The LP dual has variables f_v, u_i, h_i (matrix) with

    maximize f_0 + sum_i alpha_i(u_i+h_i:x_i);
    f_(v_s) <= w_s f_(a_s)+(1-w_s) f_(b_s);
    f_v + u_i + h_i:v <= |v-x_i|²/2.

It is a discrete rank-one-convex minorant of a minimum of quadratic obstacles. Feasible finite LP duals give lower bounds on the GRID-restricted cost only, not on the unrestricted cost unless an independently justified global extension is supplied. Every exact primal solution gives an unrestricted upper bound, and zero primal cost certifies that the input law is a laminate.

On nested exhaustive rational grids (e.g. coordinates with denominator dividing n! and norm in a box of radius n) the costs decrease to d by R25. This eliminates unbounded TREE DEPTH from each grid calculation, and in contrast with R25 it can attain exact zero with finitely many occupation variables even when no finite tree on the terminal support exists. The exact-zero mesh/resolution/geometry cutoff is still missing. In particular one should not enumerate increasingly fine grids and call finite failure a proof of nonlamination.

### 8.6 Executed LP controls, including the previous no-collapse example

The actual tests were solved with SciPy HiGHS and ALL primal equalities, nonnegative variables, dual inequalities, and equality of objectives were replayed using Python Fraction arithmetic (not floating tolerances). Diagonal coordinates (x,y) represent diag(x,y); allowable splits share one coordinate.

* Four-well cycle, minimal grid: P=((0,0),(1,0),(1,1),(0,1)), terminal atoms X=((2,0),(1,2),(-1,1),(0,-1)), weights (1,2,4,8)/15. Eight states, four splits, 36 variables, cost 0. The occupation certificate in backward cycle order is (16,8,4,2)/15 starting at (0,0). Each split is a midpoint; the return probability after one complete cycle is 1/16. No two terminal atoms are rank-one connected, so no nontrivial finite tree with those terminal atoms exists.
* N18 six-well cycle: the exact P_i, X_i and weights from [the no-local-collapse note](IWANIEC_MORREY_NO_LOCAL_COLLAPSE.md), translated by -P_1. Twelve states, six splits, 78 variables, exact cost 0, total expected splits 1292/485, variance 136332/485. This recovers the previously blocked example by a nonlocal cyclic flow, not by the refuted local move.
* Artificial +/-diag(2,1), equal weights, diagonal grid {-3,...,3}²: 49 states, 490 splits, 588 variables, exact cost 2, target variance 9. The determinant lower bound in Section 7.2 certifies that this also equals the unrestricted cost.
* Compatible independent sawtooth rows diag(+/-2,+/-1) with equal weights, same 49-state grid: 686 variables, exact cost 0, variance 5. The four-well cycle on this enlarged grid also has zero cost.

In addition, 32 rational depth-three binary-tree regression controls (seed 20261125, directions (1,0), (0,1), (3,4)/5 and (5,-12)/13) checked the orthogonal split, every two-row minor of the stacked increment, Pythagorean error identity (15), and the capture of at least half of appended unrevealed variance. These tests check finite algebra, not the general duality or stopping theorem.

For reproduction of the LP controls, the following is the executed test (with the same rational reconstruction and exact replays). It needs scipy and numpy but no external solver binaries beyond HiGHS.

```python
from fractions import Fraction as F
from itertools import combinations,product
import numpy as np
from scipy.optimize import linprog

def solve(name, atoms, masses, grid):
    grid=tuple(sorted(set(grid))); n=len(grid); r=len(atoms)
    idx={v:i for i,v in enumerate(grid)}
    splits=[]
    for a,b in combinations(grid,2):
        if a[0]!=b[0] and a[1]!=b[1]: continue
        j=0 if a[0]!=b[0] else 1
        for v in grid:
            if v[1-j]!=a[1-j] or not a[j]<v[j]<b[j]: continue
            w=F(b[j]-v[j],b[j]-a[j])
            splits.append((idx[v],idx[a],idx[b],w))
    m=n+3*r; N=len(splits)+n*r
    A=[[F(0) for _ in range(N)] for _ in range(m)]
    rhs=[F(0) for _ in range(m)]; rhs[idx[(0,0)]]=F(1)
    c=[F(0) for _ in range(N)]
    for j,(v,a,b,w) in enumerate(splits):
        A[v][j]+=1; A[a][j]-=w; A[b][j]-=1-w
    for i,(x,mass) in enumerate(zip(atoms,masses)):
        rhs[n+3*i:n+3*i+3]=[mass,mass*x[0],mass*x[1]]
        for v,y in enumerate(grid):
            j=len(splits)+i*n+v
            A[v][j]=1; A[n+3*i][j]=1
            A[n+3*i+1][j]=F(y[0]); A[n+3*i+2][j]=F(y[1])
            c[j]=sum(F((aa-bb)**2,2) for aa,bb in zip(x,y))
    res=linprog(np.array(c,float),A_eq=np.array(A,float),
                b_eq=np.array(rhs,float),bounds=(0,None),method='highs')
    assert res.success, res.message
    v=[F(float(t)).limit_denominator(10**8) for t in res.x]
    d=[F(float(t)).limit_denominator(10**8) for t in res.eqlin.marginals]
    assert min(v)>=0
    assert all(sum(a*b for a,b in zip(row,v))==b for row,b in zip(A,rhs))
    assert all(sum(d[i]*A[i][j] for i in range(m))<=c[j] for j in range(N))
    pc=sum(a*b for a,b in zip(c,v)); dc=sum(a*b for a,b in zip(d,rhs))
    assert pc==dc
    terminal=[sum(v[len(splits)+i*n+j] for i in range(r)) for j in range(n)]
    var=sum(w*(x[0]**2+x[1]**2) for w,x in zip(terminal,grid))
    source=sum(w*(x[0]**2+x[1]**2) for w,x in zip(masses,atoms))
    energy=sum(v[k]*w*(1-w)*sum((grid[a][i]-grid[b][i])**2 for i in (0,1))
               for k,(_,a,b,w) in enumerate(splits))
    assert var==energy and var-source==2*pc
    print(name,len(grid),len(splits),N,pc,sum(v[:len(splits)]),var)
    return pc

P=[(0,0),(1,0),(1,1),(0,1)]
X=[(2,0),(1,2),(-1,1),(0,-1)]
W=[F(1,15),F(2,15),F(4,15),F(8,15)]
assert all(a[0]!=b[0] and a[1]!=b[1] for a,b in combinations(X,2))
assert solve('T4 minimal grid',X,W,P+X)==0
G=list(product(range(-3,4),repeat=2))
assert solve('positive determinant artificial pair',[(-2,-1),(2,1)],[F(1,2)]*2,G)==2
assert solve('independent two-row periodic sawtooth',
             list(product([-2,2],[-1,1])),[F(1,4)]*4,G)==0
assert solve('T4 enlarged grid',X,W,G)==0
P6=[(5,2),(0,2),(0,-10),(8,-10),(8,-6),(5,-6)]
X6=[(-15,2),(0,-22),(32,-10),(8,-2),(2,-6),(5,26)]
W6=[F(k,485) for k in [9,36,24,96,192,128]]
center=lambda p:(p[0]-5,p[1]-2)
assert solve('N18 six-well cycle',[center(p) for p in X6],W6,
             [center(p) for p in P6+X6])==0
```

### 8.7 Disposition

P22 gives the exact ordinary-distance projection and complementary-laminate theorem; P23 gives the optimal-target tail and positive-accuracy radius reduction; R26 gives the finite occupation LP with cyclic exact certificates; (20)-(21) is the remaining input-adaptive spatial variance-capture gate. These advances remove the need for an analytic joint Hamiltonian assumption in P21, and remove unbounded splitting depth from the computational formulation on any fixed grid. They do not prove the universal spatial inequality, the exact-zero finite mesh cutoff, a cheaper optimal martingale dilation for every actual gradient law, or beta_*=0. The original bound remains unchanged. The hand arguments use the measure-theoretic and rank-one approximation results of Section 7, not new Lean declarations. No comprehensive novelty or independent verification claim is made.

## 9. 25 November: scalar-subordinate optimal lifts and a uniform finite-grid error theorem

**Outcome.** The complementary optimal lift in P22 has a stronger, common martingale structure: it is the limit of binary rank-one martingales whose second block is a scalar predictable contraction of the first block at EVERY split. This works for every closest coupling, not just a specially chosen minimizer. Independently, the finite occupation LP R26 now has an explicit uniform matrix-grid resolution and radius for any prescribed positive ADDITIVE accuracy on bounded input laws. The proof uses the finite LP dual, discrete rank-one inequalities, a controlled interpolation and a globally RC barrier, together with P23's exponential tails. Neither the radius nor the mesh depends on input atom count or splitting depth. Combined with R16, it gives a finite two-sided approximation to the universal b=-beta_* using rational nodal assignments and ONLY occupation LPs for the law-side computations. The spatial geometry cutoff from R16 remains enormous, and the new matrix grids are also impractically large. No exact-zero contraction, accuracy-independent cutoff or improved universal numerical beta bound is proved.

### 9.1 Every closest laminate has a scalar-subordinate joint martingale

Use the notation of Section 8.2. For any centered L2 variable S and ANY closest laminate coupling Y, let Z=C(S-Y), where C is the cofactor involution. The common law of (Y,Z) is in the W2 closure of finite binary martingales starting at (0,0) whose increments are

    (R,c R),    rank(R)<=1,    -1<=c<=1,                     (24)

with c measurable at the parent node. This is stronger than the unconstrained stacked rank-one laminate assertion (17). It does not assert that S, Y or the complementary residual is compatible with the original spatial gradient.

Proof. Use the same finite tree approximants Y_l as in (15), including the original right projections P_j onto the directions of the approximating tree increments. Put

    e_l=E|S-Y_l|²-D2(S),
    loss_j=sigma1(Delta M_j)²-|Delta M_j P_j|² >=0.

Replacing the projections by leading singular projections, and appending binary refinements to resolve S while capturing at least half the remaining variance, proves the combined excess-cost estimate

    V_l + E sum_j loss_j + U_l/2 <= e_l.                    (25)

Here V_l and U_l are defined in (15). For each binary node use an oriented orthonormal basis n,Jn of the two-dimensional domain, J denoting counterclockwise rotation by pi/2. Write the two complementary increments as a tensor n and b tensor Jn (we use a,b for target vectors only within this calculation). Their covariance Gram matrix is

    [[u,w],[w,v]],    u=|a|², v=|b|², w=a dot b.

If L denotes its larger eigenvalue minus u, then L=loss_j, v<=u+L and w²=L(u+L-v). Project b onto the line segment [-J a,J a], writing b'=c J a, |c|<=1. This gives the estimate

    |b-b'|² <= 3 L.                                        (26)

If u=0, choose b'=0. If 0<u<L, the error is at most v<=u+L<2L because zero belongs to the segment. If u>=L and u>0, the squared component parallel to a is w²/u<=2L. The squared clipping error of the perpendicular component is at most (sqrt(v)-sqrt(u))_+²<=(v-u)_+<=L. This proves (26), including L=0 (when u=0 also v=0). At a binary node a,b for the two children are proportional to a common pair, so the coefficient c obtained by projection is identical for both children and is predictable.

Keep the first projected martingale A_n from Section 8.2, and replace each complementary increment by b' tensor Jn, forming B'_n. Its cofactor increment is c a tensor n, so (A_n,C B'_n) satisfies (24). Orthogonality of martingale differences and (26) give squared error at most 3 E sum loss_j relative to the original complementary B_n. By (25), the law of this pair converges in W2 to the given (Y,C(S-Y)). In particular for every continuous function of the pair of at most quadratic growth that is convex along the directions (24), its Jensen inequality holds on the optimal joint law. For bounded S the same holds for polynomial-growth continuous tests of any finite degree: A_n and B'_n are contractions of the bounded conditional-mean martingale with jumps bounded by 2||S||_infty and the same conditional remaining variance estimate as in (22), hence have uniform exponential tails.

Some exact consequences (write vec for matrix vectorization):

    E[vec(Y) vec(Z)^T] is symmetric;
    E[vec(Y) vec(Y)^T - vec(Z) vec(Z)^T] is PSD.

Indeed the respective contributions at every split are c vec(R)vec(R)^T and (1-c²)vec(R)vec(R)^T. The second matrix is in the closed cone generated by rank-one outer squares (equivalently PSD with zero cofactor trace by R04). Thus for every RC quadratic q, E q(Y)>=E q(Z) when q is homogeneous of degree two. More importantly, the full cone-direction Jensen inequalities hold, not merely these second moments.

By the optimality argument of Section 8.3, every optimal martingale dilation X,Y in P20 with a fixed-law optimal F admits (24) with Z=C DF(Y), up to sign (sign change of c preserves the cone). This is an exact strengthening of P21 for hypothetical universal near-extremizers. One possible exact-zero attack is to combine these scalar-subordinate martingales with the actual spatial identity P S=(1+2b)X+o(L2). No such contraction is obtained just by the covariance inequalities, and the stronger martingale structure does NOT justify treating conditional residuals as gradients.

### 9.2 Uniform finite-grid approximation of the unrestricted dilation LP

Here is a separate, quantitative advance on the computer-assisted gate. Scale first to a centered finite law nu of rational atoms and rational masses, supported in the Frobenius unit ball. Write d_G for the exact rational occupation LP of Section 8.5 on grid G, and d for (10). For any rational 0<epsilon<=1 choose the parameters below, ALL independently of nu:

    k = smallest integer >=1 with 42240 (k+1)^2 4^(-k) <= epsilon/4
    r = 8 k, D = 4 r
    B0 = 6 D² + 96, L0 = 8 B0/r
    rho = epsilon/[8(L0+1)], delta = epsilon/4
    H0 = 144 L0/rho, K0 = 144 L0/rho²
    n = max(8, ceil(16 K0/delta), ceil(1/rho))
    m = max(5, ceil(30 H0/delta))
    h = 1/(n m²)
    G = h Z^4 intersect [-D,D]^4.

**Theorem.** The finite LP is feasible and

    d(nu) <= d_G(nu) <= d(nu)+epsilon.                     (27)

In particular it gives a certified two-sided interval [max(0,d_G-epsilon),d_G] from a SINGLE exact LP. For a rational radius R>0 use the rescaled grid R G and the error epsilon R². The grid does not have to contain the input atoms: the transport constraints require their conditional means exactly, not their membership as target states.

The number of grid states is (2D/h+1)^4. In asymptotic notation for epsilon decreasing to zero, k=O(log(1/epsilon)), h^(-1)=O(k^7 epsilon^(-7)), hence the state count is O(epsilon^(-28) (log(1/epsilon))^32). This is polynomial in reciprocal accuracy up to logarithms for the matrix-grid part only, not a practical complexity bound for the overall unrestricted problem. These conservative constants make even moderate accuracy grids vastly too large to solve directly. No assertion of an exact finite grid at epsilon=0 is made.

**Feasibility and the lower bound.** A direct grid-supported martingale coupling is available: conditional on X, choose one of all four matrix entries with probability 1/4, and then choose +4 or -4 in that entry with conditional mean 4 X_entry. Every entry of X lies in [-1,1], so these probabilities are feasible. For each fixed chosen entry the unconditional signs have equal probabilities by centering of X. The resulting law is a mixture of four symmetric rank-one two-point grid splits from zero; every target state is in G since D>=32 and 4 is on the grid. This exact conditional martingale coupling suffices for feasibility. No intermediate non-grid state is needed. Soundness of the occupation LP gives d_G>=d. The objective is bounded on the feasible set, and positive variance increments bound split occupations, so the LP has an optimum and finite-dimensional linear-programming strong duality applies.

**Normalize a dual solution.** For any feasible grid dual f_v,u_i,h_i from Section 8.5 whose objective is nonnegative (negative objectives are harmless), define the finite convex piecewise affine function

    g(x)=max_i [u_i-Q(x_i)+(h_i+x_i):x],   Q(x)=|x|²/2.

The constraints give f_v+g(v)<=Q(v) on G, and its objective is at most f_0+int g(X)-E Q(X). Shift f and g by opposite constants to get f_0=0, then subtract a supporting linear functional of g at zero from g and add it to f. The objective bound and constraints are unchanged by centering. Now g>=g(0)=-A for A>=0, and int g(X)>=0.

Let e_l, l=1,...,4, be the coordinate rank-one matrix units. Midpoint grid inequalities give

    g(8 e_l)+g(-8 e_l) <= 64,
    g(+/-8 e_l) <= 64+A.

For any |x|<=1, express x as the convex combination of 0 and these signed coordinate points with total nonzero weight theta=||x||_1/8<=1/4. Thus g(x)<=-(1-2theta)A+64theta<=-A/2+16. Since its average on nu is nonnegative, A<=32.

Consequently f_v<=Q(v)+32<=2D²+32. Split zero along the first row to its two signed row values of v, then along the second row in each branch; the four leaves are the row-sign flips of v, each of weight 1/4, all nodes in G. Degenerate zero splits can simply be omitted. Since f_0=0, the discrete RC inequalities yield f_v>=-3(2D²+32). In particular |f_v|<=B0 uniformly on the WHOLE grid, irrespective of how small individual source masses may be.

We also need a global upper bound on the convex function. After the normalization, for each input atom x_i retain one of the affine pieces of g active at x_i, discarding all other pieces. Let g' be their maximum. This does not change g on any input atom and g'<=g everywhere. At x_i and x_i+/-e_l, the convex hull of 0 and the signed 8 e_l contains the argument, so g<=96 there, while g(x_i)>=-32. The l-th coordinate of any affine slope active at x_i is between -128 and 128 by evaluating at x_i+/-e_l. Each retained slope has norm <=256. It follows that globally

    g'(y) <= 352+256 |y|.                                  (28)

The dual objective is still bounded by int g'(X)-E Q(X); all grid inequalities f_v+g'(v)<=Q(v) hold. This normalization avoids any unproved regularity or slope bound for a general dual optimal solution.

**Interpolate and mollify the grid values.** Let I_h f be the ordinary four-coordinate multilinear interpolant on the grid cube. On any coordinate line through grid points, its divided differences are nondecreasing. Their absolute values for segments meeting the smaller cube [-3r,3r]^4 are at most 2B0/(r-h)<=4B0/r by comparison to the endpoint slopes. Multilinear interpolation averages these slopes in the other coordinates. Hence I_h f is L0-Lipschitz on the smaller cube and bounded in absolute value by B0 on the full cube. For any z in h Z^4 with rank(z)<=1, the centered z-difference of I_h f is nonnegative wherever the interpolation cells at x and x+/-z are inside the grid cube: the weights are the same after a lattice translation, and the discrete inequality holds at each corresponding vertex triple.

For a concrete smooth approximation let the one-dimensional kernel be the triple convolution of the normalized uniform measure on [-a,a], with a=rho/6. Take the product of four such kernels. This is a nonnegative probability kernel K supported in the Euclidean ball of radius rho, with mean zero. Its first and second partial derivatives are integrable; the L1 norm of each second partial is at most a^(-2), since each differentiated uniform factor has signed derivative of total variation 1/a. For any unit direction v the L1 norm of the second directional derivative is at most 4/a²=144/rho², by the entrywise l1 bound on v. Set f_rho=(I_h f)*K on the interior. The convolution is C² there, and for x in the region needed below the Hessian operator norm and its Lipschitz bound are respectively at most H0 and K0: subtract the constant I_h f(x) under the second-derivative integral for the first bound, and use the L0-Lipschitz difference at x and x' for the second. All kernel points lie in [-3r,3r]^4 for arguments of norm <=2r+1. The lattice centered differences along rank-one z remain nonnegative after convolution.

For any unit rank-one R=a1 tensor a2 with unit factors, round each factor to multiples of 1/m. The resulting matrix Rhat has rank one, |Rhat-R|<=5/m and |Rhat|<=2. Its direction z=Rhat/n lies exactly in h Z^4, and |z|<=1/4. For x in B_(2r), Taylor integration of the nonnegative centered z-difference and the Hessian-Lipschitz bound give

    D² f_rho(x)[Rhat,Rhat] >= -8 K0/n.

Comparison with R using the Hessian operator bound loses at most 15 H0/m. Thus D² f_rho(x)[R,R]>=-delta by the choices of m,n. The same argument works on a small open collar beyond B_(2r). It follows that

    F_rho=f_rho+delta Q

is RC throughout B_(2r), in the usual rank-one segment sense. This is a uniform error proof, not merely consistency of a finite difference stencil at an unknown smooth envelope.

At every point of the interpolation domain, convexity of g' and the vertex constraints give

    I_h f(x)+g'(x) <= I_h Q(x) <= Q(x)+h²/2.

The last inequality is the sum of four scalar linear-interpolation quadratic errors, each at most h²/8. Mollify and apply convex Jensen to g', using the centered kernel, to obtain

    f_rho(x)+g'(x) <= Q(x)+(rho²+h²)/2.                   (29)

Also f_rho(0)>=-L0 rho.

**Global rank-one-convex extension and use of the OPTIMAL tail.** Define the convex barrier

    q(x)=128(|x|²-2r²).

On B_r it is <=-128r², below F_rho since B0<=98r². On the sphere of radius 2r it is 256r², strictly above F_rho, whose upper bound on B_(2r) is B0+2 delta r²<=100r². Take max(F_rho,q) inside B_(2r), and q outside. Agreement on an open collar of the boundary makes the resulting function f_ext globally RC (local line convexity implies convexity on the entire line). It agrees with F_rho on B_r and has quadratic growth. In particular outside B_r it is at most 128|x|²; this also bounds the inner branch wherever |x|>=r. From (28), when |y|>=r>=8 we have g'(y)<=86|y|². Consequently

    f_ext(y)+g'(y)-Q(y) <= 220 |y|²    for |y|>r.

On B_r, (29) gives the sharper upper bound delta Q(y)+(rho²+h²)/2. By P20 choose an actual optimal martingale coupling X,Y for nu. From P23, P(|Y|>8j)<=4^(-j), for all j>=1. It follows by partition into annuli that

    E[|Y|² 1_(|Y|>8k)]
       <= 64 sum_(j>=k) (j+1)^2 4^(-j)
       <= 192(k+1)^2 4^(-k).

The last estimate uses (j+1)^2<=(k+1)^2(j-k+1)^2 and sum_(l>=0)(l+1)^2 4^(-l)=80/27<3. Thus the contribution of the exterior upper bound to the error is at most epsilon/4 by the choice of k. This argument uses the optimal target directly, not the radius-inflating conditional-mean repair of Section 8.4.

Since X,Y is a martingale, int g'(X)<=int g'(Y); since Y is a laminate and f_ext has quadratic growth, int f_ext(Y)>=f_ext(0)=f_rho(0). Therefore the objective of ANY feasible grid dual is at most

    int (f_ext+g')(Y)-int Q(X)-f_ext(0)
       <= d(nu)+delta int Q(Y)+(rho²+h²)/2+L0 rho
                   +42240(k+1)^2 4^(-k).

The simple row-doubling bound on the OPTIMAL cost gives int Q(Y)<=int |X|²<=1. With the parameter choices delta=epsilon/4, L0 rho<=epsilon/8, h<=rho<=epsilon/8 and the tail budget epsilon/4, the total error is strictly below epsilon. Apply LP strong duality. This proves (27) uniformly over all the input laws. All infinite-depth issues are handled by the finite occupation LP, the attained optimal coupling and its exponential tail, not by an assumed bound on the number of splits.

### 9.3 Two-sided universal beta enclosures using only rational occupation LPs

As a consequence, the law-side portion of R16's finite positive-accuracy reduction no longer needs finite integrand sample variables or a global Hessian repair. For rational 0<epsilon<=1 take the R16 periodic triangular mesh side n0=n(1,epsilon/4). Define b_n0 as the supremum of d(Law(Du))/||Du||² over this mesh, so b_n0<=b<=b_n0+epsilon/4, with b=-beta_*. Homogeneity of d permits unit gradient variance.

Subtract one nodal value of u. On this mesh every triangle has area 1/(2 n0²), so a unit-variance gradient has norm at most sqrt(2)n0 on each triangle. Every horizontal and vertical edge increment has norm at most sqrt(2), hence the nodal values have norm <=2 sqrt(2)n0. Round their components to a rational lattice of spacing s=epsilon/(128 n0), keeping the reference node zero and periodicity. The rounded field X' is ACTUALLY a mesh gradient; its L2 error relative to the original normalized X is at most 4 n0 s=epsilon/32. The rounded variance E' lies in [1/2,2], and the rounded node values lie in the fixed coordinate box [-4n0,4n0].

The direct stability estimate

    |d(Law(X))-d(Law(X'))|
          <= (||X||_2+||X'||_2)||X-X'||_2/2

follows by integrating the normalized unit gradient-Lipschitz integrands along the line segment joining the two actual fields and then taking their supremum. With t=||X-X'||_2<=epsilon/32, |E'-1|<=(2+t)t and d(X')<=E'/2. Therefore

    |d(X)-d(X')/E'| <= 2t+|E'-1|/2 < epsilon/8.

Enumerate the finite list of rounded periodic nodal assignments in the box with E' in [1/2,2]. Every slope law is rational and supported in B_R with R=2 n0. For EACH such law use (27) on the rescaled matrix grid with unit-ball tolerance epsilon/(8 R²). This is one finite grid shared across all the laws (though the LP transport variables vary with the law). The resulting d_G is at most d+epsilon/8, hence d_G/E' is at most d/E'+epsilon/4. Let U be the largest exact rational d_G/E' among this finite list. Then

    b_n0-epsilon/8 <= U <= b_n0+epsilon/4,
    max(0,U-epsilon/4) <= b <= U+3 epsilon/8.

Thus there is a finite certified enclosure of width at most 5 epsilon/8, obtained by rational gradient enumeration and rational occupation LPs only on the law side. This is conditional on the earlier hand R16, P20, P22/P23 and R26; it is not a practical implementation or a new proof of R16. The mesh side supplied by R16 and the resulting LPs are far too large for direct execution. The point of the theorem is that all three previously unbounded searches (integrands, splitting depth and matrix-grid refinement) now have a common finite positive-accuracy stopping rule. Spatial geometry still uses the earlier explicit but enormous localization cutoff. No uniform positive separation between b=0 and b>0 is supplied, so this does NOT give an exact decision procedure.

### 9.4 Verification and disposition

Executed 256 rational vector controls for the correction (26) and eight rational accuracy-budget controls for (27) (epsilon=1,1/2,1/10,1/100,1/1000,1/10000,3/17,7/16). The correction checks certify L>=error/3 without square-root approximation: for t=error/3>0, verify t²+(u-v)t-w²<=0, whose nonnegative root is L. The parameter checks verify the Hessian budget, barrier bounds and total error strictly below epsilon, using only exact rational arithmetic. Largest observed error/epsilon was below 0.622. These tests do not certify the analytic martingale limit, growth extension, convex separation or interpolation proof. No new occupation LP of the explicit large uniform size, full universal enumeration, or Lean build was performed. For example epsilon=1/10 yields r=120 and a grid denominator with 58 decimal digits; this is a theoretical cutoff, not a computational claim of feasibility at that size.

Reproducible arithmetic checks (the exact control loop and parameter budget used; no new standalone file):

```python
from fractions import Fraction as F
from math import ceil
import random

def params(e):
    k=1
    while F(42240*(k+1)**2,4**k)>e/4: k+=1
    r=8*k; D=4*r
    B=6*D*D+96; L=F(8*B,r)
    rho=e/(8*(L+1)); delta=e/4
    H=144*L/rho; K=144*L/rho**2
    n=max(8,ceil(16*K/delta),ceil(1/rho))
    m=max(5,ceil(30*H/delta))
    h=F(1,n*m*m)
    assert 8*K/n+15*H/m<=delta
    assert rho<=F(1,8) and h<=rho
    assert B<=98*r*r and B+delta*2*r*r<=100*r*r
    err=F(42240*(k+1)**2,4**k)+(rho**2+h**2)/2+L*rho+delta
    assert err<e
    return k,r,D,n,m,h,err/e

for e in [F(1),F(1,2),F(1,10),F(1,100),F(1,1000),F(1,10000),F(3,17),F(7,16)]:
    print(e, params(e)[0:3], float(params(e)[-1]))

rng=random.Random(20261125)
dot=lambda a,b:sum(x*y for x,y in zip(a,b))
for _ in range(256):
    a=tuple(F(rng.randint(-9,9),rng.randint(1,9)) for _ in range(2))
    b=tuple(F(rng.randint(-9,9),rng.randint(1,9)) for _ in range(2))
    u,v,w=dot(a,a),dot(b,b),dot(a,b)
    Ja=(-a[1],a[0])
    c0=dot(b,Ja)/u if u else F(0)
    c=max(F(-1),min(F(1),c0))
    bp=tuple(c*x for x in Ja)
    diff=tuple(x-y for x,y in zip(b,bp))
    t=dot(diff,diff)/3
    assert t==0 or t*t+(u-v)*t-w*w<=0
    assert dot(a,bp)==0 and dot(bp,bp)<=u
```

**Decision:** P24 strengthens the common optimal joint lift to the scalar-subordinate cone (24); R27 gives the uniform finite matrix-grid error theorem and the resulting rational LP-only two-sided universal enclosures. These remove auxiliary computational and structural gaps, but not the exact spatial inequality (21). The next attack must exploit the constrained joint martingale representation and actual Fourier compatibility to force a strict contraction, or produce an independent effective separation from zero. Do not run the enormous prescribed grid as a new exact-zero strategy; it only certifies fixed positive accuracy. No proof of unrestricted Morrey, strict contraction, uniform exact-zero cutoff, new numerical universal bound, comprehensive novelty review or Lean verification is claimed.

## 10. 25 November: uniform strict subordination slack and exact cofactor transport of the optimal deficit

**Outcome.** At any prescribed strictly negative normalized Jensen gap, the full radial derivative norm must be separated from saturation by a uniform positive constant, with no amplitude, support, smoothness-modulus, or fixed-energy hypothesis. In the attained optimal pair this is a positive lower bound on the scalar-subordination slack of P24. The proof uses the convex conjugate of the normalized convex complement and the actual determinant-radius transport inequality from R17/P14, rather than independent moment constraints. Separately, the dual norm of P22 has an exact cofactor-scaling law. It transports every closest laminate and every optimal martingale dilation, including their defects, and yields quantitative balance and phase-alignment constraints on every hypothetical universal near-extremizer. These are unrestricted necessary conditions and exact transformation identities. Neither forces beta_*=0 yet.

### 10.1 A uniform exclusion of full radial stress saturation

Let F be globally C11 rank-one convex, F(0)=DF(0)=0, Lip DF<=1, and X a centered periodic W1,2 gradient. Write

    E = int |X|² > 0, p=DF(X), S=X-p,
    ell(X)=|X|²-|p|²>=0, L=int ell(X).

For 0<gamma<=1/2 define

    T=16/gamma,
    K=2^(ceil(2T)+2),
    zeta²=gamma/2,
    eta=zeta²/(128 K),
    delta(gamma)=eta gamma/8=gamma²/(2048 K).

**Theorem.** If int F(X)<=-gamma E, then

    int |DF(X)|² < (1-delta(gamma)) E.                     (30)

This is uniform over ALL normalized energies and actual compatible gradients; in particular it permits varying C11 energies and concentration of their squared gradient norms. The constant is deliberately conservative and exponentially small in 1/gamma. It is not a separation of a nonzero beta_* from zero.

Proof. Put Q(x)=|x|²/2, G=Q-F, and let G* be the ordinary convex conjugate, allowing extended values. The function G is convex, nonnegative, has zero tangent at zero and Lip DG<=2. The function

    h(s)=G*(s)-|s|²/4

is convex (possibly extended) and nonnegative. One justification, including the degenerate case: G+epsilon Q is uniformly convex and (2+epsilon)-smooth, so its conjugate minus |s|²/[2(2+epsilon)] is convex. This follows from the inverse Hessian bound, or the standard strong convexity of the conjugate of a smooth convex function. As epsilon decreases to zero the conjugates increase to G*, directly from the supremum definition. Their pointwise limit after subtraction of the indicated quadratics is h, so h is convex as well.

Write s_+=(s+C s)/2, s_-=(s-C s)/2, the two cofactor eigenspace projections, with C the cofactor involution. Since F(R)>=0 on the rank-one cone by RC and its zero tangent, G(R)<=|R|²/2 there. Testing G* only on rank-one matrices gives

    G*(s)>=sigma1(s)²/2,
    h(s)>=(sigma1(s)²-sigma2(s)²)/4
         = |s_+||s_-|/2.                                (31)

The last identity follows from |s|²=|s_+|²+|s_-|² and 2 det s=|s_+|²-|s_-|².

At s=DG(x)=x-DF(x), Fenchel equality and the norm identity give exactly

    G(x)= |s|²/4 + ell(x)/2 - h(s).

Also G(x)>=|s|²/4: use the smooth convex descent inequality at x-s/2 and nonnegativity of G. Hence

    0<= h(s)<=ell(x)/2,
    |s_+||s_-|<=ell(x).                                  (32)

For a sign e in {+1,-1}, call s dominant in e if |s_e|>=|s_-e| (break ties arbitrarily). By (31)-(32), |s_-e|<=sqrt(ell(x)). Completing the square in the dominant plane in the Fenchel equality gives

    G(x)=x:s-|s|²/4-h(s)
         <= |x_e|²+|x| sqrt(ell(x)),
    F(x)>=-e det x-|x| sqrt(ell(x)).                       (33)

The elementary global bound F(x)>=-|det x| also holds: split x into its two orthogonal singular rank-one summands R,B and use F(R)>=0, the supporting derivative inequality along B, and |DF(R)|<=|R|. These bounds require no isotropy of F.

In particular the EXACT saturation case L=0 needs no radius transport theorem. The zero set of h is convex and by (31) is contained in the union of the two cofactor eigenspaces. It is therefore contained in one of them (unless it is just zero). All s=DG(x) on the law with ell(x)=0 lie in that single plane. Equation (33) and the mean determinant identity then give int F(X)>=0. This argument even works for arbitrary centered laws with correct determinant mean; the quantitative argument below is where actual compatibility enters.

We next prove the uniform version. First take X bounded. The determinant-weighted positive and negative laws of X have equal mass, by int det X=0. Couple them as in [R17, Section 6.1](IWANIEC_MORREY_COFACTOR_DUALITY.md#61-logarithmic-transport), matching the logarithms of the operator norms. Explicitly, the verified QC truncated determinant and its reflected version imply that there is a coupling pi of these two measures with

    int |log(||x||op/||y||op)| d pi
       <= (1/2) int ||X||op² + 2 (mass pi) log 2
       <= E.

This is the actual-gradient transport inequality already proved in R17/P14, not a property of arbitrary correct-minor probability laws. It uses the pinned verified lean4-iwaniec input. The mass is <=E/4. If the mass is zero, F(X)>=0 by the rank-one bound, and there is nothing to prove.

On a pair (x,y) of opposite determinant signs put

    g_pair= -F(x)/|det x| - F(y)/|det y| <= 2.

Partition the coupling into the following cases (in the stated order):

1. Log-radius discrepancy >T: the total contribution of g_pair is at most 2E/T by the transport bound.
2. Either ell(x)>eta|x|² or ell(y)>eta|y|²: the coupling marginal masses of these bad sets total at most L/(2 eta), because |det x|<=|x|²/2. Their contribution is at most L/eta.
3. On either member, |s(x)|<=zeta|x|: by (32), G(x)<=(zeta²/4+eta/2)|x|². Since Q(x)>=|det x| and F(y)>=-|det y|, the pair deficit is at most G(x)/|det x|. Thus the total contribution of these pairs is at most (zeta²/4+eta/2)E.
4. The remaining pairs have comparable Frobenius radii (ratio at most K, since sqrt(2) exp(T)<K), both |s|>zeta times their own radius, and ell<=eta times its square. The dominant cofactor signs of s(x),s(y) MUST agree.

For the last assertion suppose, to the contrary, that s(x) is dominant in + and s(y) in -. Put t=|y|/(|x|+|y|) and r=t|x|=(1-t)|y|. For sbar=t s(x)+(1-t)s(y), the triangle inequality and (32) imply

    |sbar_+| >= r(zeta/sqrt(2)-sqrt(eta)) >= r zeta/(2 sqrt(2)),
    |sbar_-| >= r zeta/(2 sqrt(2)).

Therefore (31) gives h(sbar)>=r² zeta²/16. But convexity and (32) give

    h(sbar)<=(eta/2)[t|x|²+(1-t)|y|²]=(eta/2)|x||y|
            <=2 eta K r²=r² zeta²/64,

where (|x|+|y|)²/(|x||y|)<=4K. This is a contradiction. For a common dominant sign, (33) on the two opposite-determinant members cancels the determinant terms in g_pair, leaving at most

    |x| sqrt(ell(x))/|det x| + |y| sqrt(ell(y))/|det y|.

After integration this is at most sqrt(E L), by Cauchy-Schwarz and the prescribed coupling marginals.

The rank-one part of the law contributes no negative deficit. Summing the four cases proves the unrestricted estimate (initially for bounded gradient fields)

    -int F(X)/E <= 2/T + L/(eta E) + zeta²/4 + eta/2 + sqrt(L/E).  (34)

For a W1,2 field use periodic smoothing of its potential. The resulting gradients converge strongly in L2; the quadratic growth bound on F and the Lipschitz bound on DF give convergence of both the energy and L. Thus (34), for fixed parameters, holds without any bounded-amplitude assumption. If L/E<=delta(gamma), the right side of (34) is strictly less than gamma: 2/T=gamma/8, delta/eta=gamma/8, zeta²/4=gamma/8, eta/2<=gamma/512, and sqrt(delta)<=gamma/8. This proves (30).

**Consequence for P21/P24.** Take a hypothetical b=-beta_*>0 and the exact fixed-law optimal potentials on the universal near-extremizing sequence of Section 7.4, normalized by E=1. For all sufficiently large indices apply (30) with gamma=b/2. Put m=2b, let q be the zero-mean solenoidal part of p, and let V=Cq (compatible). Stationarity of F+b|.|² gives Pp=-mX+o(L2), so

    ||V||_2² <= 1-m²-delta(b/2)+o(1).

This strengthens the upper stress budget of N23 by an explicit positive amount at EVERY positive hypothetical b, with no shared energy or amplitude bound.

Moreover in the actual optimal martingale dilation X,Y=X+R, p(Y)=p(X)+R and E[R|X]=0. Hence for the joint optimal pair Y,Z=-C p(Y),

    ||Y||_2²-||Z||_2²=E-||p(X)||_2²=L.

On any approximating scalar-subordinate splitting sequence from P24 this difference is the limit of

    E sum_j (1-c_j²)|Delta Y_j|².

By (30) its normalized limit is bounded below by delta(b/2)>0. Thus a positive universal deficit cannot concentrate all of the optimal scalar martingale-transform energy at |c|=1. This does not prove a uniformly cheaper dilation, since changing predictable multipliers can change the spatial conditional mean. In particular P24 by itself does not show that a universal near-extremizer must saturate this norm bound.

### 10.2 Exact cofactor-scaling law for the dual norm

For arbitrary centered L2 S (not necessarily a gradient), write S=S_++S_-, E=||S||_2², D=int det S, and B=N*(S)² from Section 8.3. The singular-value identity at every matrix yields the exact formula

    B=E/2 + sup_F E sum_j |Delta M_(j,+)| |Delta M_(j,-)|,    (35)

where the supremum is over finite binary filtrations with arbitrarily well-resolving terminal conditional means M_n of S. Indeed sigma1(U)²=|U|²/2+|U_+||U_-|. The variance telescopes to E as the terminal revelation error tends to zero, and appending refinements cannot decrease the captured variance. Arbitrary auxiliary randomness is allowed, exactly as in P22.

The second term of (35) is positively bihomogeneous in S_+,S_- separately. In particular for T_theta S=S+theta C S and -1<=theta<=1,

    N*(T_theta S)²=(1-theta²) B+theta² E+2 theta D.          (36)

This follows by scaling the two cofactor components by 1+theta and 1-theta. Equivalently, along each split,

    sigma1(U+theta C U)²
      =(1-theta²) sigma1(U)²+theta² |U|²+2 theta det U.

These identities are valid also at the endpoints where one cofactor component disappears. There, arbitrary filtrations of the transformed variable may be glued to the original variable by conditional disintegration, or (35) directly gives half the transformed squared norm. No invertibility assumption at the endpoints is needed.

**Transport of every closest laminate.** If Y is any ordinary nearest laminate to S, set Z=C(S-Y), so (Y,Z) is jointly laminate by P22, S=Y+C Z and the following exact identities hold:

    ||Y||²=B,  ||Y||²+||Z||²=E,
    E det Y=E det Z=E Y:C Z=0,
    E Y:Z=D.

Here E in front of a random variable denotes expectation, while the scalar E without an argument denotes the squared norm of S. The cross-minor equality follows by testing the rank-one linear images Y+tZ; the determinant expansion of S gives the last equality. Thus Y_theta=Y+theta Z and Z_theta=Z+theta Y are jointly laminate, and S_theta=Y_theta+C Z_theta. The norm of Y_theta is exactly the right side of (36). Its inner product with S_theta equals its own squared norm. Therefore it is an attained nearest laminate to S_theta, by the polar-norm characterization (18)-(19). This transports the whole optimal coupling, including at theta=+/-1. It is an immediate exact geometric consequence of P20/P22, not an assertion of spatial gradient realization.

### 10.3 Exact transport of the optimal martingale deficit

Let X be ANY centered L2 law, F an exact optimizer for d=d(Law(X)), p=DF(X), and Y=X+R an optimal dilation from Section 7. By P21, S=X-p=Y-DF(Y) is a function of X, and E[R|X]=0, DF(Y)=p+R. By Section 8.3, Y is nearest to S; here Z=-C DF(Y). Apply the preceding transport. Then

    X_theta=E[Y_theta|X]=X-theta C p,
    Y_theta-X_theta=R-theta C R.

Y_theta is a martingale dilation of X_theta by the tower property. It is OPTIMAL: N(X_theta)<=||Y_theta|| by P20, while S_theta is measurable in X and

    E S_theta:X_theta=E S_theta:Y_theta=||Y_theta||²,
    N*(S_theta)=||Y_theta||.

Polar duality gives the reverse inequality, including the trivial zero-norm case. Hence N(X_theta)=||Y_theta|| exactly. Set D_X=E det X, and write d_theta for d(Law(X_theta)). The conditional variance and determinant identities of P21 give

    d_theta=(1+theta²)d+2 theta D_X,
    D_(X_theta)=(1+theta²)D_X+2 theta d.                    (37)

In detail, E|R-theta C R|²/2=(1+theta²)E|R|²/2-2 theta E det R, and E det R=-D_X. The determinant expansion of X-theta C p uses E X:p=-2d and E det p=D_X. Thus the particularly simple EXACT pair of scaling laws is

    d_theta+D_(X_theta)=(1+theta)²(d+D_X),
    d_theta-D_(X_theta)=(1-theta)²(d-D_X).                 (38)

This gives a whole explicit path of attained optimal problems, with exact endpoint calibration d_theta=|D_(X_theta)| at theta=+/-1. It does not remove the spatial compatibility issue. In fact for an actual gradient law, D_X=0, so D_(X_theta)=2 theta d: if d>0, every nontrivial member of the exact cofactor-shear path is incompatible with a centered gradient even at the minor level. At hypothetical universal near-extremizers the corrected spatially compatible shear is X-theta C(p+mX), approximately X-theta V; it differs by -theta m C X from X_theta. The optimal-cost identity (38) does NOT hold automatically after that correction. Finding a profitable, genuinely compatible correction rather than merely applying the optimal cofactor transport is a precise remaining problem.

### 10.4 Quantitative balanced and phase-aligned extremal reduction

Let P be the spatial compatible gradient projection, Q_sol its mean-zero solenoidal complement, and let a=1+2b, b=-beta_*. Equation (20) means

    A=||P S||² <= a B

for every centered spatial field S, where B=N*(S)². Denote its slack by s0=a B-A>=0. Let E_+=||S_+||², E_-=||S_-||², E=E_++E_-, D=(E_+-E_-)/2=int det S.

Since C exchanges the two spatial subspaces, P restricted to either cofactor eigenspace has squared norm exactly half the original squared norm. Consequently A-E/2 is a cross term, positively bihomogeneous in the two cofactor components. The same is true of B-E/2 by (35). Rescale the two components to equal L2 norms (if either is zero use the immediate A=B=E/2). Apply A<=aB to the balanced pair and undo the common cross-product scaling. This proves

    s0 >= (a-1)( E/2-sqrt(E_+ E_-) )
       >= (a-1) D²/E,                                    (39)

where the E=0 case is trivial. In particular if a>1 the universal supremum of A/B can be taken over EXACTLY balanced fields with int det S=0, and every sequence approaching a>1 has vanishing relative determinant imbalance. The first claim follows also from the exact ratio: for fixed normalized cofactor components, if the spatial cross term exceeds the martingale cross term, the ratio is maximized by equal norms. If the cross difference is nonpositive the ratio is <=1.

There is a simultaneous phase constraint. Write J for the fixed right-angle rotation matrix and L0=<P S,P(S J)> in the real L2 inner product. Right rotation of S preserves N* by the singular-value capture formula. Also ||P(S J)||²=E-A, because right multiplication by J exchanges the spatial compatible/solenoidal subspaces. Therefore maximizing ||P(S exp(phi J))||² in phi gives

    a B >= E/2+sqrt((A-E/2)²+L0²),
    L0² <= s0 [2(A-E/2)+s0].                             (40)

These estimates use the actual spatial projection, not abstract minor or covariance constraints.

For the universal near-extremizers of P21 with E_X=1, d->b>0, m=2b, S=X-p and B=1+2d, stationarity gives P S=a X+o(L2) and Q_sol S=-q. Therefore s0->0, with ||S|| uniformly bounded. Since C exchanges P and Q_sol,

    D=<P S,C Q_sol S>=-a <X,V>+o(1).
    
Likewise P(S J)=-q J, and q J=J Cq=J V, so

    L0=-a <X,J V>+o(1).

Equations (39)-(40) prove

    <X,V> -> 0,    <J X,V> -> 0.                          (41)

Here JX denotes left multiplication by the target rotation. Thus the compatible stabilized cofactor stress is asymptotically orthogonal to the entire two-dimensional real span of X and JX, even for changing normalized C11 energies and concentrating fields. Combined with (30), a positive universal deficit has uniform strict scalar-subordination slack and exactly balanced/phase-aligned optimal dual fields. Equations (39)-(41) do not prove that V is nonzero uniformly over all such changing energies, or that orthogonality forces V to vanish. The fixed-energy P19 coercivity has its own distinct hypotheses. The strict spatial capture inequality for these balanced fields is still open.

### 10.5 Checks and disposition

Executed in the local container: nine SymPy cofactor identities (including the eigenspace determinant/discriminant formula, product and rotation rules); eight exact Fraction parameter budgets for (30)-(34), with gamma in {1/2,1/4,1/8,1/10,1/20,1/100,3/17,1/1000}; and 100 exact rational controls of the signed singular-value scaling and the paired cost/determinant scaling (38), including endpoint parameters. All passed. These checks verify the finite algebra and the explicit error budgets, not the analytic transport, convex conjugacy or near-extremizer arguments. No solver run on a large grid or additional finite-support search was needed.

**Decision.** P25 is uniform radial stress/subordination rigidity (30); P26 is exact optimal cofactor transport (36)-(38), together with the quantitative spatial extremal reduction (39)-(41). The determinant transport used in P25 is the prior R17 hand derivation from the verified truncated determinant; P26 uses the prior hand P20/P22 duality and standard Hilbert projection identities. The remaining gate is to exploit the strict scalar-subordination slack on balanced, phase-aligned spatial fields, or construct a cheaper compatible dilation correcting the explicit nonzero minor defect in (37). Do not infer exact zero from the positive slack alone; in particular it is not a uniform separation of b from zero. No improved numerical bound on b, strict self-contraction, exact-zero proof, new formalization or independent verification is claimed.

## 11. 25 November: simultaneous directional budgets, exact whole-mesh maximization, and a stop rule for fixed-law transforms

**Outcome.** The scalar universal deficit controls the full row covariance of one martingale-dilation residual at a time, in the Loewner order, simultaneously in all target directions; there is an analogous column statement. This is stronger than separate existence statements for each anisotropic metric. At universal near-extremizers every scalar-optimal coupling matches both covariance matrices up to the relative near-optimality error. Independently, the complete positive-accuracy LP program R27 can eliminate the enumeration of individual real or rational nodal assignments: one rational dual polyhedron per spatial mesh and target grid gives the exact maximum over the whole continuous finite-element gradient sphere by projecting its vertices onto the gradient subspace. These are global statements with no fixed wave or atom-count hypothesis. They do not prove a uniform exact-zero mesh cutoff. We also establish exact stop rules: the first-order normalized joint Hamiltonian inequality is already a consequence of P21 optimality for arbitrary laws, and the known flat face combined with cofactor scaling cannot amplify the universal ratio by merely realizing its conditional residual on microscopic spatial scales, even with perfect microscopic capture. This rules out the proposed direct use of integrated P25 slack to extend that flat face. No proof of beta_*=0 or new universal numerical bound is claimed.

### 11.1 Uniform matrix-valued residual budget for the complete class of gradients

Let X be a centered actual periodic W1,2 planar gradient, with E=int |X|²>0. Put b=-beta_*, m=2b and let C_X=int XX^T. Consider all square-integrable martingale dilations X,Y with centered laminate target Y in P20, and set R=Y-X. The following is an unrestricted consequence of P20 and the definition of b:

    there exists a single such coupling with int RR^T <= m C_X.       (42)

The inequality is positive-semidefinite order, and in particular holds simultaneously against EVERY positive target-row quadratic weight, not only for one chosen direction. A second, possibly different coupling satisfies

    int R^T R <= m int X^T X.                                       (43)

Proof of (42). For any positive definite symmetric A, the field A^(1/2) X is an actual gradient. Apply P20 and the universal bound d<=b E to this field. Multiplying both variables of the resulting coupling on the left by A^(-1/2) preserves the martingale condition and laminate status, since invertible left multiplication takes rank-one directions to rank-one directions. Thus

    inf_(couplings of X) tr(A int RR^T) <= m tr(A C_X).

The inequality holds for semidefinite A as well: apply it to A+epsilon I, use the nonnegativity of the extra trace term, and then send epsilon to zero. This only proves separate existence for each A; the simultaneous conclusion requires the following compactness and separation argument.

Let U be the set of symmetric matrices B for which there is an admissible coupling with B>=int RR^T. This set is convex by mixing admissible joint laws with the common first marginal. It is upward closed under addition of PSD matrices. It is also closed. Indeed if B_j in U converges, take witnessing couplings pi_j. Their residual second moments have uniformly bounded traces, so the joint laws are tight with bounded second moments. Along a weakly converging subsequence, the first marginal stays fixed and all martingale identities

    int (Y-X) phi(X) d pi_j=0

pass to the limit for bounded continuous phi by uniform integrability of first moments. These identities characterize conditional mean zero. The target law remains a laminate by the globally Lipschitz RC tests of P20, and has finite second moment. For each v in R², lower semicontinuity of the nonnegative continuous function |v^T(Y-X)|² gives the desired v-quadratic inequality against the limiting B. Consequently B belongs to U.

If m C_X were outside this closed convex upward set, strict separation in the finite-dimensional symmetric matrix space would give A with

    inf_(B in U) tr(A B) > m tr(A C_X).

Upward closure forces A>=0 (otherwise the infimum is minus infinity). This contradicts the preceding anisotropic scalar inequality. This proves (42), including singular row covariance and the case b=0.

For (43), use right multiplication by an invertible matrix. Right multiplication changes the period lattice, but the universal square-torus constant still applies: for rational invertible B, choose a positive integer L such that LB is an integer matrix. The field X(LBx)B is the gradient of u(LBx)/L on the original unit torus and has law X B by Haar invariance of the surjective torus endomorphism. Approximate real B by rational invertible matrices and use the L2 continuity estimate for d in Section 9.3. Pulling back the resulting optimal coupling proves the column-weight inequality, and the same separation gives (43). There is NO claim that the two separately selected couplings must coincide for a general X. For the same reason one must not conclude domination of the full vectorized four-by-four covariance by the product-metric tests; those metrics do not form the whole PSD cone.

There is a common-coupling conclusion at universal near-extremizers. Let E=1, d=d(Law(X)), F be an exact fixed-law optimizer, p=DF(X), and let j=b-d>=0. For every scalar-optimal dilation P21 gives

    int RR^T=-int X p^T,
    int R^T R=-int X^T p.

The first moments on the right are symmetric, by P21. The QC stabilized energy H=F+b|.|² has Lip DH<=1+m and int H(X)=j. The functions of a constant target matrix A and a constant domain matrix B given by

    A -> int H(AX),          B -> int H(XB)

are nonnegative everywhere, including singular matrices by continuity (use the right-period argument above). Their derivatives have Lipschitz constants at most 1+m because E=1. Apply the elementary descent bound to each at the identity to obtain

    ||int X p^T + m int XX^T||_F <= sqrt(2(1+m)j),
    ||int X^T p + m int X^T X||_F <= sqrt(2(1+m)j).         (44)

Thus EVERY scalar-optimal dilation at a universal near-extremizing sequence has both row and column covariances of R asymptotic to m times the corresponding input covariance, with the explicit square-root residual error. This common-coupling result uses stationarity, not an unjustified simultaneous choice in (42)-(43). It complements the upper stress slack of P25 and the phase/trace restrictions of P26. The unknown m is still the original universal constant; (42)-(44) do not force m=0.

### 11.2 Finite matrix-grid LP maximization over a whole real gradient mesh

Fix ANY finite rational periodic triangulation of the torus (in particular the square mesh of R16). Index its triangles by i=1,...,N and let their positive rational areas alpha_i sum to one. Let V be the real linear subspace of compatible arrays x=(x_i) of two-by-two gradients obtained from periodic piecewise affine potentials on this triangulation. It is a rational subspace: the nodal-gradient map has rational entries and a rational basis can be extracted by Gaussian elimination. Every x in V has sum alpha_i x_i=0. Equip this array space with the weighted Frobenius inner product

    <x,y>_alpha = sum_i alpha_i x_i:y_i,  E(x)=<x,x>_alpha.

Assume V is nonzero. Let G be a finite rational matrix grid affinely spanning R4 and containing zero and the signed coordinate diamond large enough for the simple martingale coupling of Section 9.2 for EVERY unit array x in V. For instance take a rational R>max_i alpha_i^(-1/2) and include +/-4R times the four matrix units. The grid-restricted cost d_G is the occupation LP of Section 8.5. We now optimize ALL unit arrays in V, not a discretized list of nodal assignments.

Change the primal objective from half residual variance to target energy:

    L_G(x)=min sum_(i,v) pi_(i,v) Q(v),   Q(v)=|v|²/2.

By the martingale constraint, L_G(x)=d_G(x)+E(x)/2. This change is essential: the new objective and the constraint matrix are independent of x; only the right sides of the conditional mean constraints depend on it. The exact common dual polyhedron has variables f_v,u_i,h_i with

    f_(v_s) <= w_s f_(a_s)+(1-w_s) f_(b_s);
    f_v+u_i+h_i:v <= Q(v).

The objective for the given array is

    f_0+sum_i alpha_i(u_i+h_i:x_i).                          (45)

All entries of the constraints are rational. It is a pointed polyhedron after imposing the harmless gauges f_0=0 and h_1=0. To check this explicitly, a lineality direction must satisfy the equalities in every second displayed inequality. Since G affinely spans R4 this implies that all its h_i are a common vector h, all u_i are a common scalar u, and f_v=-u-h:v. Such directions also satisfy all homogeneous split equalities. Their objective is zero on centered arrays, and the two gauges kill exactly this lineality. The gauged polyhedron is nonempty (zero is feasible), has finitely many vertices, and has no lines. For every x on the unit sphere in V the occupation primal is feasible by the diamond construction and bounded; thus its dual maximum is attained at a vertex. This uses ordinary finite-dimensional LP strong duality, not a bounded-dual-slope assumption or a claim that the original polyhedron is compact.

For a vertex z write

    c_z=f_0+sum_i alpha_i u_i,    H_z=(h_i)_i,
    q_z=||P_V H_z||_alpha²,

where P_V is weighted orthogonal projection onto V. Every c_z and q_z is rational, q_z>=0. In a rational column basis D of V, with W the diagonal weight matrix repeated over matrix entries, the projection is

    P_V=D(D^T W D)^(-1)D^T W.

The following whole-continuum maximum is therefore EXACT:

    U_G = max_(x in V,E(x)=1) d_G(x)
        = max_(vertices z) [c_z+sqrt(q_z)-1/2].               (46)

Proof: maximize (45) over the unit sphere for each vertex, giving c_z+sqrt(q_z) by weighted Hilbert duality, and interchange the two finite/compact maxima. For q_z>0 a maximizing array for that vertex is P_V H_z/sqrt(q_z); it is an actual compatible algebraic slope array, not merely a moment law. If q_z=0, any unit array attains its constant objective. This proves the formula for all real nodal values, including irrational maximizers. One need not enumerate or round nodal assignments. Enumerating rational vertices is still generally expensive; the formula does NOT turn the maximum of a convex piecewise linear function on a sphere into an ordinary LP. An exact certificate for U_G<=t, for rational t, checks the two rational inequalities

    t+1/2-c_z >= 0,     q_z <= (t+1/2-c_z)^2

for every vertex of the common polyhedron. Alternatively a violated vertex provides the explicit algebraic maximizing candidate. A lower bound on the grid-restricted objective is not itself a lower bound on the true unrestricted deficit.

Combining (46) with the existing hand R16/R27 yields a positive-accuracy whole-mesh certificate without nodal quantization. The R27 proof works verbatim for real atoms and real masses (the constraint matrix is rational, and no step of the uniform estimate uses their rationality); alternatively extend its bound by continuity of the finite parametric LP value on the centered feasible neighborhood of the unit sphere. For rational eta>0 choose the R16 spatial mesh with tolerance eta/2. Choose rational R as above, and use R27 on the rescaled matrix grid with additive error eta/2 on B_R (unit-ball tolerance eta/(2R²), decreasing it to at most one if needed). Denote by b_mesh the true maximum d on its unit gradient sphere. Then

    b_mesh <= U_G <= b_mesh+eta/2,
    b_mesh <= b <= b_mesh+eta/2,

so the resulting exact enclosure is

    max(0,U_G-eta/2) <= b <= U_G+eta/2.                     (47)

One fixed rational polyhedron with an explicit finite vertex procedure suffices for each requested accuracy. This replaces the nodal enumeration in R27 and is uniform over arbitrary integrands and gradients by the earlier localization theorem. Both the spatial mesh and the target grid may still be enormous. The number of vertices can be astronomical. No exact-zero termination bound or practical complexity claim follows. In particular even when a whole continuum consists of laminates, a fixed target grid generally has strictly positive U_G because a zero-cost coupling would have to leave every input atom unchanged.

### 11.3 Exact stop rule: normalized joint first-order tests already follow from the fixed-law optimum

Take any centered L2 law X, not necessarily a gradient, and its exact optimal F and martingale dilation Y in P20/P21. Write R=Y-X, p=DF(X), d=d(Law(X)), so E[R|X]=0 and DF(Y)=p+R, E|R|²=2d. By P22 the pair (Y,C DF(Y)) is jointly laminate.

For ANY globally C11 rank-one convex K on 4x2 matrices, with K(0,0)=0, satisfying the directional upper curvature bound

    D²K[(v,Cv),(v,Cv)] <= 2 gamma |v|²

globally (the bound in the P18 normalized joint Hamiltonian construction), Taylor integration along that particular residual direction gives

    K(Y,C DF(Y))
       <= K(X,Cp)+DK(X,Cp):(R,CR)+gamma |R|².

The derivative term has mean zero by conditional expectation, and the left side has nonnegative integral by the joint laminate property. Thus

    int K(X,Cp)+2 gamma d >= 0.                              (48)

Since int X:p=-2d, (48) is exactly the normalized first-order inequality in P18, already true for every fixed-law optimum even on artificial non-gradient laws. No spatial compatibility was used. This does not assert that a negative generator cannot be discovered by genuinely exploiting spatial compatibility to derive a contradiction. It DOES show that merely adding more first-order joint generator tests to the P20/P21/P24 optimal-law constraints cannot add a missing spatial restriction. Prioritize a modification of the actual field or of the dilation problem that uses more than these fixed-law conditions.

### 11.4 Flat faces cannot be extended by integrated subordination slack alone

For the same optimum let S=X-p=Y-DF(Y), Z=-C DF(Y), and B0=E+2d=||Y||_2². Then S=Y+C Z. The equality in Section 8.3 and the fact that Y itself has a laminate law give N*(S)=N*(Y)=sqrt(B0), and both inner products with Y equal B0. Therefore by convexity of N* and its polar formula,

    T_lambda=Y+lambda C Z,
    N*(T_lambda)²=B0        for 0<=lambda<=1.              (49)

But the flat segment has an exact obstruction at the endpoint. Make a conditionally independent copy Y' of Y given X. It has the SAME laminate marginal and E[Y'|X]=X, so it is an admissible competitor for N*(T_lambda). For lambda>1,

    N*(T_lambda) >= <T_lambda,Y'>/||Y'||_2
                    = (E+2 lambda d)/sqrt(E+2d)
                    > sqrt(B0)                           (50)

if d>0. Thus the ray cannot remain flat beyond lambda=1 on ANY positive-defect law. The strict integrated subordination slack in P25 does not justify that flat extension. This obstruction is exact and uses a common optimal coupling, not an artificial quadratic control. It does not rule out different perturbation directions or nonlinear compatible rearrangements.

Combining the entire known flat segment with the exact cofactor scaling (36) still cannot provide the proposed amplification if the construction only keeps the original spatial macro-field and rearranges the conditional residual at a microscopic scale. Here is an explicit all-parameter check. Work along a hypothetical universal near-extremizing sequence with E=1, d->b>0, m=2b, a=1+m, p=-mX+q+o(L2), where q is solenoidal and V=Cq is compatible. P26 gives <X,V>->0 and D_S=int det S->0. Pass to a subsequence with ||V||²->w. The norm of Z tends to w+m a, since p(Y)=p(X)+R and ||R||²->m.

Consider the transformed field

    W_(lambda,theta)=T_lambda+theta C T_lambda,
           0<=lambda<=1,  |theta|<=1.

Equations (36) and (49) give, exactly before taking limits,

    N*(W_(lambda,theta))²=B0+2 lambda theta D_S
                             +lambda² theta² ||Z||².

This follows also by expanding det(T_lambda), using int det Y=int det Z=int Y:CZ=0 and int Y:Z=D_S. Its limit is

    B_(lambda,theta)=a+lambda² theta²(w+m a).

Keep the original macroscopic spatial variable omega for X and q. Conditional mean and residual of W are

    E[W|omega] = (1+lambda m)X-lambda theta V
                 +(theta+lambda theta m)CX-lambda CV+o(L2),
    W-E[W|omega] = (1-lambda)(R+theta CR).

The first two terms of the mean are compatible, the other two solenoidal. The residual squared norm tends to m(1-lambda)²(1+theta²) because int det R=0. Even granting perfect capture of the entire microscopic residual, every such macro-preserving rearrangement has gradient-projection energy at most

    A_max=(1+lambda m)²+lambda² theta² w
                   +m(1-lambda)²(1+theta²).              (51)

For clarity about the scope: if microscopic realizations on the torus converge weakly to the specified conditional mean and have the prescribed residual norm, apply the bounded linear projection P, expand its squared norm, and use weak convergence to eliminate the cross term and the contraction norm of P to bound the fluctuation. No assumption that arbitrary conditional residuals are gradients is needed. This upper bound is deliberately generous; it applies to any such limiting rearrangement. It is NOT an upper bound for arbitrary changes of the macroscopic field.

The exact difference from the universal extremal target is

    a B_(lambda,theta)-A_max
       = m[a(1-lambda²)
           +theta²(lambda² w+a² lambda²-(1-lambda)²)]
       >= m[(1-theta²)a(1-lambda²)+theta² m] >=0.          (52)

For the last inequality interpolate linearly in theta² between zero and one. At theta²=1 the bracket equals

    m+2 lambda+lambda²(w+m+m²-1) >= m.

It is strict for m>0 except at lambda=1, theta=0 (the original field). The result covers all parameters and every permissible stress variance w>=0, not just one finite-dimensional control. Consequently the flat segment and cofactor scaling cannot yield a strictly larger spatial ratio by this macro-preserving microscopic construction, even under perfect residual capture. Do not continue a ladder of lambda, theta or microscopic projection choices in this class. To finish, one needs a genuinely different spatial operation (one that changes the macro compatible structure rather than just appending the conditional residual), an exact geometric cutoff, or a proof of positive gap separation. We have not obtained any of these.

### 11.5 Executed controls

I ran a separate small Python/SciPy HiGHS control in this turn, not the enormous prescribed grids. For independent periodic sawtooth rows the four diagonal atoms diag(+/-s,+/-t) have probabilities 1/4 and form a true laminate for every real s,t. On the diagonal nine-state grid {-1,0,1}², for 0<=s,t<=1 the exact terminal-energy LP is L_G=(s+t)/2: round each coordinate independently, conditionally to zero or its signed unit endpoint with the correct mean. The target is a product of centered one-row laws and has a two-stage finite splitting tree on the grid. The fixed terminal-energy dual f=0,u_i=0,h_i=(sign1,sign2)/2 certifies equality since h_i:v<=Q(v) at every integer grid point. Thus on the real unit amplitude circle the whole continuum maximum of the **grid error** is (sqrt(2)-1)/2, attained at s=t=1/sqrt(2); the true deficit is zero throughout. This illustrates both the exact algebraic maximization of (46) and why a positive grid result must not be advertised as a counterexample.

Seven rational primal/dual certificates were constructed and all balance, transport, nonnegativity and objective identities checked with Fraction, followed by independent HiGHS replays. The inputs (s,t) were (1,0),(0,1),(3/5,4/5),(5/13,12/13),(20/29,21/29),(119/169,120/169),(0,0); the respective exact restricted deficits were 0,0,1/5,2/13,6/29,35/169,0. The last is not a normalized unit input. An additional 225 rational parameter controls verified both the identity and the lower bound in (52), including the equality criterion. These checks are finite regression controls; the continuous statements follow from the proofs above. I did not enumerate the dual vertices on a general four-dimensional grid or solve the full uniform problem. No Lean build or independent review was performed.

**Disposition.** P27 is the simultaneous directional covariance budget, R28 is the whole-continuum mesh maximum, N25 is the exact redundancy/flat-face stop rule. All three concern the unrestricted program; none changes the numerical value of the best recorded bound or closes the exact-zero gate. The earlier P20/P22/R16/R27 hand dependencies remain to be checked in final formal assembly.

