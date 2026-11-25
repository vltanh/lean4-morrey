# Direct beta_* attack: product-metric Legendre duality does not yet contract

24 November 2026. Follow the active [exact-zero directive](README.md#target). This tests a particular direct self-contraction mechanism on the original normalized universal margin. There is no assumption of polyconvexity, bounded amplitudes, fixed atom count or attainment of the infimum.

**Outcome:** the Legendre transform below gives normalized RC energies for an entire family of anisotropic parameters. The associated universal beta inequalities imply a rowwise stress-covariance bound, with all row parameters eliminated by a two-variable LP. However an isotropic formal state with positive b survives the optimized quadratic Fenchel comparison for EVERY product metric. Hence the proposed comparison does not yield beta_*=0. Do not turn this into a new independent gate or continue a parameter ladder. No improvement of the universal numerical bound, exact-zero proof, gap separation, or true negative witness. Hand proof with actual exact algebra and five LP controls; no Lean or independent review.

## 1. A direct normalized dual construction

Use row-major Frobenius coordinates on 2x2 matrices; C is the symmetric orthogonal cofactor involution, X:C X=2 det X. Let F be globally C11 and RC, F(0)=DF(0)=0, Lip DF<=1. The planar quadratic Finsler lemma (R17) gives, at a.e. Hessian H,
    H >= c C,   |c|<=1.
Indeed H is RC as a quadratic form, and writing H=c C+PSD and testing on the two C eigenspaces bounds c by the full Hessian norm.

Choose a positive product metric K=diag(k1,k2,k3,k4), with
    k1*k4=k2*k3=s>1,
and define D=s-1, i'=5-i for the cofactor partner, A=diag(k_i')/D. Orthogonal row/column changes are also allowed. Such K is induced by positive definite constant left and right matrix factors. Set
    G(X)=F(X)+X:K X/2,
    V(Y)=G*(Y),
where * denotes ordinary convex conjugation. No claim that F itself is convex is made.

For every c in [-1,1], K+c C is positive definite (each paired 2x2 block has determinant s-c²>0). By compactness of this scalar interval there is a common positive lower eigenvalue, hence G is uniformly convex globally. It is C11, has G(0)=DG(0)=0, and its Legendre transform V is globally C11. Put
    B=(K+I)^(-1), R=A-B.
At almost every dual point, Hessian inversion, the Finsler bound and operator convexity of matrix inversion on positive definite matrices give
    B <= D²V <= (K+c C)^(-1)
       <= [(1+c)(K+C)^(-1)+(1-c)(K-C)^(-1)]/2
       = A-(c/D) C.
Here the endpoint inverses are exactly A minus/plus C/D. The inversion inequality can also be proved from the variational formula z:M^(-1)z=sup_w(2z:w-w:Mw). Strong monotonicity and bi-Lipschitzness of DG justify the a.e. Hessian inversion and passage through null sets.

Consequently the dual difference
    L(Y)=Y:A Y/2 - V(Y)
is RC and has Hessian between (c/D) C and R. The diagonal entries of R are
    r_i=(k_i'+1)/[D(k_i+1)],
so R is positive and r1*r4=r2*r3=1/D². In particular R is a product of positive row and column metrics, and
    R^(-1/2) C R^(-1/2)=D C.
Thus L composed with R^(-1/2) is RC, with full Hessian between -I and I, and zero tangent at zero. This normalization is sharp for the entire input class: F=±det gives normalized Hessian ±C. Use mollification and the a.e. Hessian criterion to justify RC on every rank-one line. Left/right changes preserve compatibility in the usual affine-domain formulation, including general affine lattices by periodic localization. The actual test for L is Y; its image under the rank-one-preserving product map R^(1/2) is legitimate for the normalized energy. It need not be a compatible field on the original square without the domain change.

Writing b=-beta_*, the universal definition therefore yields the exact all-gradient inequality
$$
\int V(Y)\le\frac12\int Y:(A+2b R)Y
$$
for every mean-zero compatible Y. This is the key use of beta_* itself; there is no appeal to PC reweighting or a finite-test surrogate for QC.

## 2. Optimizing the comparison at a hypothetical near-extremizer

Suppose b>0. Take a normalized universal near-extremizing sequence F_j,X_j, with X_j a mean-zero periodic gradient, int|X_j|²=1 and int F_j(X_j)->-b. Write p_j=DF_j(X_j). Let P be the zero-mean gradient projection and Q the mean-zero solenoidal projection. For H_j=F_j+b|.|², QC follows from the universal beta bound at every base. The nonnegative affine-compatible functional int H_j(Z)-H_j(mean Z) has derivative Lipschitz constant at most 2(1+2b), hence its Hilbert descent estimate gives
    mean p_j ->0,  Pp_j+2b X_j ->0 in L².
Put q_j=Qp_j and a=1+2b. Then p_j-X_j=-a X_j+q_j+o(L²). No minimizer, uniform amplitude or full-stress compatibility is assumed.

For any fixed K as above, write z=K X+p (suppress the sequence index) and r=p-X. Strong convexity of V in the metric B and Fenchel equality give
    V(Y) >= X:Y-G(X)+(Y-z):B(Y-z)/2.
Subtract this lower bound from the beta upper bound. Since z=(K+I)X+r and A+2bR-B=a R, obtain the necessary inequality, for EVERY compatible Y,
$$
0\le {a\over2}\int Y:R Y+\int r:B Y
 +\int F(X)+\tfrac12-\int X:p-\tfrac12\int r:B r.
\tag{1}
$$
The last three scalar terms before -r:B r converge to a/2. The remaining terms are quadratic moments, so the o(L²) stationarity errors vanish for any FIXED metric. The exact Legendre value V(Y) was bounded from below here; the argument is not a claim that its true value equals this quadratic lower bound.

### 2.1 Eliminate the entire row-metric family

For K=diag(k,k,l,l), k,l>0, kl>1, B and R commute with P and Q. Their respective row coefficients are
    B1=1/(k+1), B2=1/(l+1),
    R1=(l+1)/[(kl-1)(k+1)],
    R2=(k+1)/[(kl-1)(l+1)].
The minimizer of the right side of (1) over compatible Y is the actual compatible field
    Y=-(a R)^(-1) B(Pp-X).
This step preserves compatibility and does not condition a gradient law.

Take a subsequence along which row covariance matrices int XX^T and int qq^T converge to R_X and S_q. Let E_i,V_i be their diagonal entries; E1+E2=1. Substitution of the optimal Y and passage to the limit yield
    sum_i (a B_i+B_i²/R_i) E_i + sum_i B_i V_i/a <=1.
The exact algebraic identity
    a B_i+B_i²/R_i=1+2b B_i-B_(other)
reduces this to
$$
B_1(2bE_1-E_2+V_1/a)+B_2(2bE_2-E_1+V_2/a)\le0.
\tag{2}
$$
The parameter range is exactly B1>0, B2>0, B1+B2<1. Maximizing a linear function on its closure is a two-variable LP with optimum the largest of its three vertex values. Thus (2) for all row metrics is equivalent to both parenthetical coefficients being nonpositive. Rotating the target rows arbitrarily gives the compact necessary matrix inequality
$$
\boxed{\, S_q\ \preceq\ (1+2b)\,[I_2-(1+2b)R_X].\,}
\tag{3}
$$
It holds for any subsequential limit of these second moments of a hypothetical universal near-extremizer. This in particular forces R_X <= I_2/(1+2b). Taking traces recovers the elementary total-stress bound tr S_q<=1-4b². No contradiction follows, including at isotropic row covariance. This is only an auxiliary necessary condition, not a new completion target.

## 3. Exact failure of the proposed contraction comparison

The failure is not just a poor choice of k,l. Consider the FORMAL critical moment state
    int vec(X) tensor vec(X)=I_4/4,
    p=-2b X, q=0, int F=-b,
with 0<b<=1/8. The covariance and projected stress relation can even be achieved by actual Fourier fields if the energy/constitutive requirement is dropped: take the two components of the potential to be sums of two orthogonal one-variable sine modes, using distinct frequencies for the two rows, and scale to unit squared gradient energy. Set p=-2b X as a formal stress. There is no claim of an F in the RC class realizing these gradients and prescribed negative energy.

For any product K, including arbitrary row/column orthogonal changes, the isotropic covariance is unchanged. To test (1) at this formal state, minimize the quadratic expression over ALL square-integrable Y, not merely compatible ones. The enlarged optimization is NOT a valid additional universal necessary condition for actual near-extremizers; it is used here only to give a stronger sufficient check that the formal state passes every legitimate compatible comparison. Its exact minimum is
    a/2 * [1-(1/4) sum_i (a B_i+B_i²/r_i)].
For the cofactor partner i'=5-i, the same identity holds:
    a B_i+B_i²/r_i=1+2b B_i-B_i'.
Hence the minimum equals
$$
\frac{a(1-2b)}8\sum_i B_i>0.
$$
It is positive for EVERY finite admissible product metric. The formal state therefore passes every inequality obtained by this universal dual normalization and quadratic Fenchel comparison, even allowing all comparison fields and all product metrics. The full normalized energy constraint and actual value of the conjugate are not captured by this moment state. It is not a countermodel to Morrey or to arguments using additional true constitutive information. It does not establish the impossibility of other Legendre transformations or more precise conjugate estimates.

In particular, further parameter optimization of (1) cannot on its own yield beta_*>=theta beta_* for theta<1. A successful direct proof using this idea would require a genuinely stronger estimate of the common conjugate energy, or an integrand-dependent reduction of its normalized Hessian bound with quantitative gain. No such estimate was established. Stop this comparison-only attack rather than create another hierarchy.

## 4. Actual computational verification

Executed research/audit/beta_legendre_exact.py (Python 3, SymPy, SciPy/HiGHS). It checked the exact cofactor-metric inverse and normalization identities, 54 rational product-metric controls, and five LP comparisons against exact triangle-vertex elimination. The LPs detect violations for some artificial unbalanced covariance/stress data, but not the balanced formal state; the proof of its survival for the entire parameter domain is the analytic identity above. SHA-256 19e9f33b2d0f11994ed15ec86b9427a041cc95fef3f68e8a23219bdd115aa7bf; Git blob 8a7d8775bfaac6393ac6c45a897fddedd520e622.

The beta_* exact-zero objective is unchanged. No full unrestricted certificate, actual counterexample, improved universal bound or formal proof was obtained.
