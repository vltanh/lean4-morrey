# Full stationary lift: energy-momentum compatibility and a local quadratic curvature repair

24 November 2026. Continuation of [joint Hamiltonian flow](IWANIEC_MORREY_JOINT_HAMILTONIAN_FLOW.md). This replaces the short-time global ODE requirement by a local, explicit curvature repair and adds the conservation law from inner variations. It applies to every smooth globally RC planar integrand, without isotropy or homogeneity. The higher-dimensional input can be any smooth RC energy on 6x2 matrices, including row pullbacks of the verified 3x2 and 4x2 examples.

**Hand results.** (1) At QC equality for bounded gradients, the full six-row constitutive lift below is a genuine compatible field with the correct base. (2) A negative RC Jensen gap on that lift transfers to a planar counterexample by an explicit O(t²) rank-one curvature repair on a witness ball and global convex-tail gluing. No numerical Hamiltonian integration or global Hessian bound on the original polynomial is required. Equality laminates lift to laminates for this larger graph. (3) Small QC gaps give quantitative inner-stress stationarity, including actual L² compatibility approximation for uniformly bounded gradients. (4) All direct full-rank linear row embeddings of the original three-wave Sverak witness into the gradient/stress graph are impossible; the direct Cassese power-field block assignment fails exactness in its negative-density range. General row remixing is NOT ruled out: an exact split-signature example passes the closed-one-form condition, although that particular remix fails the degree-two determinant support test.

No qualifying negative planar pair, proof of critical-state rigidity, new Lean theorem or independent review. The exact symbolic controls were executed locally. The first variation formulas and energy-momentum conservation law are standard variational identities (cf. the stationary differential inclusion literature, https://doi.org/10.1007/s00526-021-01981-z). The particular full-lift rank-one perturbation and quantitative repair are the new arguments here; no exhaustive priority claim.

## 1. The full lift and all compatibility equations

Use Frobenius inner products, C X=cof X, and J=[[0,-1],[1,0]]. Thus C X=J X J^T, and C is a symmetric orthogonal involution. For F in C^1 define
    p(X)=DF(X), T(X)=F(X)I-X^T p(X),
    L_F(X)=[X; C p(X); T(X)J].
The semicolons stack rows, so L_F(X) is 6x2. Let F be globally QC, X=A+Du a bounded periodic gradient, and
    J_F(A,u)=int F(X)-F(A)=0.
All three blocks of L_F(X) are compatible, with mean L_F(A).

For the first block this is the hypothesis. For the second, use the first variation with respect to u and the base A:
    div p(X)=0, int p(X)=p(A).
The row rotation by J^T turns a solenoidal row into a curl-free row; multiplying the result by the constant target rotation J preserves compatibility. Hence C p(X) is a periodic gradient plus its affine mean. For the third, take a periodic smooth vector field xi and the torus diffeomorphism x->x+t xi(x). The transported affine-plus-periodic map has the same base. Changing variables, its energy is
    int F(X(I+t Dxi)^(-1)) det(I+t Dxi).
The equality map is a global minimizer, so its derivative at zero vanishes:
    int [F(X)I-X^T p(X)]:Dxi=0.
Thus div T(X)=0 rowwise. To get the mean, use the inequalities on every affine lattice (equivalently the ordinary domain-independent definition of QC). For every invertible constant B,
    int F(X B)-F(A B)>=0.
Indeed compose the map with the domain-linear change B; averaging over its transformed fundamental cell preserves the average. At B=I this gap is zero, so differentiation gives
    int X^T p(X)=A^T p(A).
Together with the equality of energies, int T(X)=T(A). Therefore T(X)J is a gradient plus T(A)J. The potentials are Lipschitz because all fields are bounded and the periodic curl-free potential has the given L-infinity weak derivative. No differentiability of the original map beyond Lipschitz is assumed.

Exactly the same mean identities (not the spatial compatibility claim) hold for equality of any compact laminate with mean A and any globally RC F: translating all atoms by h, or right-multiplying them by any constant B, preserves the laminate inequalities, so the two differentiations are legitimate.

## 2. Null rank-one directions of the full lift

Let F be C^3 and RC on a neighborhood of a closed matrix ball. At X put H=D²F(X), and let R be a Frobenius-unit rank-one matrix. Set ell=H[R,R]. The planar Finsler lemma from [cofactor duality](IWANIEC_MORREY_COFACTOR_DUALITY.md) gives
    H=c C+P, P>=0.
If ||H||<=M, one may take |c|<=M, ||P||<=2M. At ell=0, P R=0, so HR=c C R. Since ell(X) is nonnegative in an open neighborhood and vanishes, its spatial derivative v=D³F[R,R,.] is zero.

The exact first and second directional derivatives are
    D L_F[R]=[R; C HR; ((p:R)I-R^T p-X^T HR)J],
    D² L_F[R,R]=[0; C v; (ell I-2 R^T HR-X^T v)J].
At ell=0, the first derivative is rank one, and the second derivative is zero. To see the first, write R=a tensor n. Both R and C HR=cR have row direction n. The matrix (p:R)I-R^T p is the planar adjugate of R^T p=n tensor (p^T a), so after multiplying by J its rows also have direction n. The other term X^T C R J has this row direction since C R=(Ja) tensor (Jn) and (Jn)^T J=n^T. To see the second, use v=0 and R^T C R=det R I=0.

Consequently for any C² RC K on 6x2, the function g=K o L_F satisfies D²g[R,R]>=0 at every null LH direction of F. This is the exact tangent condition for RC of the perturbation, not an assertion that g itself is RC.

For completeness even without a fourth derivative, on any fixed compact witness ball let
    k(t)=max_(X,R) (-ell-t D²g[R,R])_+/t,
where the maximum is over X in the ball and unit rank-one R. Then k(t)->0 as t->0+: otherwise take a convergent sequence of maximizers; boundedness of D²g forces ell->0, while the limiting D²g would be negative on a null direction, a contradiction. Thus F+t g+(t k(t)/2)|X|² is RC on that ball. The next section makes this repair quadratic in t and explicitly computable.

## 3. Uniform local quadratic repair

Suppose F is globally RC and C^4, K is globally RC and C². Let the witness range and A lie in B_r, choose R>r, and use the following nonnegative bounds, enlarged if needed to be rational:
    M >= sup_(B_(R+1)) ||D²F||op;
    G >= sup_(B_(R+1)) |DF|;
    B >= max(1, sup_(B_(R+1)) ||D³F||op, sup_(B_(R+1)) ||D^4 F||op);
    N >= sup_(L_F(B_R)) ||D²K||op;
    L >= sup_(L_F(B_R)) |DK|.
Tensor operator norms use unit Euclidean inputs. Define rational bounds
    A0=1+(1+R)M+3G,
    D0=(1+R)(M+1),
    E0=(1+R)(B+1)+3(M+1),
    a0=2 N A0 D0+L E0.

Here is the bound at ANY X in B_R and unit rank-one R1. Write ell=D²F[R1,R1]. In the Finsler decomposition put u=P R1. Then |u|²<=2M ell. Furthermore
    |v|²=|grad ell|²<=2B ell.
Indeed take the descent step -v/B, whose length is <=1 by the third derivative bound; the whole segment stays in B_(R+1). Taylor's bound with D^4F<=B and nonnegativity of ell at its endpoint prove the inequality.

Compare D L_F[R1] with the rank-one matrix obtained by replacing HR1 by c C R1 in the first derivative formula. Their difference has norm <=(1+R)|u|<=D0 sqrt(ell), and each has norm <=A0 (use sqrt(2)+1<=3 for the p terms). Since K has nonnegative rank-one Hessian, the first term of the second-derivative chain rule is bounded below by -2 N A0 D0 sqrt(ell). For its other term,
    |D² L_F[R1,R1]|
       <=(1+R)|v|+sqrt(2)ell+2|u|<=E0 sqrt(ell),
using ell<=M and sqrt(2M)<=M+1, sqrt(2B)<=B+1. Therefore
    D²g[R1,R1]>=-a0 sqrt(ell).
Completing a square gives the pointwise uniform estimate
$$
D^2(F+t g)[R_1,R_1]\ge \ell-a_0t\sqrt{\ell}\ge -a_0^2 t^2/4.
$$
Thus for every t>=0 the energy
$$
\boxed{P_t(X)=F(X)+tK(L_F(X))+\frac{a_0^2t^2}{8}|X|^2}
\tag{1}
$$
is rank-one convex on B_R. For a global extension shift P_t by a constant to make it positive on B_R, take its maximum on B_R with a steep convex barrier b(|X|²-r²), and use the barrier outside B_R. Choose b>0 so that it strictly dominates the shifted P_t on the boundary sphere. The restriction to each rank-one line glues convexly, because the barrier dominates on a collar of the interface. On B_r the barrier is nonpositive, so the extension agrees exactly with shifted P_t on the entire witness and base range. A convex smooth maximum with width smaller than the strict margins gives a C11 global extension if desired. Neither the original F nor K needs a global Hessian bound.

**Theorem A (full-lift negative certificate).** For an actual bounded periodic planar gradient with mean A, put
    E=int |Du|²,
    j0=int F(A+Du)-F(A),
    d0=int K(L_F(A+Du))-K(L_F(A)).
If
$$
\boxed{j_0+t d_0+(a_0^2t^2/8)E<0}
\tag{2}
$$
for some t>0, then a globally finite RC planar energy has a strict negative Jensen gap on the SAME compatible test. This follows from (1) and the null mean of Du, and from the global extension. If j0=0, d0<0 suffices. At exact QC equality the d0 in (2) is a genuine 6x2 gradient Jensen gap by Section 1. Any RC K in 3x2 or 4x2 can be pulled back along a constant row map of the full lift. Unlike the earlier global Hamiltonian criterion, all curvature constants in (2) are evaluated only on finite balls. Polynomial energies and rational periodic PL data allow exact rational bounds (bound each polynomial and its derivatives by absolute coefficient sums on a sufficiently large enclosing cube). No numerical ODE is required. This is an analytic sufficient criterion; we have not implemented a full new polynomial certificate checker or found a strictly negative instance of (2).

**Corollary (full lift of equality laminates).** If nu is a compact planar laminate, F is globally RC and C^3, and int F dnu=F(A), then (L_F)#nu is a laminate on 6x2 with mean L_F(A). Apply the local o(t) repair at the beginning of Section 3 and global gluing to the fixed bounded support. Its Jensen gap on nu is nonnegative, hence d0>=0 after dividing by t and taking t to zero. The mean identities are in Section 1. Approximate any finite higher-dimensional RC test K by smooth RC mollifications on the compact lifted support; this proves Jensen for every such K. No finite-depth hypothesis on nu.

## 4. Quantitative inner stationarity at near equality

Let F be globally C11 and QC with Lip DF<=M, recentered at base zero so F(0)=DF(0)=0. Write X=Du, E=int|X|², j=int F(X)>=0; allow arbitrary periodic W1,2 tests. Then j<=ME/2. The earlier Hilbert descent estimate gives the small mean and compatible part of p=DF(X). There is also the following energy-momentum estimate:
$$
\left|\int T(X):D\xi\right|
 \le 12\sqrt{MEj}\ \|D\xi\|_\infty
\tag{3}
$$
for all periodic smooth xi (the norm is the supremum operator norm). Moreover
    |int X^T p(X)|² <= 2MEj,   |int T|<=sqrt(2)j+sqrt(2MEj).

For the mean, the function of B given by int F(X B) is nonnegative for all invertible B by periodic QC, hence for every B by continuity. Its derivative has Lipschitz constant <=ME; apply the descent lemma at B=I. For (3) normalize ||Dxi||infty<=1. The inner-variation energy I(t)=int F(X(I+tDxi)^(-1)) det(I+tDxi) is nonnegative for |t|<=1/4, since the domain map is a diffeomorphism and the transported map is W1,2. Its second derivative is bounded a.e. by 64ME: if Y=X(I+t Dxi)^(-1), h=det(I+tDxi), then |Y|<=2|X|, |Y'|<=2|X|, |Y''|<=5|X|, |h|<=2, |h'|<=3, |h''|<=2. Combine with |F(Y)|<=M|Y|²/2 and |DF(Y)|<=M|Y|. The product rule gives at most 56 ME, so 64 suffices. Taylor in either sign yields |I'(0)|<=j/t+32ME t. Choose t=sqrt(j/(32ME))<=1/8; when j=0 use the limit. M E=0 is trivial. The derivative is exactly the left side of (3).

In particular if M,E and |X|_infty are uniformly bounded and j tends to zero, the third block is asymptotically compatible in L². Here are the details rather than an inference from a weak distributional residual. For every periodic vector potential xi with ||Dxi||₂<=1, use ordinary Lipschitz truncation at level lambda>=1: there is a periodic Lipschitz xi_lambda with ||Dxi_lambda||infty<=C lambda and ||Dxi-Dxi_lambda||₁<=C/lambda. This follows by the Hardy-Littlewood maximal bound on |Dxi|, the Sobolev pointwise Lipschitz estimate on the good set, and coordinatewise McShane extension on the flat torus: the bad set has measure <=C/lambda², the gradients agree a.e. on its complement, and Cauchy-Schwarz on the bad set bounds the original derivative's L¹ norm there. The gradient of the extension is bounded by C lambda. Smooth periodic convolution permits use of (3) on the truncated potential. Taking the supremum over xi gives for the zero-mean gradient projection P
    ||P T||₂ <= C [lambda sqrt(M E j)+||T||infty/lambda].
The bound on |X| gives a bound on T. Choosing lambda->infty sufficiently slowly proves ||P T||₂->0. The mean T tends to zero as well. Rotation by J swaps the zero-mean solenoidal and gradient subspaces, so T J is L²-close to an actual zero-mean compatible gradient. The same conclusion holds for a family with equiintegrable |X|⁴ in place of the L-infinity bound, using the L² norm of T on the small bad set and the bounded L² norm of the truncation error. In particular, all 2x2 minors of the full lift then have the asymptotically correct means, by L² continuity of the minors.

**Scope:** the critical sequences from the universal C11 margin have only a known L² gradient bound, not uniform L∞ or equiintegrable fourth moments. For them (3) and the mean-stress estimates remain valid, but we cannot conclude L² compatibility of the third block without controlling concentration. Also neither exact nor approximate full stationarity alone gives the missing energy rigidity.

## 5. Direct realization tests on the two higher-dimensional mechanisms

### 5.1 All direct linear row embeddings of the classical Sverak witness

Write the original compatible three-wave field in radians as
    W3 = sum_i e_i tensor k_i r_i,
    k1=(1,0), k2=(0,1), k3=(1,1),
    (r1,r2,r3)=(cos x,cos y,cos(x+y)).
Suppose its full-rank constant row embedding into 4x2, with an arbitrary constant base added, equals [X; C DF(X)] for a globally RC C11 planar F. Denote the upper and lower two-vector coefficients of each row-embedding column by a_i,b_i.

A useful exact finite-difference consequence of the Finsler lemma is
    dist(DF(Y)-DF(X), span(C(Y-X)))²
       <= 2M (DF(Y)-DF(X)):(Y-X)
when Y-X has rank one and Lip DF<=M. For smooth F integrate H=cC+P along the segment, use |P R|²<=2M R:P R and Jensen. For C11 mollify, prove the inequality for each smoothing and pass to the limit. In particular a zero right side forces the stress difference to be parallel to the cofactor of the rank-one difference.

The three-wave support includes each of the pairs with r_i=+1 and -1, other r's zero: use phases 0, pi/2 and pi. On this pair, the upper difference is 2a_i tensor k_i and the lower difference is 2b_i tensor k_i. Their cofactor-stress inner product is zero. If a_i=0 then the constitutive law forces b_i=0; otherwise the finite-difference lemma gives b_i=c_i a_i.

There is also an independent integrability constraint: the one-form DF(X):dX is exact on the phase torus, since it is d(F(X)). Both X and the asserted stress are smooth functions of phases even if F is only C11. Its exterior derivative says
    sum_(i<j) (p_i:X_j-p_j:X_i) dr_i wedge dr_j=0,
where X_i=a_i tensor k_i and p_i=C(b_i tensor k_i).
The three coefficients dr_i wedge dr_j are linearly independent as functions: evaluation at (pi/2,pi/2), (pi/2,0), (0,pi/2) isolates the three pairs. Consequently
    (c_i-c_j) (C X_i):X_j=0.
The second factor is nonzero exactly when a_i,a_j are linearly independent (all k_i are nonparallel). If two a_i are independent, the graph of such nonparallel pairs connects all nonzero a_i, so all c_i are the same. All columns of the row embedding then lie in the common two-dimensional graph b=c a. If all a_i are collinear, the columns lie in the direct sum of two copies of that line, again dimension at most two. Zero columns do not increase the dimension. Contradiction to rank three.

Thus the complete family of direct linear full-rank embeddings of this particular three-wave witness into the constitutive graph is excluded, not just the naive assignment of its first two rows. It also excludes direct linear embeddings into the full six-row lift: at each pure-mode pair the rank-one restriction of F is affine (its endpoint directional derivatives agree). The stress-energy difference is exactly
    2[((p0:X_i)I-X_i^T p0-A^T p_i)] J
for common centers A,p0. This is a fixed linear row combination of X_i and C p_i: use adj(X_i^T p0)J=adj(p0) J X_i and p_i J=J C p_i. Hence the additional pair differences cannot increase the rank of the embedding.

For any bounded compact family of such full-rank embeddings with a common positive lower singular-value bound and common C11 bound on F, there is a positive L² separation from an exact constitutive fit. Otherwise center the input and stress and extract convergent row matrices and a locally uniform subsequential limit of the recentered gradients DF using their uniform Lipschitz bound. The limit is the derivative of a globally C11 RC F, by local uniform convergence of the functions, and is an exact forbidden lift. This is a compactness separation, not an explicit numerical bound.

This does NOT rule out projecting a nonlinear joint lift onto the Sverak field, with additional compatible rows or extra modes in the kernel of the row projection. That is the relevant surviving transfer problem.

### 5.2 Direct Cassese power-field assignment, and a row-remix check

Use the power field behind the Dragičević lower bound for B², used in Cassese's [FourByTwo formalization](../../Morrey/Cassese/FourByTwo.lean) (see also [the cited lower bound](../../Morrey/Common/External/Dragicevic/LowerBound.lean)). On an annulus, let f(z)=z² |z|^(-2 alpha), 0<alpha<1/2, u0=partial_bar f, u1=partial f. Put X0=Du0, Z0=Du1. In conformal/anticonformal complex coordinates and with sigma=|z|^(-2 alpha), theta=2 arg z,
    X0=(A sigma exp(i theta), B sigma exp(2i theta)),
    Z0=(D sigma, A sigma exp(i theta)),
    A=-alpha(2-alpha), B=alpha(1+alpha), D=(2-alpha)(1-alpha).
This follows by elementary Wirtinger differentiation. The canonical chain uses lower block sqrt(2) Z0, so its beta equals sqrt(2) alpha_X0 and the second chain residual vanishes.

If sqrt(2) Z0=C DF(X0) on an open annulus, the one-form p:dX0 must be closed. The conformal coefficients of p are sqrt(2) D sigma and -sqrt(2) A sigma exp(i theta), since C preserves the conformal part and negates the anticonformal part. Using the Frobenius pairing 2 Re(z zbar'+w wbar'), compare the sigma and theta derivatives of this one-form. With ac=A D and bd=-A B (omitting the common sqrt(2) factor), closedness requires
    ac+3 bd=0,
equivalently alpha²+3alpha-1=0, or D=3B. At alpha=1/4, the limiting exponent used for the L4 lower bound, this condition fails. The verified Cassese quartic on 4x2 is K=30 x²+20xy-2y² with
    x=3(|beta_X|²+|beta_Z-sqrt(2) alpha_X|²), y=|alpha_Z|².
For the direct power pair x=3B² sigma², y=2D² sigma². At alpha=1/4 the exact density is -32049/32768 sigma^4, but when D=3B as required by the direct constitutive assignment the density is +702 B^4 sigma^4. Thus the direct exact assignment and the canonical negative-density regime are disjoint. These are local annular identities, not a claim about a cutoff global witness.

Arbitrary invertible row mixing changes the exactness condition. In terms of a symmetric split-signature form S on the four-dimensional row space and the column vectors M_1(theta),M_2(theta) of the unscaled joint power matrix, the condition becomes
    M_1^T S M_2' - (M_1')^T S M_2=0.
Indeed the symplectic form d(p:dX) is a constant pairing of the two matrix columns by a symmetric split form; row changes conjugate this form. At alpha=1/4 the nondegenerate S=diag(-49,-49,1,1) satisfies the condition exactly. For example the corresponding row remix
    X=Z0+7X0, Z=J(Z0-7X0), p=C Z
has closed one-form, with
    det X=(49/8) sigma² (1-cos theta),
    (p:X)/2=-(49/8) sigma² sin theta.
The latter is a primitive of p:dX on the entire open cone in these parameters. Nevertheless this particular row remix cannot be realized by a global C11 RC F on ALL radial scales sigma>0: subtract the constant value at zero and observe p(sigma,theta) is linear in sigma, so F agrees with (p:X)/2 there and DF(0)=0. Logarithmic Cesaro averages of s^(-2)F(s X) have a locally uniformly convergent subsequence by the common C11 normalization, and their limit is positively 2-homogeneous RC (the difference after any fixed dilation is bounded by O(1/T) times |X|², using the endpoints of the averaging interval of length T). They preserve these values on the cone. By [the prior degree-two origin support theorem](IWANIEC_MORREY_ANISOTROPIC_ORIGIN_RECTIFIED.md) the limit must dominate c det for some real c. The displayed ratio -sin(theta)/(1-cos(theta)) is unbounded below near theta=0 from the positive side, contradiction. This uses all-scale realization; no such global contradiction follows merely from closedness on a fixed annulus. Other remixings and non-power fields remain open. In particular the exactness condition alone is not a rank-one convex extension theorem.

## 6. Verification and next target

The companion [full_stationary_lift_exact.py](../../research/audit/full_stationary_lift_exact.py) was actually executed with SymPy. It checked symbolic null rank-one first and second derivatives, the general cubic-jet chain rule, the three-wave exterior-derivative independence, the Cassese power-field exactness polynomial and both exact densities, and the split-signature row remix and determinant-support identities. Two initial symbolic equality tests were corrected to compare expanded differences, and an initial incorrect hand value for the negative density was replaced by the exact -32049/32768; final execution passed. The script checks finite algebra identities only. No large solver run or qualifying negative joint field is claimed.

The unrestricted problem is not closed. Use (2) to test genuinely nonlinear row projections of the full stationary lift, or derive an exact rigidity inequality for its compatible critical states. The three-wave direct embedding route is exhausted at exact linear lifts, and the direct Cassese power pair cannot be used as an exact constitutive assignment. The remaining question is not another ladder of exponents or mesh sizes. It is whether the nonlinear constitutive and energy-momentum constraints can coexist with a sufficiently negative higher-dimensional gap, or can instead enforce universal planar Jensen.
