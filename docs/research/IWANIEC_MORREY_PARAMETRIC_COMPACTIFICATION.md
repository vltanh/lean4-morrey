# Unrestricted compactification on oriented graph bivectors

24 November 2026. Fresh-eye research after the reset. **All finite-valued planar RC integrands and all bounded compatible gradients are covered by the reduction**, not only homogeneous or isotropic energies. The new angle is a compact domain for the entire integrand side of the unrestricted question.

Results: exact extension of arbitrary local RC data to a globally line-convex positive-homogeneous function on the decomposable bivector cone; explicit compactness and a positive polynomial smoothing operator; a finite, effectively specified family of globally RC tests at every prescribed relative area accuracy, uniform over all compatible fields, amplitudes, bases and integrands. An exact compact positive-stress criterion has a fixed mass equal to the area excess. The underlying geometric chart change also identifies a useful obstruction that has not been handled by the graph swap.

This is a hand proof, with exact algebra controls actually executed. No independent mathematical review, exhaustive prior-art audit, Lean verification, or universal Morrey proof. The finite families depend on accuracy; there is no exact finite stopping cutoff, no bound on gradient complexity, and no claim of universal positive-stress feasibility. This extends the earlier homogeneous angular finite-accuracy result to the entire unrestricted problem by changing the variables, rather than assuming matrix homogeneity.

## 1. The graph cone and its compact section

Use the Euclidean exterior algebra of R^4, with orthonormal basis e12,e13,e14,e23,e24,e34 for V=Lambda^2 R^4. For a 2x2 matrix X, define

    m(X)=(e1+X11 e3+X21 e4) wedge (e2+X12 e3+X22 e4)
        =(1,X12,X22,-X11,-X21,det X).
    r(X)=|m(X)|=sqrt(1+|X|_F^2+(det X)^2).

A bivector xi=(a,b13,b14,b23,b24,b) is simple (decomposable) iff xi wedge xi=0, equivalently
    a b = b13 b24 - b14 b23.
Write L(xi)=[[-b23,b13],[-b24,b14]], so this equality is a b=det L(xi). On the open chart a>0,
    xi=a m(L(xi)/a).

Let C be the closed cone of all simple bivectors, including zero. Define the following two rational linear coordinate triples:

    p=(xi12+xi34,xi13-xi24,xi14+xi23),
    q=(xi12-xi34,xi13+xi24,xi14-xi23).

The cone is exactly |p|=|q|, since |p|^2-|q|^2=4(a b-b13 b24+b14 b23). The Euclidean norm in V is sqrt((|p|^2+|q|^2)/2). In particular its unit section S is exactly S^2 x S^2 with the metric inherited from V; both triples have norm one. Orientation is retained: xi and -xi are distinct. No evenness assumption.

Call Phi:C->R line-convex if its restriction to EVERY affine line contained in C is convex. For two simple bivectors xi,eta, the entire line through them is simple iff xi wedge eta=0. For their positive-a graph representatives this means exactly that the matrix difference has rank at most one, by the 2x2 determinant polarization identity. A nonnegative continuous positively 1-homogeneous line-convex Phi gives the globally finite matrix energy

    F_Phi(X)=Phi(m(X)).

This is RC because m is affine on every rank-one line, including all signs of det X. It is not in general homogeneous or isotropic as a function of X. For actual gradient laws with mean A, E m(X)=m(A) by the mean and determinant identities. The area integral of Phi on the graph is precisely E F_Phi.

## 2. Exact extension of arbitrary RC data on any bounded graph range

**Theorem A.** For any finite RC F on real 2x2 matrices and any compact K of matrices, there are a real constant c and a continuous nonnegative positively 1-homogeneous line-convex Phi on ALL of C such that

    Phi(m(X))=F(X)+c  on K.

In particular, any strict Morrey counterexample transfers exactly, with no change of its actual gradient witness or its gap, to a function of this compact angular form. Conversely a violation for any such Phi is an unrestricted planar counterexample.

**Proof.** Choose real numbers T>L>max(1,max_K r). The set of matrices with r<=T is compact. By continuity of finite RC F, choose c such that f=F+c>=0 on this set. On the positive chart define its perspective

    U(xi)=a f(L(xi)/a).

It is continuous, 1-homogeneous and convex on every portion of a simple line in a>0: a line segment with positive a's induces a rank-one segment between the graph matrices, with weights proportional to the original weights times their positive a's. Apply RC and multiply by the intermediate a. This uses neither a global convexity claim for F nor an orientation assumption on its matrix determinant.

Use the globally convex nonnegative 1-homogeneous barrier on V

    B(xi)=M (|xi|-L a)_+.

Choose M>0 large enough that f(X)<M(T-L) on r(X)=T. Define

    Phi(xi)=max(U(xi),B(xi)) if a>0 and |xi|/a<T,
             B(xi) otherwise.

At the nonzero interface a>0, |xi|/a=T there is a strict gap B>U, so the formula agrees locally with B. The positive chart portion used in the maximum is separated from a=0 away from the origin. Everywhere off zero, the restriction to any simple line is locally convex and hence convex along that line. At zero, homogeneity and boundedness on S give continuity. A line through zero has two linear half-lines; nonnegativity gives the correct ordering of the slopes. Thus Phi is globally line-convex, continuous, positively 1-homogeneous and nonnegative. At m(X), X in K, the barrier is zero and f>=0, proving exact equality. QED.

One may translate an arbitrary base to zero and scale its bounded gradient witness into a fixed arbitrarily small matrix ball before this construction, if desired. Such rescaling is an affine change of the matrix integrand, not a claim of matrix homogeneity. There is no orientation-symmetrization step; replacing a by |a| in the barrier would introduce a downward crease at a=0 and would not justify convexity.

## 3. Uniform compactness without a curvature or exponent assumption

Normalize the nonnegative cone by max_S Phi<=1. There is a universal angular Lipschitz bound:

    |Phi(xi)-Phi(eta)| <= 5 M0 |xi-eta|,   xi,eta in S,
    M0=max_S Phi.

Indeed on a linear subspace of the form u wedge R^4, every vector and every line is simple. The restriction is a finite convex positively 1-homogeneous function, hence subadditive; its Lipschitz constant is at most M0 by applying subadditivity in both directions. For xi,eta unit and eps=|xi-eta|<1/2, write xi=u wedge v with u,v orthonormal. Let i_u denote contraction, set v'=i_u eta/|i_u eta| and u'=-i_(v') eta. The pair is orthonormal and eta=u' wedge v'. The contraction has operator norm at most one, hence |v'-v|<=2eps and |u'-u|<=3eps. Compare via the intermediate u wedge v', first with common u, then with common v'. The sum of the two bivector distances is at most 5eps. If eps>=1/2, use 0<=Phi<=M0 on S. This proves the estimate. The normalized nonnegative cone is compact in the uniform angular norm by Arzela-Ascoli and closedness of all defining line inequalities. No noncompact tail in the base matrix variable occurs in this compact section.

## 4. A positivity-preserving polynomial averaging operator on the whole cone

This is the computationally useful part, since arbitrary Euclidean convolution of angular data need not preserve the line condition.

On S identify f(p,q)=Phi(xi) with |p|=|q|=1. Use normalized sphere area dσ on S^2. For an integer N>=0 define

    P_N(p,q)=(N+1)^2 integral f(p',q')
        ((1+p·p')/2)^N ((1+q·q')/2)^N dσ(p') dσ(q').

It is a polynomial of degree at most N in each triple, and, crucially, its positive 1-homogeneous extension on C is line-convex. Here is an exact proof of preservation, not a sampled curvature argument.

Consider a uniform unit quaternion Q=(a,v) on S^3, with its probability reweighted by a^(2N) and renormalized. The induced rotation R_Q on R^3 has the following distribution when applied to a fixed unit x: its image y has density

    (N+1)((1+x·y)/2)^N

relative to dσ. To verify this, before reweighting, y is uniform, and the conditional fiber is Q times the circle of unit quaternions (cos θ,x sin θ), with uniform angle. The scalar component of the product is a cos θ-(v·x)sin θ. Its 2N-th power average is a constant depending only on N times [a^2+(v·x)^2]^N. The quaternion rotation identity gives a^2+(v·x)^2=(1+x·R_Q x)/2. Normalization follows by integrating T^N for T=(1+x·y)/2 uniform on [0,1]. Thus the claimed density is exact.

Take two independent such rotations of the two triples. Their product is a linear orthogonal map of V preserving C (because it preserves both norms), hence sends simple lines to simple lines. The homogeneous extension of P_N is the positive average of Phi composed with these linear maps. It remains line-convex and nonnegative. The weight is independent of the original (p,q); this independence is essential.

For the normalized M0<=1 cone, the preceding Lipschitz bound gives a uniform approximation with explicit rate:

    ||P_N-f||_{S,infty} <= 10/sqrt(N+2).

Under the kernel, E |p-p'|^2=4/(N+2), by integration of 4(1-T) against (N+1)T^N; likewise q. Hence the mean squared bivector distance is 4/(N+2), giving the bound by Cauchy-Schwarz. No angular regularity of f beyond that derived from the cone is assumed.

More generally rotational averaging converges uniformly for any continuous (even signed) line-convex homogeneous function on C. For smooth angular data it converges in C^2: the quaternion measures concentrate at the two scalar unit quaternions, which both induce the identity rotation; composition by rotations is continuous in C^2 on the compact manifold. This observation is used in the duality argument below.

## 5. Exact semialgebraic curvature test and a predetermined finite family

Let P(p,q) be any polynomial and define its homogeneous extension by

    Phi_P(xi)=|xi| P(p/|xi|,q/|xi|)   for xi!=0, Phi_P(0)=0.

The nonradial unit tangent to a simple line at a unit xi has coordinate triples (u,v) satisfying

    |p|=|q|=|u|=|v|=1,  p·u=q·v=0.

Conversely every such pair is an allowed tangent. Indeed the Euclidean orthogonality and wedge-polarization orthogonality equations give p·u+q·v=0 and p·u-q·v=0, while simplicity of the tangent gives equal norms. The full line of xi+t h is simple. The curvature of the homogeneous extension along this line at t=0 is exactly

    L P(p,q,u,v)
      = P - p·D_p P - q·D_q P + D^2P[(u,v),(u,v)].

This follows by differentiating sqrt(1+t^2) P((p+tu)/sqrt(1+t^2),(q+tv)/sqrt(1+t^2)). Radial components are in the Hessian kernel of a 1-homogeneous function, and scaling gives the curvature condition at all nonzero xi. For P>=0, global line convexity is therefore equivalent to L P>=0 on the compact semialgebraic set K={(p,q,u,v) with the preceding unit and orthogonality constraints}. Without P>=0 the same criterion works: along every allowed great circle the curvature is h''+h, and integration against sin t on [0,pi] gives h(0)+h(pi)>=0. Thus the slope condition on each line through zero also follows from L P>=0. The constant polynomial 1 has L 1=1, an exact positive order unit.

For normalized f, expand P_N in the full monomial basis of separate degrees <=N. There are

    K_N=binomial(N+3,3)^2

coefficients, each bounded in absolute value by B_N=(N+1)^2 4^N. This follows by bounding the absolute sum of coefficients of each kernel factor by ((1+sqrt(3))/2)^N<2^N and integrating |f|<=1. A monomial of total degree d<=2N has absolute curvature bounded by 1+d^2 on K: the Euler term contributes at most 1+d, and the second derivative term at most d(d-1), since all coordinates of p,q,u,v have modulus at most one.

Given a prescribed rational epsilon in (0,1), choose any integer N with 10/sqrt(N+2)<=epsilon/2, then choose a positive rational step delta with

    K_N delta (2+4N^2) <= epsilon/2.

Round each coefficient to a multiple of delta within delta. Let R be the rounded polynomial and put

    c_N=K_N delta(1+4N^2),   Q=R+c_N.

The uniform value error from rounding is <=K_N delta, and the curvature error <=c_N. Since P_N>=0 and L P_N>=0, this repair guarantees Q>=0 and L Q>=0 EXACTLY. Also ||Q-f||<=epsilon. The candidates Q are members of the following **predetermined finite family**:

1. enumerate all coefficient vectors in delta Z^K_N with |coefficient|<=B_N+delta;
2. add c_N to their constant coefficient;
3. keep precisely those satisfying the two polynomial universal inequalities Q>=0 on S and L Q>=0 on K.

The filter is decidable by real closed field quantifier elimination on rational coefficients, not by grid sampling. The family may be prohibitively large; no implementation or timing claim is made. Every member is globally RC as a matrix function through Phi_Q(m(X)); every normalized nonnegative Phi is within epsilon of some member. The degree and coefficient bounds are independent of the original F, the base, the witness and its amplitude or complexity.

**Theorem B (finite-accuracy unrestricted tests).** For every actual gradient law with mean A, put S_area=E r(X). For every nonzero nonnegative line-convex Phi as above and its angular maximum M0, one of these same finitely many tests Q satisfies

    |J(F_Phi)/M0 - J(F_Phi_Q)|
          <=epsilon [E r(X)+r(A)] <=2 epsilon S_area.

The last inequality uses E m(X)=m(A) and norm convexity. Thus if every member obeys Jensen against all actual compatible laws, the entire parametric cone obeys Jensen up to relative area error 2epsilon; conversely any negative normalized gap larger than that error is detected by one of the tests. By Theorem A and epsilon->0, unrestricted Morrey is exactly equivalent to all these rational polynomial parametric tests having nonnegative Jensen, over all positive accuracies.

Any strict counterexample can therefore be taken to have the special *algebraic* integrand Phi_Q(m(X)), smooth in matrix space, with growth bounded by a constant times sqrt(1+|X|^2+det(X)^2). An arbitrarily small additional positive constant in Q gives strict positive angular curvature if desired, with the original strict gap preserved. Smooth and periodic piecewise affine rational test approximations preserve a strict gap by the standard bounded-gradient smoothing/interpolation arguments. For a rational nodal PL test and rational base the integrand values and integrals are real algebraic, so their strict sign is decidable exactly. This is an unrestricted certificate hierarchy with compact curvature constraints and at most area growth, not a hierarchy confined to homogeneous matrix energies.

**Critical limitation:** N and the list size depend on epsilon, and no positive lower bound on the size of a possible normalized counterexample is known. Nor is there a bound on the mesh of an actual compatible witness. Neither passing finitely many tests nor the existence of the finite family proves exact Morrey. The result gives uniform finite accuracy on the entire integrand side; it does not solve the law side.

## 6. One compact positive curvature stress with mass fixed by area excess

There is a compatible-law formulation on the SAME fixed compact space K, independently of matrix amplitude. Let sigma be the signed angular area measure of a bounded compatible law:

    sigma = (X -> m(X)/r(X))_#(r(X) nu) - r(A) delta_(m(A)/r(A)).

By identifying S with the sphere pair, Jensen is sigma(f). Its constant moment sigma(1) is the graph-area excess E r(X)-r(A)>=0. The following equivalence holds for any such finite sigma (in fact any finite signed angular measure, with the positivity condition implying sigma(1)>=0):

(a) sigma(f)>=0 for all continuous signed angular data whose homogeneous extensions are line-convex on C.

(b) There exists one nonnegative measure mu on K such that
    sigma(f)=integral L f dmu for every smooth angular f,
    mu(K)=sigma(1).

Here L for smooth functions means f plus the second derivative along the simultaneous unit great circle in the two sphere coordinates. Its polynomial expression is in Section 5.

For necessity, consider the linear functional on the subspace of C(K) consisting of L f:
    T(L f)=sigma(f).
If L f=0, both f and -f have line-convex extensions, so sigma(f)=0. Thus T is well-defined. It is positive on nonnegative elements by the curvature criterion (including the great-circle proof of the through-zero condition). Since L 1=1, it is bounded with norm T(1)=sigma(1), as seen by applying positivity to ||L f||_infty +/- L f. Hahn-Banach extends it with the same norm; this extension is positive, since it has the same value on the constant 1 as its norm. Riesz representation gives mu and the exact mass. For sufficiency apply the identity to smooth line-convex tests and then use the positivity-preserving angular polynomial averaging from Section 4 for continuous signed tests. No extra consistency or tail moment bound is needed.

Finite-degree polynomial moment feasibility at every degree suffices for (b): the constant fixes the mass, compactness gives a weak-* subsequence, and C^2 density via the rotation averaging extends the identity to all smooth f. For each fixed degree Caratheodory's theorem in the moment vector space bounds the number of positive atoms by the number of polynomial basis functions (constant included); all atom constraints are polynomial on K. At rational periodic PL input, sigma(P) is algebraic for rational P. Consequently finite-degree feasibility is an exact semialgebraic question. With the degree selected from Section 5, feasibility already certifies the uniform finite-accuracy Jensen statement for the normalized nonnegative cone for that law.

The entire unrestricted Morrey problem is equivalent to universal feasibility of (b) for actual compatible laws, by Theorem A and the fact that every graph energy induced by a signed line-convex Phi is globally RC. This does NOT assume that any law satisfying merely the bivector mean identity admits a positive measure. Indeed that false stronger statement would force polyconvexity. The prior matrix-space stress route remains useful, but this version puts the entire unrestricted integrand domain and tangent variables on one fixed compact algebraic manifold; no homogeneity in the original X or radial truncation is needed.

## 7. Graph-coordinate changes and the new geometric gate

An invertible real 4x4 map with 2x2 blocks B,C,D,E takes graph coordinates (x,u) to (y,v)=(Bx+Cu,Dx+Eu). On the chart where B+CX is invertible put

    T(X)=(D+EX)(B+CX)^(-1),    j(X)=det(B+CX).

Its induced exterior-square map satisfies
    Lambda^2 P m(X)=j(X) m(T(X)).

It preserves simple lines exactly. If j>0 and the domain map y(x) is a globally invertible affine-plus-periodic (or affine-boundary) map, then area change of variables identifies the Jensen gap for the transformed integrand j F_Phi(T(X)) with the corresponding integral gap in the new chart (up to the positive cell-area factor). One sufficient condition for smooth compactly supported perturbations is invertibility with det(B+CA)>0 and ||(B+CA)^(-1) C Dphi||op<1 uniformly: after applying the inverse base map the domain change is identity plus a contraction in the Lipschitz seminorm, hence a global diffeomorphism. This is a genuine compatible-law transfer, unlike conditioning by arbitrary functions of the gradient.

However, a general graph projection can fold or have a singular derivative. Do not apply the inverse/area change of variables as if such a chart were globally injective. Line convexity of the parametric extension of a known QC integrand in one graph chart does NOT prove QC in other charts with folds. This is the new geometric difficulty. A universal argument using oriented surfaces, their slices or graph changes must provide a positive curvature stress for all actual graph laws or an exact progress operation, not merely exploit the identity E m(X)=m(A). The compact algebraic formulation gives a concrete common target for that argument.

## 8. Verification and status

The companion symbolic check verifies the graph/Hodge identities, six polynomial curvature Taylor controls, spherical-kernel normalization and squared displacement, and the flat-kernel identities used in the companion contact note. It was run locally with Python/SymPy. The exact extension, line-convexity preservation, uniform approximation, duality and all-graph equivalence are analytic proofs. No solver enumerated the huge finite families or proved universal stress feasibility. No local Lean build, publication-priority claim or unrestricted resolution. The original target remains open.

The basic graph bivector and change-of-chart geometry are standard exterior algebra, and this note does not claim novelty of those constructions. The specific exact compactification-plus-positive-polynomial-averaging reduction was not found in a brief source/ledger check; no exhaustive priority search is claimed. Earlier [homogeneous uniform cone](IWANIEC_MORREY_HOMOGENEOUS_UNIFORM_CONE.md), [angular curvature stress](IWANIEC_MORREY_ANGULAR_CURVATURE_STRESS.md) and [global certificate](GLOBAL_CERTIFICATES.md) notes are related but use matrix homogeneity or a matrix-ball polynomial hierarchy. This proof addresses arbitrary matrix energies without either symmetry or homogeneity.
