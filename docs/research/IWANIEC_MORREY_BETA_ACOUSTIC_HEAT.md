# Direct acoustic heat estimate: beta_* >= -1/8

24 November 2026. Return to the original normalized relative margin, without contact-law or chart transformations.

**Main hand theorem.** If a finite continuous planar energy F has global rank-one curvature bounds 0<=m<=M, meaning both F-m|X|²/2 and M|X|²/2-F are rank-one convex, then for every base and bounded periodic compatible gradient,

    J_F(A,u) >= (5m-M)/8 * int |Du|².                     (1)

In particular for globally C11 rank-one convex F with Lip DF<=1,

    -1/8 <= beta_* <= 0.

This applies also to periodic W1,2 tests in the globally C11 class. It is not restricted to homogeneous or isotropic energies, and needs no Iwaniec or finite-mesh theorem as an input. The curvature ratio M/m<=5 is a sufficient condition for QC.

**Ledger correction.** The previously recorded heat-stress exchange theorem, Eq. (15) in [HEAT_STRESS_EXCHANGE](IWANIEC_MORREY_HEAT_STRESS_EXCHANGE.md), already implied beta_* >= -(sqrt(3)-1)/4 (approximately -0.183013), stronger than P13 and P14. The latter radial/determinant-transport bounds are alternative arguments, not improvements on the best known bound in this repository. The new proof improves that earlier heat estimate, rather than merely the recently quoted -58/125. This oversight is corrected here.

**Limit.** No beta_* self-contraction or exact-zero theorem is proved. The scalar trace-budget relaxation of the new proof has an exact two-state equality example; additional spatial/integrand compatibility is needed even to improve this particular relaxation. No genuine negative gradient witness, Lean verification, comprehensive independent audit, or priority claim. The symbolic controls below were executed locally.

## 1. Heat identity and targeted audit

First take F smooth and u smooth periodic on the unit-area flat torus. Let u_s=e^(s Delta)u, X_s=A+Du_s, B_ij=partial_ij u_s (two-component vectors), and g=Delta u_s. Write H=D²F(X_s), with indices ai,bj for target a,b and domain i,j.

The chain rule and one integration by parts give

    -d/ds int F(X_s)
       = -int DF(X_s):Dg
       = int sum_(a,b,i,j) H_(ai,bj) g_a (B_ij)_b.        (2)

The identity is valid at each s, with no sign assertion on its last integrand. Define the signed stress S_(ai,bj)=(g_a(B_ij)_b+g_b(B_ij)_a)/2. By Hessian symmetry and B_ij=B_ji, its contraction with H is exactly the last integrand in (2).

The unweighted spatial identities are

    int |B|² = int |g|²,
    int_0^infinity int |B|² ds = E/2,   E=int |Du|².     (3)

The first is periodic integration by parts componentwise, or Parseval. The second is the usual heat Dirichlet energy identity, including decay of the mean-zero gradient at infinity. Thus J_F(A,u) equals the time-space integral of H:S.

For comparison with the old proof, if n is uniform on the unit circle, v(n)=4 B[n,n]-g, then

    S=E_n sym((g tensor n) tensor (v(n) tensor n)).

The fourth moment of n verifies this identity. The symmetric target block sym(g tensor v) has negative trace mass (|g||v|-g dot v)/2. Its average over time-space and n is bounded by (sqrt(3)-1)E/4 using E_n g dot v=|g|², E_n |v|²=|g|²+4W, and int W=int |g|²/2 where W=sum_ij|B_ij-delta_ij g/2|². The positive and negative parts are sums of rank-one tensor squares. Hence lower/upper rank-one curvature bounds 0,1 give the previously missed universal bound -(sqrt(3)-1)/4. This verifies the specific unweighted estimate of the old note; it is not a comprehensive audit of all its weighted extensions.

## 2. Improved local acoustic estimate

Normalize first to m=0, M=1. At a point with g nonzero rotate target coordinates orthogonally so that g=(G,0), G=|g|. This is a pointwise algebraic choice of basis only; no differentiation of the changing basis or claim that the rotated spatial field is compatible is involved. If g=0, H:S=0 and the desired local estimate holds immediately.

Let A0=(H_(1i,1j))_ij and B0= sym((H_(1i,2j))_ij). For each spatial unit vector n define the acoustic matrix K(n) on the two-dimensional target by

    K(n)_ab = H[a_unit tensor n,b_unit tensor n].

The assumed rank-one sandwich implies 0<=K(n)<=I. In particular, putting a(n)=n^T A0 n and b(n)=n^T B0 n, we have

    0<=a(n)<=1,  a(n)^2+b(n)^2<=a(n),                    (4)

because K(n)^2<=K(n). These are stronger joint constraints than just bounding each entry separately.

Write x=tr A0/2, y=tr B0/2, Ad=A0-xI, Bd=B0-yI. Then 0<=x<=1, and

    |Ad|_F² <= 2 x²,                                     (5)

because A0 is PSD, so each of its two eigenvalues lies in [0,2x]. The following is the important improvement. If n_perp is perpendicular to n, write a'=a(n_perp), b'=b(n_perp). Then a+a'=2x and b+b'=2y. From (4),

    ((b-b')/2)² <= (b²+b'²)/2
                 <= x-(a²+a'²)/2
                 <= x-x².

Since Bd is symmetric and trace-free in two dimensions, its squared Frobenius norm is twice the maximum of |n^T Bd n|² over unit n. Also n^T Bd n=(b-b')/2. Thus

    |Bd|_F² <= 2 x(1-x).

Adding (5) gives the uniform pointwise bound

    |Ad|_F²+|Bd|_F² <= 2x.                              (6)

Decompose the target components of the spatial Hessian as
    B^1=(G/2)I+P, B^2=Q,
where P,Q are trace-free symmetric spatial matrices. Then W=|P|²+|Q|²=|B|²-|g|²/2. The heat contraction (2) at this point is

    H:S=G(A0:B^1+B0:B^2)
       =G²x+G(Ad:P+Bd:Q).

Using (6), Cauchy-Schwarz, and one exact square completion,

    H:S >= G²x-G sqrt(2xW)
         = (G sqrt(x)-sqrt(W/2))²-W/2
         >= -W/2.                                      (7)

This calculation uses only the local rank-one sandwich; no uniform full-Hessian bound and no determinant gauge are needed.

## 3. All-gradient consequence

Integrate (7) in space and heat time. By (3),

    int_0^infinity int W = E/4.

Consequently J_F(A,u)>=-E/8 for rank-one curvature bounds [0,1].

For general bounds [m,M] with M>m, apply this to (F-m|X|²/2)/(M-m). It gives

    J_F >= m E/2 - (M-m) E/8 = (5m-M) E/8.

When M=m the centered residual has zero rank-one curvature; its acoustic matrices vanish, so (2) gives zero residual Jensen gap directly. Alternatively apply the upper bound with M+epsilon and pass to zero. This proves (1).

For a merely finite continuous F with the stated sandwich, convolve in matrix space with a positive smooth compactly supported kernel. The two rank-one bounds persist under convolution (the quadratic changes only by an affine function and constant). Smooth periodic convolution of bounded-gradient u and matrix mollification of F justify the passage to bounded periodic Lipschitz tests: the matrix range stays bounded and F converges locally uniformly; use dominated convergence along a subsequence of the gradients, or continuity and uniform boundedness. For globally C11 F the quadratic-growth Taylor bound also permits W1,2 tests by strong gradient approximation. In particular Lip DF<=1 gives upper rank-one bound 1 and RC gives lower bound 0, proving the stated lower bound for beta_*. F=0 gives the upper bound zero.

One can also apply (1) to the rank-one convex complement M|X|²/2-F. Its curvature sandwich is [0,M-m], so the two-sided estimate is

    (5m-M)/8 <= J_F/E <= (5M-m)/8

when E>0. This is useful even when no common full-Hessian norm is available.

## 4. Sharpness of the particular algebraic relaxation

Do NOT infer that optimizing the pointwise inequalities with just the scalar trace identity will force exact zero. There is an exact equality control for that relaxation.

Use two artificial states of equal weight, in both of which g=(1,0). In row-major Hessian coordinates take

    state 0: H=0, B^1=I/2, B^2=0;
    state 1: H=[[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]],
             B^1=diag(0,1), B^2=[[0,-1/2],[-1/2,0]].

Both local Hessians have operator norm <=1 and rank-one curvature in [0,1]. Indeed state 1 has H²=I, and for R=a tensor n,

    H[R,R]=(a dot n)²,  |R|²-H[R,R]=(a_1 n_2-a_2 n_1)².

The average |B|² and |g|² are both one; the average W is 1/2. The average heat contraction is -1/4, exactly -W_average/2. Since the original gradient energy in the heat identity is twice its integrated Hessian energy, the resulting relative coefficient of this algebraic relaxation is -1/8.

This artificial distribution is NOT realized by an actual heat flow. For instance its second component has g_2=0 identically while B^2 is nonzero on one state, violating even the componentwise integrated identity for a periodic Hessian. Nor is a single integrand with these Hessian assignments constructed. Thus the example establishes only sharpness under the LOCAL acoustic constraints and the GLOBAL SCALAR trace equality. It is not a lower bound on the true beta_*, and does not rule out additional compatible spatial identities.

## 5. Exact-zero issue

I attempted to reuse the signed residual as another actual gradient test at smaller variance, and to use the critical stabilization H=F-2 beta_* |X|²/2 as a stronger input to the same heat inequality. The latter gives precisely the same bound on beta_*; the former still lacks a compatibility-preserving construction. The negative part of a signed rank-one stress is a positive Hessian functional, not a negative Jensen functional of a compatible gradient law. Applying beta_* to it directly would be invalid.

Thus the self-contraction beta_*>=theta beta_* with theta<1 remains unproved. The genuinely new result is a substantially stronger direct uniform bound and curvature-contrast theorem. Further tuning of the same scalar trace-budget relaxation cannot improve its coefficient; an actual spatial mechanism is needed. No claim of near-completion or another conditional formulation being closed.

Executed research/audit/beta_acoustic_exact.py in the working container (SymPy). It verified the symbolic heat contraction and trace decomposition, the perpendicular-direction acoustic identity and square completion, and the exact two-state equality control. SHA-256 86a759858593058872897d21b9019b96bdd2a915114c572881a8b2b0a4d3dad6, Git blob 67c40b48b305e4179033e089a01dd25dbebef15d. These algebraic checks do not independently certify the analytic proof. No new Lean statements or large-scale computations were performed.
