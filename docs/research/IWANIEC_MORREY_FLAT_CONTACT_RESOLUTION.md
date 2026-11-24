# Close the anisotropic flat-region blow-up, and transfer the original flat example through a genuine inverse

24 November 2026. This note resolves a specific hard example from the fresh-eye ledger, not a new main program of special integrands. It uses the already verified truncated determinant and an exact limiting argument. The original nonhomogeneous flat example is proved QC at all bases with |delta(A)|<=1 and for smooth globally invertible orientation-preserving/reversing tests in the remaining orientation sector. Full arbitrary-gradient QC of the original E is still OPEN. The unrestricted Morrey problem is OPEN. No new Lean proof or priority claim.

## 1. The vector contact inequality supplied by a translated kernel

Use s=operator norm, d=det and delta=d/s (zero at zero). From the formally established QC truncated determinant L, the functions

    K_r^-(Y)=r^2 L(Y/r)-det Y=(s(Y)-r)_+(r-delta(Y))

are globally QC for every r>0. Let l<=m be the ordered eigenvalues of sym X. On each fixed bounded set of X, as r->infinity,

    s(X-rI)=r-l+O(1/r),
    delta(X-rI)=r-m+O(1/r).

The signed smaller singular value is positive for r>||X||op, since the path -rI+tX is nonsingular. For the expansions, use (X-rI)^T(X-rI)=r^2 I-2r sym X+X^T X, the eigenvalue perturbation bound by ||X||op^2 and the Taylor expansion of the square root. All error estimates are uniform on bounded sets, including repeated eigenvalues.

Consequently

    G(X)=(-l)_+ m = lim_(r->infinity) K_r^-(X-rI)

locally uniformly. Every translated kernel is QC, so G is globally QC, by passing to the limit on bounded gradient tests. This is the same homogeneous detector already derived in [UNRESTRICTED_CONDITIONAL_GATE, Section 3.2](IWANIEC_MORREY_UNRESTRICTED_CONDITIONAL_GATE.md). Its use below for the flat-region example is new within the present ledger; do not count the detector itself as a new theorem.

Write X=S+W, S=sym X, W skew, and W=[[0,-w],[w,0]]. Then det X=det S+w^2. If sym A is positive semidefinite, G(A)=0, and the QC inequality gives

    integral_{sym X >= 0} det(sym X) + integral w^2
         >= det A

for every actual periodic gradient X=A+Dphi. Indeed G=-det(sym X) off the positive semidefinite cone and is zero on it. For symmetric A the right side is det(sym A); for nonsymmetric A the displayed formula is still correct with det A (the mean skew contributes to the integral). This is a vector-valued contact-mass inequality with an explicit skew-square term. When X is a Hessian field, skew vanishes and this includes the scalar contact-mass conclusion. It does not assert the stronger inequality without skew for general vector maps.

## 2. Complete all-base QC of the homogeneous anisotropic example E2

The earlier [flat-region note, Section 6](IWANIEC_MORREY_FLAT_REGION.md) defines

    E2(X)=0 if l>=0;
           l^2/2-l m if l<0.

Its global vector-valued quasiconvexity was explicitly left open there. But the exact identity

    E2(X)=G(X)+ (1/2)((-lambda_min(sym X))_+)^2

settles it. The second summand is convex, because the least eigenvalue of a symmetric matrix is concave, negation and positive part give a nonnegative convex function, and squaring is convex and increasing on the nonnegative half-line. Therefore E2 is QC on real 2x2 matrices at every base for arbitrary vector-valued tests. The previous non-PC result at I is unaffected; the touching QC minorant arises through the local-uniform closure not covered by the previous flat-support no-go. No new search or contact-set regularity assumption is necessary.

## 3. Original E: exact convex supports throughout the central sector

Recall the finite isotropic E in the old note:
    E=0 on delta>=1,
    E=(1-delta)(s-(1+delta)/2) on |delta|<=1,
    E=-2d on delta<=-1.
In particular everywhere
    E+d+1/2=max(s,|d|)+ (1/2) min(delta^2,1).

Put t=|delta| and define the convex Huber-type profile
    h(t)=t^2/2 for 0<=t<=1, h(t)=t-1/2 for t>=1.

The matrix function C(X)=s+h(t) is convex: h(t)=sup_{0<=k<=1}(kt-k^2/2), and s+kt=(1-k)||X||op+k||X||_* (nuclear norm), a convex function for each k. On t<=1, C-d-1/2 equals E exactly. On t>=1, the inequality C<=|d|+1/2 is exactly (s-1)(t-1)>=0. Hence C-d-1/2 is a global PC (in fact convex plus a determinant) minorant touching E throughout the entire central sector, not just its boundary. Jensen is proved at every base with |delta(A)|<=1 for arbitrary actual planar gradients, including sign-changing determinants.

## 4. Entire remaining sector for genuine orientation-preserving inverse tests

On GL^+(2), t=delta>0. The inverse singular values are 1/t>=1/s. A direct calculation gives the exact identity

    E(X)=d(X) K_1^-(X^(-1)) + (1/2)(1-t)_+^2.

In fact d K_1^-(X^(-1))=(s-1)(1-t)_+; adding the square gives the central formula, and both terms vanish for t>=1. For a base A with delta(A)>=1, let u(x)=Ax+phi(x) be a smooth affine-plus-periodic global diffeomorphism with positive Jacobian. Then v=u^(-1) has affine base A^(-1) and a perturbation periodic in the A lattice. Changing variables gives

    integral_Q d(Du) K_1^-(Du^(-1) as a matrix inverse)
      = integral_(A Q) K_1^-(Dv)
      >= det A K_1^-(A^(-1))=0.

The integral on a fundamental cell may use u(Q) rather than A Q, since v's gradient is periodic on the target lattice. The same proof applies to smooth affine-boundary global diffeomorphisms. The square term is nonnegative. This proves Jensen at every expansive base in GL+ for the stated test class. A smooth periodic map with positive Jacobian everywhere and positive affine determinant is such a diffeomorphism: it induces a degree-one local diffeomorphism of the two tori, hence a one-sheeted covering; equivalently use properness on R^2 and the local inverse. The compact support perturbation case follows similarly from properness and degree.

For an orientation-reversing base and a negative-Jacobian diffeomorphism, compose with J=diag(1,-1). The identity E(JX)=E(X)+2 det X holds on all three sectors. Subtract the determinant null Lagrangian to obtain the reflected Jensen theorem. Together with Section 3 this covers all bases for smooth diffeomorphism tests of matching orientation.

**Important open case:** at expansive bases, an arbitrary gradient can change determinant sign, be singular or fold. The inverse need not be a single gradient map. Do not use this proof on arbitrary tests by simply changing variables on each inverse branch; neither the global inverse law nor the corresponding Jensen inequality is then available. The exact projective/graph-coordinate framework in [PARAMETRIC_COMPACTIFICATION](IWANIEC_MORREY_PARAMETRIC_COMPACTIFICATION.md) shows precisely where chart folding enters. A universal graph-coordinate method must handle it.

One useful explicit reduced candidate is H(X)=1 when delta>=1, and 2|z|-det X otherwise. It is the continuous graph-swap extension of L described by the positive-chart perspective aL(L(xi)/a): on the whole decomposable cone use b if a>=s(L(xi)), a>0, and 2|z(L(xi))|-a elsewhere. At the interface the values coincide by the Plucker identity; near nonzero points of a=0 only the exterior formula is used (the interior requires |b|<=a). Restrictions to simple lines are convex on the chart and outside by the convex exterior formula, glue continuously and have the appropriate slope ordering (the known RC L supplies convexity on the positive chart; at a=0 there is a neighbourhood of exterior points; lines through zero have nonnegative sum of opposite values since b>=-a in the interior). Swapping the two graph planes induces H, hence H is globally RC. Pointwise E+1>=H with equality on the expansive sector: in |delta|<=1 the difference is (1-delta)^2/2; in delta<=-1 it is 1-delta-s(1+delta)>=0. Thus proving QC of this graph-swapped L on arbitrary gradient tests would suffice for full E. But the original QC of L in its original chart does not establish it when the chart change folds. We do not assert this missing implication or that H is non-QC.

## 5. Scope and evidence

The all-base E2 closure and central-sector E support follow from explicit pointwise identities and the verified L. The orientation-preserving E theorem uses genuine global inverse compatibility, not an abstract minor-compatible law. The algebra check in the companion [parametric note](IWANIEC_MORREY_PARAMETRIC_COMPACTIFICATION.md) was actually executed. These are hand arguments, not newly Lean-verified statements. No full E or unrestricted Morrey proof. This closes the prior E2 benchmark and provides a concrete folding test for the general graph-coordinate approach; do not resume the subclass ladder.
