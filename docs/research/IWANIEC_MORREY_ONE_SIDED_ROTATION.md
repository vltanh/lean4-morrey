# Removing one entire rotation symmetry: the signed degree-two frame-indifferent theorem

24 November 2026. **Complete hand proof for arbitrary finite-valued
positively 2-homogeneous rank-one-convex integrands on real 2x2 matrices
with LEFT SO(2) invariance alone.** Right invariance is not assumed.
The conclusion is polyconvexity, with a compact representation by
one-column-square plus determinant supports. The integrand may take
negative values. No smoothness or polynomial assumption is needed.

There is also a global degree-one real-spectrum supporting theorem
for arbitrary anisotropic integrands, and a complete degree-one
convexity theorem under LEFT O(2) invariance alone.

These are analytic hand proofs. The accompanying symbolic checks
were executed in the working container. No new Lean theorem,
independent referee review, or publication-priority claim.
The fully anisotropic homogeneous problem remains OPEN; the
one-sided theorem removes right isotropy, not frame indifference.
This is a natural symmetry gate rather than an enumeration of
individual angular functions. The full signed bi-SO(2) homogeneous
theorem is already formally verified on main at 17fd1c3.

## 1. Complete signed degree-two theorem with only left rotations

**Theorem A.** Let F be finite-valued on R^(2x2). The following
are equivalent:

(i) F is positively 2-homogeneous, globally rank-one convex,
and F(QX)=F(X) for every Q in SO(2).

(ii) There is a nonempty compact set T in R² x R such that

$$
\boxed{
 F(X)=\max_{(v,c)\in T}\left[|Xv|^2+c\det X\right].
}
\tag{1}
$$

In particular F is globally polyconvex and quasiconvex. More
strongly there is a finite convex function Phi on Sym(2) x R,
nondecreasing in the Loewner order of its first argument, with

$$
F(X)=\Phi(X^T X,\det X).
$$

The same theorem holds with right SO(2) invariance alone, by
transposition. It applies also to conjugated left rotation groups
B SO(2) B^(-1) for any invertible B, after changing the target
coordinates. No target or domain isotropy beyond the stated
one-sided rotations is required.

### 1.1 Normalize an arbitrary differentiable invertible base

A finite rank-one-convex function is locally Lipschitz by separate
convexity, hence differentiable almost everywhere. First fix an
invertible differentiability point A. Define G(Y)=F(Y A).
Right multiplication by A preserves rank-one directions, positive
homogeneity, and LEFT rotation invariance. The new base is I.

Write H=G(I), P=DG(I), using the Frobenius contraction for the
gradient. Differentiating G(exp(tJ))=G(I) at t=0, where
J=[[0,-1],[1,0]], gives P:J=0, hence P is symmetric.
Euler's degree-two identity gives

    tr P = 2H.

Choose a unit eigenvector e for the largest eigenvalue lambda1
of P, and an oriented perpendicular unit vector e_perp.
Let lambda2<=lambda1 be the other eigenvalue.

### 1.2 One-column rank-one alignment

Fix ANY Y and write t=|Y e|. If t>0, choose Q in SO(2)
sending Y e to t e. In the oriented basis (e,e_perp),

$$
QY=\begin{pmatrix}t&b\\0&d/t\end{pmatrix},\qquad d=\det Y .
$$

In particular QY and t I share their first column; their difference
has rank at most one. Homogeneity implies G(tI)=t²H and
DG(tI)=tP. The derivative support inequality along this rank-one
segment and left invariance therefore give

$$
\begin{aligned}
G(Y)=G(QY)
 &\ge t^2 H+tP:(QY-tI)\\
 &=t^2(H-\lambda_2)+\lambda_2 d\\
 &=\tfrac{\lambda_1-\lambda_2}{2}|Y e|^2+\lambda_2\det Y.
\end{aligned}
\tag{2}
$$

The off-diagonal entry b drops out since e diagonalizes P.
There is no use of RIGHT rotation invariance of G: expressing
a matrix in the same orthonormal basis on both sides is only
a coordinate choice in the calculation of a Frobenius product.

If t=0 then Y has rank at most one and d=0. Rank-one convexity
on the line through zero and 2-homogeneity imply G(Y)>=0
(for instance compare G(tY) with tG(Y) at 0<t<1).
So (2) still holds.

The coefficient of the column-square is nonnegative, even when
H or either eigenvalue is negative. At Y=I equality holds because
(lambda1+lambda2)/2=H.

Undo the right normalization. For every X,

$$
\boxed{
F(X)\ge
\frac{\lambda_1-\lambda_2}{2}|X A^{-1}e|^2
+\frac{\lambda_2}{\det A}\det X .
}
\tag{3}
$$

Equality holds at A. The eigenvalues in this formula are those
of P=DF(A)A^T, which is symmetric by frame indifference.
This is a global polyconvex touching support at every differentiable
invertible base. It uses just ONE column direction and the determinant.

### 1.3 Compact representation handles all singular and nonsmooth bases

Absorb the nonnegative square coefficient in (3) into a vector v.
For every differentiable invertible A we have a pair (v_A,c_A)
with q_A(X)=|Xv_A|²+c_A det X<=F(X) everywhere and equality at A.

These pairs are uniformly bounded, including as the base approaches
a singular matrix. Let M be the maximum of F on unit Frobenius-norm
rank-one matrices (it is finite and nonnegative). Test q_A at
X=u tensor (v_A/|v_A|) with |u|=1, when v_A!=0. This gives

    |v_A|² <= M.

Test at I and J0=diag(1,-1). Then

    |v_A|²+c_A <= F(I),
    |v_A|²-c_A <= F(J0),

so -F(J0)<=c_A<=F(I). Let T be the closure of all these pairs.
It is nonempty and compact; every pair in T still gives a lower
support by continuity.

Define Phi(S,d)=max_{(v,c) in T}(v^T S v+c d) on ALL symmetric
S and real d. This is a finite continuous convex function (a
maximum over a compact set of linear coefficients), and is
nondecreasing in S in the Loewner order. Equivalently,
Pcal(X,d)=max_T(|Xv|²+c d) is finite and jointly convex in
the matrix and independent determinant variables.

Its restriction to the physical graph is <=F everywhere and
equal to F at every differentiable invertible A. Such points
are dense by local Lipschitz continuity and the fact that
invertible matrices form an open dense set. Continuity gives
equality everywhere. This proves (1) without making any
smoothness or nondegeneracy assumption at the remaining bases.

Conversely every maximum in (1) is positively 2-homogeneous,
left-SO(2)-invariant and polyconvex: each elementary support
is the sum of a convex square and a determinant term, and the
lifted maximum is convex. Thus it is rank-one convex. QED.

### 1.4 The material anisotropy is genuine

For example the function

    F(X)=max(|X e1|²-2 det X, 3|X e2|²+det X)

has the form (1), and is invariant under left rotations.
At X=diag(2,1) and XJ (J the quarter-turn), its values differ.
Thus the theorem is strictly broader than bi-SO(2) invariance.
Taking arbitrary compact T allows nonsmooth and arbitrary
continuous angular dependence compatible with rank-one convexity,
not just quadratic forms.

The theorem also describes the entire rank-one-convex cone at
degree two with one-sided invariance. It is not merely an
estimate for a single example or a bounded test range.

## 2. Consequences at other exponents (precise limits)

For 0<p<1 the verified degree-less-than-one theorem already
applies without any rotational symmetry.

For 1<=p<=2, let F be any finite nonnegative positively
p-homogeneous left-SO(2)-invariant RC energy. The power
F^(2/p) remains rank-one convex by convex increasing
composition, and is positively 2-homogeneous. Theorem A
therefore gives a compact T with the EXACT representation

$$
F(X)=\max_{(v,c)\in T} (|Xv|^2+c\det X)_+^{p/2}.
\tag{4}
$$

Indeed F^(2/p) is nonnegative, so taking the positive part
inside the maximum does not change that maximum; then take
the p/2 power. For signed F the same assertion applies to
its positive part, since max(F,0) remains RC.

For p<2 this proves polyconvexity of the amplified energy
F^(2/p), not of F itself. Individual generators in (4)
need not be rank-one convex, because the outer power is
concave. No implication for the original Jensen inequality
is asserted solely from (4). For p>=2, powers p/2 of the
nonnegative degree-two energies in (1) are QC by convex
increasing composition, but this does NOT classify all
frame-indifferent RC energies at those exponents.

A possible use of (4) is to seek original-energy QC
calibrations exploiting RC of the maximum, rather than
trying another family of powers. No such universal
calibration is yet proved.

## 3. Degree-one supporting theorem for arbitrary anisotropy

There is an additional exact geometric simplification at degree one.
It does not require any symmetry.

### 3.1 Every rank-one-generated plane is an ordinary convexity plane

Let F be finite-valued positively 1-homogeneous and rank-one
convex, and let R1,R2 be independent rank-one matrices.
The function f(x,y)=F(x R1+y R2) is separately convex and
positively 1-homogeneous on R². Such a function is convex.
This classical fact and perspective proof are in
Dacorogna--Maréchal, *The Role of Perspective Functions in
Convexity, Polyconvexity, Rank-One Convexity and Separate
Convexity*, J. Convex Anal. 15 (2008), 271--284,
https://journalofconvexanalysis.com/articles/jca15019/jca15019.pdf.

For completeness, on y>0 it equals y f(x/y,1), the perspective
of a convex one-variable function, hence is convex there.
On y<0 it equals (-y) f(x/(-y),-1), again convex.
Use the analogous perspective in x on x>0 and x<0.
Thus it is locally convex away from the origin and continuous.
Every line avoiding the origin has a convex restriction by
local convexity. Translate lines through the origin slightly
to avoid the origin, then pass to the limit by continuity.
This proves full convexity on the plane.

### 3.2 Real-spectrum support at every invertible base

**Theorem B.** At every invertible A there exists a linear
functional P_A with P_A:A=F(A), such that

$$
\boxed{
F(X)\ge P_A:X
\quad\text{whenever }XA^{-1}
\text{ has only real eigenvalues}.
}
\tag{5}
$$

At a differentiability point A one can take P_A=DF(A).

First suppose A is a differentiability point and
XA^(-1)=S diag(r1,r2) S^(-1) with r1,r2 real and distinct.
Define R_i=S E_ii S^(-1) A. These are independent rank-one
matrices, with A=R1+R2 and X=r1 R1+r2 R2. Section 3.1 gives
ordinary convexity on their plane, so the derivative support
at A holds at X. The repeated-real-eigenvalue case follows
by approximating XA^(-1) with real matrices having distinct
real eigenvalues: in a real Jordan basis perturb its diagonal
entries in opposite directions. Euler's identity gives
DF(A):A=F(A), so the support is linear.

At a nonsmooth invertible A choose differentiability points
A_j tending to A, all invertible. Their gradients are bounded
by a local Lipschitz constant. Extract a converging subsequence
with limit P_A. For any X with strictly positive discriminant
of XA^(-1), the discriminant of XA_j^(-1) is positive for
all sufficiently large j. Pass to the limit in the supporting
inequality. Extend to zero discriminant by the same real
Jordan approximation. Pass to the limit in Euler's identity
to obtain P_A:A=F(A). QED.

**Integral consequence.** Every probability law with mean A
and real spectrum of XA^(-1) almost surely satisfies ordinary
integral Jensen for EVERY finite degree-one RC F, with no
determinant moment needed. In particular if A is symmetric
positive or negative definite and X is symmetric a.e., the
hypothesis holds, since XA^(-1) is similar to a real symmetric
matrix (use the positive square root of A or -A).
This includes arbitrary compatible symmetric gradient fields
at those definite bases.

At rank-deficient bases, the stronger unrestricted supporting
theorem of Kirchheim--Kristensen (2016),
https://arxiv.org/abs/1505.04654, applies. Combining these
facts, at any invertible base a hypothetical degree-one
Jensen violation must use complex-spectrum matrices relative
to that base. At A=I the excluded region is explicitly
    ((X21-X12)/2)^2 > ((X11-X22)/2)^2+((X12+X21)/2)^2.
This follows by expanding (tr X)^2-4 det X. We do not assert
that actual gradient laws avoid this open region.

## 4. Full degree-one convexity theorem under left O(2) invariance

**Theorem C.** Every finite positively 1-homogeneous RC function
on real 2x2 matrices satisfying F(QX)=F(X) for Q in O(2) is
ordinary convex. No right symmetry is assumed.

In fact if only LEFT SO(2) invariance is known, the argument
below proves convexity at any differentiable invertible
base A at which DF(A)A^T is positive semidefinite. The full
orthogonal invariance guarantees this condition at every
differentiable invertible base.

### 4.1 The normalized derivative is positive semidefinite

As in Section 1, normalize an invertible differentiability base
to I by G(Y)=F(YA). Its derivative P=DG(I) is symmetric by
proper rotation invariance. For any unit v consider the
rank-one line Y(t)=I+(t-1) v tensor v. Its restriction of G
is convex. Reflection of the target across v_perp changes
Y(t) to Y(-t), so by left O(2) invariance this restriction
is even. Its derivative at t=1 is therefore nonnegative.
It equals v^T P v. This proves P>=0.

### 4.2 Rotate into a real-spectrum support region

For any Y choose Q in SO(2) maximizing P:QY (compactness).
Stationarity under left multiplication by exp(tJ) gives
P:JQY=0, hence the matrix M P is symmetric, where M=QY.
If P is positive definite, M is similar to the symmetric
matrix P^(-1/2) M P^(1/2). If P has rank one, diagonalize
P in an orthonormal basis; symmetry of MP forces the
(2,1) entry of M to vanish there, so M again has real
eigenvalues. Thus in either case with P!=0, apply Theorem B
at I to M:

    G(Y)=G(QY)>=P:QY>=P:Y.

Equality holds at I by Euler's identity. This is an ordinary
global linear lower support.

If P=0, then G(I)=0. LEFT SO(2) invariance gives G(-Y)=G(Y)
for every Y. Every matrix lies in a plane spanned by two
rank-one matrices (take its two columns, completing a plane
if necessary), so Section 3.1 and evenness give G(Y)>=G(0)=0.
The zero functional is the required support. This also
justifies the claim under proper rotations alone at a
positive-semidefinite normalized derivative.

Undo the normalization. At every differentiable invertible A
we have obtained a global linear support for F. Their
supremum is finite convex, lies below F, and agrees with F
on a dense set; by continuity it agrees everywhere. QED.

The reflection assumption in Theorem C is explicit. For
proper rotations alone P can be indefinite (even for convex
F), so this argument does not close the full left-SO(2)
degree-one gate. We do not infer that an arbitrary indefinite
P admits the same choice of real-spectrum maximizing Q.

## 5. Verification and exact remaining target

The script
[one_sided_exact.py](../../research/audit/one_sided_exact.py)
was actually executed with Python/SymPy. It printed:

    Exact rank-one tangent identity passed.
    Exact normalized minors and lifted convex-extension identities passed.
    Exact real-spectrum, frame-indifference, and generator Hessian identities passed.

The proof of Theorem A uses rank-one alignment and dense
differentiability, not numerical evidence or a finite sample
of profiles. The proof of Theorems B and C uses the elementary
perspective fact and exact matrix geometry.

**Status and next direction:** the complete signed degree-two
frame-indifferent gate is now CLOSED at hand-proof level,
as is the degree-one left-O(2) convexity gate. The signed
bi-SO(2) theorem for every exponent remains Lean verified.
We have not proved the all-base anisotropic degree-two
theorem without frame indifference; the classical
Guerra--Kristensen nonpolyconvex example prevents simply
retaining the PC conclusion there. Nor have we proved
arbitrary left-SO(2) RC=>QC for every other p.
The real-spectrum argument gives a genuine geometric
restriction on a degree-one violation but not a universal
gradient inequality. Use the compact representation and
rank-one alignment to attack the remaining phase dependence,
not a list of fixed polynomials or isolated symmetry examples.
