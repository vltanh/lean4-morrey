# Quantitative compactness and uniform finite angular tests for the entire signed homogeneous cone

24 November 2026. **Scope:** arbitrary finite-valued positively p-homogeneous
rank-one-convex F on real 2x2 matrices, with NO isotropy, sign, angular
regularity, or polynomial restriction, for every p>1.

This is a global advance on the integrand side of the homogeneous anisotropic
gate, not another family of special profiles. We prove:

1. One Gaussian average controls the ENTIRE signed angular profile,
   modulo the determinant at degree two, by explicit constants.
   The proof is based on Gaussian rank-one splitting, not an assumed
   extremal classification or a compactness assertion without bounds.
2. The normalized signed cone has a compact convex base. A strict
   homogeneous Morrey violation can be sought among its extreme points.
3. Combining the uniform normalization with exact homogeneous
   regularization gives a **finite, explicitly bounded collection of
   angular polynomial tests at any prescribed relative accuracy**.
   The same finite collection works for EVERY compatible gradient law,
   regardless of amplitude, support size or oscillation complexity.

The third theorem strengthens the earlier countable rational
counterexample principle: its polynomial degree and coefficient-grid
size are chosen before the integrand or the law is known, for fixed
p and accuracy. It does NOT supply a fixed finite list deciding exact
zero deficit, nor a bound on gradient witnesses. The general homogeneous
anisotropic RC=>QC implication remains OPEN. No new Lean theorem or
publication-priority claim. Algebraic constants were checked in the
actual working container.

For background, Guerra's [Extremal rank-one convex integrands and a
conjecture of Sverak (2019)](https://doi.org/10.1007/s00526-019-1646-5),
Theorem 1.2 and Section 5, uses compact bases for nonnegative rank-one
convex energies on a cube. Our normalization handles the entire signed
homogeneous cone, with explicit constants and a null-Lagrangian quotient.
The homogeneous isotropic theorem remains formally verified on main.

## 1. A single scalar normalization and all rank-one midpoint gaps

Use the Frobenius norm on matrix space R^4. Write Z for a random matrix
whose four entries are independent real Gaussian variables of mean zero
and variance 16. Define the linear functional

    M(F)=E F(Z).

This is finite by homogeneity, local Lipschitz continuity of F, and
Gaussian moments. It is a positive constant depending only on p times
the spherical mean of F on the Frobenius unit sphere. In particular
the functional is continuous in the uniform angular norm at fixed p.

Independent coordinate averaging is rank-one Jensen, so M(F)>=F(0)=0.
Also M(det)=0.

**Lemma 1 (uniform midpoint control).** For every |X|<=2 and rank-one
direction V with |V|<=1,

$$
0\le \Delta_VF(X):=\frac{F(X+V)+F(X-V)}2-F(X)
   \le 4096 M(F).
\tag{1}
$$

Proof. First let |V|=1. Complete V to an orthonormal basis of the four
matrix coordinates consisting of rank-one matrices, by completing the
left and right factors of V to orthonormal bases of R². The law of Z is
unchanged by this orthogonal coordinate change. Let x_i be the coordinates
of X in that basis, with V the first direction. Then |x_i|<=2.

Fix beta=1/8. The scalar N(0,16) law is a mixture of mass beta of the
uniform probability law on [x_i-2,x_i+2] and a nonnegative residual of
mass 1-beta. Indeed throughout [-4,4] the Gaussian density is at least
exp(-1/2)/(4 sqrt(2pi))>1/24>beta/4. The uniform component has mean x_i,
and the residual component has mean -beta x_i/(1-beta).
Make these mixture decompositions independently in all four coordinates.

On every one of the sixteen product components, sequential ordinary
Jensen in the four rank-one coordinates bounds its energy below by
F at its mean. The weighted law of those means is an independent
product of mean-zero scalar variables, so its energy average is
nonnegative by rank-one Jensen at 0.

On the special all-uniform component, which has mass beta^4, refine
the first uniform interval into its two equal halves. Their means
are x_1-1 and x_1+1, and the other three means are unchanged.
Separate Jensen on these refined components gives an additional
lower bound beta^4 Delta_V F(X). Thus M(F)>=beta^4 Delta_V F(X).
For |V|<1, the midpoint gap along the corresponding unit rank-one
direction is nondecreasing in its step length (it is an even convex
function of that length). This proves (1). QED.

This gives a uniform control on every local rank-one curvature
midpoint, not only the integral of one second derivative.

## 2. Quantitative approximation by a rank-one-affine polynomial

Set K=4096 M(F) and let C=[-1,1]^4 be the coordinate cube
with entries (a,b,c,d).

**Lemma 2.** There exist a linear functional L and a real number k
such that

$$
\boxed{
 |F(X)-L:X-k\det X|\le D,\qquad X\in C,\qquad
 D=529 K.
}
\tag{2}
$$

### 2.1 Coordinate interpolation

Let P be the unique multilinear interpolation polynomial of the
sixteen values of F at the vertices of C. For each coordinate i,
let T_i be linear interpolation in that coordinate between -1 and
1, keeping the other coordinates fixed. Convexity in this rank-one
direction gives T_iF>=F.

On an individual coordinate line the chord gap is a nonnegative
concave function on [-1,1], zero at its endpoints. Its maximum is
at most twice its value at zero: if a maximum is at t>=0, express
zero between -1 and t and use concavity; the weight of t is at least
1/2. The case t<0 is the reflection. The center matrix has norm
at most sqrt(3), and the step has norm one. Lemma 1 therefore gives

    0 <= T_i F-F <= 2K.

The T_i commute and are positive contractions in the uniform norm.
Telescoping their composition yields

    0 <= P-F <= 8K  on C.

Thus for any X,V with |X|<=2, V rank one, |V|<=1, X+/-V in C,

    |Delta_V P(X)| <= 9K.

We use this to bound all coefficients of P except its rank-one-affine
part.

### 2.2 Eliminate the inappropriate mixed monomials

Write P=sum_{S subset {a,b,c,d}} u_S product_{i in S} X_i.
For each adjacent pair (i,j) of entries sharing a row or column,
take V=(E_i+E_j)/2, a rank-one direction of norm at most one.
Take X_i=X_j=0 and let the remaining entries be independently +/-1.
Multilinearity gives

    Delta_V P(X) = (1/4) partial_ij P(X).

All relevant matrices are in C. Hence |partial_ij P|<=36K
at each of the four corners in the remaining variables. The
coefficients of this two-variable multilinear derivative are
averages of its corner values with signs +/-1 (Walsh interpolation).
It follows that |u_S|<=36K whenever S contains the adjacent pair.

There are four such pairs, all four triples contain one, and so
does the quadruple. Thus P differs from

    u_empty + L:X + u_ad ad + u_bc bc

by at most 9*36K=324K on C.

Now use the rank-one direction V with all four entries 1/2,
of norm one, at X=0. The exact identity is

    Delta_V P(0)=(sum_{|S|=2} u_S)/4+u_abcd/16.

Its absolute value is <=9K. Using the bounds already proved
on the four adjacent pairs and the quadruple gives

    |u_ad+u_bc| <= 36K+4*36K+9K=189K.

Therefore with k=u_ad, the polynomial
u_empty+L:X+k(ad-bc) differs from P by at most 513K.
The previous interpolation error is at most 8K.
Finally |u_empty|=|P(0)|<=8K since F(0)=0.
Adding these three errors proves (2). QED.

This finite coefficient computation is only used to bound the
normalization of an ARBITRARY integrand. It imposes no polynomial
hypothesis on F.

## 3. Compact base of the entire signed homogeneous cone

Put t=1/2 and, for p>1,

    b_p=(1+t^p)/(t-t^p)>0.

Compare (2) at each unit rank-one coordinate E_i and at t E_i,
using F(tE_i)=t^p F(E_i). Since the determinant is zero at those
points, we obtain

    |L_i| <= b_p D,  hence |L| <= 2 b_p D.

Thus on the unit sphere,

    |F(X)-k det X| <= (1+2b_p)D.

If p is not two, compare (2) at X=I/sqrt(2) and tX.
The determinant of X is 1/2. Homogeneity gives

    |(t^p-t)L:X+(t^p-t²) k det X| <= (1+t^p)D.

The first term has absolute value <=2(1+t^p)D. Therefore

    |k| <= 6(1+t^p)D/|t^p-t²|.

At degree two the determinant is itself a homogeneous null
Lagrangian. Use the canonical linear normalization

    k_*(F)=(F(I)+F(-I)-F(J)-F(-J))/4,
    J=diag(1,-1).

Equation (2) at these four matrices shows |k_*(F)-k|<=D,
since the linear terms cancel and their determinants are +1,+1,-1,-1.

Define the normalized representative F^#=F for p!=2 and
F^#=F-k_*(F)det for p=2. It is still rank-one convex and
p-homogeneous, M(F^#)=M(F), and, for compatible gradients,
its Jensen deficit is identical to that of F.

**Theorem A (explicit signed-cone coercivity).** For every p>1,

$$
\boxed{\|F^\#\|_{L^\infty(S^3)}\le C_p M(F)}
\tag{3}
$$

where one may take

    C_p=529*4096*(1+2 b_p+3(1+t^p)/|t^p-t²|),   p!=2,
    C_2=529*4096*(1+2 b_2+1/2).

These constants are intentionally conservative. No sharpness is
claimed. In particular M(F)=0 implies F=0 when p!=2, and
F=k det when p=2. This proves strict positivity of the normalization
on every nontrivial class modulo the appropriate homogeneous
null Lagrangian. The proof handles signed F directly; it does
not replace F by its positive part.

Consequently the collection B_p of RC p-homogeneous profiles with
M(F)=1 and, at p=2, k_*(F)=0, is a nonempty compact convex subset
of C(S³). Indeed (3) gives a uniform angular bound. Homogeneity
gives |F(X)|<=C_p |X|^p on all matrix space. For |X|<=2,
coordinate convexity bounds each partial derivative, wherever
it exists, in absolute value by 2 C_p 3^p, by comparison of
secant slopes using the unit coordinate steps. Local Lipschitz
regularity of finite RC functions then gives the uniform
Lipschitz bound 4 C_p 3^p on the radius-two ball. For example
one may mollify on the interior and pass to the limit, or use
the essentially bounded weak gradient. Arzela--Ascoli yields
compactness of the profiles, since the defining RC, homogeneity,
and normalization conditions are closed under angular uniform
convergence.

**All-law extremal consequence.** For any fixed probability law
nu with finite p-th moment and mean A, the functional
F -> E_nu F-F(A) is continuous linear on B_p. Its minimum is
attained at an extreme point: the minimizing face is compact
convex and an extreme point of that face is extreme in B_p
(by the Krein--Milman theorem). At p=2 impose the correct
determinant moment to remove the canonical shift from the gap.
Thus any strict homogeneous Morrey violation has an extremal
signed integrand witness in this uniformly bounded Lipschitz
angular class, with no isotropy and no nonnegativity assumption.
This is a normalized-cone reduction, not a classification of
its extremal elements.

## 4. Uniform finite angular approximation at a prescribed accuracy

We now make the previous
[homogeneous regularization theorem](IWANIEC_MORREY_HOMOGENEOUS_REGULARIZATION.md)
quantitative over the entire compact base B_p, rather than
choosing the regularization and degree separately for each F.

**Theorem B.** Fix p>1 and 0<epsilon<=1. There is a finite
collection T_(p,epsilon) of globally RC, positively
p-homogeneous functions of the form

    G(X)=|X|^p P(X/|X|),   X!=0;  G(0)=0,

with P a rational polynomial, such that for every F in B_p
some G in the collection satisfies

$$
\boxed{|F(X)-G(X)|\le\epsilon |X|^p\quad\forall X.}
\tag{4}
$$

All G in the constructed collection may be required to have
strictly positive rank-one Hessian margin on the unit sphere.
There are explicit degree and coefficient bounds depending
ONLY on p and epsilon. When p and epsilon are rational,
the finite collection can be specified by effective bounds
and exact real algebraic rank-one tests. We prove this
constructively; the bounds are large and no enumeration of
the collection is claimed to have been run.

### 4.1 Uniform scale choices

Use the normalized mollifier

    rho(Y)=(30/pi²)(1-|Y|²)_+^4.

It is C³, compactly supported, nonnegative, with integral one
in dimension four. The C³ regularity suffices for all Hessian
and scale-derivative identities below. For k<=3 its partial
derivative L¹ norms are bounded by 5040 (the exact elementary
bounds for orders 0,1,2,3 are 1,120,840,5040).
Indeed the unnormalized polynomial has derivative bounds
8,56,336 on the unit ball at orders one through three, and
the normalization times the ball volume is 15.

Let L=max(1,4 C_p 3^p) be a uniform Lipschitz bound from
Section 3, and put

    c_p=p min(1,p-1)>0,
    b=min(1/4, epsilon/(8L)),
    ell=max(1, 32 L(max(1,p-1)/4+4)/(c_p epsilon)),
    a=b exp(-ell).

For every F in B_p define its scale average

    H(X)=(1/ell) integral_a^b (F*rho_r)(X) dr/r.

It is C³ and rank-one convex. On the unit sphere
|H-F|<=Lb<=epsilon/8. The Euler defect
E=DH:X-pH satisfies exactly

    E=((F*rho_a)-(F*rho_b))/ell.

The estimates in the earlier regularization theorem use only L:
|E|<=L(b-a)/ell and |DE|<=2L/ell there. Hence radial
rehomogenization R_p H(X)=|X|^p H(X/|X|) has rank-one
Hessian >=-c_p epsilon/32 on the unit sphere, by the exact
Hessian defect formula in that theorem. These choices of a,b
are independent of F.

### 4.2 Uniform explicit angular polynomial degree

For the approximation to H, consider the cube [-2,2]^4, and
use u=(X+2)/4 in [0,1]^4. Write h(u)=H(4u-2).
All its partial derivatives of order at most three, including
the function itself, are bounded by

    M_3=5040 C_p 5^p (4/a)^3.

This follows by differentiating the convolution kernels:
on the cube all arguments of F have norm less than 5;
the derivatives of order k cost at most a^(-k) times
the derivative L¹ norm of rho and the factor 4^k from
the variable change. The bound is valid for every F in B_p.

We recall an explicit Bernstein approximation estimate here
to avoid relying only on existence of polynomial approximations.
Let B_n h denote its tensor Bernstein polynomial of degree n
in each of four variables. For n>=2,

$$
\max_{|\alpha|\le2}
\|\partial^\alpha(B_nh-h)\|_\infty\le 7 M_3/\sqrt n .
\tag{5}
$$

To verify (5), differentiate the Bernstein basis. The derivative
of multiorder alpha is the expectation of the forward finite
difference Delta_(1/n)^alpha h(K/n), times the product of
falling factorials (n)_(alpha_i), where the K_i are independent
Bin(n-alpha_i,u_i). The finite difference divided by n^(-|alpha|)
is the average of partial^alpha h at (K+S)/n, with 0<=S_i<=alpha_i,
by the fundamental theorem of calculus. The ratio of falling
factorials to n^|alpha| lies in [1-1/n,1] for |alpha|<=2.
By the derivative bound, partial^alpha h is M_3-Lipschitz in
the l¹ distance. The expected l¹ distance from (K+S)/n to u
is at most 2/sqrt(n)+2|alpha|/n: use the binomial variance
bound n/4, the mean shift alpha_i/n and the displacement
S_i/n. The prefactor error contributes at most M_3/n.
Thus the error is <=M_3(2/sqrt(n)+5/n)<=7M_3/sqrt(n).

Round each Bernstein nodal value h(k/n) to a rational grid
of spacing q>0, with error <=q. Call the resulting polynomial
on physical X-coordinates P_0(X). The rounding errors in
partial derivatives of multiorder <=2 in u-coordinates
are at most 4n²q by the same finite difference formula.
The change back to X can only reduce these partial bounds.

For the radial homogenization of any C² function V at unit X,
write a direction W=w+alpha X, w perpendicular to X. The
identities from the earlier regularization proof give

    D²(R_p V)[W,W]
      =D²V[w,w]+(pV-DV:X)|w|²
          +2alpha(p-1) DV:w+p(p-1)V alpha².

If the uniform bounds on |V|, |DV|, and the Hessian operator norm
are at most eta on the sphere, the absolute value of this
quadratic expression is bounded by C_rad eta |W|² with

    C_rad=max(p+2,p(p-1))+(p-1).

Choose

    eta=min(epsilon/8, c_p epsilon/(32 C_rad)),
    n>=max(2,(56 M_3/eta)^2),
    0<q<=eta/(32 n²), q rational.

By (5) and rounding, every partial derivative of order <=2
of P_0-H is at most eta/4 on [-2,2]^4. Since the space has
dimension four, its gradient norm and Hessian operator
norm are at most eta. Thus the rank-one Hessian of
R_p P_0 is bounded below on the unit sphere by

    -c_p epsilon/32-C_rad eta >= -c_p epsilon/16.

Choose a rational r in [epsilon/8,epsilon/4] and set
P=P_0+r. The Hessian of |X|^p has lower bound c_p on the
unit sphere, so R_p P has rank-one Hessian margin at least
c_p epsilon/16. Global RC follows by homogeneity and
convexity along rank-one lines through zero (the derivative
at zero is zero for p>1). The total angular error is at most
Lb+eta+r<=epsilon/2. This is stronger than (4).

### 4.3 A finite list chosen in advance

All possible rounded Bernstein nodal coefficients lie
in the finite rational grid [-C_p 5^p-q,C_p 5^p+q] intersect
q Z. Choose the integers and rationals in the preceding bounds
once for the chosen p,epsilon. Consider ALL arrays of
(n+1)^4 such coefficients and their resulting P=P_0+r.
Every P has total degree at most 4n. The list is finite;
one can filter it by the strict rank-one Hessian margin test
on unit X and unit rank-one W. The displayed formula for
D²(R_p P) is polynomial in X,W (on the sphere), and hence
for rational p the filter is exactly decidable by real
closed field methods. Bounds involving exponentials and
powers can be rounded outward by computable rational bounds
for rational p,epsilon; no numerical tolerance in the
actual rank-one test is needed.

The approximation just proved ensures that for every F in B_p
at least one member of the filtered list satisfies (4).
This proves Theorem B for every fixed p>1; exact effective
filtering is asserted for rational p. QED.

## 5. Uniform finite relative-gap principle for all laws

For a probability law nu with finite p-th moment and mean A,
write J_nu(F)=E_nu F-F(A). At p=2 assume the determinant
moment identity. This includes every bounded compatible
gradient law. The estimates are independent of the particular
law and do not require its support to be finite.

**Corollary.** For every fixed p>1 and epsilon>0, if ALL members
of the single finite family T_(p,epsilon) satisfy Jensen against
nu at A, then EVERY finite signed positively p-homogeneous
RC F satisfies

$$
\boxed{
J_\nu(F)\ge
-\epsilon M(F)\big(E_\nu|X|^p+|A|^p\big)
\ge -2\epsilon M(F)E_\nu|X|^p .
}
\tag{6}
$$

If M(F)=0 the gap is zero by Theorem A and the determinant
identity when p=2. Otherwise normalize F^#/M(F) to belong
to B_p. Apply (4) and the assumed Jensen for its approximant
G. Multiplying the two error terms by M(F) gives (6);
the last step uses ordinary convex Jensen for |X|^p.
QED.

Equivalently, any strict violation larger than the prescribed
relative error has a witness among finitely many preselected
angular polynomials, with a degree bound independent of F
and the particular gradient law. The finite family controls
the ENTIRE homogeneous integrand cone simultaneously.
There is no restriction of the number of oscillations,
directions, or gradient atoms. This is a uniform finite
tolerance theorem, unlike merely approximating a given
strict counterexample by some polynomial of unknown degree.

**Important limits:** Jensen for the entire finite family
has NOT been proved. The theorem controls the integrand side,
not the gradient-witness side. It supplies neither a finite
cutoff independent of epsilon nor an effective finite
description of all compatible laws. Letting epsilon decrease
to zero without certifying the tests does not prove Morrey.
No attempt is made here to enumerate those very large finite
lists or to label the approximation theorem a solution of
the exact gate. The original question remains open.

## 6. Verification

The script [homogeneous_uniform_cone_exact.py](../../research/audit/homogeneous_uniform_cone_exact.py)
was actually run using Python/SymPy:

    Rank-one midpoint, Walsh coefficient, and Gaussian mixture constants passed.
    Homogeneous normalization constants passed.
    Explicit mollifier derivative and Bernstein constants passed.

The Gaussian comparison, convex compactness, and uniform
approximation proofs above are analytic; the exact checker
only verifies their algebraic constants and identities.
This note provides a general, quantitative reduction of
the full signed angular cone, rather than another restricted
symmetry or exponent theorem. No universal QC proof or new
Lean verification is claimed.
