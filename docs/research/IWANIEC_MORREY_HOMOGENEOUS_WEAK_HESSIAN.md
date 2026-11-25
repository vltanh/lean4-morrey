# Weak Hessian structure of the entire homogeneous cone, including nonsmooth extreme points

24 November 2026. The target is arbitrary finite-valued positively
p-homogeneous rank-one-convex integrands on real 2x2 matrices, p>1,
without any rotational or sign assumption.

The preceding [smooth saturated characteristic theorem](IWANIEC_MORREY_SATURATED_CHARACTERISTICS.md)
does not justify differentiating a nonsmooth extremal integrand's
Hessian. Here we establish a weak structure theorem for EVERY member
of the full homogeneous cone, using its homogeneity rather than a
piecewise smoothness assumption.

**Results:**
1. The entire distributional Hessian is a locally finite matrix-valued
   Radon measure. The rank-one curvature measures determine all its
   coefficients except one; differentiating Euler's homogeneous
   identity recovers the missing determinant coefficient.
2. The singular Hessian part is positive semidefinite, has rank-one
   density, and annihilates the radial direction. All nonconvex
   curvature lies in the absolutely continuous part. An integrable
   homogeneous determinant multiplier reduces the whole distributional
   Hessian to a positive semidefinite matrix measure. In particular,
   every nonsmooth integrand is determined by its absolutely continuous
   Hessian via Euler's identity, not by independent singular data.
3. Purely singular rank-one curvature is completely classified:
   only convex piecewise-linear functions of the determinant at p=2,
   and zero at other p>1. A stronger uniform rigidity theorem handles
   sequences with vanishing relative absolutely continuous curvature,
   even when their singular measures might converge to absolutely
   continuous measures.

This is an all-profile weak theorem and a classification of the
purely singular curvature regime, NOT a classification of every
nonsmooth extremal. We have not proved Jensen for arbitrary nonzero
absolutely continuous rank-one-degenerate curvature. The general
homogeneous anisotropic Morrey gate remains OPEN.

The principal external input is Alberti's rank-one theorem for BV
maps, e.g. Corollary 4.6 of G. Alberti, *Rank one property for
derivatives of functions with bounded variation*, Proc. Roy. Soc.
Edinburgh A 123 (1993), 239--274,
https://doi.org/10.1017/S030821050002566X ; see also A. Massaccesi and
D. Vittone, *An elementary proof of the rank-one theorem for BV
functions*, JEMS 21 (2019), 3255--3258,
https://doi.org/10.4171/jems/903 .
The earlier compact-base theorem and the elementary planar
quadratic polyconvexity lemma are used. Analytic hand proofs;
the exact algebra checker was actually run locally. No new Lean
verification, independent review, or novelty clearance.

## 1. Recover the full Hessian from rank-one curvature and Euler's identity

Write V=R^4 for matrix space, with Frobenius inner product and
coordinates (a,b,c,d). Let C be the symmetric linear cofactor
operator
    C(a,b,c,d)=(d,-c,-b,a),
so C²=I, tr C=0, |C|_F=2, and det X=(X:C X)/2.
Use the Frobenius norm also for operators on V when estimating
their total variation.

Let F be finite, continuous, positively p-homogeneous and RC,
p>1. Finite RC functions are locally Lipschitz. Write H=D²F
initially as a symmetric matrix of distributions.

For any rank-one vector R in matrix space, the distribution
R:H R is a nonnegative Radon measure. Indeed, restrict F to
parallel lines in direction R, use ordinary convexity and its
one-dimensional nonnegative second derivative measure, and
integrate in the transverse variables. In particular the four
coordinate second derivatives H_ii are positive measures, and

    tau=tr H=Delta F

is a nonnegative locally finite measure.

### 1.1 Rank-one probes recover nine of the ten Hessian coordinates

Whenever i,j are two different matrix entries sharing a row or
column, e_i+e_j and e_i-e_j are rank-one vectors. Their directional
second derivatives recover H_ij by subtraction and give the
measure inequality

    |H_ij| <= (H_ii+H_jj)/2.

Here |.| denotes the total variation of the signed measure.
The two opposite-entry coefficients H_14 and H_23 are not
individually recovered this way, but their sum is recovered by
the four rank-one probes
    R_(r,s)=(1,s,r,rs), r,s in {-1,1}.
Indeed

    (1/4) sum_(r,s) R_(r,s):H R_(r,s) = tau,
    (1/4) sum_(r,s) rs R_(r,s):H R_(r,s) = 2(H_14+H_23).

Thus |H_14+H_23|<=tau/2. Define the scalar distribution

    T=(H_14-H_23)/2

and the symmetric matrix measure S=H-T C, whose opposite
off-diagonal coefficients all equal (H_14+H_23)/2.
All its entries are now Radon measures absolutely continuous
with respect to tau, and

$$
H=S+TC,\qquad C:S=0,\qquad \operatorname{tr}S=\tau .
\tag{1}
$$

For every rank-one R, R:S R=R:H R as distributions.
Let S=M tau be its Radon--Nikodym representation.
By the countable dense family of rank-one test directions,
for tau-a.e. X the symmetric matrix M(X) has trace one,
is Frobenius-orthogonal to C, and is nonnegative as a
quadratic form on all rank-one vectors.

The planar quadratic lemma says M-lambda C>=0 for some real
lambda. To recall its elementary proof, take the quadratic
q(Y)=Y:M Y/2, which is RC under the stated test. Any pair
U,V of opposite determinant signs has a positive scale t
with det(U-tV)=0, by the intermediate value theorem on the
determinant polynomial. The rank-one segment between U and tV
has a rank-deficient determinant-balanced mean. Rank-one
convexity and quadratic homogeneity then give
q(U)/det U>=q(V)/det V. Thus the interval between the two
orientation ratio extrema contains a multiplier. This gives
q(Y)>=lambda det Y on both orientations and on the rank-one
cone, proving the lemma.

Apply it to M. The PSD matrix M-lambda C has trace one.
Its Frobenius norm is at most one, and M is its orthogonal
projection onto the complement of C. Consequently

$$
\boxed{|S|\le\tau.}\tag{2}
$$

This bound requires no regularity of any determinant multiplier.

### 1.2 Homogeneity recovers the tenth coefficient

The Euler identity X:DF=pF holds almost everywhere by
differentiability and positive homogeneity. Differentiating
in distributions gives

$$
H X=(p-1)DF\,dX ,
\tag{3}
$$

where dX denotes Lebesgue measure in matrix space. Multiplication
by smooth coordinate functions is valid for these distributions.
Contract (3) against C X and use (1):

$$
\boxed{
|X|^2 T=(p-1)(CX:DF)\,dX -(CX)\mathbin{\cdot} S X.
}
\tag{4}
$$

On the punctured space, division by |X|² shows T is a locally
finite signed measure, with

    |T| <= (p-1)|DF|/|X| dX + |S|.

Therefore, by (1), (2) and |C|_F=2,

$$
\boxed{
|D^2F|\le 3\tau+
                 2(p-1)\frac{|DF|}{|X|}\,dX
}
\tag{5}
$$

on the punctured space. The right-hand side is locally finite
also near zero, since tau is already a locally finite positive
measure and DF is locally bounded (the radial weight 1/|X| is
locally integrable in dimension four).

Extend the recovered matrix measure by zero at the origin.
It equals the full distributional Hessian there as well:
for a test function phi multiply by a smooth cutoff that
vanishes on B_epsilon and equals one outside B_(2epsilon).
The omitted part in the distributional pairing with
D_i(D_jF) is bounded by a fixed local bound for |DF| times
    O(epsilon^4)+O(epsilon^(-1) epsilon^4),
which tends to zero. For the extended finite measure,
dominated convergence gives the same limit. Thus there is
no remaining distribution or atom at zero. In particular
(5) holds on the full matrix space.

**Conclusion:** DF is a locally BV map into R^4, with
an explicit total variation bound on its derivative.
This step is where homogeneity is used; merely assuming
finite RC without an Euler identity would not recover T
by this argument.

## 2. Exact weak structure, including singular curvature

Write the Lebesgue decomposition

    H=D²F=Q(X) dX + H^s,

where Q is its locally integrable symmetric absolutely
continuous density.

**Theorem A.** For every finite p-homogeneous RC F, p>1:

(a) H^s is a positive semidefinite matrix-valued measure,
with rank-one density relative to its total variation.
More precisely

    H^s=n(X) tensor n(X) |H^s|,
    |n(X)|=1, n(X):X=0   for |H^s|-a.e. X.

(b) Q is nonnegative on rank-one directions a.e., and there
is lambda in L¹_loc, positively (p-2)-homogeneous a.e., such that

$$
\boxed{D^2F=P+\lambda(X) C\,dX,\qquad P\succeq0.}
\tag{6}
$$

(c) The absolutely continuous Hessian determines the first
derivative and the original integrand:

$$
\boxed{
DF(X)=\frac{Q(X)X}{p-1},\qquad
F(X)=\frac{X:Q(X)X}{p(p-1)}
}\tag{7}
$$

almost everywhere. In particular the map F -> Q is injective
on the entire homogeneous class at fixed p>1.

**Proof of (a).** Alberti's BV rank-one theorem applied to
DF gives rank-one density of its singular derivative H^s.
The density is symmetric because H is a Hessian.
A symmetric rank-one matrix is positive or negative
semidefinite. The trace measure of H is nonnegative
(and its singular part is tr H^s), excluding the negative
case. Thus the asserted unit outer product formula holds.
The singular part of the Euler identity (3) is H^s X=0.
This gives n:X=0, as claimed.

**Proof of (b).** The absolutely continuous parts of the
nonnegative directional Hessian measures give the rank-one
quadratic test for Q, simultaneously on a dense countable
set and hence every rank-one direction at a.e. point.
By the planar quadratic lemma, its feasible determinant
multipliers form a nonempty closed interval. Explicitly,
the lower endpoint is the supremum of Y:QY/(Y:CY) over
negative determinant Y, and the upper endpoint is the
infimum over positive determinant Y. Countable dense
subsets on each open determinant orientation show these
endpoints are measurable. They are finite, and their
interval is contained in [-||Q||_op,||Q||_op], by testing
unit eigenvectors of C with eigenvalues +1 and -1.
Take their midpoint for lambda. It is locally integrable.
Scaling the distributional Hessian shows its ac density
is (p-2)-homogeneous (with the scaling identity understood
a.e. for each positive scale); the interval endpoints
scale in the same way. Define
    P=(Q-lambda C)dX+H^s .
It is PSD by construction and (a), proving (6).

**Proof of (c).** Separate the ac and singular parts of
(3), obtaining QX=(p-1)DF a.e. Then use the scalar Euler
identity X:DF=pF. Local Lipschitz continuity makes F
uniquely determined by its a.e. values. QED.

For a continuous homogeneous integrand, existence of a
distributional representation (6) is also sufficient for
RC: each rank-one directional second derivative is a
nonnegative measure, since R:CR=0, and local convolution
followed by passage to the continuous limit gives convexity
on every rank-one segment.

Thus (6) is an exact weak formulation of the full homogeneous
rank-one convexity condition. In particular the possible
indefinite part of the Hessian is absolutely continuous.
This is NOT the assertion that F is locally convex near
every angular singularity: ac indefinite curvature may
also be present arbitrarily nearby. Nor is it a claim
that every such F is a difference of finite convex functions.

### 2.1 A canonical radial coefficient and residual estimate

For the sequel use a different scalar coefficient

    beta(X)=(p-1) (CX:DF(X))/|X|²,    X!=0.

It is a locally integrable homogeneous function, and is
NOT asserted to belong to the PSD multiplier interval in
(6). It is instead determined by first derivatives alone.

Write tau_a=tr Q>=0 for the density of the ac part of tau,
and S_a for that of S. Taking ac parts in (4) gives
    T_a=beta-(CX):S_a X/|X|².
By (1),(2), |S_a|<=tau_a almost everywhere. Therefore

$$
\boxed{|Q(X)-\beta(X) C|_F\le3\tau_a(X).}\tag{8}
$$

Taking its action on X and using (7), we also get

$$
|(p-1)DF(X)-\beta(X)CX|\le 3 |X|\tau_a(X).
\tag{9}
$$

These inequalities use the actual ac trace, not the total
curvature including its possibly singular concentration.
They supply the compactness argument in the next section.

## 3. Uniform rigidity as the absolutely continuous rank-one curvature vanishes

The positive ac trace tau_a is the sum of the ac coordinate
rank-one curvatures. It vanishes precisely when the ac part
of ALL rank-one curvature vanishes: one direction follows
from the rank-one probes or (2), and the other from the
four coordinates. We study its total mass

    E_ac(F)=int_{|X|<1} tau_a(X) dX .

The unit ball here is in four-dimensional Frobenius matrix
space, not the spatial domain of a test gradient.

**Theorem B (vanishing-ac-curvature compactness).** Fix p>1.
Suppose F_j are finite p-homogeneous RC integrands converging
locally uniformly to F, and E_ac(F_j)->0. Then:
* If p!=2, F=0.
* If p=2, there exist real a,b with a+b>=0 such that
  F(X)=a(det X)_++b(det X)_- everywhere.
  In particular F is globally polyconvex and QC.

This is stronger than classifying functions with identically
zero ac trace. The singular Hessian measures of F_j need not
stay singular in the limit; we do not assume this.

### 3.1 Pass to a PSD residual distribution, not to singularity

By the scaling of a homogeneous Hessian measure,

    int_{B_R} tau_(a,j) = R^(p+2) E_ac(F_j),

for every R>0. Thus tau_(a,j) tends to zero in L¹ on compact
sets. On the punctured space define beta_j as in Section 2.1.
Local uniform convergence gives DF_j -> DF as distributions.
Since multiplication by (p-1) C X / |X|² is smooth away from
zero, beta_j -> beta as distributions there.
From (9),

$$
(p-1)DF=\beta CX
\tag{10}
$$

as distributions and hence almost everywhere. On the other
hand (8) and Theorem A(a) give
    D²F_j-beta_j C dX
      =H_j^s+(Q_j-beta_j C)dX,
a PSD measure plus an error tending to zero in total variation
on compact sets. Test this expression on any constant vector
and nonnegative compactly supported smooth scalar function.
Pass to the distributional limit. We conclude

$$
D^2F-\beta C\,dX\succeq0
\quad\text{on the punctured space}.
\tag{11}
$$

The crucial conclusion is positivity in (11), not singularity.
Thus the argument remains valid when singular Hessian mass
accumulates in full-dimensional sets.

### 3.2 Equation (10) forces determinant dependence

On either open determinant orientation, the gradient of F
is parallel to CX=grad det almost everywhere. In local smooth
coordinates with det as one coordinate, this says that all
other weak first derivatives of F vanish. To justify the
coordinate change, F is locally Lipschitz and the coordinate
map is a smooth local diffeomorphism (CX!=0). Its chain rule
holds a.e. by ordinary Lipschitz differentiation and
change of variables. F is therefore constant on each local
connected determinant fiber patch, by the fundamental
theorem for Sobolev functions and continuity.

The full nonzero determinant fibers are connected. For
positive determinant, use polar decomposition: the SO(2)
factor is connected and the SPD factor can be joined to
sqrt(det X) I at fixed determinant by interpolating its
matrix logarithm. For negative determinant, first apply
a fixed reflection. Hence local constancy implies constancy
on each entire fiber. Positive homogeneity now yields

$$
F(X)=
\begin{cases}
a(\det X)^{p/2},&\det X>0,\\
b(-\det X)^{p/2},&\det X<0.
\end{cases}
\tag{12}
$$

Continuity gives zero on the rank-deficient cone.

### 3.3 The PSD residual forces p=2 or the zero function

On a nonzero determinant orientation write F(X)=h(d), d=det X,
with h the relevant signed coefficient times the indicated
power. Here F is smooth. Equation (10) gives beta=(p-1)h'(d).
Differentiating F gives

    Q=h''(d)(CX tensor CX)+h'(d) C.

The scalar homogeneity identity d h''=(p/2-1)h' implies

$$
Q-\beta C
=h''(d)[(CX)\otimes(CX)-2d C].
\tag{13}
$$

To test (11), take the two vectors
    U=X J,  V=X K,
where J=[[0,-1],[1,0]], K=[[0,1],[1,0]].
Both have zero determinant differential CX:U=CX:V=0,
because tr J=tr K=0. Their determinants are d and -d,
respectively. The quadratic form in brackets in (13)
therefore has value -4d² on U and +4d² on V.
Since d!=0, positivity in (11) implies h''(d)=0.

If p!=2, the exponent p/2 is neither zero nor one.
Consequently (12) has a=b=0. For p=2 the two branches
are linear in the determinant. On the rank-one line
diag(1,t), t real, RC is precisely convexity of the
function a t_++b t_-. Hence a+b>=0. Conversely every
such scalar function of the determinant is polyconvex.
This proves Theorem B. QED.

In particular, apply Theorem B to a constant sequence
to obtain an exact classification of every homogeneous
RC F with E_ac(F)=0:
    p!=2: F=0;
    p=2: F=a det_+ + b det_-, a+b>=0.
There is no smoothness, evenness, sign, or assumption
that the singular part consists only of jump surfaces.
The determinant crease examples have zero ac rank-one
curvature but need not be convex plus one constant
determinant term. The earlier smooth saturated theorem
does not include these nonsmooth profiles.

## 4. Uniform consequences on the whole normalized cone

Use the earlier
[compact signed homogeneous base](IWANIEC_MORREY_HOMOGENEOUS_UNIFORM_CONE.md).
For the Gaussian matrix Z whose entries are independent
N(0,16), put M(F)=E F(Z). At fixed p>1 this is continuous
under uniform angular convergence by homogeneity and the
finite Gaussian p-th moment. The base with M(F)=1 is
compact in C(S³) after, at p=2, imposing the linear
normalization

    k_*(F)=(F(I)+F(-I)-F(J0)-F(-J0))/4=0,
    J0=diag(1,-1).

Write F^# for the representative after this determinant
subtraction. Both M and E_ac are unchanged by subtraction
of a determinant at p=2 (its Hessian is the constant
traceless matrix C). M=0 only for the zero class.

### 4.1 Coercivity of the absolutely continuous trace for p!=2

There is a constant c_p>0, depending only on p, such that
for EVERY signed homogeneous RC F of degree p!=2,

$$
\boxed{E_{\rm ac}(F)\ge c_p M(F).}\tag{14}
$$

Otherwise choose normalized F_j with M(F_j)=1 and
E_ac(F_j)->0. By compactness extract an angular-uniform
convergent subsequence (hence locally uniform by homogeneity).
Its limit has M(F)=1, but Theorem B gives F=0, a contradiction.
Rescaling proves (14). We do not give an explicit numerical
value of c_p; the proof is a compactness argument.

Combined with the previous signed-cone normalization,
this also bounds the uniform angular norm by a constant
times the mass of JUST the ac trace. No positivity of
the original F or smoothness of an extremal is assumed.

### 4.2 Uniform degree-two stability at the determinant crease

At p=2, let

    F_*(X)=|det X| / M(|det|).

This is the unique member of the canonically normalized
base with E_ac=0. Indeed the classification gives
a det_++b det_-, and k_*=0 forces a=b; M=1 fixes a>0.

For EVERY eta>0 there is delta>0 such that, for every
signed finite degree-two RC F with M(F)>0,

$$
E_{\rm ac}(F)\le\delta M(F)
\quad\Longrightarrow\quad
\left\|\frac{F^\#}{M(F)}-F_*\right\|_{C(S^3)}
    \le\eta .
\tag{15}
$$

Proof by contradiction: normalize a violating sequence,
take a compact-base limit, and apply Theorem B with p=2.
The normalizations identify that limit with F_*, which
contradicts the fixed positive uniform distance. QED.

This yields actual uniform control of the original Jensen
deficit near the determinant crease. If X is any compatible
gradient law with mean A and finite second moment, and the
hypothesis of (15) holds, then the polyconvex F_* and the
determinant identity give

    E F(X)-F(A)
      >= -eta M(F)(E|X|²+|A|²).

This is a uniform limiting theorem; it does NOT say that
every F with small positive E_ac is QC. At E_ac=0 the
classification proves the exact unmodified Jensen inequality.

## 5. Scope of the advance and remaining gate

These statements apply to all nonsmooth extreme points
of the normalized homogeneous cone, not just to smooth
ones or to a particular angular partition. They show that
the singular Hessian itself contributes only PSD
curvature, and cannot carry an independent nonconvex
degree of freedom in view of Euler recovery (7).
The only purely singular rank-one-curvature regime is
the determinant crease at degree two. At other degrees
the full normalized cone has a uniform positive amount
of ac rank-one curvature. At degree two, sequences with
negligible ac trace have a uniformly controlled
polyconvex limit.

The previously proved smooth saturation result concerns
the MINIMUM rank-one curvature, not its trace. It would
be invalid to infer from extremality that tau_a=0:
a degenerate Hessian can have positive trace. Likewise
(6) does not say its integrable multiplier lambda is
constant, or that the PSD measure P itself is a Hessian
of a convex function. Subtracting a variable determinant
coefficient is not subtraction of a null Lagrangian.
No global QC of arbitrary nonsmooth saturated profiles
is proved here. The outstanding target remains the
entire homogeneous anisotropic implication, specifically
the absolutely continuous rank-one-degenerate curvature
with a variable determinant multiplier. Do not replace
it by an enumeration of angular singularities.

The exact checker [homogeneous_weak_hessian_exact.py](../../research/audit/homogeneous_weak_hessian_exact.py)
was executed locally with Python/SymPy. Output:

    Exact rank-one probes, cofactor projection, and Euler recovery identities passed.
    Exact determinant-fiber tangent and opposite-sign residual identities passed.
    Homogeneous determinant-power coefficient identity passed.

The analytic distributional arguments and Alberti's
theorem prove the functional statements. No new Lean
verification or general homogeneous Morrey solution.
