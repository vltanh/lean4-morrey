# Removing homogeneity: exact failure of the affine-shell obstacle and a stronger projection theorem

23 November 2026. Hand proofs with an executed exact arithmetic separation
certificate. The target remains arbitrary finite-valued isotropic
rank-one convex integrands on R^(2x2), without homogeneity.
The previously formalized nonnegative homogeneous theorem is the baseline;
the signed homogeneous candidate is under separate audit/formalization.
**Neither the general isotropic theorem nor unrestricted Morrey is solved here.**

The concurrent [row-projection note](IWANIEC_MORREY_NONHOMOG_ROW_PROJECTION.md) also refutes the universal affine-shell obstacle, with a three-spectral-atom witness at an anticonformal base, and derives the projection sign for **every convex C¹ potential** by a scalar diffusion resolvent. The independent witness here is at a rank-one base and uses just four actual matrix atoms. The elementary directional-sign proof below is a simpler alternative in that narrower regime. The main additional positive result is the arbitrary-multiplicity, mixed-minor projection-max construction in Section 3, which also applies with the concurrent note's full convex-potential sign theorem.

There are two results:

1. A four-matrix law satisfies EVERY affine-shell test from
   [NONHOMOG_SHELL_AFFINE](IWANIEC_MORREY_NONHOMOG_SHELL_AFFINE.md)
   but strictly violates Jensen for a known QC isotropic function.
   This refutes the proposed universal support strategy, including
   approximate minorants on a compact set and arbitrary noncontact
   intervals. It is NOT a gradient-law counterexample.
2. A new generalization of the scalar projection argument constructs
   globally QC integrands from arbitrary compact convex constraints on any finite collection of scalar output combinations, and arbitrary polyconvex calibrations on all stacked original/projected rows. The core new analytic fact is a directional convex
   order inequality for the scalar constrained projection, with its
   linearized sign version. This genuinely enlarges the available
   support constructions. Their completeness for isotropic RC
   functions is NOT established.

The formalized analytic input is the pinned lean4-iwaniec commit
972c01272b2a573ae58fb43fac47c97196db2cbb, specifically
[Agazzi.quasiconvex_integrandL](https://github.com/vltanh/lean4-iwaniec/blob/972c01272b2a573ae58fb43fac47c97196db2cbb/Agazzi/Quasiconvex.lean)
and the arbitrary compact convex K version of
[Agazzi.lemma4](https://github.com/vltanh/lean4-iwaniec/blob/972c01272b2a573ae58fb43fac47c97196db2cbb/Agazzi/Proof/ScalarProjection/Main.lean),
with projection existence in ScalarProjection/Existence.lean.
The arguments here use those already formalized results, not a new
assumption about the Iwaniec conjecture. The new arguments themselves
are not yet Lean formalized, independently refereed, or novelty-cleared.

## 1. Exact global obstruction to affine-shell minorants

Use conformal coordinates z,w and write
x=|z|, y=|w|, s=x+y, delta=x-y, D=det X=s delta.
The known QC integrand is
    L(z,w)=x²-y² if x+y<=1, and 2x-1 otherwise.
Define
$$
F(z,w)=\frac{1}{2\pi}\int_0^{2\pi}
       L(z,w+\tfrac12 e^{i\theta})\,d\theta.
\tag{1}
$$
This is globally finite, continuous, isotropic under SO(2)xSO(2),
and QC: every integrand being averaged is a fixed matrix translation
of L, and bounded-gradient tests justify averaging by Fubini.
Invariance follows from invariance of L under independent complex
rotations of z,w and invariance of the circle distribution.
In particular F is globally rank-one convex, with no numerical
Hessian or other RC certificate required.

Take A=diag(1,0), so x_A=y_A=1/2, s_A=1, delta_A=0.
Take the following explicit law nu:

| Matrix | (s,delta) | Mass |
| --- | --- | --- |
| diag(1/2,1/2) | (1/2,1/2) | 4/7 |
| diag(5/4,-5/4) | (5/4,-5/4) | 16/49 |
| diag(3,3) | (3,3) | 1/14 |
| diag(3,-3) | (3,-3) | 3/98 |

The mass is one, E X=A, E det X=0=det A, and E x=E y=1/2.
Thus nu satisfies even the full matrix/determinant moments,
and Jensen for every polyconvex integrand, not just isotropic ones.

### 1.1 All radii, exactly

For e=+/-1 the affine-shell tests are
$$
K_r^e(s,\delta)=(s-r)_+(r+e\delta).
$$
Define g_e(r)=E K_r^e(X)-K_r^e(A).
The following table gives exact quadratic polynomials on the
whole indicated closed intervals. The last column is the
minimum on that interval, including endpoints.

| e | Interval | g_e(r) | Minimum |
| --- | --- | --- | --- |
| -1 | [0,1/2] | 0 | 0 |
| -1 | [1/2,1] | (4r²-4r+1)/7 | 0 |
| -1 | [1,5/4] | (-3r²+3r+1)/7 | 1/112 |
| -1 | [5/4,3] | (-5r²+21r-18)/49 | 0 |
| +1 | [0,1/2] | 0 | 0 |
| +1 | [1/2,1] | (4r²-1)/7 | 0 |
| +1 | [1,5/4] | (-3r²+7r-1)/7 | 3/7 |
| +1 | [5/4,3] | (-5r²+9r+18)/49 | 0 |

At all r>=3 both gaps are identically zero. This verifies the
entire continuous radial parameter range, not a grid approximation.
By the affine-shell representation theorem (preceding note),
nu obeys Jensen for EVERY isotropic RC affine-in-shell integrand.

### 1.2 Strict violation of a known QC test, with elementary exact bounds

For 0<=x<=1 and Y=|w+e^{i theta}/2|, the piecewise formula is
$$
L(x,Y)=2x-1+\big[(1-x)^2-Y^2\big]_+.
\tag{2}
$$
Indeed Y<=1-x is precisely the inner branch, and the difference
between the two expressions is (1-x)^2-Y². For x>1 only
the outer branch occurs.

At the base x=y=1/2, the correction in (2) is
(-1/4-(1/2) cos theta)_+, so direct integration gives
$$
F(A)=\frac{\sqrt3}{4\pi}-\frac1{12}>\frac1{20}.
$$
For the strict lower bound use sqrt(3)>17/10 and pi<22/7;
(17/10)(7/88)-1/12>1/20.

For the first atom F=0, for diag(3,3) F=5, and for
diag(3,-3) F=-1. At diag(5/4,-5/4) the correction to -1 is
$$
\frac{(-13-20\cos\theta)_+}{16}.
$$
It is at most 7/16 and is nonzero only on a set where
cos theta<-13/20<-1/2, of normalized measure less than 1/3.
Its average is therefore at most 7/48. The constant
parts of the four energies cancel exactly:
5/14-3/98-16/49=0. Consequently
$$
\int F\,d\nu\le (16/49)(7/48)=1/21,
\qquad
\boxed{F(A)-\int F\,d\nu>1/420.}
\tag{3}
$$
No numerical evaluation of the trigonometric integral is needed.

### 1.3 What is refuted, and what is not

The whole compact obstacle statement in Section 4 of
NONHOMOG_SHELL_AFFINE is false for arbitrary isotropic RC f.
In particular even approximate affine-shell minorants on the
operator-norm ball of radius R=4 cannot achieve contact at A
for this F. If G<=F on the ball is globally RC and affine
in each shell, then
$$
G(A)\le\int G\,d\nu\le\int F\,d\nu<F(A)-1/420.
$$
The same applies to nonnegative sums, arbitrary finite pointwise
maxima, and locally uniform limits of such integrands and
arbitrary polyconvex integrands: Jensen against this fixed law
is preserved by all these operations. This rules out the
universal contact-path program even if noncontact intervals
are allowed. Merely solving its differential inclusion with
more numerical resolution cannot remove the obstruction.

Moreover, **conditional on the signed homogeneous characteristic
proof under separate audit**, its touching minorants at all
nonzero bases (in particular A here) are affine in each shell.
The nonnegative p>=2 result is polyconvex, and p<=1 and p=2
also obey Jensen against nu. Thus assuming the signed proof
is correct, the law also passes Jensen for ALL homogeneous
isotropic RC integrands, every exponent and every sign.
Simple addition, supremum and locally uniform limits of those
homogeneous results together with the affine-shell and
polyconvex classes cannot remove homogeneity in general.
This is a structural obstruction, not an exponent ladder.

Since the separating F in (1) is already QC, nu cannot be an
actual gradient Young measure. We have not found a counterexample
to general isotropic Morrey. The representation theorem for
the affine-shell class itself remains valid.

## 2. Stronger analytic ingredient: directional convex order of scalar projections

Let K be a nonempty compact convex subset of R² and p in K.
On the unit torus let C(K,p) be the convex set of periodic
Lipschitz scalar functions xi with p+D xi in K almost everywhere.
Let P denote the L² metric projection onto this set. Existence,
uniqueness as an L² projection, and the following selection
property are supplied by the scalar projection theorem in the
formalized Agazzi dependency:
if zeta=P eta, a=p+D eta, z=p+D zeta, then
$$
z\in K,\qquad z=a\text{ or }z\in\partial K\quad\text{a.e.}
\tag{4}
$$
The standard statement also gives E z·(a-z)>=0.
We derive a more flexible nonlinear sign inequality.

**Theorem A (directional convex order and sign).**
For any v in R², any Lipschitz eta as above, and every
continuous convex function phi:R->R,
$$
\int\phi(v\cdot z)\le\int\phi(v\cdot a).
\tag{5}
$$
If phi is C¹, then
$$
\boxed{\int \phi'(v\cdot z)\,v\cdot(a-z)\ge0.}
\tag{6}
$$
There is no restriction on the sizes of eta or the
convex function, since all relevant gradients are bounded.

**Proof.** The set C(K,p) is closed under pointwise min/max:
the a.e. gradients of these Lipschitz functions agree with
one of the two original gradients (including the equality
set by the zero-set derivative property). It is invariant
under addition of constants and translations of the torus.

The projection preserves order. In fact, if eta1<=eta2,
let zeta_i=P eta_i. Replacing the two projections by
min(zeta1,zeta2), max(zeta1,zeta2) respectively gives two
admissible competitors. On the crossing set zeta1>zeta2,
the change in the sum of their squared L² errors is
2(eta1-eta2)(zeta1-zeta2)<=0, and elsewhere is zero.
Minimality and uniqueness force the competitors to equal
the original projections, hence zeta1<=zeta2 a.e.
Also P preserves integrals, by minimization over additive
constants. Uniqueness gives translation equivariance and
P(eta+c)=P eta+c.

For any real t, order preservation gives
$$
\max(P\eta_1,P\eta_2+t)\le P\max(\eta_1,\eta_2+t).
$$
Subtract P eta2+t and integrate, using preservation of
integrals:
$$
\int(P\eta_1-P\eta_2-t)_+\le
\int(\eta_1-\eta_2-t)_+.
\tag{7}
$$
The two differences have the same mean. Any continuous
convex function on a compact interval is a uniform limit of
convex polygonal functions, and each polygonal convex
function is affine plus a nonnegative sum of these hinges.
Thus (7) gives convex order of the differences.

Use eta1(x)=eta(x+h v)+h p·v and eta2=eta, h>0.
Translation and constant equivariance identify the projected
difference. Apply convex order to the difference divided
by h, then let h down to zero. Directional derivatives
of the Lipschitz maps exist almost everywhere and the
difference quotients are uniformly bounded. Dominated
convergence proves (5).

For the sign let eta_lambda=zeta+lambda(eta-zeta).
The metric projection of eta_lambda is still zeta for
every lambda>=0, by the normal-cone variational inequality
of the projection onto a closed convex set. Apply (5)
to eta_lambda and differentiate its right side at lambda=0
from above. C¹ continuity on the bounded range justifies
differentiating the integral. This gives (6). QED.

In particular let psi(u)=sum_{j=1}^N phi_j(v_j·u) for ANY
finite collection of vectors v_j and convex C¹ functions
phi_j. The gradient sign in (6) sums to
$$
\int \nabla\psi(z)\cdot(a-z)\ge0.
\tag{8}
$$
The same holds for a positive integral of such ridge
functions with locally dominated gradient. This includes
every positive multiple of |u|^q, q>1, by averaging
|v·u|^q on the unit circle, as well as arbitrary positive
mixtures of these powers or arbitrary one-dimensional
convex costs. This is not a claim of the sign for every
multivariate convex psi; directional convex order alone
does not imply that stronger assertion.

## 3. Arbitrary-multiplicity projection-max theorem with mixed minors

Here we combine the independently proved directional sign above
with the stronger full convex-potential sign in
[ROW_PROJECTION](IWANIEC_MORREY_NONHOMOG_ROW_PROJECTION.md),
Theorem B. The following construction is global and genuinely
nonhomogeneous. It permits arbitrary many scalar constraints,
not merely one or both original rows.

Fix any finite number N of linear functionals l_i on R² and
any vectors b_i in R². For A in R^(2x2) define the row vectors
a_i(A)=l_i A+b_i. These are gradients of affine-plus-periodic
scalar functions whenever A is a compatible matrix gradient.
Choose arbitrary nonempty compact convex sets K_i in R².
Put
$$
Z_i(a)=\partial K_i\ \cup\
             \big(\{a\}\text{ if }a\in K_i\big).
$$
An unconstrained row is allowed by setting Z_i(a)={a}.
Choose convex C¹ functions psi_i on R², with psi_i=0 for
unconstrained rows. The full sign theorem for these potentials
is proved in the concurrent note by scalar resolvents. Using
only the independent proof of Section 2, the following theorem
already works for the subclass of convex ridge-sum potentials.

Let P_0 be ANY finite continuous polyconvex integrand on
R^((2+N)x2), writing its arguments as the stacked rows of
the actual A and auxiliary Z=(z_1,...,z_N).

**Theorem B (projection-max closure).** The function
$$
\boxed{
H(A)=\max_{z_i\in Z_i(a_i(A)),\ 1\le i\le N}
\left[
P_0\!\left(\begin{bmatrix} A\\ Z\end{bmatrix}\right)
 +\sum_{i=1}^N\nabla\psi_i(z_i)\cdot(a_i(A)-z_i)
\right]}
\tag{9}
$$
is finite, continuous, and globally quasiconvex.
In particular the calibration can use all mixed two-row
minors of the original and projected rows, not merely
the determinant of a single replacement matrix. The
functionals l_i need not be independent or coordinate
projections; N is arbitrary, with no bound in the theorem.

**Proof.** The finite maximum exists by compactness of
the choice sets and continuity of the objective. The sets
Z_i(a) vary continuously in the Hausdorff metric: a
moving interior choice merges into the fixed boundary
at the interface, and outside only the fixed boundary
remains. The unconstrained choices are singletons.
Local boundedness of all candidates and uniform continuity
of the objective on compacts prove continuity of H.
If K_i has empty interior its boundary is the whole
set, so the claim is immediate for that choice set.

Fix ANY base A_0 and choose a maximizer Z_0 in (9).
For every periodic Lipschitz test A(x)=A_0+D phi(x),
choose compatible auxiliary rows as follows.

* When a chosen row z_i^0 is a boundary point of K_i,
  it can be kept constant, since it is admissible for
  every actual row.
* Otherwise a chosen constrained row must equal a_i(A_0)
  in K_i. Use the scalar projection of the periodic
  potential l_i phi onto C(K_i,a_i(A_0)). Its projected
  gradient z_i(x) has the same row mean, and by (4)
  belongs to Z_i(a_i(A(x))) almost everywhere.
* For an unconstrained row simply use the actual row.

In all cases Z(x) is the gradient of an affine-plus-periodic
Lipschitz map with mean Z_0. The stacked matrix [A(x);Z(x)]
is therefore an actual (2+N)x2 gradient with the stacked mean.
All its minors (including the mixed two-row minors)
have the corresponding affine means by the null-Lagrangian
identity. Polyconvex Jensen gives
$$
\int P_0([A(x);Z(x)])\ge P_0([A_0;Z_0]).
$$
This is valid without any vector-valued projection assertion:
we projected independent scalar potentials and then stacked
them; they need not be linear combinations of a single
projected vector map.

For a fixed boundary row, its correction term in (9)
is affine in the actual A, so its integral equals its
base value. For a projected row the base correction is
zero, and its integral is nonnegative by the convex
projection sign theorem (or by (8) for ridge sums).
For an unconstrained row the correction is identically zero.
By construction all auxiliary rows are admissible
pointwise in (9), so integration gives
$$
\int H(A_0+D\phi)\ge
P_0([A_0;Z_0])+
\sum_i\nabla\psi_i(z_i^0)\cdot(a_i(A_0)-z_i^0)
=H(A_0).
$$
All functions are continuous or measurable and bounded
on the particular test range. This proves QC at every
base. QED.

In fact the proof works if P_0 is any known finite
continuous quasiconvex integrand on the stacked matrix
space; polyconvexity is a readily verifiable sufficient
hypothesis. No unproved higher-dimensional RC=>QC
implication has been invoked.

### 3.1 Relation to L and the isotropic problem

Take N=1, a_1(A)=the first row, K_1 the unit disk,
P_0([A;z])=det(z,A^2) (a mixed minor), and psi_1(z)=|z|²/2.
The boundary expression in (9) is
max_{|z|=1}(det(z,A^2)+z·(A^1-z))=2|conformalPart(A)|-1.
The other candidate is det A when the first row belongs
to the disk. If sigma>1, then delta<=sigma and
det A-(2x-1)=(sigma-1)(delta-1). This difference can
be positive only if delta>1. But in that case every row
has norm at least the smaller singular value delta>1,
so the interior candidate is unavailable. If sigma<=1,
the first row belongs to the disk and the difference is
nonnegative. This recovers L exactly.

The concurrent row theorem allows arbitrary K and convex
psi in this one-row mixed-minor construction. Theorem B
further permits unrestricted finite collections of scalar
output combinations, independent projection constraints,
and arbitrary polyconvex dependence on all stacked rows
and minors. The choices of projected auxiliaries can
depend on the prescribed base through a maximizing tuple.
For instance projecting both rows simultaneously yields
a family whose calibration can include det(z_1,z_2),
det(A^1,z_2), det(z_1,A^2), and convex functions of
their values, not just a linear determinant of one
row replacement. One may also use a convex potential
of the projected row inside the calibration itself.

For use against an isotropic F, an individual generator
(9) need not be isotropic. One can take rotational
averages or suprema over left/right proper rotations,
and positive sums or locally uniform limits, preserving QC.
If H<=F on a rotation-invariant test ball and H touches
F at a prescribed base, its rotational supremum still
lies below F and still touches. Matrix translations
and invertible left/right transforms preserve QC.
Thus the explicit separating F in Section 1 belongs
to this enlarged construction class, whereas it fails
the entire old affine-shell class.

**The next mathematical question is support completeness
for a genuinely two-variable isotropic profile using
these spatially justified calibration choices.**
A construction must supply a lower support at every
base on every bounded gradient range, or give another
direct all-gradient inequality. Neither separate
convexity in signed singular values nor the local
quadratic rank-one condition is a proof of such
completeness. The result (9) uses actual gradient
compatibility, not an abstract minor-law approximation.

We do not propose enumerating shapes of K_i, the number
of output combinations, or degrees of P_0. The exact
no-go in Section 1 requires a qualitative change from
the old one-variable obstacle. The projection theorem
supplies that change and a flexible analytic construction
available for a universal proof. It does not by itself
establish that every isotropic RC F has these minorants.

## 4. Verification and disposition

The checker
[nonhomogeneous_shell_nogo_exact.py](../../research/audit/nonhomogeneous_shell_nogo_exact.py)
was executed locally with Python 3. It verifies the exact
matrix/determinant moments, the full quadratic interval
minimizations for BOTH signs over ALL radii, and the
rational gap bounds used in (3). Output:
    Exact mass, two matrix means, and determinant moment: passed
    All-radius Jensen tests and strict separation > 1/420: passed

Discovery used a finite LP against rotationally translated
L functions; the final separation has no floating or
grid-dependent hypotheses. The directional projection
sign and arbitrary-multiplicity projection-max extension
are hand proofs using the formalized arbitrary-K selection
lemma and (for arbitrary convex potentials) the stronger
hand proof in the concurrent row-projection note.
No new Lean proof or CI claim is made.

**Stop rule:** the affine-shell support program for all
isotropic profiles is refuted, independently at a rank-one
base and (concurrent note) at an anticonformal base.
Retain its exact positive theorem and the candidate signed
homogeneous proof; do not seek a universal continuation of
the old affine-shell differential inclusion. Continue only
with a broader spatial mechanism or direct unrestricted
isotropic Jensen proof. No wave-count, atom-count or
homogeneity-exponent ladder is resumed.
