# Unamplified isotropic Jensen on spectral shells and an all-law spectral-gap inequality

24 November 2026. Positive hand arguments for arbitrary isotropic
rank-one convex integrands, independent of homogeneity, sign, and the
candidate signed homogeneous theorem under separate audit. **The
general isotropic Morrey gate remains open.** The results below handle
variable determinants by a common-column comparison, rather than by
a new homogeneous-degree subclass or exponential reparametrization.

The most useful outputs are:

* Integral Jensen for every finite-valued isotropic RC integrand on
  constant-operator-norm gradient laws, including arbitrary changes of
  determinant sign. More generally a common singular-value interval
  condition and an explicit shear-budget criterion suffice.
* An all-base, all-law quantitative Jensen inequality where determinant
  variance has a POSITIVE coefficient in the intermediate estimate.
  The final loss is only spectral interval mismatch, with an explicit
  one-dimensional optimization over the comparison radius.
* A determinant-mass transport inequality at rank-deficient bases,
  allowing arbitrarily many different spectral scales if opposite
  orientation determinant mass can be matched across overlapping
  singular-value intervals.

These are unmodified-energy Jensen results for the stated laws, not
a universal gradient realization or a solution of Morrey. The common
column comparison alone uses correct matrix/minor means; no unsupported
claim of additional gradient compatibility is made. The exact algebra
checker was run locally. No Lean verification, independent referee
review, or priority claim.

## 1. The elementary shell comparison

Write s(X)=||X||op, l(X)=the unsigned smaller singular value,
d(X)=det X. Thus s*l=|d|, |X|_F^2=s^2+l^2. Set
I(X)=[l(X),s(X)], including I(0)={0}. Proper rotations on the
left and right classify a planar matrix by its signed singular values,
equivalently by d and |X|_F^2. A rank-one direction in conformal
coordinates (z,w) is characterized by equality of the two moduli.

At fixed determinant d, let j be the smaller of the two conformal
moduli. If d>=0, use the rank-one line

    z=sqrt(d)+i t, w=t.

It has determinant d, smaller conformal modulus |t|, and squared
Frobenius speed 4. The restriction of any finite-valued isotropic RC F
to this line is even and convex in t. For d<0 apply the reflected
argument interchanging z and w. Consequently, on a determinant fiber,
F is nondecreasing in j, hence also in the larger singular value s.
This recovers the fixed-determinant comparison of the preceding
[determinant-stabilization note](IWANIEC_MORREY_DETERMINANT_STABILIZATION.md).

For r>0 put
    H_r(d)=F(diag(r,d/r)).
This is convex on the whole real determinant axis: changing d varies
only one diagonal entry, along a rank-one line. Moreover

    F(X)>=H_r(d(X))  if r in I(X),
    F(X)<=H_r(d(X))  if r not in I(X).

The second inequality also holds at the endpoints, with equality
there, because max(r,|d|/r)>=s precisely when r is outside the
open interval I(X). Both inequalities use the fixed-determinant
monotonicity just proved.

**Theorem A (common shell / spectral interval).**
Let nu be a compact probability law, E d(X)=d(A). If there is r>0
such that r in I(X) almost surely and r is outside the open interval
(l(A),s(A)), then

    E F(X)>=E H_r(d(X))>=H_r(d(A))>=F(A).

This is the original integral Jensen inequality, for every finite
isotropic RC F. It uses only the determinant moment. In particular,
for a compatible gradient whose operator norm is constant r,
the matrix mean implies s(A)<=r by convexity of the operator norm,
so the theorem applies. The zero shell is trivial.

The determinant can fluctuate arbitrarily, including sign changes.
This is a complementary result to constant-Jacobian Jensen: here the
operator norm is held constant, not the Jacobian. No smoothness or
ellipticity margin is needed.

## 2. Exact all-law gap estimate and cancellation of determinant variance

Assume F is C^2 and isotropic, with rank-one Hessian bounds
    m |H|_F^2 <= D^2 F(X)[H,H] <= M |H|_F^2
for all rank-one H on the operator ball B_B, with 0<=m<=M.

Suppose ||X||op<=R almost surely, E X=A, E det X=det A.
For the chosen comparison radius r>0 it suffices to take
    B=max(R,r,R^2/r).
This covers all matrices used in the argument. In particular
||A||op<=R, and ||diag(r,d/r)||op<=B for |d|<=R^2.

Define
$$
Q_r(X)=\frac14\left(|X|_F^2-r^2-\frac{d(X)^2}{r^2}\right)
=\frac{(s(X)^2-r^2)(r^2-l(X)^2)}{4r^2}.
$$
Thus Q_r(X)>=0 exactly when r in I(X). Equivalently
Q_r=j(X)^2-j(diag(r,d/r))^2, where j=(s-l)/2 is the smaller
conformal modulus. This equality also holds when d=0.

The restriction g_d(t) of F to the above constant-determinant shear
line has g_d'(0)=0 and 4m<=g_d''<=4M for 0<=t<=the larger of the two
smaller conformal moduli being compared. Every point along this path
is in B_B by monotonicity of the larger singular value. Integrating
the bounds on g_d'' first from 0 to t and then between the two
moduli gives the exact two-sided comparison

$$
2m(Q_r)_+-2M(Q_r)_-\le F(X)-H_r(d(X))
 \le 2M(Q_r)_+-2m(Q_r)_-,
$$
where q_+=max(q,0) and q_-=max(-q,0).

On the rank-one determinant line diag(r,d/r) the squared Frobenius
speed is 1/r^2. Hence H_r''>=m/r^2 on the required determinant
interval, so
$$
E H_r(d)-H_r(d_A)\ge\frac{m}{2r^2}E(d-d_A)^2.
$$
In contrast to the earlier determinant-stabilization estimate this
is a POSITIVE determinant-variance contribution.

Use the lower shell comparison for X and the upper one for A:
$$
E F(X)-F(A)\ge
\frac{m}{2r^2}E(d-d_A)^2+
2m(E Q_r(X)-Q_r(A))
-2(M-m)(E(Q_r(X))_-+(Q_r(A))_+).
$$
The first two terms simplify exactly because of the two minor means:
$$
E Q_r(X)-Q_r(A)=\frac14
 \left(E|X-A|_F^2-\frac{E(d-d_A)^2}{r^2}\right).
$$
The determinant variances cancel, yielding the main all-law estimate:

**Theorem B (spectral-gap Jensen).**
For EVERY r>0, with m,M on B_B as above,
$$
\boxed{
\begin{aligned}
 E F(X)-F(A)\ge {}&\frac m2 E|X-A|_F^2\\
 &-\frac{M-m}{2}\left(
 E\left[r^2+\frac{d(X)^2}{r^2}-|X|_F^2\right]_+
 +\left[|A|_F^2-r^2-\frac{d_A^2}{r^2}\right]_+
 \right).
\end{aligned}}
$$

This is uniform over all actual bounded compatible gradients and even
over abstract laws with the correct minors. There is no wave-count or
atom-count assumption. The loss vanishes under the hypotheses of
Theorem A, giving a strict quadratic Jensen margin for m>0.

The new bound can be combined by taking the better lower bound
with the earlier determinant-stabilization inequality. It controls
large determinant fluctuations when the support intervals are
sufficiently well aligned. It does not require small perturbations
or small determinant variance.

For numerical discovery or a quantitative application, the best
radius can be chosen by one-dimensional optimization. Restrict
r to any compact positive interval [a,b] and use common Hessian
bounds on B_max(R,b,R^2/a). Set u=r^2. The integral loss
    E [u+d(X)^2/u-|X|_F^2]_+
is convex in u>0. If r is outside the open base interval, the base
loss is zero. Hence optimization there is a scalar convex problem
on each admissible interval. This is an optimization of a proved
bound for all laws, not a finite enumeration of gradient cases.

## 3. Common-column spectral compression with a shear budget

There is a nonsmooth extension of Theorem A that permits the common
comparison radius to lie inside the base interval.

For r>0 define
    b_r(X)=sqrt([|X|_F^2-r^2-d(X)^2/r^2]_+).
The matrix
$$
Y_r^\pm(X)=
\begin{pmatrix}r&\pm b_r(X)\\0&d(X)/r\end{pmatrix}
$$
has the same determinant as X. When r in I(X), it also has the same
Frobenius norm, so F(Y_r^\pm(X))=F(X) by isotropy.
Outside I(X), b_r(X)=0 and the spectral comparison is to H_r.

Let nu satisfy E d=d_A, with no matrix moment assumption needed in
this paragraph. Put B_1=E b_r(X), b_0=min(b_r(A),B_1). If B_1>0,
choose a sign independently of X with probability
(1+b_0/B_1)/2 of being positive. If B_1=0 either sign can be used.
Then the law of Y has mean
    A_r=[[r,b_0],[0,d_A/r]].
All Y matrices share the entire first column, so F is convex on
their affine plane and Jensen applies. If r in I(A) and
B_1>=b_r(A), A_r has precisely the invariants of A. If r is outside
I(A), A_r has zero shear and F(A_r)>=F(A) by Section 1.

**Theorem C.** If r in I(X) almost surely and either r is outside
the open base interval or E b_r(X)>=b_r(A), then E F>=F(A) for
every finite-valued isotropic RC F. This gives exact Jensen even
when there is no common radius outside the base interval.

For general laws there is a quantitative nonsmooth version. Let L
be a Frobenius Lipschitz constant of F on B_B as in Section 2.
Such a finite constant exists for every finite-valued RC F by
separate convexity. At fixed determinant, the two canonical shear
points of Section 1 are at Frobenius distance twice the difference
of their smaller conformal moduli. Therefore
$$
E F(X)-F(A)\ge
-2L E\left[\frac{|r-|d(X)|/r|}{2}
                 -\frac{s(X)-l(X)}2\right]_+
-L[b_r(A)-E b_r(X)]_+ .
$$
The first term is the cost of replacing spectra that miss the
comparison radius. The second is the cost of an insufficient mean
shear budget at the base. Indeed the compressed barycenter and the
representative of A in the common-column plane differ by just the
indicated shear amount whenever r in I(A); outside I(A) no base
cost is needed. All compressed matrices and comparison segments
remain in B_B. If the rank-one Hessian bound m>0 holds, the
common-column Jensen step additionally contributes
    (m/2)(E b_r(X)^2-b_0^2+Var(d)/r^2)
to this lower bound. No passage from pointwise rotations to actual
gradient compatibility is assumed: we instead use ordinary
convexity on the common-column plane.

## 4. Multiscale determinant transport at rank-deficient bases

A single common radius is not necessary for some unamplified
integral inequalities. Suppose det A=0 and let nu have the correct
determinant moment. Let nu_+ and nu_- be the finite measures on
positive- and negative-determinant matrices with densities
d and -d with respect to nu, respectively. They have equal mass.
Let pi be ANY coupling of those weighted measures supported on
pairs (X_+,X_-) with intersecting intervals I(X_+) and I(X_-).
If both measures have zero mass, use the zero coupling.

For a pair write d_+=det X_+>0 and d_-=-det X_->0, and choose
    r=min(s(X_+),s(X_-)).
On the overlap set this r>0 belongs to both intervals. Put
U(r)=F(diag(r,0)). U is convex and nondecreasing for r>=0
because the rank-one line through zero has an even convex
restriction.

The common-shell inequality and rank-one convexity of H_r give
$$
\frac{F(X_+)}{d_+}+\frac{F(X_-)}{d_-}
 \ge\left(\frac1{d_+}+\frac1{d_-}\right)U(r).
$$
Indeed the determinant-balanced weights are
d_-/(d_++d_-) and d_+/(d_++d_-). This inequality is valid
regardless of signs of the energy.

Integrate against pi and include the original zero-determinant
mass. Define a probability measure sigma on radii by pushing
the measure (1/d_++1/d_-) pi forward under r, and adding the
pushforward of the zero-determinant restriction of nu under s.
The marginal identities ensure that sigma has mass one. All
terms are integrable even when determinants approach zero,
since F is bounded on the original compact support and the
reciprocal factors cancel the weighted marginals. Thus
$$
E F(X)\ge\int U(r)\,d\sigma(r)\ge
                    U\left(\int r\,d\sigma(r)\right).
$$
For rank-deficient A, if the last mean radius is >=s(A),
this proves the original Jensen inequality for every finite
isotropic RC F. At A=0 that radius condition is automatic.

This is a weighted transport theorem with arbitrary many spectral
scales, not a fixed number of determinant values or atoms. It is
only a sufficient condition on the law: we do NOT claim that
every compatible gradient admits the overlap coupling. A complete
proof of isotropic Morrey would need a spatial construction that
also handles unmatched determinant masses or a different argument.
The common-column method has not closed that gap.

## 5. Verification, relation to the general gate

The checker [spectral_gap_exact.py](../../research/audit/spectral_gap_exact.py)
was actually run locally using Python/SymPy, with output:

    Symbolic spectral gap, variance cancellation and rank-one Hessian bounds passed.
    972 exact rational pointwise shell comparisons passed.
    48 exact full-moment Jensen bounds passed, including nonpolyconvex test laws.

The rational checks use the signed Dacorogna--Marcellini quartic
plus a Frobenius quadratic, with its exact global rank-one Hessian
SOS and explicit upper bound on each test ball. The argument for
arbitrary F is the analytic one in Sections 1--4.

The previous determinant-stabilization normal form remains valid
at hand-proof level and is the target. The new shell comparison
provides a direct positive determinant-fluctuation mechanism on
well-aligned spectra, and the quantitative inequality isolates
the cost of those that fail to align. Neither the interval overlap
condition nor the transport coupling is known to hold for all
compatible gradients; none of the estimates above removes the
determinant correction universally. Do not claim a full solution
of general isotropic Morrey. Avoid a new list of fixed atom counts
or exponent subclasses; any further universal proof must address
mixing different spectral scales with actual gradient compatibility.
