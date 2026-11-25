# Nonhomogeneous isotropic profiles: arbitrary separated angular curvature and an all-gradient curvature-error estimate

23 November 2026. Hand proofs, with symbolic and rational checks actually
executed in the working container. The user is handling the signed
homogeneous proof's audit/formalization. **General isotropic Morrey remains
open.** No new Lean result or novelty claim.

The exact nonhomogeneous affine-shell representation in
[NONHOMOG_SHELL_AFFINE](IWANIEC_MORREY_NONHOMOG_SHELL_AFFINE.md)
is the input, together with the pinned, formally proved truncated
determinant theorem
[Agazzi.quasiconvex_integrandL](https://github.com/vltanh/lean4-iwaniec/blob/972c01272b2a573ae58fb43fac47c97196db2cbb/Agazzi/Quasiconvex.lean).
The following does NOT use the signed homogeneous candidate proof.

The broader projection-max theorem from the preceding
[PROJECTION_MAX](IWANIEC_MORREY_NONHOMOG_PROJECTION_MAX.md)
note remains available. I did not establish its universal support
completeness. Here I obtain an exact positive theorem for a class with
arbitrary angular as well as radial dependence, and a quantitative
all-gradient inequality for general smooth isotropic RC profiles.
This is not a new universal affine-shell completeness claim: the
previous exact no-go remains decisive.

## 1. Notation and localized theorem

Let x=|z| and y=|w| be the conformal and anticonformal moduli.
Put s=x+y=||X||op, delta=x-y (the signed smaller singular value),
and D=s delta=det X. The spectral sector is
S_R={(s,delta):0<=s<=R, |delta|<=s}.

Every finite-valued isotropic integrand has a representation
F(X)=f(s,delta)=F(diag(s,delta)) on this sector. If F is RC,
its restriction is separately convex in s and delta wherever
the corresponding coordinate line stays in the sector.

The known globally QC kernels are
$$
K_r^\pm(X)=(s-r)_+(r\pm\delta),\qquad r>0.
$$
They are scaled reflected copies of L, with a determinant term
added or subtracted. All are continuous, and neither is assumed
pointwise nonnegative.

**Theorem A (arbitrary separated angular curvature).** Every
finite-valued isotropic RC integrand of the form
$$
\boxed{F(X)=U(s)+V(s)\delta+H(\delta)}
\tag{1}
$$
is QC. Here U,V,H are arbitrary finite scalar functions on their
respective domains, subject only to the stated RC hypothesis.
In particular H need not be affine, the radial dependence is not
homogeneous, and no regularity, sign, or growth bound is imposed.

More precisely, the following conditions are necessary for RC
and sufficient for QC. They also give a LOCALIZED criterion on
a bounded spectral sector S_R, with no RC hypothesis outside
the ball:
$$
\begin{gathered}
H\ \text{convex},\qquad
U''\ge s\,|V''| \quad\text{as measures on }(0,R),\\
U'(s)+s V'(s)\ge V(s)+H'_-(s),\\
U'(s)-s V'(s)\ge -V(s)-H'_+(-s).
\tag{2}
$$
The last two inequalities need hold only at almost every common
differentiability radius. The regularity required to interpret
the localized sufficient conditions is: U Lipschitz on [0,R],
V locally Lipschitz on (0,R] and bounded near zero, H finite
convex on [-R,R] and Lipschitz there, U'',V'' locally finite
measures with the inequality in (2). In the global RC hypothesis
all these local conditions follow automatically. At zero define
F(0)=U(0)+H(0).

The localized conclusion means Jensen at any base of operator
norm <=R for all bounded periodic gradients taking values
in the same ball. It also holds for every compact probability
law on that ball which satisfies the two conformal norm Jensen
inequalities, the determinant identity, and all the K_r^\pm
Jensen inequalities. In particular it makes no restriction on
wave count, support size, or magnitude ratios.

### 1.1 Necessity

For fixed s, subtract the affine part in delta in (1).
Rank-one convexity on diag(s,delta) proves H convex on [-s,s],
hence globally convex in the full-matrix problem.

The finite RC function F is locally Lipschitz. U(s)=f(s,0)-H(0)
is locally Lipschitz at zero and elsewhere, and convex on
s>=0. Taking differences of f(s,delta) at two fixed small
positive/negative delta proves V locally Lipschitz on
(0,infinity). Taking delta=s and subtracting f(s,0)
shows V bounded near zero: the two matrix arguments are
distance O(s) apart and H is locally Lipschitz.

For every q, the function U(s)+q V(s) is convex for s>|q|,
by the rank-one line diag(s,q). As in the affine-shell theorem,
differences of two such convex functions show that V'' is a
signed locally finite measure and U'' is a nonnegative
measure. With a common dominating measure and countably
many rational q approaching +/-s, this gives U''>=s|V''|.

Fix a common differentiability radius s>0 for U,V.
The rank-one line diag(s,t) crosses the positive conformal
point at t=s. Its left slope is V(s)+H'_-(s), and its right
slope is U'(s)+sV'(s), because for t>s the sorted spectral
coordinates become (t,s). Their ordering gives the first
boundary inequality. At t=-s the left slope is
-U'(s)+sV'(s), and the right slope is V(s)+H'_+(-s).
Their ordering gives the other boundary inequality.
This proves (2), without smoothness of H.

### 1.2 Sufficiency: start the radial integral at the base, not at zero

Choose a base E=diag(r,t), with 0<r<R and |t|<r, at a
common differentiability radius r satisfying (2).
Take any supporting slope m of H at t, so
$$
H(\delta)\ge H(t)+m(\delta-t).
$$
Convexity of H implies
H'_+(-r)<=m<=H'_-(r). The two boundary inequalities
in (2) therefore give the angular coefficient condition
$$
U'(r)\ge |V(r)+m-rV'(r)|.
\tag{3}
$$

Define a constant-plus-convex-norms-plus-determinant starter
$$
\begin{aligned}
P_{r,t}(X)={}&U(r)+H(t)-mt+U'(r)(s-r)\\
 &+(V(r)+m-rV'(r))\delta+V'(r)D.
\end{aligned}
\tag{4}
$$
Indeed s=x+y and delta=x-y; (3) says both norm coefficients
are nonnegative. Thus P_{r,t} is globally polyconvex.

Define the nonnegative radial curvature measures
$$
\mu_\pm=\tfrac12(s^{-1}U''\pm V'').
$$
On [r,R] these are finite under the stated local Lipschitz
hypotheses: U is convex and Lipschitz, so U'' has finite
mass, and |V''|<=U''/r there. Choose r at a common
differentiability point so there is no curvature atom at r.
Define the globally QC minorant candidate
$$
\boxed{
G_{r,t}=P_{r,t}+
\int_{[r,R]} K_u^+\,d\mu_+(u)+
\int_{[r,R]} K_u^-\,d\mu_-(u).
}
\tag{5}
$$
Each integral is QC by Fubini of the positive-weight Jensen
inequalities (or locally uniform approximation by finite
positive sums). For the global statement take any finite
R containing the base and the test range.

For r<=s<=R, the same exact radial reconstruction as in
the affine-shell theorem gives
$$
G_{r,t}(X)=U(s)+V(s)\delta+H(t)+m(\delta-t)\le F(X).
\tag{6}
$$
For s<=r the integrals vanish. For any fixed delta with
|delta|<=s<=r the function U(v)+delta V(v) is convex on
[|delta|,R], by the measure inequality in (2). Its tangent
at r is therefore a lower bound at s. Add the supporting
line of H to get
$$
\begin{aligned}
F(X)&\ge U(r)+V(r)\delta+
        (U'(r)+\delta V'(r))(s-r)+H(t)+m(\delta-t)\\
    &=P_{r,t}(X)=G_{r,t}(X).
\end{aligned}
\tag{7}
$$
At (s,delta)=(r,t) equality holds. Equations (6),(7)
are the global-on-the-test-ball touching support proof.
Notice that we did NOT require the affine-shell tangent
to H to satisfy the angular condition at every smaller
radius: separate convexity supplies (7) instead.
This is the essential new step.

For an arbitrary nonzero base (s0,delta0), choose common
differentiability radii r_j<s0 tending to s0, and interior
t_j in (-r_j,r_j) tending to delta0. Use (5) and (6);
since H is Lipschitz, all its supporting slopes at the
t_j remain bounded, and G_{r_j,t_j}(A) tends to F(A).
Every minorant is below F on the whole ball. Jensen for
the fixed law at its original base A therefore passes
to the limit; it is not necessary to change that law.
For base zero choose r_j tending to zero and t_j=0;
G_{r_j,0}(0)=U(r_j)+H(0)-r_j U'(r_j) tends to F(0)
by the Lipschitz bound on U near zero. Isotropy handles
all matrices with the same spectral coordinates.
This proves the localized and global assertions, including
conformal endpoints and all nonsmooth profiles. QED.

### 1.3 Scope and nonpolyconvex examples

There is an infinite-dimensional family illustrating that H
need not be affine and that Theorem A is not merely a convex
or polyconvex result. Let H be ANY finite convex function
on R, zero on (-infinity,1], with slopes in [0,2], and set
$$
F(X)=(s-1)_+(1+\delta)+H(\delta).
\tag{8}
$$
Here U=V=(s-1)_+, so U''=V'' is the unit atom at 1.
The curvature condition is saturated. Below radius 1 the
two boundary inequalities are immediate, and above radius
1 they reduce to H'_-(s)<=2 and H'_+(-s)>=0.
Thus (8) is QC by Theorem A.

These are nonpolyconvex: F is zero in the unit operator-norm
ball but is -(s-1)^2 at s>1, delta=-s. A polyaffine
support at zero for an everywhere finite polyconvex function
would have to vanish identically, since it lies below zero
on a neighborhood of zero (use the rank-one directions to
kill the linear coefficients and both determinant signs to
kill the determinant coefficient). The negative values then
contradict existence of this support.
For a nonaffine H the integrand is nonaffine in each shell
intersecting its angular curvature. It is nonhomogeneous.
For instance H(delta)=(delta-1)^2 on [1,2], linear of slope 2
after 2, and zero below 1 gives an exact rational example.

**Important limitation:** the proof constructs affine-shell
QC minorants. Theorem A, even with arbitrary H, is therefore
INSIDE the earlier affine-shell supremal closure. The exact
shifted-L separating laws in the two preceding notes still
refute completeness for arbitrary f. Do not propose a
universal representation by (1) and its unshifted positive
closures. Translations and the broader projection-max
construction are not covered by that no-go.

For smooth full-matrix isotropic F there is also an instructive
regularity restriction: if (1) is C^3 in the signed diagonal
variables across the conformal line delta=s, symmetry under
interchanging the two diagonal entries gives
f_ssdelta(s,s)=f_sdeltadelta(s,s). In (1) the latter is zero,
so V''(s)=0 for every s>0. Thus the new class should not be
advertised as a dense smooth approximation theorem for general
nonhomogeneous isotropic RC energies.

## 2. An explicit all-gradient inequality for arbitrary two-variable profiles

The same localized theorem supplies a quantitative estimate
that does NOT assume (1). Let F be any C^4 isotropic RC
integrand, and restrict its signed diagonal profile to S_R.
Define the two finite mixed-curvature bounds
$$
M=\sup_{S_R}|f_{s\delta\delta}|,\qquad
N=\sup_{S_R}|f_{ss\delta\delta}|.
$$
Smoothness in the diagonal variables includes the sector
boundaries; no differentiability of the operator norm on
the full matrix space is assumed.

**Theorem B.** For every base A and bounded compatible
gradient X=A+Dphi of operator norm at most R, with
s_A,delta_A denoting the base spectral pair, put
$$
C(s)=M(Rs^2/2-s^3/6)+N s^4/24,\qquad 0\le s\le R.
$$
Then the Jensen deficit satisfies
$$
\boxed{
F(A)-\fint F(X)\le
\fint C(s_X)-C(s_A)+
\frac M2\left[
(R-s_A)\delta_A^2+
\fint (R-s_X)\delta_X^2
\right].
}
\tag{9}
$$
In particular a uniform bound is
$$
F(A)-\fint F(X)\le \frac{13}{27}M R^3+\frac1{24}N R^4.
\tag{10}
$$
Both inequalities also hold for abstract laws with all
unshifted affine-shell Jensen tests. They are quantitative
estimates, NOT an assertion that the right hand side
vanishes for arbitrary F.

**Proof.** Freeze the angular curvature on the outermost
shell:
$$
\begin{aligned}
U(s)&=f(s,0),& V(s)&=f_\delta(s,0),\\
H(\delta)&=f(R,\delta)-f(R,0)-f_\delta(R,0)\delta.
\end{aligned}
$$
Then H is convex, and by the integral Taylor formula
in delta followed by the fundamental theorem of calculus
in s,
$$
|f(s,\delta)-U(s)-V(s)\delta-H(\delta)|
 \le \frac M2 (R-s)\delta^2.
\tag{11}
$$
All intermediate points stay in S_R: an intermediate
angular coordinate lies between 0 and delta, and the
radial integrations increase s toward R.

By separate convexity f_ss(s,delta)>=0. Taylor in delta
around zero yields
$$
U''(s)+\delta V''(s)\ge -N\delta^2/2.
$$
Taking delta=+/-s gives U''>=s|V''|-Ns^2/2.
Since
$$
C''(s)=M(R-s)+Ns^2/2\ge Ns^2/2,
$$
the corrected radial function U+C satisfies the first
curvature inequality of (2).

At delta=+/-s the original f has the two boundary
inequalities f_s(s,s)>=f_delta(s,s) and
f_s(s,-s)>=-f_delta(s,-s), from rank-one convexity
across the two conformal lines. For the frozen profile,
Taylor in delta gives
$$
|f_s(s,\delta)-U'(s)-\delta V'(s)|\le M\delta^2/2,
$$
and the radial comparison of angular curvature gives
$$
|f_\delta(s,\delta)-V(s)-H'(\delta)|
\le M(R-s)|\delta|.
$$
Thus the possible deficit in either boundary inequality
for the frozen profile at radius s is at most
M(Rs-s^2/2). But
$$
C'(s)=M(Rs-s^2/2)+Ns^3/6
$$
is at least this large. The corrected profile
$$
\widetilde f(s,\delta)=U(s)+C(s)+V(s)\delta+H(\delta)
$$
therefore satisfies every localized criterion of Theorem A.
It obeys Jensen on the ball. Inserting the error (11)
and keeping the radial correction difference yields (9).
For (10) use C(0)=0, C nondecreasing,
C(R)=MR^3/3+NR^4/24 and
(R-s)delta^2<= (R-s)s^2<=4R^3/27.
This gives MR^3/3+4MR^3/27=13MR^3/27. QED.

The estimate is useful for a genuine perturbative
nonhomogeneous problem: it is uniform in test amplitude
up to R, in all oscillation scales, and in support size.
It explicitly quantifies the dependence on radial variation
of angular curvature. It does not establish a universal
sign, since M and N need not be small for arbitrary f,
and their control is not implied by RC alone.

## 3. Verification and disposition

The accompanying [checker](../../research/audit/nonhomogeneous_angular_exact.py)
was run with Python 3 and SymPy, after fixing a test-script
symbol-shadowing error. Final output:
    Symbolic starter contact and radial repair identities passed
    39-radius nonsmooth example: boundary budgets, touching, and rational minorant controls passed
    Signed quartic: compact-sector curvature repair and error bounds passed

The nonsmooth controls check the saturated example (8) with
arbitrary rational base ratios. The signed quartic control
uses |X|_F^4-(9/4)|X|_F² det X, whose exact RC certificate
is already in the research ledger. These finite checks do
not supply the analytic quantifiers, which are proved above.

**Status and next research decision:** Theorem A removes
homogeneity for a genuine nonlinear-in-angular-variable
class; Theorem B gives a direct all-gradient quantitative
estimate for every smooth profile. Neither provides the
universal QC conclusion. Since both rely on the already
refuted unshifted affine-shell support cone, iterating
this estimate or subdividing radii without new spatial
information cannot solve the general problem. Return to
the broader arbitrary-multiplicity scalar-projection
calibration (or an actual new direct argument), not
another list of special radial/angular cases. No claim
of general nonhomogeneous isotropic Morrey, no new Lean
proof, and no reopening of the signed homogeneous audit.
