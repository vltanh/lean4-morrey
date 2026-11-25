# Removing homogeneity: exact nonhomogeneous affine-shell theorem and the remaining scalar support problem

23 November 2026. Hand proof with actually executed exact rational controls.
The nonnegative homogeneous theorem is Lean verified on the
[homogeneous-isotropic branch at f70d7e9](https://github.com/vltanh/lean4-morrey/tree/f70d7e9253ecf59ea6c862893d1fdd3fb60cffa9).
The full signed homogeneous candidate proof is in
[SIGNED_CHARACTERISTICS](IWANIEC_MORREY_SIGNED_CHARACTERISTICS.md);
its audit and formalization are separate work. **The theorem in Section 2
below does not depend on that candidate signed proof.**
The only non-elementary QC input is the already formalized truncated
determinant L in the pinned dependency
[Agazzi.quasiconvex_integrandL](https://github.com/vltanh/lean4-iwaniec/blob/972c01272b2a573ae58fb43fac47c97196db2cbb/Agazzi/Quasiconvex.lean).
The new nonhomogeneous results are hand proofs, not Lean theorems.
No full isotropic or unrestricted Morrey proof and no priority claim.

## 1. The correct nonhomogeneous variables

For any planar matrix X use its conformal and anticonformal coordinates
z,w. Put x=|z|, y=|w|, s=x+y=||X||op, delta=x-y, D=det X=s delta.
Set s=delta=0 at X=0. In particular delta is the signed smaller
singular value, not the normalized homogeneous ratio delta/s.
An arbitrary finite-valued isotropic F is
    F(X)=f(s,delta),   f(s,delta)=F(diag(s,delta)),
on the closed sector s>=|delta|. Rank-one convexity implies that f
is convex separately along the two coordinate lines within that
sector, simply by varying a diagonal entry. Homogeneity would impose
f(s,delta)=s^p h(delta/s); we do NOT impose it.

For r>0 and e in {-1,+1}, define
$$
K_r^e(X)=(s(X)-r)_+(r+e\,\delta(X)).
$$
Both are QC: K_r^- = r² L(X/r)-det X, and
K_r^+ = r² L(XJ/r)+det X, with J=diag(1,-1).
This follows from the formalized theorem for L, reflection,
positive rescaling, and the determinant null Lagrangian.
Neither kernel is assumed pointwise nonnegative.
The functions x,y are convex (norms of linear projections).

## 2. Complete theorem for arbitrary affine-in-shell profiles

**Theorem A.** Let F be any finite-valued rank-one convex function
on R^(2x2) of the form
$$
F(X)=U(s(X))+V(s(X))\,\delta(X)\quad(s(X)>0).
\tag{1}
$$
Then F is quasiconvex. More precisely F is a locally uniform limit
of finite positive combinations of x,y,K_r^+,K_r^-, together with
an arbitrary constant and determinant term. No sign, growth,
homogeneity, smoothness, radial scale separation or wave-count
hypothesis is imposed.

The hypothesis "affine in each shell" means affinity in the
*signed* smaller singular value for every fixed s. It does not
require affinity in s, and allows arbitrary radial curvature and
singular changes of the determinant coefficient at arbitrary radii.

**Proof.** First, finite-valued rank-one convex functions are locally
Lipschitz (use separate convexity in the four matrix entries).
Thus U(s)=F(diag(s,0)) is locally Lipschitz on [0,infty), convex
and nondecreasing there by the rank-one line through zero and
isotropy. The function
$$
V(s)=\frac{F(\operatorname{diag}(s,s))-
                  F(\operatorname{diag}(s,-s))}{2s}
$$
is locally Lipschitz on (0,infty) and bounded near zero by local
Lipschitz continuity of F. Define U(0)=F(0).

### 2.1 Exact measure curvature criterion

For every constant q, rank-one convexity on diag(s,q) implies
that U(s)+q V(s) is convex for s>|q|. On any interval compactly
contained in (0,infty), take a small positive and a small negative
q. The difference of the corresponding two convex functions
shows that V'' is a signed locally finite Radon measure (all
second derivatives here are distributional). Also U'' is a
nonnegative measure. For each rational q,
$$
U''+q V''\ge0\quad\text{on }(|q|,\infty).
$$
Use U''+|V''| as a common dominating measure. By taking a
countable simultaneous full-measure set, its respective densities
u,v satisfy u+qv>=0 for all rational |q|<s. Let q approach both
+s and -s. This proves the exact measure inequality
$$
\boxed{U''\ge s\,|V''|.}\tag{2}
$$
Define the two nonnegative, locally finite measures on (0,infty)
$$
\mu_\pm=\tfrac12(s^{-1}U''\ \pm V'').
\tag{3}
$$
They need not have finite mass near zero or infinity.

### 2.2 The angular boundary condition

At every radius epsilon>0 where U,V are differentiable, consider
the rank-one line diag(epsilon,t) crossing the positive and
negative conformal points t=+/-epsilon.
At t=epsilon its left slope is V(epsilon), and its right slope is
U'(epsilon)+epsilon V'(epsilon). At t=-epsilon its left slope is
-U'(epsilon)+epsilon V'(epsilon), and its right slope is V(epsilon).
Convexity of both crossings gives
$$
\boxed{U'(\epsilon)\ge|V(\epsilon)-\epsilon V'(\epsilon)|.}
\tag{4}
$$
Equivalently the coefficients of x and y in the following
polyconvex function are nonnegative:
$$
P_\epsilon(X)=U(\epsilon)+U'(\epsilon)(s-\epsilon)
  +(V(\epsilon)-\epsilon V'(\epsilon))\delta
  +V'(\epsilon)\det X.
\tag{5}
$$
Indeed s=x+y, delta=x-y. This q is a constant plus nonnegative
norms and a determinant.

### 2.3 Reconstruction, including curvature atoms

Choose epsilon at a common differentiability radius of U,V, where
neither second derivative has an atom. Such radii have full
Lebesgue measure (a difference of convex functions has finite
one-sided derivatives on each compact subinterval).
Define
$$
G_\epsilon(X)=P_\epsilon(X)+
       \int_{[\epsilon,\infty)}K_r^+(X)\,d\mu_+(r)
       +\int_{[\epsilon,\infty)}K_r^-(X)\,d\mu_-(r).
\tag{6}
$$
On any fixed bounded matrix set only a compact interval of r
contributes, and each measure is finite on this interval. Thus
Fubini proves QC of G_epsilon. Alternatively, approximate the
integrals uniformly on that compact set by finite sums with
positive weights, by uniform continuity of the kernel in r and
X. All such sums are globally QC.

For s>=epsilon, expand the kernels in (6). The coefficient of
delta has initial value V(epsilon), initial derivative
V'(epsilon), and distributional second derivative
mu_+-mu_-=V''. The intercept has initial value U(epsilon),
initial derivative U'(epsilon), and second derivative
r(mu_++mu_-)=U''. This follows from
the distributional second derivative of (s-r)_+ being a point
mass at r. Equivalently integrate twice with initial data at
epsilon. Hence
$$
G_\epsilon(X)=F(X)\quad\text{whenever }s(X)\ge\epsilon.
\tag{7}
$$
For s<=epsilon the integrals vanish. Near zero, U' is bounded
by local Lipschitz continuity and V is bounded, so (4) also
bounds epsilon |V'(epsilon)| by |V(epsilon)|+U'(epsilon).
In (5), |delta|<=s<=epsilon and |det X|<=epsilon². Thus
sup_{s<=epsilon}|P_epsilon(X)-F(0)| tends to zero, as does
sup_{s<=epsilon}|F(X)-F(0)|. Consequently G_epsilon converges
locally uniformly to F along common differentiability radii
epsilon->0. Jensen passes to the limit on every bounded gradient
test. QED.

This proof avoids an unjustified integral of (3) from radius zero:
in general the measures may have infinite mass there. Truncation
is essential and gives an actual locally uniform reconstruction.
It also avoids assuming that rank-one convexity controls an
ordinary Hessian in singular-value coordinates without the
boundary condition (4).

**Converse / exact certificate.** Suppose instead that U,V are
locally Lipschitz for s>0, with U locally Lipschitz at 0 and
V bounded near 0, and (2) holds distributionally. If (4) holds
at common differentiability radii tending to zero, the same proof
works without assuming rank-one convexity at all. The represented
function is QC and hence rank-one convex. In the smooth setting
the two simple conditions (2) and (4) characterize this
entire class. Necessity follows by the preceding proof.

This is a complete genuinely nonhomogeneous theorem, independent
of the signed homogeneous characteristic candidate. It includes
both signs of truncated determinants at arbitrarily interleaved
scales with arbitrary positive measures.

## 3. Consequence for the whole isotropic problem: exact spectral tests

Let A be any base, and write s0,delta0,x0,y0,D0 for its coordinates.
For a compact probability law of spectral pairs (s,delta) in
the sector, consider the following tests:
$$
\begin{gathered}
 E x\ge x_0,\qquad E y\ge y_0,\qquad E(s\delta)=D_0,\\
 E K_r^e(s,\delta)\ge K_r^e(s_0,\delta_0)
 \quad\text{for every }r>0,\ e=\pm1.
\end{gathered}
\tag{8}
$$
Actual gradient laws satisfy them, by the convexity of x,y,
the determinant identity and the formalized L theorem.

**Theorem B.** The tests (8) are *equivalent* to Jensen for
EVERY isotropic rank-one convex affine-in-shell integrand.
Necessity follows since x,y,+det,-det,K_r^e themselves are
affine in each shell and QC. Sufficiency follows from the
representation (6) and its locally uniform limit. Thus no
other affine-shell test needs to be checked.

There is an exact reduction of the universal support question
to a law on ONE scalar variable. Disintegrate any spectral law
over its radius s and put q(s)=E[delta|s], with |q(s)|<=s.
Replace the joint law by the graph (s,q(s)) with the same radius
distribution. Because all the tests in (8) are affine in delta,
the replacement preserves every test EXACTLY. Further, for
ANY isotropic rank-one convex F,
$$
E f(s,\delta)\ge E f(s,q(s))
\tag{9}
$$
by separate convexity on each shell. The compressed law need NOT
be a gradient law. This is why (9) alone does not prove Morrey.

For clarity the compressed law can be lifted to an abstract
matrix law having the correct matrix and determinant means.
Let x(s)=(s+q(s))/2, y(s)=(s-q(s))/2. The first two inequalities
in (8) ensure E x>=|z_A|, E y>=|w_A|. Choose independent
unit-modulus signs in the directions of z_A,w_A with mean
magnitudes |z_A|/E x and |w_A|/E y, respectively (when a
denominator is zero, the corresponding coordinate is zero
almost surely). Multiplying x,y by these signs gives conformal
and anticonformal coordinates of a law with the required mean.
The determinant moment is unchanged. This does NOT establish
spatial gradient compatibility of the lift.

A genuinely sufficient global target is therefore:
for every compact radius law and every measurable q with
|q(s)|<=s satisfying (8), prove (9)'s right side >=f(s0,delta0)
for every isotropic rank-one convex f.
The target could be stronger than isotropic Morrey. If it
fails, the witness is a failure of the affine-shell support
method, not automatically a compatible-gradient counterexample.

## 4. Exact compact obstacle formulation for arbitrary f

Fix R>s0, let S_R={(s,delta):0<=s<=R, |delta|<=s}.
All tests K_r vanish identically on S_R for r>=R, so (8)
there involves only a compact radial parameter and two signs.
On S_R, the following statements are equivalent for a continuous
isotropic f and the fixed base:

(a) every probability law satisfying (8) obeys Jensen for f;
(b) for every epsilon>0 there is a globally QC affine-in-shell
    finite sum G of the generators of Theorem A, such that
    G<=f on S_R and G(s0,delta0)>=f(s0,delta0)-epsilon.

The implication (b)->(a) follows from (8).
For the reverse work in C(S_R). Normalize every generator
by subtracting its value at the base, and form the convex cone
generated by x-x0,y-y0,K_r^e-K_r^e(A), the full line through
D-D0, and all pointwise nonnegative continuous functions.
By Hahn--Banach separation and Riesz representation, its
uniform closure contains f-f(A) if (a) holds: otherwise a
separating positive functional is a nonnegative measure which
can be normalized to a probability law satisfying (8) and
violating Jensen. Here inclusion of all nonnegative functions
ensures positivity of the separating functional, and the
determinant line ensures the exact moment equality.
Uniform approximation of f-f(A) by g+h with g a normalized
finite conic sum of the generators and h>=0 gives
g<=f-f(A)+epsilon. Adding f(A)-epsilon proves (b).

This is a scalar obstacle/support criterion, not a finite grid
proof. It gives a single precise sufficient gate without any
fixed wave count or exponent. It does not assert (a) or (b)
for arbitrary isotropic RC f.

## 5. Attempt at the universal continuation: exact differential inclusion

Here we derive the nonhomogeneous counterpart of the
homogeneous supporting-slope characteristic. This section is
a **construction criterion**, NOT a proof of global existence.

Assume f is C² in the open sector and f_delta_delta>0 (a smooth
strictly rank-one convex approximation can be obtained by
isotropic mollification in matrix space plus epsilon |A|²).
Choose a contact curve delta=z(s) with |z(s)|<s, and set
$$
M(s)=f_\delta(s,z(s)),\qquad
I(s)=f(s,z(s))-M(s)z(s).
$$
Then G=I(s)+M(s)delta lies below f on EVERY shell by
convexity in delta, with equality at z(s).
Let c(s)=M'(s) and put
$$
a=f_{ss},\qquad b=f_{s\delta},\qquad h=f_{\delta\delta},
\qquad
D_*(s)=a-\frac{(c-b)^2}{h}.
$$
All derivatives of f in this section are evaluated at (s,z(s)).
For a differentiable contact curve and locally absolutely
continuous c, the chain rule gives
$$
\begin{aligned}
z'&=(c-b)/h,\\
I'&=f_s-zc,\\
I''&=D_*-z c'.
\end{aligned}
\tag{10}
$$
Consequently the two exact affine-shell criteria (2),(4) become
$$
\boxed{
\begin{gathered}
\frac{M-f_s}{s-z}\le c\le
       \frac{f_s+M}{s+z},\qquad D_*\ge0,\\
-\frac{D_*}{s-z}\le c'\le\frac{D_*}{s+z}.
\end{gathered}}
\tag{11}
$$
The first inequality is precisely the condition that the two
angular coefficients in a local isotropic poly-affine support
are nonnegative. The second is the radial PSD condition after
subtracting c det. The last inequality is equivalent to
I''>=s|M''|, since M''=c'. There is no missing sign in this
equivalence (separate the cases c'>=0 and c'<=0).

**Pointwise feasibility at every smooth rank-one convex base.**
In 2x2, a rank-one nonnegative quadratic form is a positive
semidefinite form plus a multiple of determinant (the standard
quadratic polyconvexity theorem, also follows from the neutral
covariance cone decomposition in MARTINGALE_DEFECT).
Apply this to D²F at a base with x,y>0. In the radial
(s,delta) block the condition D²(F-c det)>=0 is exactly
the PSD matrix with entries a,b-c,h, hence D_*>=0.
The two tangential directions in the complex z,w planes give
f_s+M-c(s+z)>=0 and f_s-M+c(s-z)>=0.
Thus at least one c satisfies the first line of (11).
With strict rank-one convexity one can choose a strict
radial and angular margin locally by first subtracting a
small ordinary quadratic. This does not guarantee feasibility
of a global curve satisfying the derivative constraints.

If there exists a contact curve through an arbitrary prescribed
interior base, defined for all s>0 and satisfying (10)-(11)
with appropriate local regularity, then its G satisfies
Theorem A's converse and gives a global touching minorant.
At s->0, |z(s)|<=s and f's local Lipschitz bound implies
M is bounded (for smooth F it is immediate from bounded
matrix derivatives); I tends to F(0). The angular bounds
and I''>=0 give a bound on I' near zero from monotonicity
and finiteness, so the near-zero hypotheses hold.
If a curve reaches |z|=s one must handle endpoint contacts,
or construct an obstacle support that ceases to touch on
some shells. No such extension is assumed.

This formulation clarifies what homogeneity supplied in the
previous characteristic proof. On its active boundary one
angular coefficient vanishes. For example if c=(f_s+M)/(s+z),
differentiating along the contact gives
    c'=D_* /(s+z),
exactly the positive extreme allowed in (11); the other
angular boundary gives the negative extreme. In the homogeneous
proof the corresponding trajectory was shown to remain in a
domain with monotone restricted supports. In the general problem
the PSD interval for c may move with s and z, and pointwise
feasibility alone does NOT imply viability of (11). It is not
legitimate to choose arbitrary feasible c independently on each
shell and then differentiate it as if c' satisfied the last
inequality. Nor is there a proof here of global contact
continuation in both directions from the base.

**Main next task:** construct global scalar obstacle minorants
in Section 4, using (10)-(11) where in contact and allowing
noncontact intervals. This is a concrete positive construction
using the proven kernel cone; do not turn it into fixed-degree
or fixed-wave enumeration. If global contact continuation
fails for some profile, that does not rule out a support with
noncontact intervals or a different QC minorant.
No closure of the general isotropic implication is claimed.

## 6. Verification and scope

The standard-library checker
[nonhomogeneous_shell_exact.py](../../research/audit/nonhomogeneous_shell_exact.py)
was actually executed in Python 3. It verifies:
    exact mixed atomic/diffuse curvature representation and truncation: passed
    exact spectral compression and kernel-moment invariance: passed

The tests include both kernel orientations, signed coefficients,
atomic and diffuse radial curvature, three truncation radii,
and exact compression of conditional spectral means.
The proof supplies all unbounded function/measure quantifiers,
not these controls.

**Status:** positive homogeneity has been completely removed for
the full affine-in-shell class, including arbitrary radial
measures. More generally locally uniform limits, finite maxima
and nonnegative sums of its members are QC by closure; an arbitrary
isotropic RC function has not been shown to be in that closure.
The remaining general isotropic support gate is explicit and
one-dimensional in its scale variable, with no exponent ladder.
The new affine-shell theorem itself is independent of the
candidate full signed homogeneous proof under separate audit.
Unrestricted Morrey remains open.
