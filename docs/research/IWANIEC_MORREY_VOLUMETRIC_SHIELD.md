# Literature-guided positive result: the entire planar isotropic volumetric–isochoric split

24 November 2026. We suspend the unproductive universal signed-stress
absorption and counterexample search for this investigation. Instead,
the numerical literature suggests transferring a completed homogeneous
theorem to a nonhomogeneous class that has already received extensive
attention.

**New hand theorem, conditional only on the repository's verified
nonnegative homogeneous isotropic polyconvexity theorem for p>=2:**
Every continuous isotropic rank-one-convex energy
    W(A)=h(K(A))+g(det A),  A in GL^+(2),
where K=||A||op²/det A, with convex g and arbitrary continuous h,
is polyconvex on GL^+(2).

There is NO assumption that h is convex or that W is nonnegative,
homogeneous, or twice differentiable. This addresses the complementary
convex-volumetric class in Voss et al. (2022), where a reduction to
one least rank-one-convex candidate was not obtained. In particular
the three named minus-branch candidates, insofar as they have the
stated RC property, are covered together rather than case by case.

Combined with the existing convex-distortion theorem of Astala,
Faraco, Guerra, Koski and Kristensen, and the dichotomy proved below,
this gives RC=>QC for the entire continuous additive split class
on GL^+(2), in their orientation-preserving definition of QC.
There is also a direct proof for compact positive-determinant
gradient ranges using the signed homogeneous theorem at degrees
arbitrarily close to two.

**Scope:** this is a nonhomogeneous isotropic result on GL^+(2),
not arbitrary finite energies on all R^(2x2) and not elimination
of isotropy. No unrestricted planar Morrey result, no closure of
the previous anisotropic Gate 1. The transfer is not yet formalized
in Lean. No publication-priority claim or independent review.

## 1. What the numerical literature actually established

* Dacorogna and Haeberly, *Some numerical methods for the study
  of the convexity notions arising in the calculus of variations*
  (1998), https://www.numdam.org/item/M2AN_1998__32_2_153_0.pdf :
  extensive computations favored the planar implication; higher
  dimensional controls detected known counterexamples.

* Guerra and Teixeira da Costa, *Numerical evidence towards a
  positive answer to Morrey's problem*, Rev. Mat. Iberoam. 38
  (2022), 601–614, https://doi.org/10.4171/RMI/1286 .
  Section 5/Table 3 examined 210 three-wave, 980 four-wave and
  980 five-wave configurations using many randomly assigned
  values and approximate RC envelopes. All suspicious planar
  candidates disappeared on refinement. Section 4 gives a
  heuristic relating this to additional rank-one connections
  in planar cubes as the number of waves increases. This is
  NOT a proof of the all-wave theorem. The repository already
  has extensive notes on parity, dyadic peeling and cube
  couplings. More fixed-wave cases are not pursued here.

* Voss, Martin, Sander, Kumar, Kochmann and Neff,
  *Numerical Approaches for Investigating Quasiconvexity in
  the Context of Morrey's Conjecture*, J. Nonlinear Sci. 32,
  77 (2022), https://doi.org/10.1007/s00332-022-09820-x .
  Their magic-plus energy resisted the numerical searches;
  many nontrivial deformations attain its affine energy.
  The companion paper *Morrey's Conjecture for the Planar
  Volumetric-Isochoric Split: Least Rank-One Convex Energy
  Functions*, https://doi.org/10.1007/s00332-022-09827-4 ,
  gives a sharp logarithmic reduction and the convexity
  dichotomy for the smooth split. It identifies several
  distinct candidates on the convex-volumetric branch,
  but does not establish their completeness.

* Important subsequent resolution: Astala, Faraco, Guerra,
  Koski and Kristensen, *The local Burkholder functional,
  quasiconvexity and Geometric Function Theory*,
  https://arxiv.org/abs/2309.03495 (v2, January 2024).
  Corollaries 1.7 and 9.5 prove QC of magic-plus, and
  Theorem 1.8 proves the implication for h convex in the
  additive split. Definition 1.1 uses orientation-preserving
  C^1 diffeomorphisms with affine boundary data. Do not
  re-claim their magic-plus result as a new discovery.

The useful lesson is that a structural transformation and
a canonical energy can succeed where repeated optimization
does not. We now remove the restriction h convex in this
particular nonhomogeneous split, without classifying the
minus-branch candidates.

## 2. Input and conventions

Write s(A)=||A||op, d(A)=det A, K(A)=s(A)^2/d(A)
on GL^+(2). This K is the ratio of the two positive singular
values in descending order. The two-sided proper-rotation
invariance is exactly that used in our homogeneous theorem.

We use the verified result
[polyconvex_of_rankOneConvex](https://github.com/vltanh/lean4-morrey/blob/e0ccdbf939ce39584db1f1bfd41b65ebe092e4d4/Morrey/HomogeneousIsotropic/Main.lean#L72):
every finite-valued nonnegative isotropic positively
p-homogeneous RC function on R^(2x2), p>=2, is PC.
The entire signed homogeneous QC theorem on main is available
for the optional extension in Section 6, but is NOT required
for the new convex-volumetric theorem.

On GL^+(2), RC means the usual convexity on rank-one segments
in that set; it is rank-one convex as a domain because the
determinant is affine on these segments. PC means existence of
a convex function of (A,d) representing the energy when d=det A>0.
An extended-valued convex representative is permitted. We do
not assert a finite extension of W across the singular set.

## 3. Remove the global-domain restriction in the nonnegative homogeneous theorem

**Lemma A.** Every nonnegative continuous isotropic p-homogeneous
RC function E on GL^+(2), p>=2, is PC on GL^+(2).

In fact on every prescribed compact distortion cone
    d(A)/s(A)^2 >= r0 >0
there exists a finite nonnegative isotropic p-homogeneous globally
RC extension that agrees EXACTLY with E there. The cone may have
arbitrary matrix amplitudes.

Choose 0<r1<kappa<r0 (if r0=1 use the same strict choices).
Define on the entire matrix space
    B(A)=(kappa s(A)^2-d(A))_+^(p/2).
This is PC: the convex lift (X,z)->(kappa s(X)^2-z)_+^(p/2)
uses the convex squared operator norm and convex nondecreasing
positive-part power with exponent at least one. B is nonnegative,
isotropic and p-homogeneous. It vanishes for d/s²>=kappa and is
strictly positive for d/s²=r1.

By homogeneity and continuity, on the compact set s(A)=1,
d(A)=r1, E is bounded and B=(kappa-r1)^(p/2)>0.
Choose M>0 so M B>E there. Define
    E_ext=max(E,M B)  on d/s²>r1,
    E_ext=M B         on d/s²<=r1 and at zero.
The maximum uses E only in GL^+(2). A strict uniform boundary
gap gives equality with M B on a neighborhood of each nonzero
interface point. Thus the extension is locally convex along
every rank-one line away from zero: either it is the maximum
of two locally RC functions or it coincides with M B.
It is continuous at zero by the bounded angular range and
positive homogeneity. Every rank-one line through zero is
entirely singular and uses only M B, so its restriction is
also convex. Hence E_ext is globally RC. It agrees with E
on the requested cone because E>=0 and B vanishes there.

The verified homogeneous theorem makes E_ext PC. For any
finite probability law on GL^+(2) of mean A in GL^+(2) with
the correct determinant moment, select r0 positive below all
the distortion ratios of its atoms AND of A. PC Jensen for
this single extension gives Jensen for E on the original law.

This implies PC on GL^+(2) by the ordinary convex roof on the
lifted graph: infimize the weighted E values over all finite
convex combinations with a given lifted mean (X,z). The roof
is convex, bounded below by zero, and agrees with E at all
physical points. Its domain is actually R^(2x2) x (0,infinity):
for every X and z>0, choose H with cof X:H=0 and
det H=z-det X, so X+/-H both have determinant z. Such an H
exists because the determinant quadratic form has signature
(2,2); the three-dimensional kernel of cof X meets both
its positive and negative two-dimensional subspaces
(the X=0 case is immediate). Scaling one of those directions
gives the desired determinant, and H=0 covers equality.
Thus the roof is finite and continuous on that open domain.
This completes the proof of Lemma A.

In particular, the global theorem applies to a much larger
class of singular-on-the-boundary homogeneous energies than
its finite-global statement might initially suggest. The
barrier is an auxiliary positive energy, not an assumption
that the given E itself has a finite extension.

## 4. Shield and exponential transfer: nonpositive log-scale coefficient

**Theorem B.** Let W be continuous, isotropic and RC on GL^+(2),
and satisfy
    W(tA)=W(A)+2c log t,   t>0,
with c<=0. Then W is PC on GL^+(2).

For epsilon>0 form the Shield transform of exp(epsilon W):
$$
E_\epsilon(Y)=d(Y)\exp(\epsilon W(Y^{-1})).
$$
It is positive, continuous, isotropic and homogeneous of degree
    p=2-2 epsilon c >=2.
The exponential is convex increasing, hence preserves RC.
The Shield transformation also preserves RC. In dimension
two this follows directly from the determinant being affine
on rank-one segments and adjugation being linear. Namely,
if Y=(1-t)Y0+tY1 with rank(Y1-Y0)<=1 and positive determinants,
then
    Y^(-1)=[(1-t)d0/d]Y0^(-1)+[t d1/d]Y1^(-1).
The inverse endpoints are rank-one connected, since
    Y0^(-1)-Y1^(-1)=Y0^(-1)(Y1-Y0)Y1^(-1).
Apply RC Jensen to exp(epsilon W) and multiply by d.
No differentiability of W is needed.

By Lemma A, E_epsilon is PC. To transfer this fact back,
take any finite lifted-minors law X_i with positive
determinants d_i, weights theta_i>=0, total one, mean A,
and sum theta_i d_i=d_A>0. The weights
    omega_i=theta_i d_i/d_A
sum to one. Linearity of the adjugate gives
    sum omega_i X_i^(-1) = adj A/d_A = A^(-1).
The inverse determinant average is
    sum omega_i det(X_i^(-1))=1/d_A.
Thus the inverse law is again a lifted-minors law.
PC Jensen for E_epsilon gives, after multiplication by d_A,
    exp(epsilon W(A)) <= sum theta_i exp(epsilon W(X_i)).
Subtract one, divide by epsilon, and let epsilon decrease
to zero. The finite-sum limit proves the original W Jensen
for every such law.

For a continuous isotropic log-homogeneous W one can write
W=h(K)+c log d. Its h is nondecreasing: restrict to the
rank-one shear I+t E12, which has determinant one and K
strictly increasing from one to infinity for t>=0. The
energy along that line is even by its singular-value
representation and convex by RC. Consequently h>=h(1).
Since c<=0, c log d is convex and has an affine lower bound
on d>0. Hence W has a lower affine bound in the lifted
variables. The convex-roof construction from Lemma A is
proper, finite on R^(2x2) x (0,infinity), and represents W
on its physical graph. This completes the proof.

Thus every nonpositive log-homogeneous RC isotropic energy
is PC, including negative energies. This is a new transfer
of the positive homogeneous theorem, not the invalid
assertion that an arbitrary logarithm of a PC energy is PC.

**Another immediate consequence:** for any degree q<=0, a
nonnegative q-homogeneous RC isotropic energy on GL^+(2)
is PC, because its Shield transform is nonnegative and
(2-q)-homogeneous. The same inverse-minors argument without
the exponential/limit proves the assertion. Together with
Lemma A this covers all q<=0 and q>=2 on this open domain.
The isochoric q=0 theorem was already known (Martin, Ghiba,
Neff 2017). No novelty claim for the old subcase.

## 5. Close the entire additive split class (including nonsmooth profiles)

**Theorem C.** Let h:[1,infinity)->R and g:(0,infinity)->R
be continuous. Suppose
    W(A)=h(K(A))+g(d(A))
is RC on GL^+(2). If g is convex, W is PC on GL^+(2).
If g is not convex, h is convex. In either case W is QC
in the orientation-preserving definition of Astala et al.,
using their Theorem 1.8 in the second case.

### 5.1 Exact logarithmic normalization, with continuous h

First suppose g is C², but do not assume any differentiability
of h. Set
    beta=inf_(z>0) z²g''(z).
We prove that beta is finite and that the replacement
    W0(A)=h(K(A))-beta log d(A)
is RC, with W-W0 a convex function of d.

Fix any rank-one line Y(t)=Y0+tH in GL^+(2) on an open
interval. Its determinant d(t) is affine and positive.
Write q(t)=h(K(Y(t))). For each lambda>0,
    q(t)+g(lambda² d(t))
is convex by RC of W under positive dilation.
The second derivative of q is a signed Radon measure
locally on the line (convex function minus C² function).
Its singular part is nonnegative. Its ac density m(t)
satisfies
    m(t)+lambda^4 g''(lambda² d(t)) (d')² >=0
a.e., simultaneously for all positive rational lambda
after discarding their countable union of null sets.
By continuity in lambda this holds for every lambda>0
at the remaining points.

Take the particular line Y(t)=diag(t,1), 1<t<2.
Here K=t and d=t, d'=1. At a point where its ac
density is finite and all the preceding inequalities
hold, the inequalities bound z²g''(z) below by a finite
constant as lambda ranges over (0,infinity). This proves
beta> -infinity. It is bounded above by its value at z=1.

Return to the arbitrary line. Taking the infimum in
lambda, its curvature inequality becomes
    m(t)+beta (d')²/d(t)²>=0.
This is also true if d'=0, by the original inequality.
Adding back the nonnegative singular part proves that
the distributional second derivative of
    q(t)-beta log d(t)
is a nonnegative measure. Hence W0 is RC. Finally
    (g(z)+beta log z)''=g''(z)-beta/z²>=0,
so W-W0 is convex in d, and is PC.

When beta>=0, Theorem B applies to W0 with c=-beta<=0.
Therefore W is PC. In particular this holds when g is
convex.

When beta<0 the same curvature inequality on diag(t,1),
t>1, gives the measure bound
    D²h >= (-beta)/t² dt
on (1,infinity). In particular h is convex (including
the endpoint by continuity). This gives the usual dichotomy
without assuming smoothness of h.

### 5.2 Remove C² of g by averaging logarithmic scales

Take a nonnegative smooth compactly supported approximate
identity rho_j on R (support tending to zero) and put
    g_j(z)=int rho_j(t) g(e^t z) dt.
This is smooth on z>0, being convolution in the log variable,
and converges locally uniformly to g. The energy
    W_j(A)=h(K(A))+g_j(d(A))
is exactly the average of W(e^(t/2) A), so remains RC.

If g is convex then each g_j is convex. Section 5.1 and
Theorem B give PC of each W_j. Jensen on each fixed finite
lifted-minors law passes to W. The shear argument again
gives h>=h(1), and convex g has an affine lower bound,
so the convex roof is proper and gives PC of W on the full
positive-determinant domain. This proves the new statement
for every continuous h and convex g, without smoothness.

If g is not convex, a strict scalar Jensen violation at two
fixed arguments persists for all sufficiently large j.
Thus g_j is nonconvex, its beta_j<0, and Section 5.1
forces h convex. The existing Astala et al. Theorem 1.8
then applies directly to W. This proves Theorem C.

**Further structural corollary (entire continuous split).**
Every RC split W is a sum of a PC split and a nonnegative
multiple of the single magic-plus energy
    W_magic^+(A)=K(A)-log K(A)+log d(A).
Indeed, for convex g the multiple is zero by Theorem C.
For nonconvex g, take the above sequence of smooth g_j
with beta_j<0, c_j=-beta_j>0. Its logarithmic normalization
gives
    W_j = c_j W_magic^+ +
        [h(K)-c_j(K-log K)] + [g_j(d)-c_j log d].
The last bracket is convex in d. The middle profile is
convex by D²h>=c_j/t² dt and is nondecreasing: its
right derivative at 1 is nonnegative since h is
nondecreasing and (t-log t)' at 1 is zero. Thus the
middle bracket is PC, using the convex perspective
(X,z)->||X||op²/z on z>0 and convex nondecreasing
composition on its physical range [1,infinity).
For a global convex lift, replace the perspective argument
by max(1,||X||op²/z).

The coefficients c_j are uniformly bounded: choose a
point t>1 with finite ac second derivative of h where
all countably many measure-density bounds hold, giving
c_j<=t² h''_ac(t). Pass to a subsequence c_j->c>=0.
The two scalar profiles in brackets converge locally
uniformly and preserve their convexity and the stated
monotonicity. Consequently the same decomposition holds
for W. This combines the new convex-volumetric result
with the already known magic-plus decomposition, rather
than claiming the latter as novel. No enumeration of
least energies is needed.

PC is stronger than QC on the convex-volumetric branch.
For the other branch the established magic-plus theorem
supplies Jensen on the orientation-preserving test class.
None of these assertions imply a finite-valued extension
of a singular GL^+(2) energy to all matrices.

## 6. Optional direct QC transfer for arbitrary log-scale coefficient

The full verified signed homogeneous theorem yields another
useful formulation. For c>0 choose epsilon>0 arbitrarily small,
so p=2-2 epsilon c>1 and |1-2/p| is arbitrarily small.
On a fixed compact distortion cone d/s²>=r0>0 choose
    |1-2/p|<kappa<r0.
The global homogeneous RC barrier
    B_p(A)=[s(A)^(p-2)(kappa s(A)^2-d(A))]_+
is the positive part of the reflected signed Burkholder
plus (kappa-|1-2/p|)s^p, both globally QC by the pinned
verified results. It is therefore RC. It vanishes on the
desired cone and is positive on d/s²=r1<kappa.
Using the exact max extension of Lemma A, now with this
barrier, extend the positive E_epsilon of Section 4 to
a globally RC finite p-homogeneous isotropic integrand.
The signed homogeneous theorem gives QC of the extension.

For a smooth orientation-preserving perturbation of the
affine map A with compact support, whose gradient has
compact range in GL^+(2), the map is a global diffeomorphism:
it extends as the affine map outside the support, is a
proper local diffeomorphism and has degree one. The inverse
has compact positive-determinant gradient range and affine
boundary data on the image domain. Apply the extended
E_epsilon Jensen inequality to its inverse, then change
variables. This yields
    avg exp(epsilon W(Du)) >= exp(epsilon W(A)).
Divide the difference by epsilon and let epsilon->0.
Since W is bounded on the compact original gradient range,
the limit proves original-energy Jensen. Together with
Theorem B this works for every real log-scale coefficient.
It also proves the smooth compact-range split result using
Section 5 alone, without citing the external magic-plus
theorem. Do not claim this last limiting argument for
unbounded distortion or inverses without the required
regularity/integrability. The existing magic-plus theorem
has its own stronger admissible-map results.

## 7. Verification, status and recommended direction

The elementary companion
research/audit/volumetric_shield_exact.py was executed locally:
    Exact determinant-affine rank-one and adjugate identities passed.
    Exact inverse-minors reweighting passed.
    Exact logarithmic reduction and magic-minus support identities passed.

These are exact algebra checks, not a substitute for the
extension, convex roof, or distributional proofs above.

**Completed at hand-proof level:** positive homogeneous
p>=2 extension from GL^+(2) to compact distortion cones;
polyconvexity for arbitrary isotropic nonpositive logarithmic
scale dependence; polyconvexity of every continuous RC
convex-volumetric split; and the full continuous split
implication combined with the previously published magic
theorem. The new complement relies only on the verified
nonnegative homogeneous PC theorem, not on the unresolved
anisotropic stress correction.

**Remaining:** genuinely coupled scale/distortion profiles,
arbitrary orientation changes and anisotropy. The entire
unrestricted Morrey problem is NOT solved. The next meaningful
extension would remove the additive split, by finding a
touching support or decomposition for coupled profiles.
Do not assume such a decomposition: supremum or subtraction
operations on the radial and angular dependences require
separate RC justification. This is a new positive direction
motivated by published experiments, not another attempt to
finish the prior Gate 1 by relabeling an equivalent equation.
