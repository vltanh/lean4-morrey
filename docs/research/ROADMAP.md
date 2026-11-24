# Roadmap to completion

## Material-anisotropic scale reduction on GL^+(2) — 2026-11-24

See [OBJECTIVE_ISOCHORIC](IWANIEC_MORREY_OBJECTIVE_ISOCHORIC.md) for the hand proofs. The signed left-SO(2)-invariant degree-two theorem extends to the open positive-determinant cone without requiring any finite extension across det=0. Shield inversion then gives the exact polyconvex representation of every finite, objective, scale-invariant RC energy as a supremum of |Xv|²/det X+k. The entire volume-affine coupling h0(X)+det(X) h1(X), with arbitrary scale-invariant material-anisotropic shape functions, is consequently PC.

For every continuous additive split h(X)+g(det X), with h scale invariant, the maximal finite beta such that g+beta log is convex exists whenever the split is RC. Its logarithmic normalization h-beta log det is RC. This reduction needs no rotational invariance; the beta=0 objective case is now completely PC, including every convex g with a finite limit at zero. For nonzero beta the remaining objective logarithmic gate has arbitrary shape and base; the positive-log stationary-shape case follows from a normalized magic-plus support. The general objective logarithmic gate and genuinely nonlinear shape-volume couplings remain open. These are all-base hand proofs where specified, not Lean-verified theorems. They do not establish unrestricted planar Morrey, or remove the last rotation invariance.

## Literature-guided theorem — entire continuous isotropic additive split on GL^+(2)

The [new volumetric–isochoric theorem](IWANIEC_MORREY_VOLUMETRIC_SHIELD.md)
uses the completed homogeneous result to attack a major class
identified by the numerical literature. Voss et al. (2022) failed
to find a counterexample in magic-plus, and Astala–Faraco–Guerra–
Koski–Kristensen subsequently proved its QC and the entire split
when the distortion profile h is convex (arXiv:2309.03495,
Theorem 1.8). The convex-volumetric branch, including the three
minus candidates and arbitrary other profiles, is the complementary
target. The new result is STRONGER than QC on that branch.

**New theorem:** EVERY continuous RC isotropic
    W(A)=h(K(A))+g(det A), A in GL^+(2),
with g convex is PC, without any convexity hypothesis on h.
The proof uses ONLY our verified nonnegative homogeneous PC
theorem p>=2. First extend any nonnegative p-homogeneous RC
energy on GL^+ to a global finite RC energy agreeing on ANY
prescribed compact distortion cone r=d/s²>=r0>0: use the PC
barrier (kappa s²-d)_+^(p/2), with 0<r1<kappa<r0,
scaled to dominate the original on r=r1. Max inside and
barrier outside. The strict boundary gap gives local RC;
all rank-one lines through zero use the barrier. Global
homogeneous PC and finite-minors tests imply original PC
on GL^+, even if the original blows up near det=0.

**Shield/exponential bridge:** every RC isotropic W with
W(tA)=W(A)+2c log t, c<=0, is PC. Apply the preceding lemma
to E_eps(Y)=det Y exp(eps W(Y^(-1))), which is positive RC
and homogeneous of degree 2-2eps c>=2. For a finite lifted
minors law X_i of mean A, reweight inverse atoms by
theta_i det X_i/det A. Linearity of the 2x2 adjugate gives
the inverse mean and correct inverse determinant moment.
E_eps Jensen becomes ordinary exponential W Jensen;
subtract one, divide by eps and let eps->0. A proper
convex roof gives W polyconvex. Also nonnegative homogeneous
energies on GL^+ of degree q<=0 are PC by Shield.

**Exact logarithmic normalization:** for C² g, even with
merely continuous h, beta=inf z²g''(z) is finite by RC.
On every rank-one line, the determinant is affine and
q(t)=h(K(Y(t))) has a measure second derivative (difference
of convex and smooth); dilate the whole line by lambda
and use the nonnegative curvature of q+g(lambda² d).
Take the infimum in lambda on a common full-measure set
of rational scales, and use positivity of the singular
part. This proves W0=h(K)-beta log d is RC, and W-W0
is convex in d. If g is convex then beta>=0, so W0 PC
by the Shield theorem. Otherwise beta<0 implies h convex
from the diag(t,1) line. Smooth arbitrary continuous g
by averaging log-scale dilations, preserving RC and
convexity of g if present. Pass Jensen to the limit;
nonconvex g forces convex h. Thus the COMPLETE additive
split RC=>QC follows, in the orientation-preserving
definition of the published theorem. Every RC split is
also a sum of a PC split and a nonnegative multiple of
the already established magic-plus energy, by the known
logarithmic reduction on the other branch.

For c>0 an optional direct compact-distortion QC transfer
uses p=2-2eps c near two, the barrier
[s^(p-2)(kappa s²-d)]_+ with kappa>|1-2/p|, and the full
verified homogeneous QC theorem. Apply inverse-gradient
Jensen and the change of variables, then eps->0. No
unbounded-distortion or singular inverse claim for this
particular argument.

These are analytic hand proofs, exact Shield/logarithmic
algebra controls actually executed, no new Lean theorem.
The prior art and the verified input are linked in the
note. **Scope:** a new nonhomogeneous positive-determinant
isotropic class, NOT the unrestricted anisotropic G1 or
general nonhomogeneous isotropic Morrey. G1 remains open.
The literature-guided next target is genuinely coupled
scale/distortion profiles rather than more stress gauges,
fixed wave counts, or numerical counterexample searches.

## GATE 1 — angular radial reweighting and exact terminal-state geometry at degree two

The [new angular adaptive theorem](IWANIEC_MORREY_ANGULAR_ADAPTIVE_SPLITTING.md)
exploits freedom of amplitudes/probabilities while preserving homogeneous
moments. It does NOT yet supply the required universal positive stress.
For finite unit directions v_i, normalize second angular weights to a_i
summing to one and base to b. Generalized feasible states satisfy
    b=sum s_i v_i, s_i>=0, sum s_i²/a_i<=1,
    det b=sum a_i det v_i.
At positive s_i the radial realization is r_i=a_i/s_i,
theta_i=s_i²/a_i; zero s_i with a_i>0 denotes concentration.
This compact state space includes all finite compatible input laws.
Let rho be the minimum of the norm sum at fixed a,b.

**Strict slack gives an exact positive split:** choose first-moment
coefficients positive on all generators of the minimal conic face
containing b, with norm sum<1. If their span contains rank-one H,
perturb s along a coefficient representation of H and a along
h with sum h_i det v_i=cof b:H. Small symmetric variations
b±eps H,s±eps k,a±eps h are feasible. Normalize each child's
angular mass m, scale its base by 1/sqrt(m), and use mixture
weight m/2. The base source is a rank-one Jensen source, angular
mixture unchanged, and resolved second moment strictly increases
by eps² |H|². Every nontrivial ordinary minor-compatible slack
law has such an H. An explicit ordinarily blocked diagonal law
at b=(1,2) was unblocked by radial reweighting; exact norm slack
4257/125000 and both exact children verified.

**Tightness:** rho=1 gives a linear ell with
s_i=a_i ell(v_i)_+, ell(b)=sum a_i ell(v_i)_+²=1. Finite
matrices are v_i/ell(v_i) on ell=1, other angular data
are concentrations on ell<=0. Strict convexity of scalar
square forces EVERY split to preserve this hyperplane and
the finite radii. For an ordinary law, tightness iff its
affine support avoids zero. In particular all ordinarily
blocked states whose affine span contains zero have slack.

**Global optimal decomposition:** maximize integral |b|² over
probability measures on the compact angular state space with
fixed angular mixture and all homogeneous RC Jensen inequalities
from original base to conditional bases. Exact splits improve
the objective. Any inactive concentration submass with zero
determinant moment can be separated and atomized by the complete
degree-two origin theorem, also improving the objective.
Solved states (e.g. base zero, or a contains |b|² at direction b)
can be replaced by atomic states. Every nonsolved optimal
residual is one of three explicit types: (I) tight ordinary
two-sheeted determinant hyperboloid trap on ell=1; (II) slack
determinant-definite 2D mean face with opposite-sign inactive
concentration; (III) tight finite part on ell=1 with
determinant-definite 1D or 2D centered variation and opposite-sign
concentration. This handles concentration rigorously, rather
than assuming bounded radial amplitudes. A specific type III
state has exact negative RC gap -1/16 (two finite diagonals
around I plus concentration at -I). It is NOT a gradient
counterexample. Thus these residuals cannot be eliminated by
the algebraic determinant constraint alone.

**All p>1 hyperplane transfer theorem:** on a compact law
supported on ell(X)=1, homogeneous p-Jensen for ALL RC
integrands already implies the unrestricted RC Jensen tests.
Use weak-* angular laminate realization (proved for arbitrary
angular measures), then scalar strict convexity:
E ell=1, E |ell|^p->1 forces concentration on ell=1 and
uniform p-integrability there. Angular mass outside a positive
ell-direction neighborhood tends to zero, giving uniform
integrability of the full p-moments. On ell=1 the angular
measure determines the full law. Test arbitrary RC functions
by patching their values on a compact range with a convex
p-growth exterior using max. Thus homogeneous G1 at any fixed
p>1 would already settle unrestricted RC Jensen on all affine
hyperplane-supported gradient laws (translate hyperplanes
through zero if needed).

Actual scalar-level conditioning: the signed pushforwards
of Dphi_1 and det Dphi under phi_1 both vanish by primitive
integration. Conditional means vary only in the second row
and each conditional law obeys the determinant identity.
This is a legitimate positive barycenter split, but the
conditional laws need not be actual compatible gradients.
No theorem relating the optimal remaining residuals I--III
to sufficient spatial compatibility was obtained. The
earlier heat/polar signed stress absorption also remains
unproved. Exact rational/symbolic script was executed;
no Lean proof. G1 remains OPEN, not a finite exhaustive
classification or an absorption proof.

## GATE 1 — positive directional marginals, affine-frame calibration, and polar residual

The [new spatial constructions](IWANIEC_MORREY_DIRECTIONAL_FRAME_STRESS.md)
preserve positivity, but do NOT yet close G1. Directional
heat along any e followed by heat of the surviving field along
e-perp gives a PSD full-matrix stress M_e with the correct
Hessian source for every smooth F. It has the exact vanishing
cofactor marginal
    (Y -> Ye)_# (C:M_e)=0.
During the first stage H=D(Ye), and g(Ye) det H integrates
to zero by pullback of an exact two-form for every continuous g.
The second-stage H has rank at most one. Thus all F with a
feasible determinant multiplier depending only on Ye satisfy
global Jensen; no curvature-contrast restriction is needed.
Homogeneous angular pushforward retains the corresponding
integrable weighted marginal cancellation.

**Do not attempt to close G1 by simply averaging these sweeps.**
For the radial plane map phi=x exp(-|x|²/2), p=4, the angular
test det u has cofactor pairing pi/56>0 for EVERY sweep direction.
The Gaussian moment identity is exact. Radial cutoff and
periodization on a large torus preserve positivity uniformly
in e, using the heat L⁴ energy estimate for tails and uniform
finite-time Gaussian convolution bounds. Thus an actual
periodic compatible gradient defeats this particular family
of corrections. This does not refute G1 or Morrey.

**Fully positive affine-frame stress:** let u=B(x)x+b(x),
where the Lipschitz affine-frame map (B,b) has derivative rank
<=1 a.e. and is constant (A,b0) near the boundary of a disk.
Then R=Du-B is rank one. For every C² F the one-forms
DF(B)^T dB and DF(B)^T db are closed by rank-one dependence
of the combined derivatives. Integrate to K,l, with
tr K=F(B), and div(Kx+l)=F(B)+DF(B):R. Boundary flux
equals |Omega| F(A). Consequently the energy gap equals
int int_0^1 (1-t) D²F(B+tR)[R,R] dt dx, a completely
PSD cofactor-free stress for ALL F, independent of F.
This includes arbitrary scalar-parameter affine frames
(arbitrary nested or non-nested level sets, matrix and
translation paths), not just radial scalar stretches.
No universal frame-factorization or approximation is proved.

**Polar decomposition for every smooth compact perturbation:**
write w=u(r n)/r, m=n_theta, Y=w tensor n+w_theta tensor m,
xi=r w_r, zeta=w+w_thetatheta. Then Du=Y+xi tensor n
and Y_theta=zeta tensor m. Radial Taylor and angular
integration by parts give the exact energy gap as a
positive rank-one radial Taylor stress (for RC tests)
plus (1/2) int r D²F(Y)[xi tensor m,zeta tensor m] dtheta dr.
The latter is pointwise cofactor-free, but signed. It
vanishes for affine first-harmonic shells. Its absorption
for general w remains unproved. This is an actual spatial
identity, not an enumeration of angular integrands.

The exact polar/frame algebra and Gaussian calculation
were executed successfully. **G1 remains OPEN.** Neither
the marginal criterion, the affine-frame factorization,
nor the polar decomposition proves the required universal
positive correction. No new Lean verification or priority
claim.

## GATE 1 — explicit spatial cofactor correction; positive absorption remains open

The [new spatial heat-stress exchange](IWANIEC_MORREY_HEAT_STRESS_EXCHANGE.md)
works directly with arbitrary compatible gradients, not a finite
configuration or an assumed integrand classification. For heat
flow X_s=A+Dphi_s, set B_ij=partial_ij phi_s, g=Delta phi_s,
H_j=partial_j X_s, and M_h=sum H_j tensor H_j.
Push spatial tensors to the angular sphere with weight
omega=|X_s|^(p-2) integrated over space and heat time, writing
[T] for the resulting measure. M=[M_h] is PSD and satisfies
the exact angular source equation D_p M=sigma. Its trace
T is bounded by J_p/c_p, J_p=E|X|^p-|A|^p.
A SECOND exact energy identity, via first variation and
spatial integration by parts, gives the signed tensor
    S_ai,bj=(g_a B_b,ij+g_b B_a,ij)/2.
Its cofactor trace vanishes pointwise, and D_p[S]=sigma.
Write P=(B11-B22)/2,R=B12 and split H_j=T_j+V_j with
T_1=[g/2,0], T_2=[0,g/2], V_1=[P,R], V_2=[R,-P].
For PSD G=sum T_j tensor T_j and V=sum V_j tensor V_j,
the exact exchange is S=M_h+G-V. In particular
    D_p[G]=D_p[V], C:[G]=0, C:[V]=C:M.
So the explicit correction [G]-[V] satisfies BOTH linear
requirements of G1 for every compatible field and p>1.
It may fail PSD; no domination permitting full subtraction
of [V] has been proved. Equality is valid at each heat time,
not after multiplying by arbitrary angular weights.

**Uniform negative-stress budget:** with n uniform on S¹,
v(n)=4 D²phi_s[n,n]-g, the exact circle fourth moments give
S=E_n sym((g tensor n) tensor (v(n) tensor n)).
Split the target sym(g tensor v(n)) into its positive and
negative spectral parts. Their pushforwards S_+,S_- are
both PSD and cofactor-free, with D_p S_+=sigma+D_p S_-.
Write U=int omega |g|², T=int omega |D²phi_s|².
Their trace difference is U and the negative mass obeys
    N=tr S_- <= (sqrt(U(4T-U))-U)/2
              <= (sqrt(2)-1) T.
At p=2 periodic Hessian integration gives U=T and the
coefficient improves to (sqrt(3)-1)/2.
This is a concrete signed spatial repair, not positivity
of the original source. The residual source D_p S_-
need not be a compatible gradient law, so the coefficient
less than one does NOT justify a recursive contraction.

**Positive global corollary:** weighted integration by parts
with omega_eps=(|X_s|²+eps²)^((p-2)/2) yields U>=k_p T,
k_p=(p-1)² for 1<p<=2, 4/(p+2) for p>=2.
Thus N<=r_p U with r_p=(sqrt(4/k_p-1)-1)/2. For arbitrary
smooth-off-zero homogeneous angular F with rank-one Hessian
bounds m,L on the sphere, J_F>=m U-(L-m)N. It is QC at all
bases when L/m<=1+1/r_p. At p=2 the threshold is 2+sqrt(3),
and the same unweighted argument applies even to arbitrary
NONhomogeneous C² integrands with global constant rank-one
curvature bounds. This is not a density theorem for
arbitrary RC functions.

The exact heat-exchange, circle-moment and constant checks
were run successfully. Hand proofs, no new Lean result or
priority claim. **G1 remains OPEN:** the cofactor equation
and angular-source equation now have an explicit joint
signed solution, but positivity for arbitrary curvature
remains unproved. Do not claim closure via an unproved
iteration, or replace the main target by the contrast
subclass. The formally verified homogeneous isotropic
theorem remains closed.

## Angular curvature stresses — compact positive-measure equation and uniform moment optimization

The [new angular-stress theorem](IWANIEC_MORREY_ANGULAR_CURVATURE_STRESS.md)
gives an exact law-side formulation for EVERY p>1 and arbitrary
signed homogeneous profiles, without a ray count or tree depth.
For the signed angular p-moment difference sigma, define L_p f
as the Hessian of the homogeneous extension evaluated at a unit
matrix and a unit rank-one direction. Its order unit L_p 1 is
p(1+(p-2)(u:H)^2)>=c_p=p min(1,p-1). Jensen against the
entire homogeneous RC cone is equivalent to a nonnegative
measure mu on S³ x unit rank-one directions with
    int f d sigma = int L_p f d mu
for EVERY C² angular f, and mass <=sigma(S³)/c_p.
Proof: positive functional on the subspace L_p f/L_p 1,
norm-preserving Hahn--Banach and Riesz representation.
The exact homogeneous smoothing theorem removes smoothness.

Equivalently there is a PSD matrix measure M on S³ with
C:M=0 as a measure, C the linear cofactor operator. PSD
and zero cofactor trace are exactly the rank-one covariance
cone (factor the PSD matrix and choose a zero-diagonal
orthonormal basis for the resulting traceless symmetric
form). Write its radial scalar, mixed tangent vector and
tangent tensor as a,b,K_t. The angular equation is
    div_S² K_t-2(p-1)div_S b+p tr K_t+p(p-1)a=sigma,
with cofactor constraint
    (u:C u)a+2(Cu)·b+C:K_t=0.
Trace mass is bounded by the ordinary convex p-power
Jensen gap divided by c_p. Straight Taylor interpolation
of ANY gradient law X=A+H gives the positive measure
    M_0=E int_0^1 (1-t)|A+tH|^(p-2)
                      (H tensor H) delta_direction(A+tH) dt
solving the angular equation. Its remaining defect is
C:M_0, a weighted signed pushforward of 2 det H.
At p=2 gradient compatibility gives zero TOTAL mass
of that defect, not zero as a measure. **Missing spatial
step:** alter M_0 in the kernel of the angular equation
to make cofactor trace zero while preserving PSD. No
proof of universal existence of this correction yet.

**Uniform finite moment optimization:** for a finite
angular configuration D with cube directions, enforce
the stress equations only for polynomials of degree <=n.
This defines closed convex outer hulls C_n(A) decreasing
to the closed angular-laminate hull C_D(A). The constant
test bounds stress mass, and Caratheodory gives <=N+1
stress atoms where N is the number of polynomial tests.
Thus for rational p and algebraic data, distance d_n to
C_n(A) is one finite semialgebraic optimization, with
no lamination-depth variable. The whole-cone approximation
theorem gives a priori n(p,delta), independent of the
rays, root and law, such that for actual hull distance d,
    d_n <= d <= (1+delta)d_n+delta(|A|^p+||w||_1).
Key uniform bound: every useful ray-data separator with
||f||_infinity<=1 gives a finite RC envelope bounded
above by 2^p |X|^p via cube splitting, below by
-15*2^p |X|^p via a coordinate product split of zero.
So one degree bound approximates ALL possible envelope
separators, not one previously known F. At rational
parameters the bound is effective. This replaces the
previous unbounded two-sided tree search by a single
predetermined finite moment optimization at positive
relative accuracy. No exact zero-distance cutoff.

Actual symbolic identities and 85 order-unit rational
bounds passed. The solver is specified, not implemented
or benchmarked. No new Lean theorem, no closure of
homogeneous anisotropic Morrey. The only spatial step
identified above remains unproved; do not present the
positive-measure reformulation as proving the conjecture
or as a finite exact classification.

## Angular realization — exact law-side reduction and uniform finite-depth approximation

The [new angular-laminate theorem](IWANIEC_MORREY_ANGULAR_LAMINATE_REALIZATION.md)
uses the previous finite-ray envelope but does not assume
any regularity of its Hessian. For arbitrary p>1 and finite
unit directions D including the cube-vertex directions,
let L_D,p(A) be the angular p-weight vectors of finite
laminate trees rooted at A with leaves t v_j:
    k_j=sum_{leaf i on ray j} theta_i t_i^p.
The set is convex by randomizing trees at their common root.
For ANY law on those rays with finite p-moment and angular
vector w, Jensen against EVERY homogeneous RC F is
EQUIVALENT to w in closure L_D,p(A). A strict separator
f gives a finite ray envelope even when f is arbitrary
signed data: a product tree at A contains any given B with
weight 1/16, and all remaining vertices can be sent to
the cube rays. Thus a finite lower bound at A forces
finiteness at every root. The RC homogeneous envelope then
violates Jensen, since E_D^f(v_j)<=f_j and w>=0.
This only requires realization of angular moments, NOT
the full gradient law. Add cube directions with zero
law weights when necessary. The finite-law reduction
covers the whole homogeneous anisotropic implication.

**Two-sided computability for finite algebraic data and
rational p:** the l1 distance from w to closure L_D,p(A)
has finite upper certificates from finite-depth trees
(semialgebraic constraints), and lower certificates from
norm-bounded separators and rational angular polynomial
RC minorants of the data. The finite-dimensional convex
distance dual and a shrink/raise strict-slack perturbation
show lower certificates approach the true distance.
Dovetailing terminates to ANY prescribed positive accuracy,
including when the true distance is zero. It does not decide
exact equality. Likewise ray-envelope values for data
admitting a strictly lower homogeneous RC minorant have
two-sided terminating approximation certificates.

**Uniform effective finite-depth theorem, independent of
ray count and arrangement:** for fixed p>1,M,eta,epsilon>0,
ALL homogeneous F with ||F||_{S³}<=M and F-eta |X|^p RC,
ALL closed angular sets D containing the cube directions,
and ALL A admit a tree of depth <=N(p,M,eta,epsilon)
with cost <=E_D^F(A)+epsilon |A|^p. Adding a small convex
homogeneous term supplies this margin for arbitrary F.
For rational parameters N is effectively computable.
Key mechanism: replace a leaf t v by a four-level coordinate
split with mass >=1-4delta on the nearby ray t v', then
send the other vertices to cube rays. This changes depth
by at most eight and costs O(t^p (data error+delta)).
The strict margin bounds the p-moment of every near-optimal
tree even for signed F. This yields joint envelope
continuity under Hausdorff changes of D and uniform changes
of F. Apply the prior uniform angular polynomial net
and a finite direction/base net, compute the depth of a
near-optimal tree for every auxiliary configuration, then
transfer back to the original arbitrary rays and base.
The existence/effectivity proof does not enumerate or
compute these very large finite lists in this turn.

**Remaining gate:** prove actual compatible gradient laws
have the angular membership in (1). The new finite-accuracy
depth bound and distance oracle are not a finite exact
classification and do not settle this membership. There
is no bound uniform as epsilon or strictification decreases
to zero. The 243 exact product-split controls and root
embedding check were actually executed. Hand proofs, no
new Lean theorem or priority claim; homogeneous anisotropic
Morrey remains OPEN.

## MAIN GATE REDUCTION — dense exactly saturated homogeneous envelopes

The [new finite-ray envelope theorem](IWANIEC_MORREY_HOMOGENEOUS_RAY_ENVELOPES.md)
bypasses regularity of extremals and applies to EVERY positively
p-homogeneous finite RC F, p>1, with no symmetry or sign restriction.
Take finitely many rays K_D (including directions of the 16
coordinate cube vertices), prescribe the original F data there,
and define E_D(X) as the infimum of F costs over finite laminates
rooted at X and supported on K_D. Four coordinate splitting
levels ensure a finite upper bound E_D<=2^p M |X|^p, with
M=angular sup |F|. RC Jensen gives E_D>=F. Concatenation
gives RC, positive scaling gives exact homogeneity, and
E_D=F on all prescribed rays. It is the maximal RC function
below the data even among nonhomogeneous competitors.

Off those rays E_D is viscosity saturated: a smooth lower
touching with strictly positive rank-one Hessian would allow
a local max with a slightly raised, strictly rank-one convex
quadratic perturbation of the test, preserving every datum.
This contradicts maximality.

**A.e. Taylor theorem for the entire homogeneous cone:**
the previous weak-Hessian theorem gives DF locally BV. At
Lebesgue points of its ac Hessian Q with singular density
zero, subtract the Taylor polynomial. BV Poincare and dyadic
telescoping of gradient means give mean gradient remainder
o(r); W^(1,1) Poincare and the same telescoping give mean
function remainder o(r²). The rescaled original functions
after subtracting ONLY their affine first jet are separately
convex. Local L¹ bounds give uniform local bounds and
equicontinuity by signed separate-convex interpolation, so
averaged convergence to the Taylor quadratic upgrades to
local uniform convergence. Thus Q is an ordinary second-order
Taylor coefficient a.e. The lower-touching condition then
forces min_{rank H=1,|H|=1} Q_D[H,H]=0 a.e., since K_D
is a finite union of rays of Lebesgue measure zero.

**Exact density of the saturated class:** if D includes
a delta-net of the unit sphere, uniform secant Lipschitz
bounds from the cube interpolation upper bound and equality
of the data yield
    0<=E_D(X)-F(X)<=8*4^p M delta |X|^p
for ALL X. Hence a.e.-saturated homogeneous RC integrands
are dense from above in the entire homogeneous cone.
Proving QC for them is EQUIVALENT to proving general
homogeneous anisotropic Morrey. No smooth-extreme-point
regularity assumption is needed. The ray directions at
any positive approximation accuracy can be chosen uniformly
over the normalized cone. If a strict counterexample
has finitely many gradient atoms, include their directions:
E_D retains their energies EXACTLY and can only increase
the base energy. The violation survives unchanged or
strengthened. There is no finite ray-count bound for
exact Jensen and no finite-depth assertion for envelopes.

**Further global theorem:** for homogeneous p>1, viscosity
saturation on the whole punctured space extends across
zero by perturbing a lower touching with a small nonzero
linear function (DF(0)=0). Comparison with a smoothed,
strictly rank-one convex exterior-data envelope then gives
F(A)=inf of all finite laminate costs rooted at A with
every leaf norm >=R, for EVERY R>0. Hence a globally
viscosity-saturated F cannot be coercive. At degree two,
the earlier coercive determinant-shift theorem for positive
rank-one trace implies that every such globally saturated
F has a zero rank-one direction, without smoothness or
symmetry. This is stronger than the earlier smooth
null-direction conclusion, but requires viscosity saturation
everywhere, not just a.e.

The exact rational checker was actually executed: 625
coordinate-laminate controls and 153 signed interpolation
controls passed. Analytic hand proofs; no new Lean theorem.
**Remaining single full-cone target:** QC of the nonsmooth
a.e.-saturated envelopes. Smooth saturation is not enough;
the new approximants may have angular singularities and
can fail viscosity saturation on obstacle rays. Their
variable determinant multiplier is still uncontrolled.
No universal QC proof or claim of finite exact classification.

## Entire nonsmooth homogeneous cone — weak Hessian recovery and vanishing-ac-curvature rigidity

The [new weak-Hessian theorem](IWANIEC_MORREY_HOMOGENEOUS_WEAK_HESSIAN.md)
covers EVERY finite p-homogeneous RC F, p>1, with no symmetry,
sign, differentiability or angular partition assumption. The
rank-one directional second derivatives are positive measures.
Coordinate and four all-entry rank-one probes give all Hessian
coefficients except the coefficient T of the linear cofactor
operator C. Write D²F=S+T C, with S a matrix measure perpendicular
to C and trace tau=Delta F>=0. Planar quadratic polyconvexity
applied to its density gives |S|<=tau. Differentiate Euler:
    D²F X=(p-1) DF dX.
Contract with C X to recover the missing distribution:
    |X|² T=(p-1)(CX:DF)dX-(CX)·S X.
Therefore the entire D²F is a Radon measure, including the
origin by a cutoff argument, with
    |D²F|<=3 tau+2(p-1)|DF|/|X| dX.

Apply Alberti's rank-one theorem to the BV map DF. The
singular Hessian has symmetric rank-one density and
nonnegative trace, hence is PSD; Euler implies its density
annihilates X. With Q the ac Hessian density, the exact weak
formulation is
    D²F=P+lambda C dX, P>=0,
where a measurable midpoint of the planar quadratic
multiplier interval gives lambda in L¹_loc, homogeneous
of degree p-2. No singular indefinite curvature is needed.
Euler also recovers the ORIGINAL F a.e. from Q:
    DF=QX/(p-1), F=(X:QX)/(p(p-1)).
Thus nonsmooth Hessian singularities do not supply
independent first-order data. This does not imply that
lambda is constant or that P is a convex Hessian.

**Uniform rigidity theorem:** put tau_a=tr Q>=0 and
E_ac=int_(B1) tau_a. For any locally uniformly converging
sequence of RC p-homogeneous F_j with E_ac(F_j)->0,
the limit is zero if p!=2, and
    F=a det_+ + b det_-, a+b>=0
if p=2 (thus PC and QC). Proof uses beta=(p-1)DF:CX/|X|²
from Euler, not an assumed feasible multiplier: the recovery
identity gives |Q-beta C|<=3 tau_a. Scaling and passage in
distributions yield (p-1)DF=beta CX and D²F-beta C>=0
in the limit, even if singular mass becomes ac. The first
identity forces constancy on connected determinant fibers.
Homogeneity gives F=h(det), with separate orientation powers.
The PSD residual is h''(d)[CX tensor CX-2d C].
Testing XJ and XK (J skew, K symmetric off-diagonal)
gives opposite values -4d² and +4d² in brackets,
so h''=0. This yields the classification, including
the exact pure-singular-curvature case.

On the earlier compact signed homogeneous base, this implies
E_ac(F)>=c_p M(F) for all p!=2 (positive c_p by compactness).
At p=2, modulo determinant and after M(F)=1 normalization,
small E_ac forces uniform angular closeness to the SINGLE
normalized polyconvex |det| profile. These results include
all nonsmooth extreme points, not just smooth sectors.

The preceding smooth theorem uses vanishing MINIMUM
rank-one curvature, whereas the new pure-singular
classification uses vanishing ac TRACE. Extremality has
NOT been shown to force that trace to vanish. The remaining
issue is the ac rank-one-degenerate part with variable
determinant multiplier; no universal QC proof is claimed.
Symbolic rank-one probes, Euler recovery and determinant
fiber identities were checked by an actually executed
script. Hand proofs, one external BV theorem, no new Lean
verification or novelty claim. Signed homogeneous isotropic
remains formally closed; homogeneous anisotropic remains open.

## Global extremal rigidity — straight saturated characteristics and degree-two classification

The [new saturated-characteristic theorem](IWANIEC_MORREY_SATURATED_CHARACTERISTICS.md)
studies the full anisotropic normalized homogeneous cone, with
no symmetry or fixed angular polynomial assumption. For C³ RC F
off zero whose minimum rank-one Hessian curvature vanishes everywhere,
write Q=D²F, C=linear cofactor (signature (2,2)), and
P=Q-lambda C>=0. Saturation makes lambda unique and continuous:
every null rank-one R satisfies Q R=lambda C R. Also
D³F[W,R,R]=0 for every W by differentiating the nonnegative
rank-one curvature at a zero. On constant-rank kernel strata
lambda is C¹ by Schur complement/implicit function theorem
(including totally determinant-null kernels using tr S_k=0).

**Global affine-ray theorem:** choose maximal rank of P on
the punctured space or a nonempty open multiplier-level region.
If C restricted to ker P is indefinite at maximal rank,
its regular nulls span the kernel, and differentiating the
kernel relation shows Dlambda[R]=0 for all such R. The
ambient field (X',R')=(R,0) is tangent to the regular null
bundle. In the remaining radical case, differentiate PR=0
and use PSD to get Dlambda[R]=0 and D_R K=0, hence straight
radical characteristics with constant kernel. Both yield
DF(X+tR)=DF(X)+t lambda CR. Vary the initial X in a local
C¹ null section and differentiate:
    P(X+tR)(I+t DR(X))=P(X)+t (CR) tensor Dlambda(X).
This rank-one update is the global continuation identity.
On a regular stratum the RHS retains rank and CR remains
transverse to its range, so no finite endpoint exists.
On a maximal radical stratum a finite endpoint must drop
rank, which can occur for at most one t (a nonzero maximal
minor of the RHS is affine in t). Thus every invertible
point in a chosen nonempty open maximal stratum has an
unbounded affine rank-one half-line; regular case gives
an entire line. Multiplier constant throughout. Homogeneity
p>1 then forces a zero rank-one trace direction.

**Positive global degree-two theorem:** EVERY C³ saturated
2-homogeneous RC F (arbitrary signs and anisotropy) is a
convex function plus a constant determinant, hence PC/QC
at ALL bases. First subtract a determinant to make G>=0
by the complete degree-two origin theorem. For G, Q is
PSD iff its multiplier lambda is zero. If U={lambda!=0}
is nonempty, choose a maximal stratum THERE (lambda stays
constant along a characteristic). The unbounded affine
half-line X+tH has G(H)=0 and DG(H)=0. Taylor gives
    lim G(Y+tH)=q_H(Y)=D²G(H)[Y,Y]/2
for every Y. Rank-one convexity and finite limit force
G>=q_H globally; the affine ray is constant, giving
contact at X. Since H is a global minimum, q_H is convex.
Thus D²G(X)>=D²G(H)>=0, a contradiction to X in U.
The rank-zero case gives a constant determinant directly.

**All noninteger p>1:** for C³ and C^(ceil p) profiles,
global saturation forces F=0. Taylor at H on an unbounded
affine ray gives distinct positive powers t^(p-j), none
equal to 1 or 0, plus a vanishing remainder. Comparing
with the affine function forces F(X)=0 on the whole
chosen open stratum, contradicting its positive rank.

Every smooth extreme point of the compact normalized
signed cone must be saturated everywhere: a strictly
elliptic angular patch admits a nonzero smooth local
homogeneous bump preserving the linear normalizations,
and F±eps bump stay RC. Hence all C³ degree-two extremes
are QC; at noninteger degrees no extreme has the indicated
smoothness. Any general proof via extremality must address
nonsmooth angular profiles. Ordinary smooth approximation
does NOT preserve extremality or saturation, so these
theorems do not close the general gate. They describe
global characteristics for arbitrary null multiplicities,
not a fixed-case or degree enumeration.

Exact cofactor/Schur/continuation identities were checked
by the executed symbolic script. Hand proofs, no new Lean
verification or novelty claim. General homogeneous
anisotropic Morrey remains open; the signed homogeneous
isotropic theorem remains formally closed.

## General homogeneous cone — quantitative compactness and uniform finite angular tests

The [new all-profile quantitative theorem](IWANIEC_MORREY_HOMOGENEOUS_UNIFORM_CONE.md)
covers EVERY signed finite p-homogeneous RC integrand, p>1, with
no isotropy. For a Gaussian matrix Z with independent N(0,16)
entries, let M(F)=E F(Z)>=0. Gaussian rank-one product splitting
gives the uniform midpoint bound
    0 <= (F(X+V)+F(X-V))/2-F(X) <= 4096 M(F)
for all |X|<=2 and rank-one |V|<=1. The all-uniform branch of
a Gaussian mixture has probability (1/8)^4; split that branch
in direction V. Separate coordinate Jensen bounds the other
components. This works for signed F directly.

Multilinear interpolation on [-1,1]^4 and the adjacent-entry
rank-one midpoint tests bound every unwanted mixed monomial
coefficient. One additional rank-one all-entries direction
bounds the sum of the two opposite-pair coefficients.
Thus |F-L:X-k det X|<=529*4096 M(F) on the cube.
Positive homogeneity bounds the linear coefficients, and
the determinant coefficient unless p=2. At p=2 subtract
the canonical determinant coefficient k_*(F) obtained
from the four values at +/-I and +/-diag(1,-1).
For the resulting representative F^#, explicit constants give
    ||F^#||_{S³} <= C_p M(F).
M(F)=0 only for the zero class (modulo determinant at p=2).
Consequently M(F)=1 and the determinant normalization at p=2
define a compact convex base with a uniform Lipschitz bound.
Any strict homogeneous Jensen violation has an extremal
witness on this base; no extremal classification is assumed.

**Uniform finite tolerance theorem for the WHOLE angular cone:**
for EVERY fixed p>1 and epsilon>0 there is a SINGLE finite
collection T_(p,epsilon) of globally strongly RC homogeneous
angular rational polynomials, chosen before F or the test law.
Each normalized F is within epsilon |X|^p of a member
everywhere. The uniform Lipschitz bound supplies common
log-mollification scales in the earlier regularization;
an explicit C³ convolution kernel gives uniform derivative
bounds. Tensor Bernstein approximation with a rational grid
gives a computable degree bound 4n depending only on p,epsilon,
and a vanishing homogeneous convex correction preserves
strong RC. For rational p,epsilon the finite list is
specified by exact semialgebraic rank-one Hessian tests.
No polynomial family is assumed in the original hypothesis.

If every member of T_(p,epsilon) satisfies Jensen against
ANY given compatible law nu with mean A, then every original
signed homogeneous RC F satisfies
    E F-F(A) >= -epsilon M(F)(E|X|^p+|A|^p).
Equivalently every violation larger than this prescribed
relative error is detected by one of finitely many tests,
uniformly over all gradient laws and arbitrary angular
profiles. This strengthens the previous qualitative density
statement to a uniform finite-accuracy bound. It does NOT
bound the gradient witness, prove QC of the test collection,
or produce a finite cutoff independent of epsilon.
The explicit estimates are conservative, and no enumeration
of the large finite lists was carried out. The algebra
checker was actually executed successfully. Hand proofs;
no new Lean result or general homogeneous anisotropic
closure. Do not turn the tolerance result into a claim
that exact Morrey reduces to finitely many tests without
a further theorem.

## General homogeneous cone — exact regularization and positive-trace normalization

The [new global approximation and rigidity note](IWANIEC_MORREY_HOMOGENEOUS_REGULARIZATION.md)
proves a density theorem for EVERY finite-valued positively
p-homogeneous RC integrand, for every fixed p>1 and without
isotropy. Average ordinary mollifications F_t over a log interval:
    H=(1/log(b/a)) int_a^b F_t dt/t.
The Euler defect E=DH:X-pH telescopes exactly to
(F_a-F_b)/log(b/a), so BOTH E and DE become uniformly small
on the unit sphere when b->0 and b/a->infinity. Rehomogenize
G(X)=|X|^p H(X/|X|). The precise Hessian change for V=w+alpha X
at unit X, w perpendicular to X, is
    -E|w|²-2alpha DE:w-alpha² DE:X-(p-1)alpha²E.
It is uniformly o(1)|V|². Repair with a vanishing
positive multiple of |X|^p to get exactly homogeneous,
smooth-off-zero, uniformly strongly RC approximants.
Preserves nonnegativity and all original orthogonal
invariances. This is not ordinary convolution that loses
homogeneity. It works in arbitrary finite dimensions.

**Exact main-gate reduction:** p=1 follows from p>1 by
subtracting a linear support at zero (Kirchheim--Kristensen)
and using the convex powers (F-L)^(1+eps) as eps->0.
The already verified p<1 case is zero. Hence it suffices
to solve the arbitrary smooth strongly RC angular problem
for p>1. Any hypothetical strict homogeneous counterexample
survives with a rational exponent p>1, rational angular
polynomial P in F(X)=|X|^p P(X/|X|), and a rational
piecewise-affine periodic gradient witness. The rank-one
Hessian test on unit spheres is polynomial by the exact
defect identity, so each such candidate is decidable by
real algebraic methods; its energy witness is algebraic.
No uniform degree/size bound, and no unbounded enumeration
is proposed as a completion strategy.

**Positive trace at degree two:** if m=min_{rank H=1,|H|=1} F(H)>0,
no evenness or strict Hessian assumption is needed for a
coercive determinant shift. With M=max_{|X|=1}|F(X)| and
L a local Lipschitz constant, tau=min(1/4,m/(4sqrt(2)L),
m/(16M)) gives F(X)>=c det X + m tau² |X|².
For normalized opposite-det X,Y, connect X to tY,
and form U=(tX+Y)/sqrt(1+t²), V=(X-tY)/sqrt(1+t²),
both rank one. The ratio gap is at least m|U|²>=
4m/(|X|²+|Y|²). The minimizing determinant ratios
are attained away from rank-one because of positive
trace. The midpoint shift gives the global bound.
For EVEN F, both reciprocal connections (X,tY) and
(X,-Y/t) can be used for arbitrary p>1; combine their
inequalities with weights 1/(1+k), k/(1+k), k=t^(p-2).
This gives a signed determinant-power lower support
for ALL p>1, and the uniform estimate
    F(X)>=(m/2)|X|^p+c sign(det X)|det X|^(p/2)
for 1<p<=2. The factor is sharp at p=2 (operator norm).
For p!=2 the signed power is not a null Lagrangian,
so no universal QC inference. Neither lower bound
proves RC of the remainder after subtracting the
coercivity term.

**Affine-plane rigidity, NO HOMOGENEITY:** the earlier
null-plane theorem is now stronger. Any finite RC
integrand affine on a full common-factor rank-one plane
is PC, at every base. Normalize F([a,0])=0. A finite
convex function constant on a whole line is invariant
under that line; use this first on the common-left-factor
plane and then on the first-column plane at fixed b
to get F([a+tb,b])=F([a,b]). Thus F=G(b,det X).
Common first columns at independent b endpoints give
lifted Jensen. Convexity along lines avoiding b=0
bounds G above and below near the missing axis by
values at b±e,b+2e, e perpendicular to b. Uniform
secant-slope bounds give a finite continuous convex
extension across b=0. This proves the original energy
PC with no sign, smoothness, homogeneity or symmetry.

The symbolic Hessian, radial derivative and opposite-ray
identities were actually executed successfully. Hand proofs;
no Lean or publication-priority claim. The new regularization
covers the entire angular cone, but its universal QC gate
remains open. No universal extremal decomposition into
null directions or affine planes has been proved. The
signed homogeneous isotropic theorem is formally closed.

## No rotational symmetry — exact null-ray recession and null-plane classification

The [new rank-one-null theorem](IWANIEC_MORREY_RANKONE_NULL.md)
replaces all rotational symmetry by a precise rank-one degeneracy.
An elementary quotient lemma says a continuous RC function invariant
under translations along a nonzero rank-one H is convex: for every
direction K with cof(H):K!=0 add a scalar multiple of H to make its
determinant zero, then use density of those directions.

For arbitrary p<2, F(H)=F(-H)=0 gives F(X+tH)=O(|t|^(p-1))
by homogeneity and local Lipschitz continuity at +/-H. Convexity
on that rank-one line and sublinear growth at both ends force
invariance. Thus EVERY antipodal null-line subquadratic homogeneous
RC F is convex, without isotropy.

At p=2, even ONE null rank-one ray has an exact finite recession
R_H(X)=lim F(X+tH)/t. It is finite positively degree-one RC and
invariant along H, hence convex by the quotient lemma. It vanishes
on each of the two common-factor rank-one planes containing H:
convexity and homogeneity bound F(K+tH)<=2F(K) there.
Subadditivity gives invariance along their three-dimensional sum,
the kernel of cof(H):X. Thus
    R_H(X)=a_H(cof(H):X)_+ + b_H(cof(H):X)_-,
with a_H+b_H>=0. This gives exact global bounds on the slope of F
along H. For an antipodal zero H=E11, F is independent of entry a
when d=0 and is uniformly C|d|-Lipschitz in a everywhere.
If differentiable at both null rays, subtract the already proved
origin determinant support to make F nonnegative. The two recession
slopes then vanish, yielding ordinary convexity of the shifted F,
hence PC of the original signed F.

**Complete quadratic null-plane theorem:** if F([a,0])=0 for every
a, the recession in a is a universal convex piecewise-linear
function of det[u,b]. Convexity in a and the zero determinant
recession imply exact invariance under a->a+tb. Therefore
F([a,b])=G(b,det[a,b]). For independent b1,b2 choose a common a
with prescribed determinant values, giving lifted Jensen along
the rank-one second-column segment. Uniform boundedness from the
recession estimates gives local Lipschitz extension across b=0
and full convexity of finite G on R² x R. This proves PC at ALL
bases, with no sign or rotation invariance. Covers any common-factor
rank-one null plane, by coordinate changes. If all rank-one
traces vanish, G is independent of b and F is a convex piecewise
linear function of det.

The note also proves the universal trace bound
(2-p)F(U+V)<=F(U)+F(V) for arbitrary rank-one U,V and p>1,
by separate convexity, rescaling, and taking a one-sided limit.
For p>2 this controls the negative part by any rank-one
decomposition; all-zero rank-one trace forces global nonnegativity.
For p<2 it gives an upper bound, and applying RC at V supplies
the complementary lower bound.

These are new hand-level all-base results for degeneracies of
completely anisotropic profiles, not a general solution. Exact
determinant and trace algebra checked locally. Arbitrary positive
rank-one trace and the nonsmooth single-null-ray case remain open;
no universal decomposition into the new classes is proved.
The attempt to extend the one-sided scaled-rotation tangent
calibration to arbitrary p did not close that gate. No new Lean
theorem. The verified signed bi-SO(2) result remains CLOSED.

## CLOSED at hand-proof level — one-sided SO(2) symmetry at degree two

The [new one-sided rotation theorem](IWANIEC_MORREY_ONE_SIDED_ROTATION.md)
removes an entire rotation group, not merely a perturbation of
an isotropic core. For every finite signed positively 2-homogeneous
F with LEFT SO(2) invariance only, RC iff
    F(X)=max_{(v,c) in compact T} (|Xv|²+c det X).
In particular F is PC and QC at ALL bases, with arbitrary material
anisotropy. At a differentiable invertible A, normalize by
G(Y)=F(YA), and diagonalize the symmetric P=DG(I)=DF(A)A^T,
whose eigenvalues lambda1>=lambda2 sum to 2G(I). Align Y e
to t e by a LEFT rotation, where e is the top eigenvector,
t=|Y e|. The rotated matrix and tI are rank-one connected,
so homogeneity and the tangent inequality give
    G(Y)>=(lambda1-lambda2)|Y e|²/2+lambda2 det Y.
Equality at I. The resulting polyconvex supports at all smooth
invertible bases have uniformly bounded vector and determinant
coefficients by testing on rank-one matrices and I,diag(1,-1).
Compact closure gives the exact representation everywhere,
including singular/nonsmooth bases. No right-rotation or sign
assumption. Also valid for right rotations only by transpose.
The note includes an exact representation of the positive part
of any one-sided p-homogeneous RC energy for 1<=p<=2 by
max_T (|Xv|²+c det X)_+^(p/2), via convex power amplification.
This does NOT prove original-energy QC when p<2.

**Additional degree-one theorems:** for arbitrary anisotropic
positively 1-homogeneous RC F, at EVERY invertible A there is
a linear support on the entire region where XA^(-1) has real
eigenvalues. The proof uses the classical separately convex
degree-one perspective theorem on rank-one-generated planes.
It gives original Jensen for arbitrary laws supported in this
region. Together with Kirchheim--Kristensen at rank-deficient
bases, possible failures at invertible bases require complex
relative spectrum. Furthermore, for LEFT O(2) invariance,
normalized derivative P is PSD by reflection and rank-one
convexity. A rotation maximizing P:QY makes QY P symmetric,
so QY has real spectrum (also for rank-one P). The real-spectrum
support then gives a GLOBAL linear support. Dense differentiability
proves convexity of EVERY finite degree-one RC F with only
left O(2) invariance. For proper rotations alone this proof
works at positive-semidefinite normalized derivatives, not at
all bases.

Exact symbolic checks executed successfully. Analytic hand
proofs, no new Lean theorem or novelty claim. The entire
signed bi-SO(2) homogeneous theorem is formally verified.
The one-sided degree-two and left-O(2) degree-one gates are
closed at hand-proof level. Remaining: arbitrary anisotropy,
and other exponents with one-sided proper rotations. The main
target remains all positively p-homogeneous RC=>QC, not a
degree-by-degree or fixed polynomial enumeration.

## Anisotropic advance — full-matrix half-space projection and QC gluing

The [new half-space projection theorem](IWANIEC_MORREY_FULL_MATRIX_HALFSPACE.md)
imposes ANY full-rank linear gradient constraint ell(X)=B:X>=0
at a base with ell(A)>0. Minimize the scalar periodic obstacle
functional int |B grad rho|²/2+ell(X)rho over rho>=0.
The projected vector map is zeta=phi-B grad rho. Its L²
projection property follows from the obstacle variational
inequality, giving H¹ regularity by translation contraction.
Invertibility of B gives rho in H². Complementarity and the
Sobolev zero-set derivative property then give the EXACT
selection Z=X or ell(Z)=0, with ell(Z)>=0. The residual
ell(X)-ell(Z) is bounded, so the standard linear elliptic
L^q estimates give the projected map W^(1,q) for all finite q.
No Lipschitz claim is made.

The new strong identity is int Ze·(X-Z)e=0 for EVERY spatial
direction e, by integration by parts to int ell(Z)D_ee rho,
which vanishes pointwise. The projection also preserves
J:(B^(-1)X) pointwise and contracts every convex function
of ell(X), since the original ell has zero conditional mean
on the set where the pressure is positive.

**Global QC gluing:** take Q0 to be a nonnegative spatial
quadratic form plus determinant/affine terms and arbitrary
convex functions of ell and the preserved skew scalar.
For any continuous QC Q1 of polynomial growth with Q1<=Q0
on ell=0, define G=max(Q0,Q1) on ell>0 and G=Q0 on ell<=0.
Then G is QC, by the projection pointwise comparison
G(X)>=Q0(X)+Q1(Z)-Q0(Z) and the three contraction/invariance
properties. This allows genuinely full-rank constraints,
not just scalar rows, and arbitrary QC branches.

For B=I, using Q0=|Im z|^p and Q1=(det_+)^(p/2) yields
explicit nonnegative anisotropic non-PC QC integrands for
ALL p>=2; the corrected three-atom minors witness at I
works for every exponent. For p=2 the energy is squared
skew part/4 (in entry-difference coordinates) plus the
positive-definite symmetric determinant truncation.
Using Q0=M_p|Im z|^p and Q1=B_p instead (the verified
signed Burkholder) gives QC nonconvex anisotropic energies
for all p>1, with an explicit four-atom minors witness for
1<p<2 by a vanishing-mass determinant repair.

The note also gives a degree-demotion quantitative origin
bound for arbitrary smooth p-homogeneous anisotropic F:
with rank-one ellipticity m and full Hessian bound M on
the unit sphere, put m'=m-M|p-2|(3p+1)/(p(p-1)) and
K(p)=|p-2|/p+(2^(|p-2|/2)-1)/2. If m'>=0 then
E F(X)>=(m'/2-2M K(p)/(p(p-1))) E |X|^p at zero.
For each positive m/M this proves the original signed
origin Jensen on an open exponent interval around two,
without any closeness to isotropy. Not a universal
exponent closure; the main direction is the new
full-matrix spatial calibration, not an exponent ladder.

The exact algebra checker was run successfully. These
are hand proofs, not Lean-verified new theorems. The
general homogeneous anisotropic gate is open; no
universality of the gluing class has been established.
The homogeneous isotropic theorem for all signed p>0
is formally CLOSED on main.

## CURRENT DIRECTION — remove isotropy first (homogeneity retained)

**Verified baseline:** main at
[17fd1c3](https://github.com/vltanh/lean4-morrey/commit/17fd1c3a83f0c96fbc25a5d916187290f6fc0098)
contains Theorem A, the full signed homogeneous isotropic
RC=>QC theorem for every p>0.
[Lean CI passed](https://github.com/vltanh/lean4-morrey/actions/runs/45424739241).
The signed homogeneous theorem is CLOSED, not a hand
candidate awaiting audit. The nonhomogeneous isotropic
attack below is paused at the user's request. The new
target is arbitrary positively p-homogeneous RC=>QC
without isotropy, at every base.

The [new anisotropic note](IWANIEC_MORREY_ANISOTROPIC_ORIGIN_RECTIFIED.md)
contains two positive theorems:

**Complete p=2 origin gate, including arbitrary signs:** every
finite positively 2-homogeneous F satisfying laminate Jensen
at zero (even just two-step laminates with <=3 atoms) has
a global determinant lower support F>=c det. Proof: opposite
determinant rays can always be joined by positive rescaling
to rank-one connected matrices. Balance their determinant
to get a rank-deficient barycenter, and dilute that barycenter
against its small opposite to obtain a zero-base laminate.
Degree two cancels the rescaling in the weighted energy,
forcing a nonempty interval of determinant multipliers.
This proves QC at zero for ALL such integrands and gives
an exact finite origin witness bound. It also reduces the
entire signed degree-two all-base problem to nonnegative
ones by subtracting c det, a null Lagrangian. The all-base
degree-two theorem remains open. Do not confuse the weaker
origin-only homogeneous Morrey question of Cassese with
our all-base target.

**Global all-base QC for the classical anisotropic non-PC
obstruction and its arbitrary nonlinear shear extensions:**
for F([[a,b],[c,d]])=a_+ d_+ + q(b,c), global RC iff QC iff
both q and q+bc are convex. Necessity follows by rank-one
lines with arbitrary off-diagonal directions. Sufficiency
uses ONE scalar projection of the first row onto a>=0,
obtained from the formalized compact constraint theorem
by order-preserving Lipschitz contraction. The determinant
of the mixed projected/original two-row gradient has the
right mean. After centering, the energy gap is at least
E[f(B,C)+P C]. Minimize f(p,y)+p y in y and use the tangent
slope alpha(p)=f_B(p,y(p)). Convexity of f and f+BC implies
alpha'>=0 by a two-Hessian inequality. The nonlinear
directional scalar projection sign integrates the tangent
term with the correct sign. Smooth approximation removes
regularity and strictness. This proves QC at ALL bases of
Guerra--Kristensen Proposition 3.7 and all its p>=2 powers,
despite its exact non-PC witness. It also covers the
minimal coupled shear q=(b-c)^2/4 and arbitrary convex
q with q+bc convex, without fixed-degree or homogeneity
constraints on q. Hand proofs and actual symbolic/rational
checks; no new Lean theorem or novelty claim.

**Main remaining gate:** arbitrary angular profiles on the
normalized matrix sphere, with homogeneity retained.
Nonzero bases and p!=2 origins have not been settled
in general. No universal completeness of the new
anisotropic projection generators is proved. Avoid
another ladder of polynomial degrees or local bounds.

## Exact energy-dependent tail budget and target-composition compatibility

The [new determinant-tail and spatial weighting note](IWANIEC_MORREY_TARGET_WEIGHTED_TAIL.md)
removes the smoothing error from the previous transport bound.
For any C³ isotropic RC F and any smooth contact path through
the base, let U(s)+V(s)delta be its angular supporting line on
each shell, and Q>=0 the angular remainder. Define
N(r)=E(s-r)_+-(s_A-r)_+,
T(r)=E[(s-r)_+delta]-(s_A-r)_+delta_A.
The exact original-energy identity is
    E F-F(A)=E Q+integral (U'' N+V'' T).
The known K_r tests give |T|<=rN, so an explicit sufficient
budget is E Q + integral (U''-r|V''|)_+ N
>= integral (r|V''|-U'')_+ N.
No global log-Lipschitz estimate or smoothing error is needed.
This is not a proof of the sufficient budget for all F/laws.

**Spatial improvement at zero base:** any periodic Lipschitz
u satisfies int q(u) det Du=0 for every bounded Borel q,
by the determinant null Lagrangian applied to target
compositions. Thus positive and negative determinant mass
balance even after pushforward to target values.
The QC entropy calibrations s²/2 ± d log s follow directly
from positive truncated-determinant integrals.
For any C¹ target transformation with B=DT(u), apply them
to T composed with u. The result is
    |int det B d log s| <= (1/2) int s(BDu)²
                          +(1/2) int |det B d| log kappa(B).
Singular-matrix determinant products are continuously zero.
For conformal target transformations with holomorphic
derivative h this gives the exact weighted inequality
    |int |h(u)|² d log s| <= (1/2) int |h(u)|² s²,
including its polarized cross-moment version for all
holomorphic polynomials at once. These constraints depend
on spatial/target information, not merely on the radial law.
They do not imply unrestricted localization by arbitrary
nonnegative target weights without distortion costs.

The symbolic truncated-log and moving-ray identities and
15 full-moment exact tail identities were actually checked.
The universal energy-dependent compensation remains unproved;
do not call this closure of the isotropic gate. No new Lean
theorem, and no fixed-wave/degree enumeration is proposed.

## Positive transport advance — compatibility across arbitrary spectral scales

The [weighted spectral transport theorem](IWANIEC_MORREY_WEIGHTED_SPECTRAL_TRANSPORT.md)
extracts an actual gradient-compatibility estimate from the formalized
truncated determinant. Push positive and negative determinant mass
onto log(s), s=operator norm, and add the opposite base determinant
atom to balance the masses. For all bases and all bounded compatible
gradient laws the unnormalized optimal log-radius transport cost is
    W1 <= (E s²-s_A²)/2 + log(2)(E|det X|+|det A|).
Proof: for any 1-Lipschitz g, exponentially smooth after shifting by
log(2), obtaining h'+h''=g' and |h-g|<=log(2). The integrands
s²/2 ± det X h(log s) satisfy the exact affine-shell QC criterion.
Their Jensen inequalities and transport duality give the result.
For smooth RC F at rank-deficient bases, this yields the original
energy estimate
    E F-F(A) >= (m/2) E|X-A|² - L_R W1,
where L_R bounds the log derivative of f_delta(s,0)/s.

The same note extends determinant pairing from zero determinant
to EVERY base d0. Couple the measures (det-d0)_+ nu and
(d0-det)_+ nu. For each pair independently select a common
column radius, inflating its spectra at fixed determinant only
if necessary, while remaining in the original operator ball.
Rank-one average to determinant d0; apply scalar convexity on that
fiber to the resulting mean smaller conformal modulus bar j.
For rank-one Hessian bounds m,M the exact comparison is
    E F-F(A) >= (m/2) E|X-A|²
      -(M-m)/2 (I_cost+4(j_A²-bar j²)_+).
Both intermediate variances cancel. For no inflation and
adequate fiber modulus the original nonsmooth theorem follows.
Optimal rank-one joins for overlapping spectra are explicit;
the optimal bounded pair inflation radius at zero has a
closed scalar formula, allowing an actual transport optimization
over all scales rather than a fixed common radius.

Symbolic identities and 64 exact rational controls executed.
This is positive progress for unmodified integral Jensen, not
closure: finite logarithmic cost does not imply zero spectral
inflation or an adequate fiber modulus at nonzero bases.
The remaining universal step requires stronger control of
the energy-dependent transport cost from gradient compatibility.
No new Lean theorem or novelty claim. The determinant-square
normal-form gate and full isotropic Morrey remain open.

## Positive unamplified Jensen — spectral shells and determinant transport

The [spectral-gap theorem](IWANIEC_MORREY_SPECTRAL_GAP_JENSEN.md)
gives a direct determinant-fluctuation comparison for EVERY
isotropic RC F, without homogeneity. At radius r, H_r(d)
=F(diag(r,d/r)) is convex in d by rank-one convexity. The
constant-determinant shear monotonicity gives F(X)>=H_r(d)
whenever r belongs to the singular-value interval I(X).
Thus if a common r is outside the open base interval,
ordinary integral Jensen follows, even for nonsmooth F.
In particular ALL constant-operator-norm gradient laws
obey unmodified Jensen, including determinant sign changes.

For C² F with rank-one Hessian bounds 0<=m<=M, set
Q_r=(|X|_F²-r²-d²/r²)/4. Integrating shear Hessian bounds
compares F-H_r with 2m Q_r and 2M Q_r. Jensen of H_r
contributes POSITIVE determinant variance m Var(d)/(2r²).
The variance cancels exactly against the corresponding
term in E Q_r-Q_r(A). Hence for all minor-compatible laws:
    E F-F(A) >= (m/2) E|X-A|_F²
      -(M-m)/2 (E[r²+d²/r²-|X|_F²]_+
                    +[|A|_F²-r²-d_A²/r²]_+).
The loss depends on spectral interval mismatch; with common
Hessian bounds it can be optimized over r² by scalar convex
optimization outside the base interval. This complements
the determinant-only stabilization estimate.

Common-column spectral compression permits a comparison radius
inside the base interval if the mean shear budget suffices.
A multiscale determinant-mass transport theorem at rank-deficient
bases permits arbitrarily many distinct radii if positive
and negative determinant masses can be coupled across
overlapping intervals. No assertion that all gradient laws
admit these calibrations or transport couplings is made.
These are positive unmodified Jensen results and a quantitative
all-law estimate, not closure of the general gate.
972 pointwise and 48 full-moment rational controls and
symbolic identities were executed successfully. Hand proofs,
no Lean or novelty claim. The previous determinant-square
normal-form gate remains open. Avoid a fixed-case ladder;
the unresolved issue is mixing different spectral scales
using actual gradient compatibility.

## POSITIVE general isotropic reduction — determinant-only stabilization and two convex branches

The [new determinant-stabilization theorem](IWANIEC_MORREY_DETERMINANT_STABILIZATION.md)
applies to EVERY C⁴ strongly rank-one-convex isotropic integrand,
without homogeneity or separated profile. On each bounded test
ball B_R, F+C_R det² is polyconvex, with an explicit coefficient
C_R=M4/24+(M3/2+R M4/6)²/(4m), where m is the strict
rank-one Hessian margin on B_(3R), and M3,M4 are stated spectral
derivative bounds. It has touching poly-affine supports using
only one complex coordinate and determinant, with a strict
quadratic margin in that coordinate.

The key elementary fact is the constant-determinant shear
line z=sqrt(d)+it,w=t. For d>=0 the restriction
g_d(t)=f(sqrt(d+t²),|t|) is even convex; hence F on the
determinant-d fiber agrees with a convex function of w.
Reflect for d<0. This gives the ORIGINAL integral Jensen
inequality for all constant-Jacobian gradient laws, arbitrary
finite-valued isotropic RC F, all bases, no smoothness.
For smooth strongly RC F, determinant Taylor estimates and
this strong fiber convexity give
    int F(X)-F(A) >= (m/4) int |X-A|_F²
                       - C_R int (det X-det A)²
for EVERY bounded compatible law and every base, without
exponential amplification. The determinant is allowed to
change sign. The remaining cost is explicitly isolated.

**Exact global reduction of the entire finite-valued isotropic
problem:** it suffices to prove QC of every globally RC function
    max{p_+(|w|,det X), p_-(|z|,det X)} - (det X)²,
where both p_± are finite convex functions of two variables,
nondecreasing in their modulus argument. The determinant
coefficient is fixed to one. Construct the two convex branches
by taking suprema of the above supports on an enlarged test
ball. Repair global RC outside that ball with a convex radial
term b(|X|_F²-4R²)_+², zero on the original test ball;
this term has an identical convex representation in either
branch's variables. Local rank-one convexity on overlapping
interior/exterior regions yields global RC. Scaling the
energy gives the fixed coefficient. Every hypothetical
strict Jensen violation of the original arbitrary isotropic
F survives smoothing, strictification and this construction.

This is not another homogeneous-exponent or finite-case
ladder. It is a structural normal form for the WHOLE gate.
The determinant cost is not eliminated yet. No claim of a
general isotropic proof or new Lean result; 4050 exact rational
support controls and the symbolic checker passed. The signed
homogeneous audit is separate. Prior literature on planar
incompressible isotropic elasticity is acknowledged. The new
theorems are independent of the signed homogeneous candidate.

## POSITIVE nonhomogeneous theorem — uniform exponential quasiconvexification on bounded ranges

The [new integral Jensen theorem](IWANIEC_MORREY_NONHOMOG_EXPONENTIAL.md)
is an all-base, all-gradient positive result, without any
homogeneity or separated-profile assumption on F. For every
C² uniformly strictly rank-one-convex isotropic F and every
finite R, there are lambda_R>0,kappa_R>0 such that for EVERY
lambda>=lambda_R, EVERY base A in the radius-R ball and EVERY
compatible gradient X=A+Dphi in the same ball,
    int (exp(lambda(F(X)-F(A)))-1)/lambda
       >= kappa_R int |X-A|_F².
Thus a SINGLE smooth exponential reparametrization of F is
strongly QC on the entire bounded gradient range. In particular
the ORIGINAL energy obeys the uniform weighted Jensen inequality
int (F(A)-F(X))_+ <= C_R int(F(X)-F(A))_+,
with C_R=exp(lambda_R osc_{B_R}F), even with a strict quadratic
margin. The constants are chosen before the gradient test, not
for one fixed witness.

Proof uses three published results: Conti--De Lellis--Müller--
Romeo connected-set polyconvexity, Heinz's arbitrary isotropic
set theorem, and the Ball--James transition-layer estimate for
incompatible compact sets (planar incompatibility criterion).
Subtract a small nonnegative smooth spectral penalty vanishing
on the base orbit. The resulting enlarged low-energy sublevel
is compact lamination convex on a larger ball. Support its
base component in the lifted minors space. The penalty makes
the tangent spectral Hessian of the energy minus the normalized
support strictly positive; exponential curvature controls the
normal direction. Adjust the determinant coefficient slightly
to obtain positive phase-control coefficients. Critical bases
are zero or conformal/anticonformal and admit explicit quadratic
or polyaffine calibrations; all are covered. This gives a strict
local quadratic Jensen margin. Isolate the base component by a
clopen spectral band (no component-count restriction); the
complement is incompatible. The transition-layer estimate
bounds excursions into that complement by positive-energy
transition mass. A sufficiently large exponent pays for those
excursions. Strong Jensen is open in the base via C² Taylor
estimates, so compactness gives a uniform exponent for all bases.

**Literature correction:** Heinz, WIAS 1637 (2011), Theorems
7.2--7.3, already proves the arbitrary disconnected isotropic
set theorem, including the previous rank-deficient supremal
conclusion. The previous truncated-determinant proof is an
alternative proof at those bases, not a new general-set result.
The new theorem is an integral weighted/reparametrized
Jensen result, not simply a support theorem.

Exact spectral algebra checker executed successfully. Hand
proof using published results; no Lean verification or novelty
claim. **Remaining target: remove the reparametrization**, or
prove the weight can be reduced to 1 for the original F.
No proof that lambda_R can tend to zero is supplied. General
isotropic Morrey remains open. No new obstructions or restricted
exponent/wave ladder is the focus of this work; the user's signed
homogeneous audit/formalization is separate.

## Nonhomogeneous main result — spectral-component selection at all bases, rank-deficient supremal Jensen

The [new spectral-component theorem](IWANIEC_MORREY_SPECTRAL_COMPONENTS.md)
uses the formalized truncated determinant and the published
connected isotropic set theorem of Conti--De Lellis--Müller--Romeo
(2003). For every compact SO(2)xSO(2)-invariant lamination-convex K,
its connected components correspond exactly to components of the
union of singular-value intervals I(X)=[|delta(X)|,s(X)].
Each fiber at a common possible column norm is path connected:
proper rotations align one column, then use a rank-one segment.
Each component is polyconvex by the published theorem.

For ANY compact gradient law supported in K (or a correct-minors
law satisfying every K_r^± test), let R be its largest support
operator norm and J=[a,b] the component of the interval union
containing R. If a=0, the entire law and its mean belong to the
single connected component K_J. If a>0, J has fixed determinant
sign sigma; gap radii r tending to a from below give a strictly
negative K_r^(-sigma) average, forcing sigma*delta(A)>=a.
The base interval must lie in J with that orientation.
At rank-deficient bases the second case is IMPOSSIBLE. This
removes connectedness for the rank-deficient-base QC hull
assertion, for arbitrarily many components.

**New theorem for EVERY finite-valued isotropic RC F, without
homogeneity:** F(A)<=ess sup F(X) at every rank-deficient base
and every compact gradient law. Apply component selection to
a norm-truncated energy sublevel. For strictly RC F, saturation
of this supremal inequality forces all energies equal, by
interiority of the lifted minors hull. This is a positive
all-profile SUPPORT-level result, not integral Jensen.
A law with positive mass above F(A) can still have mean
energy below F(A); the remaining step is a weighted Jensen
inequality, not another component-count ladder.

**STOP RULE for fixed componentwise heat:** start from
u=(v,v²), v=cos x+cos y. det Du=0 initially but Fourier decay
creates a nonzero Jacobian at t>0. The already polyconvex
energy (det X)²+||X||_F²/1000 has an exact heat-energy INCREASE
of 99/128000 at t=log 2. Therefore universal solvability of
the previous sufficient exact-two-form PSD criterion is
false, even for smooth uniformly strictly RC PC functions.
The criterion remains valid where feasible. Exact checker
executed successfully. Hand proofs, no new Lean verification.
General nonhomogeneous isotropic integral Morrey remains open.

## STOP RULE — full-vector L² projection is not a universal energy descent

The [new exact normal-stress obstruction](IWANIEC_MORREY_VECTOR_DESCENT_NOGO.md)
refutes the last proposed direct energy-decreasing use of the
operator-ball projection. Even for the convex isotropic energy
F=||A||_F^4 it can strictly INCREASE the gradient energy.
The actual compatible projected map is locally (r-1,(4/5)theta),
extended periodically by Kirszbraun. A compactly supported
normal stress certifies its exact L² projection status;
differentiation gives strictly reversed energy. No abstract
spectral law, numerical projection, or grid is involved.

More generally for EVERY C³ isotropic F, descent for all
operator-ball radii at zero affine base would force
f_st+(t f_s-s f_t)/(s²-t²)=0 at every s>|t|.
The proof realizes arbitrary relevant compatible third jets
on the saturated operator-norm sphere by an analytic
Cauchy problem. Violation of this PDE at any interior
spectral pair gives an actual periodic projection reversal.
Rank-one convexity does not imply the PDE. The exact
checker passed. The valid full-vector boundary selection,
quadratic signs and QC-extension theorem are unaffected.

**Historical direction (universal heat feasibility refuted above):** exact
two-form heat-flow dissipation for arbitrary smooth
isotropic profiles, extending the approach of
Bruno--Pasqualotto (arXiv:2608.06367). Section 4 gives
two explicit 3x3 PSD tests for two scalar angular-form
potentials, with no fixed exponent or polynomial degree.
Pointwise feasibility follows from quadratic polyconvexity;
global integrability of the correcting form is NOT proved.
Do not treat this as a completed general theorem. Avoid
further fixed-L²-projection energy-descent attempts,
unshifted affine-shell completeness, or another ladder
of restricted exponents. General isotropic Morrey remains
open. The signed homogeneous audit/formalization is separate.

## Nonhomogeneous main attack — full-vector operator-ball projection

The [vector projection theorem](IWANIEC_MORREY_NONHOMOG_VECTOR_PROJECTION.md)
is a hand-proved analytic extension of the scalar projection
mechanism. For arbitrary finite-dimensional vector maps,
project the periodic part in L2 onto maps whose full
gradient has operator norm <=R, with the same affine base.
**Exact boundary selection:** the projected gradient
equals the original gradient or has operator norm exactly R,
almost everywhere. The local proof uses a shifted affine
inner ball, Kirszbraun's Euclidean extension theorem to
fill a thin annulus, and a strict improvement of the
projection objective if an interior-gradient noncontact
point exists. Translation variations give the simultaneous
directional signs int (Dv)e dot (Du-Dv)e>=0 for every e,
and the corresponding squared-gradient contraction.

This clips the whole compatible matrix field at once, not
independent scalar output rows. The new projection-max
theorem takes the maximum over the entire operator-norm
sphere or the original interior matrix, of arbitrary
polyconvex stacked [X;Z] calibrations plus a nonnegative
quadratic directional correction. All mixed minors of the
stack have the correct mean. A further extension theorem
allows ANY already QC core on the closed operator ball
(localized Jensen only), and gives a globally QC exterior
extension via a convex boundary supremum and determinant.
The spectral form for a mixed-minor calibration is an
explicit scalar clamped quadratic; the exact local constants
and 792 rational boundary checks passed.

**Historical goal (direct universal energy descent refuted above):**
energy-decreasing comparison with the full-vector projection,
or global touching lower supports
using its boundary calibrations for arbitrary isotropic RC F.
The new lemma does not say Du-Dv is rank one or provide
arbitrary nonlinear matrix-potential signs. No universal
calibration existence or full isotropic QC theorem is
claimed. No new Lean theorem or novelty claim.
Avoid another sequence of separated-curvature subclasses,
fixed wave counts or projection counts. The signed
homogeneous audit remains separate.

## Nonhomogeneous follow-up — arbitrary separated angular curvature and quantitative mixed-curvature bound

The [new angular-curvature theorem](IWANIEC_MORREY_NONHOMOG_ANGULAR.md)
proves RC=>QC for **every** finite-valued profile
f(s,delta)=U(s)+V(s)delta+H(delta), with arbitrary nonlinear
convex H and no homogeneity, sign, smoothness or growth
hypothesis. RC yields U''>=s|V''| and two explicit conformal
boundary inequalities involving H'_±. Conversely these
conditions suffice even **locally on a bounded spectral sector**.
At base (r,t), take a supporting slope of H, start the
positive truncated-determinant integral at radius r, and
use separate radial convexity to bound the starter on every
smaller radius. This proves a global-on-the-ball touching
minorant, including nonsmooth and conformal bases.

For EVERY smooth isotropic RC profile on S_R, freeze angular
curvature at the outer shell, and repair its radial profile
by the explicit convex correction
C(s)=M(Rs²/2-s³/6)+Ns^4/24, with M=sup|f_sδδ|,
N=sup|f_ssδδ|. The localized theorem gives a direct
all-gradient Jensen deficit estimate (9), in particular
deficit <=(13/27)M R³+N R^4/24. The bounds are uniform in
wave count and atom count. Symbolic and exact rational
checks actually passed, including a nonsmooth example and
a signed RC quartic.

**Do not overstate:** these proofs use the unshifted
affine-shell cone, whose universal completeness was already
refuted. They give exact nonhomogeneous positive results
and a quantitative estimate, not a proof for arbitrary f.
The general target remains the broader projection-based
spatial calibration or a genuinely new all-gradient
inequality. No new Lean theorem. The signed homogeneous
audit/formalization is separate.

## Nonhomogeneous follow-up — arbitrary-multiplicity projection-max theorem

The [mixed-minor projection note](IWANIEC_MORREY_NONHOMOG_PROJECTION_MAX.md)
independently gives a four-matrix affine-shell separator at the
**rank-one base diag(1,0)**, with exact all-radius tests and
strict gap >1/420 for a rotationally averaged translated L.
It complements the concurrent three-spectral-atom no-go
at the anticonformal base J below. The exact four-atom law
also has correct full matrix/minor moments. Conditional on
the signed homogeneous candidate, it passes all homogeneous
isotropic RC tests as well; simple positive/supremal closure
of the homogeneous results, PC and affine-shell functions
cannot settle arbitrary nonhomogeneous isotropic RC.

An elementary alternative proof establishes directional convex
order of the scalar projection by its order/mean preservation
and translation equivariance; linearization gives the gradient
sign for convex ridge potentials. The concurrent note below
proves the stronger sign for arbitrary convex C¹ potentials.

**Projection-max closure theorem (arbitrary N):** constrain
any finite family of scalar output combinations l_i A+b_i
to arbitrary compact convex gradient sets K_i. Take the
maximum over the boundary-or-original auxiliary rows of an
arbitrary polyconvex stacked (2+N)x2 calibration plus the
nonlinear projection-sign corrections. This is globally QC:
fix a maximizing tuple at the base and independently project
the active scalar potentials, so the entire stack is a
compatible gradient with all mixed minors preserved.
This generalizes the one-row determinant calibration to
arbitrary simultaneous constraints and nonlinear mixed-minor
calibrations; N is not fixed. The proof works for arbitrary
convex C¹ potentials using the concurrent sign theorem,
or for ridge sums by the independent elementary proof.

No universal support completeness claim is made. The earlier
affine-shell continuation problem is refuted, not a pending
ODE gate. Continue toward general isotropic RC=>QC with
the broader spatial mechanism, not an enumeration of
projection counts or shapes. The exact checker for the
rank-one-base no-go was actually run; the new projection-max
proof is hand-level. The signed homogeneous audit is separate.

## MAIN NONHOMOGENEOUS ATTACK — generalize the scalar projection, not just radial shells

The [new shifted-shell and nonlinear projection note](IWANIEC_MORREY_NONHOMOG_ROW_PROJECTION.md)
gives both a rigorous stop rule and a substantially larger positive
QC construction, independent of the signed homogeneous audit.

**Refuted:** universal touching unshifted affine-shell minorants.
The explicit isotropic QC function
F(X)=L_1(|z|,||w|-1|) is a supremum of translated formalized L
integrands. At base J, the spectral law (s,delta)=(0,0),(2,-2),(4,2)
with masses 3/8,1/2,1/8 satisfies the conformal norm and determinant
moments and EVERY K_r^± test, but its F-Jensen gap is exactly -1/4.
This excludes even approximate touching affine-shell supports on
the radius-4 ball, and their positive/supremal closures with PC.
The gap persists for smooth positive coercive strongly RC energies.
The law is NOT a gradient law. The affine-shell theorem itself
remains valid, but its proposed universal support extension is FALSE.
All kernel tests below the base radius follow automatically from
the three norm/minor conditions; above the base, endpoint checking
on a finite support is exact by concavity between radii.

**New positive mechanism:** the L² scalar projection zeta for ANY
compact convex gradient constraint K obeys
integral grad Phi(p+D zeta) dot D(eta-zeta)>=0
for EVERY convex C¹ potential Phi, not just the quadratic.
Proof: a scalar implicit convex diffusion resolvent is order
preserving by testing the positive part of the difference of
Euler equations. Its translation/constant equivariance preserves
ALL gradient support-function constraints. Apply the original
projection variational inequality to the resolvent, then pass
to the limit using uniform convexity and smooth approximation.

As a consequence, for ANY compact convex K, convex C¹ Phi and
real c, the generalized row-truncated determinant is globally QC:
on first rows a in K take max(c det(a,b),C(a,b)); outside K take
C(a,b), where C is the convex supremum over z in boundary K of
c det(z,b)+grad Phi(z) dot(a-z). The proof combines the nonlinear
projection sign with the determinant null Lagrangian. Rotational
suprema/averages yield isotropic nonhomogeneous generators with
arbitrary constraint geometry and nonlinear boundary calibration.
This extends the analytic L machinery itself beyond radial cutoffs.

**Remaining main task:** find global touching QC calibrations
for arbitrary isotropic F using the row-projection inequalities
(10) or another genuinely universal construction. Their existence
is not proved. Do not continue the refuted affine-shell ODE
or enumerate a new sequence of special cases. Full isotropic
Morrey remains open. Exact checker for the three-radius no-go
was executed successfully; nonlinear projection proof is hand-level.

## PRIMARY RESEARCH DIRECTION — remove homogeneity while retaining isotropy

The user is handling the audit/formalization of the signed homogeneous
candidate. Do not reopen the already verified nonnegative theorem.
The new [nonhomogeneous affine-shell theorem](IWANIEC_MORREY_NONHOMOG_SHELL_AFFINE.md)
proves RC=>QC for every finite-valued integrand
F(X)=U(s)+V(s)delta, s=operator norm, delta=signed smaller singular value,
without homogeneity, sign, smoothness or growth assumptions.
It uses only the already formalized L theorem, NOT the signed
homogeneous candidate under separate audit.

Rank-one convexity gives the distributional inequality
U''>=s|V''| and the conformal boundary condition
U'>=|V-sV'|. Hence the two nonnegative measures
mu_±=(U''/s ± V'')/2 represent the entire function, by
positive integrals of the QC kernels K_r^±=(s-r)_+(r±delta)
plus a polyconvex initial support. Truncation at epsilon>0
handles possibly infinite measure near zero and converges
locally uniformly. This closes the full arbitrary radial
affine-shell class, not a fixed-exponent family.

The exact spectral tests for this whole class consist of
the two conformal norm inequalities, the determinant identity,
and the two kernel tests at all positive radii. Compress any
spectral law to its conditional mean delta at each radius:
all these tests are unchanged, while Jensen in delta lowers
EVERY isotropic RC integrand. This does not preserve actual
gradient compatibility. The compact obstacle duality gives
an exact criterion for universal touching affine-shell lower
supports on bounded sets.

**Remaining global target:** arbitrary two-variable isotropic
profiles. The contact-path calculation gives a scalar
differential inclusion for c=M' with
z'=(c-f_sdelta)/f_deltadelta, D*=f_ss-(c-f_sdelta)^2/f_deltadelta,
and -D*/(s-z)<=c'<=D*/(s+z), plus the explicit angular bounds.
Pointwise feasibility follows from planar quadratic
polyconvexity; global viability does NOT follow. **SUPERSEDED:
the proposed universal affine-shell obstacle minorant is refuted
by the exact shifted-shell witness above.**
Do not infer full isotropic Morrey or pursue a new exponent,
wave, or polynomial-degree ladder.

Exact rational mixed atomic/diffuse representation and
spectral compression controls passed in the working container.
Hand proofs, not new Lean results. The signed homogeneous
audit and formalization remain separate.

## SIGNED HOMOGENEOUS ISOTROPIC — candidate complete hand proof, every p>0

**Formal baseline corrected:** the separate
[homogeneous-isotropic branch at f70d7e9](https://github.com/vltanh/lean4-morrey/tree/f70d7e9253ecf59ea6c862893d1fdd3fb60cffa9)
has Lean proofs of the nonnegative theorem for every p>0,
signed p=2, p=1 and 0<p<1, and its
[CI including axiom audit passed](https://github.com/vltanh/lean4-morrey/actions/runs/45323677832).
The pinned lean4-iwaniec dependency at 972c0127 contains
Agazzi.quasiconvex_integrandL and Agazzi.quasiconvex_burkholderB.
Older descriptions of this baseline as unformalized/conditional
are superseded.

The [new signed characteristic-integration proof](IWANIEC_MORREY_SIGNED_CHARACTERISTICS.md)
removes the nonnegativity assumption at hand-proof level for
EVERY p>0 and EVERY base, retaining isotropy and homogeneity.
It uses the formalized truncated determinant L rather than
postulating a new analytic theorem.

At a hard base the restricted signed support q in the previous
spectral note touches F, is valid on the unit operator-norm ball,
and supplies monotone supporting planes in (|z|,det) for p<2
or (|w|,det) for p>2. Choose e=-1 or +1 respectively.
Strongly convexify the scalar profile by adding a vanishing
convex Frobenius p-power; parameterize by the inverse supporting
slope T(m) and k(m)=h(T(m))-mT(m). The scalar ODE
dm/dlog(s)=p(k(m)-a m)/(T(m)+e) stays in the hard region
and is well-defined through nonsmooth profile kinks.
The scaled determinant coefficient c_s satisfies e c_s'>=0
by monotonicity of the restricted supporting planes; the t'
terms cancel exactly. Thus w(s)=e c_s' is a nonnegative weight.

Integrate the scaled truncated-determinant QC kernels
K_r^e=(sigma-r)(r+e delta) for sigma>r, zero otherwise,
from radius 1 to infinity with weight w. The resulting global
QC function q+integral w K touches F at the base and, for
every sigma>=1, equals sigma^p times the supporting line
of h at the evolved slope. Hence it lies below F on ALL
matrices, including the earlier exceptional cones. Endpoint,
nonsmooth and non-strict cases follow by the argument in the
note. There is no fixed-wave or fixed-exponent hierarchy.

**Status:** proposed complete signed homogeneous-isotropic
QC theorem by hand; independent proof audit and new Lean
formalization remain. The symbolic checker was executed:
14 exact identities and two exact kink controls passed.
Do NOT claim unrestricted Morrey or general nonhomogeneous
isotropic Morrey. Next priority is independent logical audit
and formalization of the signed extension, then removing
homogeneity while retaining isotropy.

## Signed problem: unconditional spectral half-space supports for EVERY nonzero base

The [new signed spectral-support theorem](IWANIEC_MORREY_SIGNED_SPECTRAL_SUPPORT.md)
gives explicit polyaffine supports for every signed isotropic
p-homogeneous RC integrand, oriented to have its negative values at
negative determinants. Normalize the base operator norm to 1.
For 1<p<2 the support is valid on **all matrices with signed smaller
singular value delta<=1**; for p>2 it is valid on **all matrices with
delta>=-1**. Both cover arbitrary gradient amplitudes and all base
ratios. For the superquadratic hard case the support is also valid
on all nonnegative-energy matrices. Jensen follows on these regions
for every compact law with the correct matrix/determinant moments.
This result is unconditional and does not use the 2026 QC preprint.

The subquadratic hard case uses the new negative scale-maximum proof:
the scale polynomial tends to minus infinity at BOTH ends when det<0,
so its stationary maximum (even negative) is controlled by one
rank-one tangent. Direct rank-one slope inequalities extend the
support to positive determinants with delta<=1. The complementary
superquadratic argument uses the stationary polynomial and two
endpoint estimates to cover every negative-energy matrix with
delta>=-1. The easy bases use elementary signed Burkholder
polyaffine supports on the same spectral regions, with no external
QC theorem.

The theorem gives an explicit global deficit bound by the integral
of a scale-rescaled support discrepancy over the exceptional cones.
**Remaining signed gate:** compensate this discrepancy for all
actual compatible gradients, not just those avoiding expansive
opposite-orientation matrices. No proof of this compensation or of
the full signed conjecture is claimed. The [exact checker](../../research/audit/iwaniec_signed_spectral_exact.py)
was run locally: 160 polynomial and 27 interval feasibility controls
passed. Hand proofs only, no Lean or external review claim.

## PRIMARY RESEARCH DIRECTION — signed isotropic homogeneous quasiconvexity

The fixed-wave and abstract martingale/compatibility-penalty research
is retained below as historical work, but suspended as the main direction.
Return to the provisional all-p>=2 nonnegative isotropic homogeneous
polyconvexity theorem and the conditional 1<p<2 quasiconvexity theorem.
Remove nonnegativity first, targeting QC rather than PC, simultaneously
for all exponents and all base matrices.

The [signed scale-maximal generator theorem](IWANIEC_MORREY_SIGNED_SCALE_MAX.md)
uses **Theorem 1** of Agazzi et al. (2026), arXiv:2609.28311v2,
rather than only its Burkholder corollary. It proves an infinite-dimensional
family of signed, isotropic, p-homogeneous QC integrands for every p>1
by taking the pointwise maximum of the scaled truncated determinant L_r
with a scaled convex competitor BEFORE integrating over radii. Explicit
convergence and scaling arguments make the Jensen proof global.

For every p>2 the new explicit family agrees with Burkholder exactly
on a prescribed cone t<=c in (0,1) and is strictly above it outside,
addressing the earlier signed-cone support limitation constructively.
For every 1<p<2 another exact signed family has a negative conformal
base where no affine Burkholder-profile support is possible, yet is
globally QC. Both follow directly from the 2026 L theorem; no numerical
rank-one-convexity assumption or fixed-wave hypothesis is used.

**All-integrand base coverage:** for 1<p<2, the signed theorem holds
at every nonnegative-energy base, including zero, by the endpoint
tangent argument. For p>2, all nonpositive-energy bases are covered,
and the remaining positive-energy bases with admissible affine tangent
are also covered. The signed p=2 case is polyconvex; p=1 is classical
convexity under isotropy; 0<p<1 gives identically zero.

**Next main gate:** prove quasiconvexity at the genuinely missing
signed bases for every profile. Try constructing touching global
minorants using the new scale-maximal generators; the convex competitor
is not fixed to a single parametric family. No completeness theorem
for this support method is established. Do not substitute an infinite
sequence of special exponents, model gradient fields or new equivalent
martingale formulations for the global signed-profile problem.

The [checker](../../research/audit/iwaniec_signed_scale_exact.py) passed
in the working container. Hand proofs conditional on the cited preprint;
no Lean or human review claim. The signed problem and unrestricted
Morrey remain open.

## MAIN GATE correction — the proposed universal Delta-preserving split is REFUTED

The [new exact no-go theorem](IWANIEC_MORREY_DELTA_NOGO.md)
proves that **all minor-compatible laws with full covariance condition
number <=3/2 automatically have Delta=0**, uniformly over EVERY affine
transform in the penalty. The proof combines the semiconvex bound
g<=s/2 for the determinant-index Jensen gap with the negative-sheet
bound g<=(1/2+kappa)v, where s,v are the transformed centered symmetric
and skew variances and kappa is the covariance condition number.

The explicit law with atoms +/-5I,+/-5J each of mass 1/104 and
+/-diag(1,-1),+/-[[0,1],[1,0]] each of mass 25/104 has mean and
mean determinant zero, covariance (25/26)I4, and Delta=0. Yet the
globally rank-one convex signed Dacorogna--Marcellini quartic
F=|X|^4-(9/4)|X|²det X has **exact Jensen gap -50/13**.
Rank-one convexity has a direct rational SOS proof. This is an
abstract nonlaminate, NOT an actual compatible-gradient witness.
The no-go does not depend on the recent quasiconvexity preprint.

Consequently r_comp(nu)>r(nu)>0 for this abstract law: an optimal
unconstrained decomposition cannot simultaneously have zero average
Delta, by the exact trap classification. The stronger proposed
uniform splitting principle on ALL minor-compatible Delta-zero
laws is false and must NOT be pursued further. The counterexample
persists for smooth compact densities with connected support.
A further proof gives both laminate and nonlaminate realizations
of any prescribed positive definite determinant-neutral covariance.

The original equality r_comp=r for ACTUAL gradient laws remains
open and equivalent to Morrey; it is not refuted by this example.
The quantitative trap exclusion and exact neutral martingale tools
are unaffected. Any continuation must use spatial information
beyond these determinant-index tests and second moments, not
another finite-wave hierarchy.

The [exact checker](../../research/audit/iwaniec_delta_nogo_exact.py)
was actually executed locally: exact moments, quartic gap, SOS
coefficients and 256 rational affine controls passed. The all-transform
inequality is a hand proof, not a sampling inference. No Lean or
external review claim.

## MAIN GATE refinement — quantitative compatibility penalty detecting EVERY terminal trap

The [new trap compatibility note](IWANIEC_MORREY_TRAP_COMPATIBILITY.md)
uses spatial compatibility beyond mean/determinant moments. Every
blocked geometry from the adaptive theorem has an invertible affine
normalization to a symmetric law of mean I and determinant one,
with opposite-sheet mass w>0. The classical Šverák determinant-index
integrand, together with a periodic Helmholtz decomposition, gives
an explicit all-gradient inequality for arbitrary full 2x2 laws:
h(sym A)<=E h(sym X)+||sym X||_2 ||skew(X-A)||_2.
Thus a normalized blocked law is at W2 distance at least
w/(3||X||_2+2) from every compact homogeneous gradient law.
The known qualitative hyperboloid rigidity is acknowledged as
prior art; this is a quantitative form and all-trap application.

A full-matrix extension theorem approximates any continuous
quadratic-growth symmetric Hessian-quasiconvex function on compact
symmetric sets by smooth globally strongly QC functions with
bounded Hessian (Helmholtz projection plus quadratic skew penalty).
It gives explicit full-matrix QC separators for every trap.

**Single compatibility penalty Delta(eta):** maximize the positive
violation of the displayed sheet inequality over affine transforms
P X Q+B with the three Frobenius norms <=1. This is a compact
12-real-parameter maximum, continuous on laws with common compact
support, zero for every gradient law, and strictly positive for
EVERY nontrivial blocked law. It does not depend on wave count,
atom count or integrand degree.

Let r be the earlier minimum unresolved variance over feasible
adaptive decompositions, and r_comp the same minimum constrained
to average Delta=0. For gradient laws r_comp is feasible at least
at the trivial decomposition. **The sole new main target** is
r_comp=r for all actual gradient laws. Equivalently it suffices
to construct feasible decompositions with residual approaching
r and average Delta approaching zero. Compactness and the exact
trap classification would then force r=0 and settle Morrey.
A stronger sufficient uniform construction is a nonzero rank-one
split preserving Delta=0 at every non-Dirac minor-compatible
law with Delta=0; its existence is NOT established. **SUPERSEDED: this stronger uniform principle is refuted by the Delta no-go above.**

**Mandatory caution:** an explicit smooth separable product
gradient (already a laminate) admits a legal nonzero rank-one
minor-preserving observation with a nonlaminate trapped posterior
of probability 1/9. Thus arbitrary greedy neutral conditioning
does NOT preserve compatibility. The optimization over choices
is essential. This is not a negative Morrey witness.

The [exact checker](../../research/audit/iwaniec_trap_compatibility_exact.py)
was actually executed: 2D/3D trap moments, four nonsymmetric
normalization controls and the smooth plateau probability bounds
passed (explicit W2 lower bound 1/72 for the diagonal trap).
Hand proofs only, no Lean/external review/novelty claim.
No fixed-wave or atom-count investigation is resumed.

## MAIN GATE refinement — exact input-adaptive representation and complete terminal-trap geometry

The [new adaptive martingale note](IWANIEC_MORREY_ADAPTIVE_MARTINGALE.md)
contains three global structural results, not more fixed-wave cases.

**Mandatory change to Beurling strategy:** a single COMMON
filtration for all inputs is impossible, even approximately.
The product identity of three Fourier phase martingales proves
that twelve fixed smooth individually laminate two-ridge gradients
have total common-filtration determinant cost >=1, independently
of depth and auxiliary randomness. Continuous covariations give
the same obstruction. For projected Beurling representations in
a common continuous filtration, some input has expected absolute
trace-bracket mismatch >1/300. Thus a successful determinant
martingale construction must be input-specific, not a universal
linear/common-filtration representation.

**Exact continuous characterization:** every compact laminate
(and only such a law) is the terminal law of a bounded continuous
matrix martingale whose determinant is a martingale. This follows
from unit-speed stopped Brownian rank-one splits, tightness on
compact time intervals and a uniform terminal time tail bound.
It removes any concern that exact continuous representation might
be strictly stronger than D=0.

**Global adaptive reduction:** at a conditional law satisfying the
minor identity, use its centered lifted covariance in R^5.
An exact minor-preserving rank-one binary observation exists
iff the projection at zero determinant-coordinate contains a
nonzero rank-one matrix. All nontrivial blocked laws are supported
on BOTH sheets of a two-sheeted hyperboloid, in affine dimension
2 or 3, and none is a laminate. A compact maximal-variance
decomposition over minor-compatible conditional laws with
laminate barycenter distribution leaves only Diracs and these
classified traps; its minimum residual r satisfies D<=r/2 and
r=0 iff D=0.

Every nonconstant smooth periodic gradient has connected support
and satisfies the minor identity, so admits an exact
minor-preserving nonzero rank-one split. Positive likelihoods
retain the original support and permit further finite steps,
but this does NOT establish vanishing residual at infinite depth.
Conditional laws may lose actual gradient compatibility.

**Sole open global gate:** use actual gradient compatibility to
avoid the nontrivial two-sheeted traps in an OPTIMAL adaptive
decomposition (r=0), or construct the equivalent exact input-specific
neutral martingale. An arbitrary nonoptimal trapped decomposition
does not refute Morrey. No proof of global avoidance or actual
negative witness is provided; no wave/degree ladder is resumed.

The [exact checker](../../research/audit/iwaniec_adaptive_martingale_exact.py)
passed locally: 64 rational phase-filtration controls and
two 2D/3D trap controls plus the explicit positive-likelihood split.
Hand proofs only, no external review, novelty or Lean claim.

## MAIN ROUTE — unrestricted scalar determinant defect; fixed-wave investigations suspended

The [new global martingale-defect theorem](IWANIEC_MORREY_MARTINGALE_DEFECT.md)
defines a nonnegative scalar D(nu) for ANY compact planar matrix law:
inf over finite binary conditional-expectation filtrations of
E sum |det Delta M| plus half the unresolved terminal variance.
**No fixed wave count, integrand degree, isotropy or homogeneity.**

- Quantitative repair: nearest rank-one truncation of each binary
  increment, with a controlled stopping rule, yields a finite-order
  laminate supported in B_{4R}(A) at W2-squared distance <=2D(nu)
  in the infimum. A two-sided coupling continuity bound and the
  classical bounded prelaminate approximation theorem show
  **D=0 iff laminate**. For every smooth RC F of local Hessian
  bound K, the Jensen deficit is <=K D(nu).
- Exact global dual: D is the supremal Jensen deficit over smooth
  functions with Hessian lower bound -2|det H| in each direction.
  A determinant-penalized binary Bellman envelope proves exact
  duality, not a heuristic or finite termination guarantee.
- Continuous covariance repair: a PSD determinant-neutral
  covariance is a sum of rank-one outer products. Itô yields
  the Jensen deficit <=K times expected absolute determinant
  bracket variation.
- **Beurling projection bridge:** for any projected martingale
  representation U_T=g(P), E[V_T|P]=Bg(P), define delta as
  expected total variation of the difference of the two complex
  trace brackets. Unitarity gives projection variance <=delta;
  Taylor plus the covariance estimate gives the actual gradient
  Jensen deficit <=2K delta, without a false conditional Jensen
  step. A smooth bounded-Hessian extension matching the test
  ball removes all growth restrictions.

The exact checker actually passed 160 rational martingale controls,
59 with early stopping, plus a projection algebra control.
These are hand proofs and exact regression checks, not Lean or
human certification. No proof of the zero-defect assertion or
counterexample is claimed.

**Sole main mathematical gate:** prove D(law(A+Dphi))=0 for
every periodic Lipschitz phi, e.g. construct projected Beurling
martingale representations of arbitrary smooth periodic gradients
with absolute bracket mismatch delta -> 0. Alternatively find
a genuine compatible gradient with certified D>0.
Standard projected representations and norm bounds do not give
this pathwise/total-variation property. A signed cancellation is
not enough. No wave-count or degree ladder will establish it.

The earlier four-wave D/TQ corner list is retained below as
historical subordinate work but **suspended**: closure of one or
both corners would not advance the missing global implication
without a universal coupling/induction argument.

## N=0,...,4 ledger: entire four-wave problem reduced to TWO fixed corner inequalities

The [new exhaustive four-wave reduction](IWANIEC_MORREY_FOUR_WAVE_CASES.md)
clarifies the crucial quantifier: the bound of four applies to
minimal odd-resonance supports, NOT to total wave count.
N=0,1,2 are elementary and N=3 is the published
Sebestyén–Székelyhidi theorem. The general N=4 gate is now
reduced by hand proofs to **two fixed 16-atom weight laws**,
each tested on arbitrary rank-one H_1,...,H_4 and arbitrary F:
D has density (1+e123/2+e124/2)/16 and TQ has density
(1+e123/2+e1234/2)/16. Both corner inequalities remain OPEN.

New proof components: (i) exhaustive six-row normalized mod-2
classification of four pairwise nonparallel frequencies;
(ii) **universal absolute fourth-Walsh-correlation bound 1/2**
for all distinct directions, including the nonminimal
triple+quadruple case, by lattice-projection index bounds,
Cauchy–Schwarz, and a separate explicit unit-triad integral;
(iii) complete three-direction case (one parallel pair) using
conditional triangular correlation, 2-adic support and a
six-vertex outer polytope, reduced to the SAME two corners.
One/two spatial directions are elementary. No additional
integer-frequency cases remain in this sufficient N=4 reduction.

The [exact checker](../../research/audit/iwaniec_four_wave_cases_exact.py)
was run locally: 22 mod-2 multisets, six parallel-pair
generating points and two rational polygon sign-law controls
passed. One actual unit double triad attains D exactly;
one triple+quadruple field has correlations 1/2 and 1/4,
so the earlier total-parity budget genuinely fails.

**Next bounded task:** prove D and TQ, e.g. via fixed-weight
rank-one cube certificates parametrized by split-signature
determinant forms. These are sufficient outer corner laws;
failure for arbitrary H_i without actual spatial compatibility
would not itself be a four-wave counterexample. No bound on
certificate-tree size is asserted. Neither Lean nor external
human review yet. Even closing both corners would not prove
the all-N induction needed for unrestricted Morrey.

## All-N composition theorem for overlapping circuits, and nonunit three-ridge waveforms

The [new random-cube composition theorem](IWANIEC_MORREY_CUBE_COUPLING.md)
handles arbitrary N bounded rank-one-subspace-valued profiles with
pairwise independent reference variables and a joint density p
relative to the product marginals. It proves universal Jensen whenever
||p-1||∞ ≤ 1/[2(3^N-2N²-1)], or under the sharper local
mixed-difference parity budget. Randomly sampled pairs in each
coordinate yield translated rank-one cubes with overlapping parity
interactions. The proof uses the published planar three-wave theorem,
finite subset Möbius inversion for **exact** probability reconstruction,
and independent midpoint convex Jensen. The same theorem gives
conditional block removal with an arbitrary retained tail.

An explicit **arbitrary-N actual-gradient** application has all
frequency lengths within a factor of five, no dyadic or parallel-block
peeling, and m nonparallel minimal triple circuits sharing two core
waves, with simultaneously nonzero triple correlations. The two core
ridge derivatives are arbitrary bounded vector-valued profiles.
A uniform grid-discrepancy argument proves near-product density for
every phase choice. This is not an assertion of arbitrary comparable-
scale Jensen; the family is weakly dependent.

A separate nonperturbative antithetic-pair argument handles two
arbitrary bounded ridge derivatives plus a sawtooth in a third
nonparallel direction whenever that direction's coefficient in
the primitive frequency relation has magnitude ≥2. Arbitrary third
step profiles are covered if the coefficient times their minimum
interval length is ≥16. The unrestricted three-ridge waveform claim
remains open; there is no fixed-winding fine-partition limit.

The [checker](../../research/audit/iwaniec_cube_coupling_exact.py)
actually passed: exact nonbinary overlapping-cube reconstruction,
exact rational grid discrepancy controls, and arithmetic construction
checks through 102 variables. Hand proofs only; no Lean or human
certification or novelty claim.

**Remaining P2 gate:** remove the small-dependence assumption or
prove a gap-preserving universal conditional decomposition for
strongly correlated clusters. Do not enumerate larger isolated
cases or infer universal Jensen from pairwise independence.

## Bounded minimal resonance circuits and complete parallel-block peeling criterion

The [new arithmetic/circuit theorem](IWANIEC_MORREY_MINIMAL_RESONANCE.md)
proves for **arbitrary N and arbitrary integer frequencies** that
every odd-resonant subset contains an inclusion-minimal odd-resonant
subset of size at most four. This bound is sharp. Normalize the
subgroup generated by a subset, reduce modulo twice that subgroup,
and use an odd-index argument. The only minimal patterns are a
parallel pair, three distinct nonzero mod-2 classes, or a pairwise
nonparallel quadruple in two mod-2 classes with multiplicities 2+2.

**All isolated minimal blocks are laminates:** the full four-circuit
case is now closed by the Fourier Cauchy–Schwarz argument with
odd determinant denominator, including non-unimodular coordinate
pairs. No special frequency-family hypothesis remains for minimal
four-circuits. The deep input is the published planar three-wave
theorem. The all-N pure-parity mixture also handles arbitrary overlaps
when the total absolute nonconstant Walsh correlation is at most 1/2
and all pair moments vanish; this covers the doubly resonant
nonunit-triad 2+1+1 four-wave class uniformly in phases.

**Complete all-N theorem for parallel-block peeling:** a tuple
can be fully eliminated by parallel rank-one blocks satisfying
the even/infinite-order tail-lattice criterion **if and only if**
it contains no rank-two minimal odd-resonant circuit. A greedy
algorithm works in every such case; it removes an entire parallel
nonzero mod-2 class and recomputes the lattice. Any rank-two circuit
is invariant under all permitted peeling steps. This is a
necessary/sufficient condition for this METHOD, not for Jensen.

The [exact checker](../../research/audit/iwaniec_minimal_resonance_exact.py)
passed locally (150 small exact classifications and a 63-wave
irreducible control). Hand proofs; no Lean/human certification.

**Remaining P2 gate:** interactions between bounded circuits are
still unbounded. Explicit tuples of arbitrary size have every
wave in a rank-two triple circuit and admit no parallel-block
peeling. Do not infer a bounded wave-count reduction or universal
Jensen from the bounded minimal-circuit classification; a genuine
coupling/conditional laminate theorem is required.

## Unrestricted wave count: conditional dyadic lamination and arithmetic peeling

The [new conditional-lamination theorem](IWANIEC_MORREY_DYADIC_LAMINATION.md)
establishes a block removal inequality for arbitrary finite-valued planar
rank-one convex integrands, at every base and for arbitrary phases and
amplitudes. An arbitrary block of at most three integer-frequency waves
can be removed in the presence of ANY tail whose frequencies are
multiples of a suitable explicit power of two. In the distinct nonzero
mod-2 classes, a factor of 4 suffices. The key is a finite-grid triple
parity bound **conditional on the entire tail**, including the sharp
unit-triad case; the published N=3 theorem is the deep input.

Iteration proves Jensen for arbitrarily many interacting dyadic-scale
blocks, with no wave-count bound (explicit cross-scale correlation 1/4).
The general lattice peeling rule also removes any wave of even or infinite
order modulo the lattice of the others, or a whole such block in a
common rank-one subspace. A hypothetical negative gap survives deletion.
The [exact finite-grid checker](../../research/audit/iwaniec_dyadic_grid_exact.py)
passed locally. These are hand proofs, not Lean-certified or independently
refereed, and no novelty claim is made.

**Remaining unrestricted gate:** control irreducible comparable-scale
resonance clusters, which still have unbounded size. Do not enumerate
ever larger separated chains or infer a bounded wave-count cutoff.
No general four-wave or unrestricted Morrey proof is claimed.

## New unrestricted four-wave gate — one genuine correlated family CLOSED

The [correlated four-wave theorem](IWANIEC_MORREY_FOUR_WAVE_PARITY_THEOREM.md)
is a **global every-integrand, all-amplitude,
all-phase** rank-one Jensen theorem for the
**four-parameter integer frequency family**
\(u,v,a u+b v,c u+d v\),
where a,d are arbitrary odd and
b,c arbitrary nonzero even integers,
with u,v independent integer vectors.
It does not assume isotropy, homogeneity,
p-growth, positivity, polynomiality
or strict ellipticity.
The gradient sign law has a nonzero
four-way parity correlation (rho=1/3
at zero phase), yet the all-phase
Fourier/Cauchy–Schwarz estimate
\(|\rho|\le1/2\) places it in a planar
laminate family. The critical
input is Sebestyén–Székelyhidi's
**already published N=3 theorem**.
The [exact checker](../../research/audit/iwaniec_four_wave_parity_exact.py)
passed rational polygon/probability
and integer odd-resonance controls.

Two **unbounded-N** structural results:
(a) absent any subset odd-frequency
resonance, all signs are independent
for EVERY choice of phases, so the
resulting gradient law is a finite
laminate of arbitrary order;
(b) every N≥3 pure-parity law
\(2^{-N}(1+\rho\prod_i\epsilon_i)\)
on rank-one cube directions is a
laminate whenever \(|\rho|\le1/2\),
by the published N=3 case followed
by repeated rank-one conditional splits.

**Remaining open positive gate:** for
an arbitrary 4-wave tuple, the
sign law may have **several nonzero
triple and fourth-order Walsh
coefficients**. A universal rank-one
Jensen argument for those genuinely
coupled measures is not supplied.
Even a complete N=4 theorem would
not alone imply the ALL-N
characterization required for
Morrey. Avoid rediscovering
N≤3 prior art or treating
minor-compatible laws as
gradient laws; this work operates
on **actual** periodic gradients.



## Unrestricted sign/regularity gate — closed by reduction

[Positive smooth coercive strongly RC reduction](IWANIEC_MORREY_POSITIVITY_REDUCTION.md): any strict Morrey counterexample can be mollified, exponentiated and quadratically strictified while preserving a negative compatible-gradient Jensen gap. The unrestricted theorem is equivalent to its restriction to this positive smooth coercive class. The reduction also preserves isotropy but not homogeneity. The universal QC step remains open.


## Unrestricted exact finite-symmetry reduction

[New elementary reduction](IWANIEC_MORREY_FINITE_SYMMETRY_REDUCTION.md): any unrestricted strict counterexample can be translated, localized by a finite maximum of affine-biased orbit copies, and clipped to become nonnegative and invariant under any prescribed finite rank-one-preserving orthogonal group. Thus proving QC for all such nonnegative finite-symmetry RC energies at all bases is equivalent to unrestricted Morrey. No homogeneous or continuous-isotropy reduction follows. Hand proof, no novelty or Lean claim.


## G1 achieved conditionally: global anisotropic and nonhomogeneous QC neighborhoods of EVERY strict isotropic core

**Assume** the p≥2 nonnegative isotropic
p-homogeneous RC⇒PC hand theorem has
been independently verified, as
requested by the user. The new
[quantitative all-p stability theorem](IWANIEC_MORREY_ANISOTROPIC_QUANT_STABILITY.md)
then proves a **direct all-gradient bridge**
for each smooth isotropic p-homogeneous
core F0 obeying
\(F_0(A)\ge\alpha|A|^p\) and
\(D²F_0(A)[H,H]\ge\mu|A|^{p-2}|H|²\)
on every rank-one H, with α,μ>0.

An explicit p-power subtraction
\(B=F_0-c|A|^p\),
\(c=\tfrac12\min(\alpha,\mu/[p(p-1)])\),
remains nonnegative isotropic p-hom
and globally RC, hence **PC by the
assumed theorem**. The p-power's
explicit uniform convexity constant
\(c_p=p/[(p-1)4^{p-1}3^{p-2}]\)
gives a **quantitative QC margin**.
Any arbitrary, including anisotropic
and nonhomogeneous, C² perturbation G
satisfying
\[
\|D²G(A)\|_{\rm op}
 \le c\,c_p\,|A|^{p-2}
\]
then yields F0+G globally **RC and QC**,
with positive weighted Jensen margin
\(c\,c_p/2\) for EVERY periodic
gradient with arbitrary amplitude
and wavelength.

A nonconvex explicit isotropic
quartic core
\(F_0=s(s-2\det A)+s²/100\)
admits the exact perturbation
Hessian radius \(1/259200\);
[exact coefficient checker](../../research/audit/iwaniec_anisotropic_stability_exact.py)
passed.

**CLOSED G1 only in this quantitative
strict ellipticity regime**:
this is an infinite-dimensional
neighborhood around EVERY such
core, not just a finite sample.
**G2–G4 remain OPEN**:
the proof does not control arbitrary
large anisotropic/nonhomogeneous
departures, degenerate rank-one
ellipticity, or all compatible
gradient Young measures.
An unrestricted result must
control these without a small
weighted C² assumption.
The assumed isotropic theorem and
this new deduction remain
hand-level, not Lean-certified.


## Global two-line frequency-tail theorem (all gradient fields, 23 Nov 2026)

The **unconditional** [two-direction Fourier-tail bound](IWANIEC_MORREY_TWO_LINE_SPECTRAL.md)
applies to every globally RC finite-valued
2×2 F, including signed, anisotropic,
nonhomogeneous and nonsmooth energies,
at EVERY base and for EVERY periodic
W¹∞ planar gradient. Fourier projection
onto any two primitive frequency lines
is a genuine compatible two-ridge field,
and the standard two-ridge rank-one Jensen
inequality applies. Hence
\[
 F(A)-\fint F(A+D\varphi)
 \le L_R
 \sqrt{\|D\varphi\|_2^2-
        e_{(1)}-e_{(2)}},
\]
where \(e_{(1)},e_{(2)}\) are the
two largest Fourier gradient energies
grouped by primitive line. A true
Morrey counterexample with gap δ>0
would need at least \(\delta^2/L_R^2\)
of energy outside its two strongest
Fourier directions. The [exact
spectral regression](../../research/audit/iwaniec_two_line_spectral_exact.py)
passed.

**Scope:** No finite reduction for
general gradients is obtained. The
published two-wave Jensen result is
the essential input. A proposed
three-direction replacement was
invalidated by an inequality-direction
error (see [retraction](IWANIEC_MORREY_THREE_RIDGE_GLOBAL_QC.md)).
The unrestricted positive Morrey
gate remains control of arbitrary
three-and-higher correlated gradients
with no strict LH margin.


## UNRESTRICTED progress and explicit failed extension (23 November 2026)

**New valid exact all-N positivity theorem.** The
[strict-curvature high-resonance theorem](IWANIEC_MORREY_STRICT_RESONANCE.md)
shows that for **every** \(C^2\) isotropic OR anisotropic,
positive OR signed, homogeneous OR nonhomogeneous
integrand having a uniform rank-one Hessian
margin \(\mu>0\) and full Hessian bound M on
the relevant matrix cube, arbitrary finite N
compatible sinusoidal waves satisfy **exact Jensen**
whenever a suitable n obeys
\(4n<\ell\) and \(4MR^2/n\le\mu\sum_j\|H_j\|_F^2/4\).
This follows from an exact independent-phase
strong Jensen margin plus the established
Bernstein/Fourier resonance approximation bound;
the proof has **no fixed wave-count restriction**.
[Exact signed/anisotropic/nonhomogeneous rational regression](../../research/audit/iwaniec_strict_resonance_exact.py)
passed locally, with minimal resonance length
1026 and a positive margin above the
Bernstein correlation-error bound.

**MANDATORY correction:** An attempted derivation of
Jensen for *all arbitrary three-ridge waveforms*
from the 2017 Sebestyén–Székelyhidi
three-**sawtooth** theorem was **INVALID**:
randomizing vector-valued ridge derivatives
into sawtooths and invoking rank-one convexity
gives \(F(\mathbb EZ)\le \mathbb EF(Z)\),
while the published Jensen lower bound
controls only the randomized average.
Those two inequalities give **no lower
bound for the original ridge field**.
See the [explicit retraction/audit](IWANIEC_MORREY_THREE_RIDGE_GLOBAL_QC.md).
The proposed all-gradient spectral
distance-to-three-lines estimate is
therefore **NOT PROVED** and must
NOT be used in any further gate.

**Next global gate:** Control the
short-resonance correlations without
requiring a positive uniform rank-one
Hessian margin. No existing argument
handles all gradient fields; unrestricted
Morrey remains OPEN. Do not claim a
positive all-three-ridge result until
a fundamentally different lower-bound
argument is supplied.


## Global Morrey route: arbitrary-F rank-one Fourier resonance sieve (23 November 2026)

**New exact result:** the [all-N resonance theorem](IWANIEC_MORREY_RESONANCE_SIEVE.md)
works for EVERY finite-valued globally rank-one-convex \(F:\mathbb R^{2\times2}\to\mathbb R\),
including signed, anisotropic, nonhomogeneous functions.

For an actual periodic gradient consisting of ANY FINITE number of rank-one
sinusoidal waves with integer wavevectors \(k_j\), define \(\ell\) as the
smallest nonzero integer-relation order \(\sum|n_j|\) with
\(\sum n_j k_j=0\). For ANY rank-one-convex polynomial \(F\) of total
degree \(d\), \(\ell>d\) **guarantees exact Jensen** at every base,
arbitrary amplitude and any phases. For arbitrary (nonpolynomial) RC
\(F\), a four-coordinate tensor Bernstein proof gives a **quantitative**
bound on its possible Jensen deficit of \(4L_RR/\sqrt{n}\) whenever
\(4n<\ell\) (or \(4M_RR^2/n\) for C² \(F\)). Therefore any prescribed
strict negative gap forces a **bounded-order integer resonance**.
The [pure rational checker](../../research/audit/iwaniec_morrey_resonance_exact.py)
tests all 35 quartic cosine moments for a triple with minimum
resonance length 7, and a nonzero cubic-triad correlation.

**PRIOR ART:** Two-wave quasiconvexity from RC is known, and the
three-sawtooth-wave planar theorem is **Sebestyén–Székelyhidi (2017)**,
restated by Guerra–Teixeira da Costa (2021), Theorem 3.3(d).
Do not duplicate these achievements or claim novelty. The
new sieve is a global frequency-geometry reduction, **NOT**
a proof of all-wave Jensen, and no uniform bound on the
number or size of waves is obtained.

**Decisive open gate:** Prove a phase-correlated *resonant*
energy inequality uniformly over arbitrary wave count and
all rank-one-convex \(F\), or exhibit an exactly certified
compatible-gradient counterexample. Do not grind a
growing list of fixed wave counts; the bound is intended
to isolate the universal resonance mechanism.


## 23 November: global anisotropic and nonhomogeneous QC open neighborhood

The [new open-family theorem](IWANIEC_MORREY_ANISOTROPIC_OPEN_QC_NONPC.md)
produces **an infinite-dimensional open ball** of
positive, coercive, uniformly strongly RC,
globally QC but nonpolyconvex 2×2 integrands.
They are permitted to be **both anisotropic and
nonhomogeneous simultaneously**.
The exact four-atom nonpolyconvexity
gap survives **every** bounded C²
perturbation with
\(\|G\|_\infty<10^{-4}\),
\(\|D^2G\|_\infty<10^{-3}\).
Global QC is conditional on the
Bruno–Pasqualotto (2026)
quasiconvexity theorem for the
Dacorogna–Marcellini quartic;
all other inequalities have exact
hand proofs and a rational checker.
This goes beyond the isotropic
homogeneous subclass for **all
gradient amplitudes and oscillations**,
but the proof uses *one known QC
core plus a convex perturbation*.
It is not a proof of universal
RC⇒QC. Do not confuse the
minor-law PC counterexample
with a compatible-gradient QC
counterexample.

The [fresh independent logic audit](IWANIEC_MORREY_PGE2_BRIDGE_LOGIC_AUDIT.md)
checks seven central Case I identities
and the no-homogeneity obstruction
exactly; no fatal gap in the new
isotropic p≥2 hand proof was
identified. The isotropic theorem
is NOT Lean-certified or externally
human-reviewed.

**Unrestricted next target:** a
phase-sensitive and scale-sensitive
gradient Jensen bound for arbitrary
RC integrands, or a genuine
globally certified compatible-gradient
counterexample. Existing
[negative certificate hierarchy](GLOBAL_CERTIFICATES.md)
is complete with *unbounded*
degree/mesh/SOS order, but
supplies no universal finite cutoff.
No theorem currently bridges
this missing step.


## Research update — provisional isotropic completion, unrestricted remains open (23 Nov 2026)

The new [all-p≥2 isotropic p-homogeneous theorem](IWANIEC_MORREY_PGE2_POLYCONVEXITY.md)
claims a **global poly-affine minorant at every matrix** for
every nonnegative isotropic p-homogeneous RC integrand, p≥2.
An [independent logical audit](IWANIEC_MORREY_PGE2_INDEPENDENT_AUDIT.md)
verified the major algebra and the formerly missing Case I
rank-one-line/scaling step and found no fatal gap. This is a
**provisional AI hand proof**, not a Lean theorem, external
referee report, or settled priority claim. All previous
I12 "still open" text below is historical and is
**superseded provisionally** by this audit; the
generalized result must be independently verified
before being treated as accepted.

**Unrestricted Morrey remains OPEN.** Do NOT attempt to
remove homogeneity or isotropy while demanding
polyconvexity: both are provably impossible.

- Remove isotropy: nonnegative anisotropic positively
  p-homogeneous RC energies are nonpolyconvex for
  **every p≥2**. The [corrected exact
  three-atom witness](IWANIEC_MORREY_P2_SIGNED.md)
  repairs a determinant arithmetic error in
  Guerra–Kristensen (2022), Proposition 3.7.
- Remove homogeneity: the [fully explicit
  strictly positive isotropic example](IWANIEC_MORREY_NONHOMOG_PC_NOGO.md)
  W(A)=exp(||A||_F^4−(9/4)||A||_F² det A)
  is RC but nonpolyconvex, certified by
  a rank-one Hessian SOS and four exact atoms.

Neither witness shows **nonquasiconvexity**.
The new unrestricted gate is an actual-gradient
Jensen theorem for arbitrary anisotropic and
nonhomogeneous RC functions (or a fully verified
counterexample). The proposed isotropic proof's
critical equality F(A_tau)=F(A/lambda), when two
matrices share signed singular magnitudes,
breaks **without isotropy**. Its stationary
rescaling breaks **without homogeneity**.
These are exact barriers to this proof route.

### Smooth/coercive/strongly rank-one convex does not repair the PC bridge

The [positive isotropic no-go](IWANIEC_MORREY_NONHOMOG_PC_NOGO.md#2a-the-counterexample-can-be-smooth-coercive-and-uniformly-strictly-rank-one-convex)
extends to
\(W_\varepsilon(A)=
 e^{\|A\|_F^4-(9/4)\|A\|_F^2\det A}
 +\|A\|_F^2/1000\).
It is **real analytic, coercive, strictly positive and
globally rank-one convex with an exact uniform
ellipticity margin 1/500**, yet fails
four-atom polyconvex Jensen at zero with an
explicit rational gap. Therefore none of
smoothness, coercivity or a strong
Legendre–Hadamard margin allows simply
discarding the homogeneity hypothesis of
the p≥2 isotropic polyconvexity theorem.
An unrestricted proof **must** use
actual gradient compatibility to
establish **QC**, not PC.


### An all-anisotropic averaged positive consequence (conditional on the new theorem)

For any **nonnegative positively p-homogeneous,
p≥2, rank-one-convex** F, even if anisotropic,
the bi-SO(2) average
\(\bar F(A)=\int_{SO(2)^2}F(RAS)\,dR\,dS\)
is nonnegative, p-homogeneous, isotropic and RC,
so the new theorem, if independently validated,
implies \(\bar F\) is polyconvex.
Thus for **every** minor-compatible law ν with barycenter A,
\[
\int\!\!\int F(RBS)\,dR\,dS\,d\nu(B)
\ge\int F(RAS)\,dR\,dS .
\]
This is a globally quantified
**rotation-averaged Jensen inequality**, not a
pointwise inequality for F. The anisotropic
three-atom non-PC example shows deaveraging
cannot hold for arbitrary minors laws.
The full QC/Morrey implication remains
the main unresolved obstacle.




**Status: open.** The positive and negative routes below are alternatives. Neither is completed
by the present ledger. The main task is a statement about every planar gradient and every
rank-one-convex integrand, or one globally certified planar counterexample.

### Signed p=2 extension and an anisotropic no-go (22 November 2026)

A [new hand proof](IWANIEC_MORREY_P2_SIGNED.md) removes
nonnegativity entirely for **isotropic 2-homogeneous**
rank-one-convex energies: each is *globally polyconvex*
because its convex signed-singular profile has affine
supports with nonnegative intercepts. This is independent
of Iwaniec 2026 and remains unformalized in Lean.
The same note fixes a determinant-arithmetic error
in Guerra–Kristensen (2022), Proposition 3.7 by
an exact 3-point minors-preserving counterexample
to polyconvexity for a **nonisotropic** rank-one
convex 2-homogeneous energy.

**Stop rule:** No claim that GL-transformed signed
p=2 isotropic polyconvex generators and their
positive/supremum closures can span *all* anisotropic
rank-one-convex p=2 integrands. The verified
nonpolyconvex example rules out that approach.
This does not refute quasiconvexity.

### Smooth coercive nonpolyconvex QC generators (22 November 2026)

The new [Iwaniec stabilization note](IWANIEC_MORREY_SMOOTH_QC.md)
gives a **four-atom exact rational minors-preserving
Jensen witness** of strict nonpolyconvexity,
gap -1/17, for the coercive, strongly rank-one-convex
\(W_{1/8}=1+L+\|A\|_F^2/8\). This survives
smooth convolution and invertible affine transformations;
quasiconvexity remains conditional on the 2026
global L theorem. This closes the **regularity/
coercivity robustness issue for this generator**,
but the four atoms are not a planar gradient law.

**Stop rule:** Smoothness, coercivity,
strict rank-one convexity, anisotropy and
nonhomogeneity of particular QC generators
do not imply a universal representation of
every rank-one-convex integrand. The
[L-cone no-go](IWANIEC_MORREY_CONE_NOGO.md)
still rules out the simple positive-cone approach.


The same construction has a **sharp scalar threshold**:
\(W_\varepsilon=1+L+\varepsilon\|A\|_F^2\)
violates lifted-minor Jensen at zero whenever
\(\varepsilon<1/4\), but for every
\(\varepsilon\ge1/4\) it satisfies
\(W_\varepsilon(A)\ge
W_\varepsilon(0)+\det A/2\) globally.
This closes its *at-zero poly-affine support*
question only; global polyconvexity is not
claimed for large ε.

### Global L-cone no-go (22 November 2026)

The [exact no-go theorem](IWANIEC_MORREY_CONE_NOGO.md)
shows that the positive cone of **all** matrix-translated
and invertible GL-transformed Iwaniec calibrators L,
augmented by **all** polyconvex functions, has a
strict, exact support-envelope gap of **1**
at a simple rank-one-convex anisotropic
2-homogeneous integrand T. The proof uses its
whole rank-one-flat line and the corrected
Guerra–Kristensen minors witness; it does not
claim T is not quasiconvex.

**Stop rule:** Do not claim that closure of
positive polyconvex plus L-generator cones
can settle unrestricted Morrey, regardless of
the number of terms, transformations or
pointwise supremum operations. The
no-go is global in this class. Any
renewed calibration program must introduce
a qualitatively new generator or abandon
global pointwise minorants; otherwise
prioritize an all-gradient Jensen proof
or an actual negative planar witness.

### A global p>2 support at ALL rank-one bases of the exact candidate

The exact p=4 candidate in
[the hybrid no-go](IWANIEC_MORREY_HYBRID_NOGO.md)
is **polyconvex at every rank-one base**, not merely
locally quasiconvex. The [global support theorem](IWANIEC_MORREY_RANKONE_SUPPORT.md)
provides an explicit determinant-affine minorant touching
at \(\operatorname{diag}(1,0)\), with a
**178+6-cell exact Bernstein/Hessian proof**
covering every real 2×2 matrix, and extends
through SO(2)×SO(2) isotropy and homogeneity.
The homogeneous-cone no-go remains valid,
but it no longer suggests this candidate
could violate QC at rank-one bases.
Do not spend further search effort on
**any amplitude** periodic gradient witnesses
at these bases.

The [separator nonrealizability theorem](IWANIEC_MORREY_SEPARATOR_NONREALIZABLE.md)
independently proves the old two-ratio
profile separator cannot meet the matrix
barycenter and determinant moments, even
before requiring gradient compatibility.
Its two exact SOS identities yield
\(\mathbb E\|A\|_{\rm op}\le59/60<1\).

### A sharper all-p nonconformal completion gate

For any differentiable isotropic positively
p-homogeneous integrand, the [one-multiplier
support criterion](IWANIEC_MORREY_GENERAL_SUPPORT_CRITERION.md)
gives a **necessary and sufficient** condition
for a global poly-affine minorant touching
at \(E_t=\operatorname{diag}(1,t)\), \(|t|<1\):
find \(c\) in the explicit orientation interval
satisfying one scalar inequality for
**every** amplitude a≥0 and signed
ratio s∈[-1,1]. For globally RC F the interval
has nonnegative width
\(2(ph(t)-2th'(t))/(1-t^2)\).
If there is no feasible c, **at most two
scalar amplitude/ratio tests** witness
failure (1D interval Helly theorem).
This is a finite *negative witness type*,
not a finite positive decision procedure.

**Main p>2 gate:** Prove a feasible c exists
for **every** nonnegative isotropic
rank-one-convex p-homogeneous integrand,
every exponent p>2, and every base t,
or construct an exact counterexample
to this *polyconvexity* claim.
The overall Morrey QC problem is still
weaker and remains open regardless
of a failed poly-affine support.

The exact p=4 support persists for an
**open C² neighborhood of profiles and
exponents near 4**, and for an
**open interval of nonconformal full-rank
base matrices**, by the strict exact
certificate and Hessian compactness.
This goes beyond the rank-one base
without inventing a finite cutoff.

**Prior-art qualification:** Wiedemann–Peter
(2026), [Theorem 1.4 and Corollary 1.5](https://doi.org/10.1007/s00526-025-03222-z),
already reduce global isotropic polyconvexity
to diagonal signed-singular variables.
The one-multiplier criterion specializes
that context; do not claim the general
diagonal reduction is new.

### Uniform local-gradient stability excludes every small perturbation

The exact p=4 candidate of the
[hybrid no-go](IWANIEC_MORREY_HYBRID_NOGO.md)
has an explicit 1/6 strict rank-one Hessian
margin at \(A_0=\operatorname{diag}(1,0)\).
A [global-frequency, local-amplitude proof](IWANIEC_MORREY_LOCAL_STABILITY.md)
gives \(J_F(A_0,\varphi)\ge
\frac1{24}\fint\|D\varphi\|_F^2\)
for **all** periodic fields whose gradients
are sufficiently small in L∞,
independent of wavelength or grid.
The same argument works uniformly on any
compact set of nonconformal nonzero bases,
using the strict acoustic positivity
from the exact rational certificate.

**Search gate:** No further small-amplitude
local test near such bases can give a
Morrey counterexample. A negative
gradient witness, if any, must be
large-amplitude/nonlinear. This is only
a stability result and does **not**
establish quasiconvexity for arbitrary
test gradients or settle Morrey.


### CLOSED: The proposed p>2 hybrid envelope is not complete

[Exact p=4 no-go theorem](IWANIEC_MORREY_HYBRID_NOGO.md)
gives an **entire globally rank-one-convex**, nonnegative isotropic
4-homogeneous F with a rational Bernstein
proof and strict rational two-point separator.
The hybrid envelope is strictly below F
at a rank-one base, with exact gap
\(356912972869/17832200896512>0\).
A standard-library rational [checker](../../research/audit/iwaniec_hybrid_no_go_exact.py)
verifies the scalar acoustic sign conditions and
the separating constants without floating point.

**Status:** the old G_p "completeness for all p>2"
gate is **refuted** already at p=4; it must not
remain an open positive target. This is NOT
a negative planar-gradient Jensen witness,
and therefore NOT a counterexample to
quasiconvexity or Morrey. The obstruction
applies to the stated generator class only,
not arbitrary quasiconvex functions.

**Reorientation:** either enlarge the
generator class in a provably useful way
or test the new exact F with actual periodic
gradient laws. Do not spend additional
effort on the false positive G_p statement.


### Exact univariate acoustic reduction of the whole smooth isotropic class

The [acoustic criterion](IWANIEC_MORREY_ACOUSTIC.md)
gives necessary-and-sufficient **rank-one convexity**
tests for every real-valued C² signed-singular profile
and every p>1, using **one scalar r∈(-1,1)**
and two endpoint conditions. Its exact algebra
is [symbolically checkable](../../research/audit/iwaniec_acoustic_exact.py).
No claim of priority over classical
Knowles–Sternberg-type conditions is made;
the global endpoint argument is still
hand-level, not Lean-checked.

**Main positive gate:** At p>2, prove that
every such admissible profile has a globally
touching minorant from the hybrid
Burkholder–polyconvex generator cone,
or produce an exact separating profile
showing the cone is incomplete. A separating
profile is only a method no-go, not a
Morrey counterexample. This is a universal
one-dimensional functional gate, **not**
a finite-mesh/fixed-degree search.


### Critical novelty and exponent correction

See [the exponent audit](IWANIEC_MORREY_EXPONENT_AUDIT.md).
The 0<p<1 case is trivial **in all matrix dimensions**:
every finite-valued globally RC p-homogeneous function vanishes.
At p=1, isotropic RC⇒convex on 2×2 is **Dacorogna (1989)**,
not a new result. Reserve novelty claims for an
independently validated all-base result at 1<p<2
or the signed p=2 conclusion. Main unclosed extensions:
signed 1<p<2, p>2 (the old hybrid-completeness
gate was refuted), or removing isotropy/homogeneity.

### Published warning: polyconvex level sets need not give polyconvex energies

Voss–Ghiba–Martin–Neff (2022)
[exhibit an isotropic RC but nonpolyconvex
integrand on GL⁺(2)](https://arxiv.org/abs/2009.09690)
with compact connected sublevel sets.
This refutes a naive function-level
inference from connected/convex
sublevels in that restricted domain.
It does **not** refute the globally
finite, nonnegative, p>2 homogeneous
Guerra–Kristensen question.
[Scope audit](IWANIEC_MORREY_LEVELSETS.md#3a-important-published-no-go-for-the-naive-cross-level-inference).
Use the **quantitative** four-atom
moment-energy inequalities, not
separate level-set inclusions, for
the remaining global proof.


### Global endpoint of finite-atom reduction: only T3/T4 remain

The [pair-merging theorem](IWANIEC_MORREY_FOUR_ATOM.md#5b-remove-all-rank-one-edges-from-a-minimal-negative-witness)
proves that **every** hypothetical
diagonal polyconvexity violation
has a minor-preserving witness
with **three or four atoms and
no rank-one-connected pair**.
Merging any rank-one-connected
pair preserves all four moments
and cannot increase the energy.
An exact four-atom unconnected
moment configuration confirms
the T4 geometry is nonempty.

This is a *completed global
structural reduction* with
uniform atom count independent
of p, profile, degree and mesh.
The remaining Jensen inequality
for the two continuous T3/T4
families is **unproved**.
Avoid branching to increasingly
large finite subclasses;
the universal functional
inequality is the next gate.


### Three-atom geometry: connected-pair class closed

In the [four-atom global theorem](IWANIEC_MORREY_FOUR_ATOM.md#5a-all-three-atom-laws-with-a-rank-one-pair-are-laminates),
**every** minors-preserving diagonal
three-atom law containing a rank-one
connected pair is a two-step laminate,
and hence obeys Jensen for every RC
integrand. This closes an infinite
geometric subclass, with no exponent
or profile restriction.
An [exact rational three-atom
example](../../research/audit/iwaniec_three_atom_geometry_exact.py)
shows the **remaining pairwise
unconnected** moment class is nonempty.
No energy inequality is solved there.
The genuinely unresolved
global diagonal-PC gates are
pairwise-unconnected three-atom
and arbitrary four-atom moment laws.


### Strict all-exponent supremal principle and power-witness limitation

The [strict global maximum principle](IWANIEC_MORREY_STRICT_SUPREMAL.md)
strengthens the published isotropic
polyconvex-sublevel conclusion:
for **every** nonnegative isotropic
positively p-homogeneous RC integrand,
any compactly supported probability
law preserving the matrix and determinant
moments whose support energies never
exceed \(F(A)>0\) must have
**all support energies equal to F(A)**.
The proof uses a full-dimensional
crosspolytope in the **five-dimensional
minors lift** at every strictly
lower-energy atom.

Consequently a strict Jensen violation
requires positive mass with energy both
**below and above** F(A). For every
**fixed** violating law, taking high
enough positive powers \(F^q\)
eventually **restores Jensen** for
that law, with an explicit q threshold
dependent on the law. There is no
uniform q across all laws: this
does **not** solve the global p≥4
PC or Morrey inequality. It rules out
a naive *single-law* extrapolation
from a putative p4 failure to all p>4.
The theorem is a hand deduction from
Conti–De Lellis–Müller–Romeo (2003),
not claimed publication-priority
or Lean-certified.


### Essential separation: three-atom PC tests versus actual gradient laws

[Three-atom rigidity audit](IWANIEC_MORREY_THREE_ATOM_RIGIDITY.md):
every homogeneous W¹∞ planar gradient
Young measure on ≤3 atoms is a
laminate. If one pair has rank-one
difference, determinant moment
compatibility gives a two-step
finite laminate; otherwise Šverák's
published three-gradient rigidity
forces the measure to be Dirac.
An exact rational example shows
three pairwise unconnected diagonal
atoms can satisfy *all minors moments*
yet fail gradient realizability.

**For the p≥4 polyconvexity target:**
Dacorogna–Koshigoe's universal test
STILL includes 3-atom laws; they may
refute PC without refuting QC.
**For Morrey:** any genuine nontrivial
finitely supported gradient law
needs ≥4 atoms. Four-atom T4
microstructures may be compatible
yet still laminates in the Jensen
sense—do not infer non-QC from
rank-two pairwise separation alone.
This prior-art theorem is a
research-route correction, not a
new proof of the universal
p≥4 or Morrey conjecture.


### Global exponent-descent obstruction: p=4 cannot simply represent p>4

The [exact all-exponent no-go](IWANIEC_MORREY_EXPONENT_DEMOTION_NOGO.md)
starts from the **globally polyconvex** isotropic
\(F_p(A)=(\det A)_+^{p/2}\) for arbitrary real p>4.
Replacing its p-homogeneity by any lower
degree q<p **without changing the signed-singular
profile** produces a function that fails rank-one
convexity along diag(1,t): the derivative
has an exact downward jump of q-p at t=1.
In particular the entire p>4 class cannot
be reduced to p=4 by multiplying by
\(\|A\|_{\rm op}^{4-p}\).

This is a *method obstruction*, NOT a
counterexample to the p>=4 polyconvexity
conjecture. A valid exponent-transfer
principle must change more than the
homogeneity prefactor, or use a
global argument independent of p.


### Exact five-variable support-obstruction query (all rational p≥4)

The [two-test interval/Helly encoding](IWANIEC_MORREY_PGE4_TWO_TEST_QE.md)
compresses failure of the Dacorogna–Koshigoe
poly-affine support at any nonconformal
base to a quantifier-free existential
real polynomial formula with just
**five real variables when p is integer,
seven when p is nonintegral rational**.
It works for polynomial profiles of
arbitrary finite degree. A local exact
nonlinear-real solver reported
UNSAT/SAT/SAT on three elementary
p=4 controls; the p=9/2 positive
control timed out. Both outcomes are
explicitly documented; no global
positive result is inferred.

**Critical premises:** To interpret an
UNSAT result as global polyconvexity
for p≥4, first verify that the input
is nonnegative and globally RC.
Conformal bases then use the published
Guerra–Kristensen theorem. For all
inputs without these premises, use
the direct four-atom QF_NRA query.
A PC failure is not an ordinary
Morrey quasiconvexity violation.


### Exact decision for EACH rational-polynomial input (not for the whole class)

[The complete input-wise QE reduction](IWANIEC_MORREY_PGE4_INSTANCE_QE.md)
encodes the full global p-homogeneous isotropic integrand
for **any specified rational p≥4 and rational
polynomial profile h of unrestricted degree**.
Three exact existential QF_NRA formulas
are SAT precisely when F fails
nonnegativity, rank-one convexity or
polyconvexity, respectively. The global
RC query uses the **defining rank-one
segment inequality**, not the smoother
acoustic shortcut; PC uses the published
1993 four-diagonal-atom equivalence.
Tarski–Seidenberg gives **complete
instance-wise decidability** with a
sound full QE/CAD engine.

**Stop rule:** No such engine was
run or is bundled. A generated
formula is NOT a certificate of
satisfiability or unsatisfiability.
This has no uniform degree or
rational-denominator cutoff and
does not decide irrational p,
arbitrary continuous h, or
nonpolyconvex quasiconvexity.
The global mathematical
\(\forall p\ge4,\forall F\) question
is still OPEN. Use this as a
candidate *validation interface*,
not as an alleged full proof.


### Uniform zero-amplitude support gap for ALL p>2

The [exact zero-amplitude theorem](IWANIEC_MORREY_PGE4_CONJUGATE.md#2a-new-zero-amplitude-is-automatically-safe-with-a-uniform-gap)
proves for **every** nonnegative
isotropic globally RC p-homogeneous
integrand with p>2, at each
nonconformal base E_t and every
orientation-admissible determinant
multiplier c,
\[
(p-1)h(t)-ct\ge (p-2)h(t)/2.
\]
Hence the a=0 support condition is
**automatic**. If h(t)>0,
every c is safe for all amplitudes
\(a\le\rho_t\) with an explicit
positive cutoff. Combined with
the previous large-amplitude cutoff
for strictly positive h, the
global scalar support problem
reduces to a compact **annulus**
\(\rho_t\le a\le R_t\),
uniformly over c in the
orientation interval.

This is a structural global
reduction (all p>2, all profiles),
not a proof that a common
support multiplier exists on
the remaining compact continuum.
No uniform all-integrand cutoff
or finite exhaustive
classification follows.


### All-p≥4 positive-proof reduction: one amplitude and explicit tail

The [Fenchel-conjugate support criterion](IWANIEC_MORREY_PGE4_CONJUGATE.md)
eliminates the second scalar variable
from the Dacorogna–Koshigoe
poly-affine support gate.
For each signed base ratio t,
a candidate determinant multiplier c
must satisfy **one scalar conjugate
inequality at every amplitude a>0**,
plus an explicit a=0 condition.
For any strictly positive profile
\(h_*=\min h>0\), **all amplitudes
a≥R are automatically safe** for
every c in the orientation interval,
with an explicit integer R determined
by h*,p,h(t),h'(t).

It also proves (without C² assumptions)
that **global PC for all strictly
positive nonnegative isotropic
p-homogeneous RC profiles, at each
fixed p≥4, implies the full
nonnegative-class theorem**:
add δ||A||_F^p and send δ→0 in the
minor-Jensen inequalities.

**Remaining gate:** Prove that the
resulting **compact continuum** of
conjugate inequalities has a common
c for every admissible profile.
This is NOT a finite list, no
uniform radius R exists across
all h by this argument, and the
proof of feasibility is OPEN.
A failed interval has a
two-amplitude dual obstruction
to **polyconvexity**, not directly
to quasiconvexity/Morrey.


### A rigorous all-p≥4 negative-certificate hierarchy (C² profiles)

The [global p≥4 semidecision theorem](IWANIEC_MORREY_PGE4_EXACT_HIERARCHY.md)
shows: **if** a nonnegative isotropic p≥4-homogeneous
rank-one-convex integrand with a C² signed-singular
profile fails global polyconvexity, **then**
a rational p≥4, a rational polynomial profile h,
and a minors-preserving rational diagonal law
on ≤4 atoms give a strict failure.
The rank-one-convexity certificate is a
**global** univariate rational Bernstein proof
over all signed ratios and all rank-one
directions. The [exact checker](../../research/audit/iwaniec_all_p_rational_cert.py)
handles rational exponents and rational-algebraic
Jensen powers. It passed strict positive
controls at p=4,9/2,5,6,10.

This hierarchy is **complete as a negative
semidecision only for the stated C² class**,
with unbounded degree, denominators, and
atom coordinates. It does NOT give a finite
positive decision procedure or a uniform
degree cutoff, and does NOT cover every
continuous/nonsmooth homogeneous RC
integrand. A negative *polyconvex* Jensen
law is not a gradient-law Morrey witness.
The old four-atom and isotropic diagonal
equivalences are Dacorogna–Koshigoe (1993)
prior art; the contribution here is a
strict regularization/rationalization
pipeline and exact checker for all p≥4.


### Global method stop rules: fractional powers and universal heatflow

The [exact fractional-power witness](IWANIEC_MORREY_FRACTIONAL_POWER_NOGO.md)
shows that raising the classical nonnegative
polyconvex quartic \(Q=s(s-2\det)\) to
\(p/4<1\) **destroys rank-one convexity**
for **every real 2<p<11/4**.
Thus downward power interpolation
from the p≥4 polyconvex quartic theorem
is NOT a general proof of all p>2.

The [exact three-wave Fourier theorem](IWANIEC_MORREY_P4_HEATFLOW_NOGO.md)
exhibits an **actual compatible smooth
periodic gradient**, with affine base, for
which the **globally polyconvex**
\(F=(\det A)^2\) has positive componentwise
heat-flow energy derivative **+920**.
The sign persists for \(F_p=|\det A|^{p/2}\)
on an open p-interval containing 4.
This supplies a short exact homogeneous
instance of the earlier H24 obstruction:
**universal heat-flow monotonicity is false
even inside the target positive isotropic
p>2 class**. It does NOT exclude specialized
flows, and is not a QC/Morrey counterexample.

**Decision:** The global G–K Question 1.7
still requires a new simultaneous
cross-level Jensen inequality or a
certified nonpolyconvex counterexample.
Do not repeat generic concave-power
interpolation or universal componentwise
heatflow as claimed positive completion
routes without a changed hypothesis.


### All-p quantitative global control, not yet an all-p proof

The [quadratic deficit theorem](IWANIEC_MORREY_GLOBAL_QUADRATIC_DEFICIT.md)
applies to EVERY finite nonnegative isotropic
rank-one-convex, positively p-homogeneous
\(F\) for **every real p≥2**, provided it
is C² near both nonzero conformal orientations.
Guerra–Kristensen's published determinant-power
polyconvex lower minorant, plus exact equality
of first derivatives at conformals, yields
\[
0\le F(A)-QF(A)\le
K_F\sigma_1(A)^{p-2}
(\sigma_1(A)-\sigma_2(A))^2
\quad\text{for all matrices }A.
\]
This is uniform over **all gradient laws,
oscillation frequencies and amplitudes**,
not a fixed-mesh bound. The rate improves
the earlier linear estimate but
**does not show zero deficit**;
the universal Jensen / full p>2 PC
question remains OPEN. It is a
straightforward quantitative consequence
of published conformal support,
not a new solution.

### Necessary quartic coefficient bounds and an entire closed sector

The [shear-bound theorem](IWANIEC_MORREY_QUARTIC_SHEAR_BOUND.md)
uses rank-one shear lines at I,D to prove
\(a\ge0,\ |b|\le4a\) for ALL invariant
quartic polynomials
\(F=a\,s^2+b\,s\,d+c\,d^2\),
and the diagonal Hessian gives the
universal necessary parabolic cutoff
\(c\ge3b^2/(8a)-2a\) for a>0.
Combining the sharp shear bound with
the previously proved positive-cone
decomposition closes **ALL** nonnegative
rank-one-convex quartics with
\(2a\le |b|\le4a\):
every one is globally PC.
Positive powers extend each to all
real p≥4.

The remaining low-coupling quartic
coefficients and all nonpolynomial
p>2 profiles are NOT classified by
these arguments; do not mistake
a coefficient-sector closure for
the unrestricted Guerra–Kristensen
question. The global QC/PC theorem
and, separately, Morrey itself
remain OPEN.


### CLASS-WIDE stop rule: positive Dacorogna–Marcellini stabilizations

An [exact quartic cone theorem](IWANIEC_MORREY_QUARTIC_STABILIZATION.md)
proves global **polyconvexity** for
\(P_{\gamma,c}(A)=s^2-2\gamma sd+c d^2\)
whenever 1≤|γ|≤2 and \(P_{\gamma,c}\ge0\)
everywhere. The nonnegativity threshold
is precisely \(c\ge4(|\gamma|-1)\),
and an explicit positive decomposition
into classical PC/convex generators
proves the conclusion. A wider
sufficient PC cone covers |γ|<1;
positive powers yield **all p≥4**.
[Exact coefficient checker](../../research/audit/iwaniec_dm_positive_stabilization_exact.py).

**Stop rule:** Never search for a
nonnegative isotropic RC/non-QC
counterexample in this **entire**
determinant-square-stabilized DM
quartic family, or its positive
powers at p≥4: every such member
is already PC. The universal
p>2 theorem, unrestricted
profiles and nonlinear forms
remain open. This is an analytic
infinite-parameter exclusion,
not a closure of the 1993
four-atom Jensen inequalities.


### PRIOR-ART CORRECTION: four atoms and supporting planes were known in 1993

[Dacorogna–Koshigoe (1993), Theorem 2.1](https://www.numdam.org/item/AFST_1993_6_2_2_163_0/), Theorem 2.1, already proves
both the **four-atom signed-diagonal Jensen equivalence** and the
**global poly-affine support equivalence** for SO(2)×SO(2)-isotropic
energies. Our rational sparsifier, one-multiplier formulas and
rank-one-pair merging are helpful explicit reformulations, but they
do NOT establish a new finite reduction. See the
[priority audit](IWANIEC_MORREY_PRIOR_ART_1993.md).

**No remaining finite-enumeration gate:** all unconnected three-/four-
atom configurations still range over continuous parameters, and the
universal Jensen inequalities remain open. Do not treat the 1993
criterion as progress towards proving the inequalities unless new
analytic control over all admissible integrands is obtained.

### GLOBAL bounded-atom reduction (all exponents, all profiles)

The new [four-atom theorem](IWANIEC_MORREY_FOUR_ATOM.md)
combines Wiedemann–Peter's published
isotropic diagonal characterization
with a four-moment extreme-point argument.
For **EVERY** finite nonnegative isotropic
RC p-homogeneous F and EVERY p>2,
F is globally polyconvex **iff** the
diagonal Jensen inequality holds for all
minor-preserving probability laws with
at most **four** atoms, at normalized
base \(E_t=\operatorname{diag}(1,t)\),
\(-1<t<1\). One- and two-atom laws
are automatically handled by RC.
Thus a negative counterexample to
the stronger polyconvexity question
is always witnessed by **three or
four** signed-diagonal atoms; a
nontrivial 3-atom law admits a
one-parameter covariance-free form.

**Crucial distinction:** This is
bounded in **atom count**, NOT a
finite degree/grid/coefficient
search. Real positions, weights,
exponents and profiles remain
arbitrary. The universal
3-/4-atom inequalities are **OPEN**.
An exact rational [cost-nonincreasing
reducer](../../research/audit/iwaniec_diagonal_four_atom.py)
checks all four moments.
A failure of the polyconvexity
inequality is **not** by itself an
actual planar-gradient Jensen gap
or a Morrey counterexample.


### Global all-exponent level-set result — closed, but weaker than Jensen

A [newly recorded all-\(p\) deduction](IWANIEC_MORREY_LEVELSETS.md)
from Conti–De Lellis–Müller–Romeo (2003) proves:
for every finite, nonnegative, SO(2)×SO(2)-isotropic,
positively homogeneous rank-one-convex integrand,
**every sublevel set is polyconvex**, without
a coercivity restriction. It yields the global
\(L^\infty\) supremal quasiconvexity inequality
at every matrix and for every bounded periodic
gradient, with arbitrary amplitude and scale.

**Critical scope warning:** The theorem concerns
the supremum of energy over a gradient field,
not the integral average. It does NOT establish
rank-one convexity⇒ordinary quasiconvexity for p>2,
and this is a direct corollary of published
set-hull theory, not a new solution.
The missing theorem is **cross-level compatibility**
of polyconvex supports or the global
one-multiplier feasibility in the signed-singular
profile representation. Do not treat
polyconvexity of all sets as polyconvexity
of the energy.


## 0. Iwaniec-dependent route (22 November 2026)

The [universal isotropic note](IWANIEC_MORREY_UNIVERSAL.md) proposes
an all-matrix RC→QC proof for every nonnegative isotropic p-homogeneous
2×2 integrand with 1<p<2 (conditional on the global 2026 Burkholder
quasiconvexity result), and an unconditional hand argument for p=2.
The new [hybrid hierarchy](IWANIEC_MORREY_GENERAL.md) gives an explicit
all-matrix quasiconvex minorant and a one-dimensional cone-completeness
gate for **every p>2**, plus GL-transformed anisotropic and
nonhomogeneous positive closures. Neither route settles arbitrary
2×2 integrands.

**Gate I8 CLOSED (negative):** The universal identity `E_p h=h` is **false**, by the [exact p=4 no-go](IWANIEC_MORREY_HYBRID_NOGO.md), and its failure persists on an [open family of profiles/exponents](IWANIEC_MORREY_HYBRID_OPEN.md). Do not try to establish this invalid positive completeness target. The unrestricted Morrey gate requires a genuinely stronger certificate family, an all-gradient inequality, or an actual planar negative witness.

The new research contains no Lean translation or independent
validation of Iwaniec's full proof. This Iwaniec-dependent route
must remain separate from the unrestricted negative-witness
search described below.

## 1. What counts as completion

| Route | Required mathematical output | Final formal output |
| --- | --- | --- |
| Positive | For every finite-valued rank-one-convex `f : ℝ²ˣ² → ℝ`, every base `F`, and every admissible planar test map `u`, prove `average f(F + Du) ≥ f(F)`. | A proof of `Pedregal.Theorem1_1_part2` or `Pedregal.Theorem1_2`, with an explicit bridge from any alternative definitions. |
| Negative | Exhibit a continuous finite-valued `f : ℝ²ˣ² → ℝ`, prove rank-one convexity globally, and give an actual planar gradient witness with a certified strict negative gap. | A planar theorem asserting continuity, rank-one convexity and failure of quasiconvexity in one of the project's definitions, with the needed bridges. |

The all-level **finite-order** laminate statement is sufficient for the positive route and is
stronger than the Jensen property actually needed. Abandoning that stronger statement is allowed.
Showing that a prescribed finite tree fails is not evidence that its gradient law violates Jensen.

## 2. Immediate priorities after the audit

The [22 November formalization audit](MAIN_FORMALIZATION_AUDIT.md) adds universal finite-laminate
Jensen, exact planar definition bridges, the dimension-general C² LH equivalence and an actual
periodic-gap acceptance theorem. Their Lean validation is recorded in that audit. These close
interfaces; they do not supply the open universal Jensen theorem or a negative candidate.
The remaining formal tasks are the exact polynomial-certificate evaluator and the periodic PL
gradient-sum-to-integral identity; the positive route additionally needs controlled dyadic
approximation. Do not treat numerical certificate checking as if it already instantiated the
Lean acceptance theorem.

Start with [COMPLETION_AUDIT.md](COMPLETION_AUDIT.md), the new exact interfaces in
[research/audit](../../research/audit/README.md), and the current [formal baseline](FORMAL_STATUS.md).
The source inventory and exact controls have been checked; repeat them after relevant changes,
not as a substitute for advancing the unresolved construction.

| Priority | Deliverable | Acceptance / stop rule |
| --- | --- | --- |
| 1 | Integrate range-sensitive base recovery and boundary Gram handling into a new discovery driver. | Use the exact quadratic diagnostic on reconstructed rational candidates. Monitor discarded linear components during floating exploration; do not silently discard tiny positive curvature. Permit singular certificates or a justified vanishing-margin schedule. |
| 2 | Add weighted-Gram discovery and rational certificate extraction, using the existing norm-basis builder and verifier. | Produce a coefficient identity with exact nonnegative square weights/PSD proof. Test the same actual-gradient inputs at orders zero and one with a recorded finite budget; do not interpret a null result as class exclusion. |
| 3 | If weighted discovery is impractical, try strict local-ball LH discovery with the explicit global radial tail. | Certify the ball, a buffer around every witness gradient, the tail bound and a surviving negative gap. Merely local RC is insufficient. |
| 4 | Independently evaluate and formalize any strict negative candidate immediately. | Same rational integrand, exact global LH certificate, actual planar test map and a strict negative integral. Reuse the existing periodic Lipschitz/domain equivalences. |
| 5 | On the positive route, prove universal exact Hessian-certificate feasibility or an equivalent all-gradient inequality. | All degrees and all admissible fields are covered. The radial-moment lemma supplies the subsequent compactness; isolated certificates are insufficient. |

The current package implements **verification**, basis enumeration and exact base diagnostics.
It does not implement a weighted-Gram solver, automatic rational extraction or an exhaustive
search. Those are concrete next engineering tasks, not completed capabilities.

There is no justified completion date or finite degree/grid/order cutoff. A bounded search can
end; the unrestricted mathematical question remains open if it finds nothing. The P₂ all-field
inequality in [STRUCTURAL_AUDIT.md](STRUCTURAL_AUDIT.md) is a useful subordinate benchmark with
a meaningful analytic endpoint. It must not displace the unrestricted goal.

## 3. Negative route: candidate to theorem

### N1 — Search in a class with a global certificate route

The polynomial/dyadic reduction H07 and the new [norm-multiplier proof](GLOBAL_CERTIFICATES.md)
give a complete negative-witness certificate hierarchy after a strict radial perturbation.
Enumerating polynomial degree, mesh, rational heights and multiplier order can detect a
counterexample if one exists. No finite bound or positive termination is supplied. A fixed
unweighted SOS class or a fixed positive Gram floor is still restrictive.

For degree at most `2m`, the exact format is
`(Nx Na Nb)^k [F_P − δ Nx^(m−1)NaNb] = Σ q_j²`, with rational `δ>0` and the homogenized LH
form `F_P`. The [verifier](../../research/audit/sphere_certificate.py) already checks this
identity and actual rational periodic PL witnesses. A strict local-on-ball certificate plus
the explicit radial extension is another valid discovery route.

Each finite campaign must state which certificate freedom changes, its actual-gradient
parameterization, artificial margins/penalties and budget. Remove permanent covariance
exclusions and let artificial margins decrease in any completeness claim. Alternating
optimization remains local even when every SDP subproblem is solved correctly.

**Exit:** save explicit integrand coefficients, base matrix, domain, actual nodal/Fourier map,
normalization and a strict negative candidate gap. A raw measure with the correct mean and
determinant moment does not meet this gate. Neither does the `3 × 2` positive control.

### N2 — Certify rank-one convexity everywhere

For a polynomial `P`, verify
`D²P(A)[a ⊗ n, a ⊗ n] ≥ 0` for every real `A, a, n`, then supply the elementary bridge from the
Hessian inequality to convexity along rank-one lines. Options include an exact rational Gram
identity with exact PSD factorization, a rigorous analytic inequality or real-algebraic
certification. If a floating SDP is rationalized, recheck every coefficient and positivity
condition after rationalization.

**Exit:** a standalone replayable certificate and its mathematical interpretation. Finite
curvature sampling, small identity residuals, approximate positive eigenvalues or solver
`optimal` status do not suffice. Failure of one SOS relaxation does not prove failure of RC.

### N3 — Certify the actual integral and admissibility

For periodic piecewise affine maps, use the exact triangle gradients and area weights; for
Fourier maps, use exact moments or interval quadrature with an explicit error bound. Independently
check gradient compatibility, mean gradient zero and the determinant identity. These identities
are necessary checks, not a substitute for constructing the map.

**Exit:** `J ≤ −ε` for an explicit positive rational `ε`, or an interval upper endpoint below
zero, after every approximation and rounding error is included. Save a second evaluator that
does not reuse the discovery code's derivative assembly.

The source now contains the general **periodic Lipschitz** equivalence
[External.Rindler.quasiconvexAtOn_iff_periodic](../../Morrey/Common/External/Rindler/Lemmas.lean),
and the bounded-open-domain equivalence in the same file. For a polynomial FE candidate,
instantiate lower semicontinuity/local boundedness, the actual periodic Lipschitz map and its
integral; a new general smoothing/cutoff proof is unnecessary. The older smooth witness lemma
[Sverak.lemma1_witness](../../Morrey/Sverak/Lemma1.lean) remains an alternative when an explicit
smooth compactly supported witness is wanted.

### N4 — Formalize and independently review the final statement

Translate the candidate, exact certificate and witness into Lean, including integrability and
the chosen definition of quasiconvexity. Use the existing Cassese–Šverák bridges where their
hypotheses fit; add the missing Pedregal bridge if that is the final interface.

**Exit:** the final planar theorem is proved, its definition matches the intended question,
`lake build` and the axiom audit pass, applicable route/Comparator checks pass, and an independent
review checks both the mathematical argument and the statement. A build that leaves the main
claim as `def ... : Prop` is not completion.

## 4. Positive route: the missing all-scale argument

### P1 — Select a sufficient global target

Choose an all-gradient Jensen inequality, a suitably controlled limiting laminate construction,
or the stronger all-level finite-order statement. Another sufficient target is: for every
compact actual planar gradient law and every degree `d`, construct an exact positive
rank-one-Hessian representation of its Jensen functional on polynomials of degree at most `d`.
State the quantifiers over bases, integrands, maps and degrees explicitly.

The [radial-moment theorem](GLOBAL_CERTIFICATES.md#4-correct-compactness-theorem-for-positive-certificates)
shows that these finite-degree positive measures need **no additional inter-degree consistency
or common support assumption**. Fixed mass and radial moments supply tightness, tail control
and a limit supported in the convex hull of the law. For arbitrary approximate certificates,
quantitative error and moment control would still be needed.

**Exit:** a precise universal feasibility theorem and its implication to the planar Morrey
statement. The conic-duality reductions H10–H11 and compactness theorem A04 do not construct
the positive measures; existence remains P2.

### P2 — Prove the central global existence or inequality

This is the unresolved mathematical core. Pedregal's map has empty values; another fixed-point
theorem cannot supply a missing hypothesis. A replacement map needs its own existence,
positivity, compatibility and compactness proof. Freeing weights changes the algebra and may
remove convexity, so it cannot be treated as a routine repair.

**Exit:** a proof applying to all admissible planar inputs. An all-quartic result, if obtained,
would be a major intermediate theorem, but would still require an all-degree/general-integrand
bridge. One fixed mesh, one open set of gradient laws or finitely many positive moment
certificates does not close this gate.

### P3 — Complete the analytic reduction in the appropriate definitions

For a laminate approach, prove Jensen for the project's `IsLaminate`, translation by a base
matrix, controlled dyadic interpolation of periodic maps and energy convergence. Reuse the
already available finite-valued RC local Lipschitz theorem and periodic Lipschitz/domain
bridges (F13–F14). A weak-limit/Hessian-measure approach instead assembles its limiting Jensen
theorem and the regularization/definition bridges it needs. The remaining work is integration
with the chosen universal hypothesis, not a new proof of every general analytic lemma.

**Exit:** a formal implication from the selected universal hypothesis to
`Pedregal.Theorem1_1_part2`. This work can proceed independently; it must continue to display
P2 as an assumption until P2 is actually proved.

### P4 — Independent review and formal closure

Check the universal quantifiers, zero-weight/boundary cases, and all compactness/positivity
arguments. Then implement the core proof and run the project's formal validation. No assertion
in an auxiliary file or imported axiom may stand in for the central theorem.

## 5. Useful side deliverables, with separate completion criteria

| Deliverable | What would complete it | Why it does not complete Morrey |
| --- | --- | --- |
| Pedregal-method note | Expose the existing formal counterexample and clearly identify the exact false premise; independently review the paper correspondence. | Refutes this argument, not its conclusion. No all-mold theorem is needed. |
| Universal level-one mold | Port the exact 48 leaf tags to `Pedregal.TriMold 1` and check all constraints in Lean. | Corrects the false B/B₁ conjectures; remains level one. |
| Uniform-weight obstruction at higher levels | Formalize the finite determinant/translation reduction and the refinement step. | Excludes uniform weights for certain data; does not exclude nonuniform fixed points. |
| Structural quartic lemmas | Independently audit and formalize the flat-line, rank-one-null, orbit and cone arguments, preserving hypotheses. | Gives subclasses or obstructions, without classifying all RC integrands. |
| Reuse Cassese infrastructure | Instantiate the current main-branch regularity, periodic/domain, polynomial and minor tools in the final planar construction. Preserve the named hypotheses of conditional nonplanar results. | Cassese's quartic is now formalized in `2 × 3`; it does not restrict automatically to a planar counterexample. |

## 6. Routes that require a new hypothesis before reopening

| Prior route | Present disposition | What would justify reopening |
| --- | --- | --- |
| Universal nonemptiness of Pedregal's original map | Refuted in Lean. | A changed construction with all needed hypotheses proved. |
| No fixed point for any level-one mold (B/B₁) | Refuted by the universal mold S*. | A genuinely different quantifier/level claim, stated explicitly. |
| Universal componentwise heat-flow energy decrease | Explicit failure even for a strongly RC polyconvex integrand. | A restricted class or different flow with a new sign argument. |
| Automatic spatial-averaging-to-laminate inference | Explicit split of rank two. | An adaptive construction with proved rank-one increments. |
| Linear span of known quartics implies positive-cone generation | Invalid inference; later cone obstruction is stronger. | A new positive decomposition theorem with valid coefficients. |
| Nonpolyconvexity plus compatible minors produces a gradient witness | False; explicit moment witnesses show the gap. | A realization theorem or an actual compatible map. |
| Quadratic bivector-norm affine planar pullbacks | Hand argument makes this class polyconvex. | A construction outside the stated form, or a flaw found in that argument. |
| Pure curvature sampling as a certificate | Earlier negative candidates failed exact LH tests. | A global exact/interval certificate. |
| Fixed positive Gram margin as an exhaustive SOS search | P₂ has exact LH-SOS but zero curvature at a nonzero feature vector. | Boundary-capable certificates or a justified margin schedule; no fixed-margin completeness claim. |
| More unstructured starts in the same quartic wells | Latest trials found flat/determinant-square/zero-integrand degeneracies. | Changed variables, geometry, objective or certificate class, with an explicit budget. |

The authoritative result and evidence for each disposition are in [LEDGER.md](LEDGER.md).
Keep this table updated when a hypothesis changes; preserve the previous rejection record.
