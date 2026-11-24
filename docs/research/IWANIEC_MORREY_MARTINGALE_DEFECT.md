# Unrestricted route: scalar martingale determinant defect, quantitative repair, and Beurling projection

23 November 2026. Hand proofs with exact rational regression controls.
**No fixed-wave-count hypothesis, isotropy, homogeneity, degree bound,
or small-amplitude assumption. Morrey remains open.**
The purpose is to replace the unbounded wave-case ladder with one
global nonnegative variational objective. No novelty clearance,
independent human review or Lean verification is claimed.

The classical background is the approximation of compact laminates
by finite-order laminates in a bounded open neighborhood of their
rank-one convex hull (Müller–Šverák, Theorem 3.1, JEMS 1 (1999),
393–422, https://sites.pitt.edu/~lewicka/2303/muller_sverak_convex_integration.pdf).
The laminate characterization and the martingale connections are
standard; see [Guerra–Teixeira da Costa (2022)](https://doi.org/10.4171/RMI/1286)
and [Bañuelos–Janakiraman](https://www.math.purdue.edu/~banuelos/Papers/Beur_Ahl.pdf)
for the projected stochastic representation of the Beurling–Ahlfors
transform. The explicit repair/transfer and dual arguments below
are derived here, not attributed to those sources.

## 1. One scalar objective on arbitrary bounded laws

All matrix norms below are Frobenius norms. Let X have an arbitrary
compactly supported law nu on R^{2x2}, with mean A and support in
the closed ball B_R(A), R>0. Permit arbitrary auxiliary randomness.
Take any finite filtration with trivial initial sigma algebra
and binary refinements (the two child probabilities need not
be equal). Write M_j=E[X|F_j], so M_0=A. The terminal X need
not have been completely revealed.

Define
$$
D(\nu)=\inf_{\mathcal F}
\mathbb E\left[\sum_{j=1}^n|\det(M_j-M_{j-1})|
                  +\tfrac12|X-M_n|^2\right]. \tag{1}
$$
Depth zero is allowed. The infimum is over all such experiments
and realizations of X. All conditional means stay in B_R(A).
Allowing randomized observations is important; a predetermined
spatial dyadic grid is not an equivalent restriction.

The cost is nonnegative, at most Var(X)/2, translation-invariant,
and homogeneous of degree two under scalar multiplication of X.
No dependence on frequency or polynomial degree occurs.

**Theorem A (global quantitative repair).** For every nu as above
and every r>0, a particular experiment with defect term c_1 and
residual term c_2 produces a finite-order laminate mu of mean A
supported in B_{3R+r}(A), satisfying
$$
W_2(\nu,\mu)^2\le (1+R^2/r^2)c_1+2c_2. \tag{2}
$$
In particular
$$
\inf_{\substack{\mu\ \text{finite-order laminate}\\
                  \bar\mu=A,\ \operatorname{supp}\mu\subset B_{4R}(A)}}
W_2(\nu,\mu)^2\le 2D(\nu). \tag{3}
$$

**Proof.** At a binary node let p and 1-p be the child weights
and let H be the difference of the two conditional means.
The original increments are (1-p)H and -pH. Truncate H to a
nearest rank-at-most-one matrix H' by retaining its larger
singular value. If its singular values are s_1>=s_2, then
|H-H'|^2=s_2^2<=s_1s_2=|det H|. Use the same weights and
replace the increments by (1-p)H' and -pH'. Zero-weight
nodes can simply be removed. Iteration gives a martingale Y,
starting at A, on the same finite tree, with rank-one child
differences. Its error E_j=Y_j-M_j is a martingale, and at
every step
$$
|\Delta E_j|^2\le|\det\Delta M_j|.
$$
By orthogonality, E|E_n|^2<=c_1.

Stop both processes at tau, the first index with |E_j|>=r,
or at n if no such index occurs. Before crossing, |E_j|<r.
The crossing increment has norm at most |Delta M_j|<=2R.
Hence |Y_tau-A|<=R+r+2R. Stopping Y on its binary tree
still yields a finite-order laminate of mean A.

Optional orthogonality gives E|E_tau|^2<=c_1 and
P(tau<n)<=c_1/r^2. Since X is in B_R(A),
$$
E[|X-M_\tau|^2|\mathcal F_\tau]
=E[|X-A|^2|\mathcal F_\tau]-|M_\tau-A|^2\le R^2.
$$
On tau=n the expected residual is at most its original
unconditional value 2c_2. Finally E[X-M_tau|F_tau]=0, so
the cross term with E_tau vanishes, giving
$$
E|X-Y_\tau|^2
=E|X-M_\tau|^2+E|E_\tau|^2
\le (R^2/r^2)c_1+2c_2+c_1.
$$
This is an actual coupling, so it bounds W_2 squared.
Set r=R and take the infimum to obtain (3). QED.

## 2. Transfer between arbitrary laws and the exact unrestricted criterion

**Theorem B (global transfer).** Suppose X,Y are coupled square-
integrable matrix variables with the SAME mean A, and set
epsilon^2=E|X-Y|^2, sigma_Y^2=E|Y-A|^2. Then
$$
D(\operatorname{law}X)\le
 D(\operatorname{law}Y)+\sigma_Y\epsilon+\epsilon^2/2. \tag{4}
$$
Formula (1) also makes sense for square-integrable laws, even
when not compactly supported. No boundedness is required for (4).

**Proof.** Start with any experiment for Y. Glue the given
conditional law of X given Y to that experiment, retaining its
filtration. Standard Borel matrix-valued random variables admit
the needed conditional law; the experiment can also be encoded
by its finite leaf label. Put N_j=E[Y|F_j] and
L_j=E[X-Y|F_j]. Then M_j=N_j+L_j and L_0=0. In 2x2,
$$
|\det(U+V)|\le|\det U|+|U||V|+\tfrac12|V|^2,
$$
by determinant polarization, |cof U|=|U| and
|det V|<=|V|^2/2. Apply this to each increment. For the
residual term use the corresponding expansion of
|X-M_n|^2/2 around Y-N_n. The two orthogonal variance
identities are
$$
E\sum|\Delta N_j|^2+E|Y-N_n|^2=\sigma_Y^2,
$$
$$
E\sum|\Delta L_j|^2+
E|(X-Y)-L_n|^2=\epsilon^2.
$$
Cauchy–Schwarz over all increments AND the residual
bounds the sum of the mixed terms by sigma_Y epsilon.
The quadratic error terms total epsilon^2/2. Taking the
infimum proves (4). QED.

For laws in a fixed ball with fixed mean A this implies
the symmetric continuity estimate
$$
|D(\nu)-D(\mu)|\le R W_2(\nu,\mu)+W_2(\nu,\mu)^2/2. \tag{5}
$$

**Corollary C.** For compactly supported nu, D(nu)=0 if and
only if nu is a laminate. In particular the unrestricted
planar Morrey implication is equivalent to the ONE
global assertion
$$
\boxed{D(\operatorname{law}(A+D\varphi))=0
\quad\text{for every periodic Lipschitz }\varphi,\ \text{every }A.}
\tag{6}
$$

If D=0, Theorem A gives finite-order laminates with a common
compact support bound converging to nu in W_2. Jensen passes
to the limit for every finite-valued RC function by continuity
on that common compact set. Conversely, a compact laminate
is approximated by finite-order laminates in any open ball
containing its convex hull (classical Müller–Šverák approximation
theorem cited above). Their barycenters converge to A and
can be translated to A without affecting their lamination
property or convergence. Their variances are uniformly bounded.
Each finite-order laminate has D=0, by its binary splitting
tree. Equation (4) with W_2 convergence proves D(nu)=0.
The periodic Lipschitz equivalence then gives (6).

A separate direct all-integrand estimate needs no approximation
theorem. If F is C^2 and rank-one convex and its Hessian operator
norm on B_R(A) is at most K, any matrix H splits by singular
value decomposition as H=H_1+H_2 with both rank at most one,
|H_1||H_2|=|det H|. Therefore
$$
D^2F(B)[H,H]\ge-2K|\det H|,\quad B\in B_R(A).
$$
Taylor's integral formula along each conditional increment,
followed by cancellation of its conditional linear term,
and a final Taylor estimate for X-M_n give
$$
F(A)-E F(X)\le K D(\nu). \tag{7}
$$
Thus any strict Morrey counterexample with gap Delta>0
for a smooth integrand with Hessian bound K>0 must have
D(nu)>=Delta/K. This is a normalized scalar obstruction,
not an assertion that a negative witness exists.

## 3. Exact Bellman dual on a compact ball

Fix B=B_R(A). Write P_x(B) for probability measures on B
of mean x. Define a continuous function f on B to be
determinant-penalized convex if for all y,z in B and
p in [0,1],
$$
f(py+(1-p)z)\le pf(y)+(1-p)f(z)+p(1-p)|\det(y-z)|. \tag{8}
$$
Since |det H|<=|H|^2/2, this also implies ordinary convexity
of f+|.|^2/2 on B. On a neighborhood of B, for C^2 f,
(8) on B is equivalent to
$$
D^2 f(x)[H,H]\ge -2|\det H|\qquad(x\in B,\ H\in R^{2x2}).
\tag{9}
$$
Necessity follows from small midpoint splits in the interior
and continuity to the boundary. Sufficiency follows by convexity
of t -> f(z+t(y-z))+t^2|det(y-z)| on [0,1].
In particular these functions are rank-one convex on B.

**Theorem D (exact dual, not just an upper bound).**
$$
D(\nu)=\sup_{f\ \text{satisfying (8)}}\left[f(A)-\int f\,d\nu\right],
\quad \nu\in P_A(B). \tag{10}
$$
The supremum is unchanged if we use only C^infinity functions
defined on a neighborhood of B satisfying (9) there on B.

**Proof.** First telescope (8) along an arbitrary binary
tree of conditional means. The conditional expected penalty
is exactly p(1-p)|det(y-z)|. The remaining terminal deficit
is at most E|X-M_n|^2/2 by conditional Jensen for the convex
function f+|.|^2/2. This proves the upper bound in (10).

For the reverse, D on P_A(B) is convex: mix two experiments
at an initial random binary branch, both children having
mean A, so this branch costs zero. Pad their depths with
trivial splits if necessary. By (5), D is continuous for
the weak topology on this compact set of laws (weak and
W_2 convergence agree on B). Its epigraph is closed and
convex in the weak topology of signed measures times R.
Separating (nu,t) for any t<D(nu) from that epigraph
gives the familiar exact convex dual
$$
D(\nu)=\sup_{g\in C(B)}
\left[\inf_{\eta\in P_A(B)}\big(\int g\,d\eta+D(\eta)\big)
-\int g\,d\nu\right]. \tag{11}
$$
Indeed the separating functional's vertical coefficient
must be positive: the epigraph is unbounded upwards
and contains a point with horizontal coordinate nu.
Normalize that coefficient to one.

For fixed g, define the value function on the whole ball:
$$
v_0(x)=\inf_{\eta\in P_x(B)}\int
   (g(y)+|y-x|^2/2)\,d\eta(y)
=\operatorname{conv}_B(g+|.|^2/2)(x)-|x|^2/2,
$$
where conv_B is the lower convex envelope, equivalently
the infimum of averages at fixed mean. Then set
$$
v_{n+1}(x)=\inf_{\substack{p,y,z\\ x=py+(1-p)z}}
\big[pv_n(y)+(1-p)v_n(z)+p(1-p)|\det(y-z)|\big]. \tag{12}
$$
This recurrence is exact for depth-n binary experiments
with arbitrary conditional terminal laws at the leaves:
the one-step cost is the conditional determinant cost;
leaf residual is v_0. Finite tree laws can be glued
by choosing independent random branches and sampling
from the chosen leaf's terminal law. Conversely any
experiment gives such a tree. Thus v=inf_n v_n satisfies
v(A)=inf_eta(integral g d eta+D(eta)). No finite-depth
termination claim is made here.

The v_n decrease (trivial splits are allowed), are
bounded below by min g, and v<=g. Passing to the
limit in the one-step upper inequalities proves (8)
for v. Hence v+|.|^2/2 is finite convex and v continuous
on the interior. For a boundary point x of B the only
law of mean x is delta_x, so v(x)=g(x). Moreover, for
all laws of mean x in B, the variance is at most
R^2-|x-A|^2. Uniform continuity and boundedness of g
give integral g >= g(x)-o(1) uniformly as x approaches
the boundary (split at distance delta and use Chebyshev).
All costs are nonnegative, so v is continuous up to the
boundary as well. In (11) we can replace each g by the
admissible f=v: its value at A is exactly the infimum
in (11), and its integral is no larger than that of g.
Together with the upper bound already proved this gives
(10).

Finally contract an admissible f by x -> A+(1-delta)(x-A),
defining it on a slightly enlarged ball. Inequality (8)
persists there since the determinant penalty scales by
(1-delta)^2<=1. Mollify with support smaller than the
enlargement; the same inequalities hold on a neighborhood
of B. Uniform continuity gives uniform convergence on B
as delta and mollifier radius go to zero. The smooth
equivalence (9) proves the last assertion. QED.

**Interpretation.** (10) is a global primal/dual identity
for a scalar defect value with explicit determinant cost.
It is not proposed as another infinite enumeration of
(12). The missing theorem is zero cost for actual
compatible gradients, not computation of v_n for isolated
finite laws. A positive proof would need a universal
construction or variational estimate, not success on
a sequence of larger meshes.

## 4. Continuous martingales: exact determinant-neutral covariance cone

The preceding discrete repair does not require stochastic
calculus. The following continuous estimate is useful for
the Beurling–Ahlfors route. Identify matrices with R^4;
let J=D^2 det be the constant symmetric matrix, so
H^T J H=2 det H.

**Lemma E.** A positive semidefinite 4x4 covariance matrix S
with tr(JS)=0 is a finite sum of outer products R_i R_i^T
of matrices R_i of rank at most one.

Factor S=UU^T, with U having r columns. The symmetric
r-by-r matrix U^T J U has trace zero. It has an orthonormal
basis with every diagonal entry zero: if nonzero, either
an isotropic unit eigenvector exists or interpolate unit
vectors between a positive and a negative eigenvector,
then restrict the form to the orthogonal complement,
whose trace is again zero. Induction gives the basis.
Apply U to that basis; each image has determinant zero
and their outer products sum to S. The converse follows
immediately by taking the trace against J.

For a square-integrable continuous matrix martingale Z_t
starting at A, write its signed determinant-bracket defect
as the random finite-variation measure
$$
d\zeta=d\langle Z_{11},Z_{22}\rangle
        -d\langle Z_{12},Z_{21}\rangle.
$$
If F is globally C^2 RC with ||D^2F||_op<=K, then
$$
F(A)-E F(Z_T)\le K E|\zeta|([0,T]). \tag{13}
$$

**Proof.** Take the covariance density S relative to the
trace of the positive semidefinite quadratic-variation
measure; write d=tr(JS)/2, the signed defect density.
Choose a unit Frobenius matrix W of determinant
-sign(d)/2, e.g. I/sqrt(2) or diag(1,-1)/sqrt(2).
Then S+2|d|WW^T is PSD and determinant-neutral.
By Lemma E its contraction with D^2F is nonnegative.
Consequently D^2F:S>=-2K|d|. Integrate Itô's formula;
the factor 1/2 yields (13).
Localization is justified by the Hessian bound,
finite expected total quadratic variation, and L2
uniform integrability of the closed martingale at
bounded stopping times (or stop at bounded matrix
norm and bracket, then pass to the limit). Thus
no uniform L-infinity bound on Z is needed. QED.

This gives a direct continuous counterpart to (7).
It is not enough that E zeta([0,T])=0; the absolute
variation is the relevant quantity.

## 5. A quantitative solution of the projection LOSS, conditional
##    on constructing nearly balanced Beurling martingales

Identify a planar matrix with the complex pair (v,u)
of conformal and anticonformal derivatives:
v=(A11+A22+i(A21-A12))/2,
u=(A11-A22+i(A21+A12))/2.
Then det A=|v|^2-|u|^2 and |A|^2=2(|v|^2+|u|^2).
Denote the inverse linear identification by L.

For a smooth periodic complex-valued deformation phi,
let g=phi_bar_z, h=phi_z=B g, where B is the periodic
Beurling–Ahlfors Fourier multiplier on mean-zero data
(the multiplier has modulus one at every nonzero
frequency). Thus E|h|^2=E|g|^2 with respect to the
uniform torus variable P. The actual gradient law
is X=A+L(h(P),g(P)).

Suppose we can represent g,h through square-integrable
continuous complex martingales U,V starting at zero,
with
$$
U_T=g(P),\qquad E[V_T|P]=h(P),
$$
and define the scalar absolute bracket mismatch
$$
\delta=E\,\operatorname{TV}\big(d\langle V\rangle
                                      -d\langle U\rangle\big).
\tag{14}
$$
Here the complex bracket denotes the sum of the real
and imaginary coordinate quadratic variations, not
the complex bilinear bracket. For Y=A+L(V_T,U_T),
E[Y|P]=X. Unitarity and orthogonality give the exact
projection variance identity
$$
E|V_T-h(P)|^2=E|V_T|^2-E|h(P)|^2
=E(\langle V\rangle_T-\langle U\rangle_T)\le\delta. \tag{15}
$$
In particular if the brackets are exactly balanced,
there can be NO hidden projection variance at all.
This is why L2 equality must not be confused with a
pathwise bracket identity.

For every globally C^2 RC F of Hessian bound K,
Lemma E and (13) applied to the matrix martingale
A+L(V_t,U_t) give E F(Y)>=F(A)-K delta. Its
determinant-bracket defect is exactly the difference
of the complex trace brackets in (14).
On the other hand Taylor's formula around X, using
E[Y-X|P]=0 and (15), gives
$$
|E F(Y)-E F(X)|\le (K/2)E|Y-X|^2\le K\delta.
$$
Combining yields the **all-gradient projection bound**
$$
\boxed{F(A)-E F(A+D\varphi)\le 2K\delta.} \tag{16}
$$
No conditional Jensen for an RC function has been
assumed. This is an L2/Taylor argument specific to the
projection variance, with no ordinary convexity assumption.

**Removing the bounded-Hessian restriction.** It suffices
to prove quasiconvexity for smooth globally RC functions of
bounded Hessian. Given any smooth globally RC F and any
closed ball containing the bounded test gradients and base,
choose radii r_0<R_0<R_1 around a fixed center, with the
test ball inside radius r_0. Take a smooth radial cutoff
chi equal to one through R_0 and zero beyond R_1.
Its product with F has bounded Hessian. Add a smooth
convex radial tail G(A)=K_0 b(rho), rho the distance
from the center, with b=0 for rho<=r_0 and
b''=psi on rho>r_0, where psi is smooth nonnegative,
at most one, and identically one from
r_m=(r_0+R_0)/2 onward. Integrate twice from r_0
with zero initial values. The radial eigenvalue of
D^2 b is psi, and the tangential eigenvalues are b'/rho.
All are bounded by one, and for rho>=R_0 they are
bounded below by 1-r_m/R_0>0. Choose K_0 so the full
Hessian of chi F+G is nonnegative outside R_0.
Inside R_0 it is F plus convex G, hence RC. This smooth
bounded-Hessian extension matches F exactly on the
test ball. Arbitrary finite-valued RC F are handled
by ordinary mollification on bounded sets, and
periodic Lipschitz maps by the existing smoothing
bridge with bounded gradients. No growth restriction
remains in the sufficiency of the following target.

**Global target (sufficient for unrestricted Morrey).**
For EVERY smooth periodic mean-zero g=phi_bar_z,
construct a sequence of projected martingale
representations above with delta -> 0.
The explicit estimate (16) would then prove Morrey,
with no wave, mesh or degree cutoff and no residual
projection problem. Existing Beurling norm bounds
or projected stochastic representations do NOT
establish this absolute bracket mismatch property.

The target is not supplied here. In particular
usual heat-filtration conditional martingales of
both actual derivatives can have a nonzero local
determinant defect even when the average signed
defect vanishes. The previous heat counterexamples
and the martingale observation in
[GENERAL_LOGIC_DIRECTIONS](IWANIEC_MORREY_GENERAL_LOGIC_DIRECTIONS.md)
already show why that direct choice is insufficient.
Changing the representation/filtration or using
a genuinely nonlocal coupling is essential.

## 6. Validation and strict stop rule

The [exact checker](../../research/audit/iwaniec_martingale_defect_exact.py)
was actually executed locally with Python 3. Output:

    160 rational binary-tree controls: rank-one repair, stopping bound, coupling transfer, variance identities passed
    Controls with an early stop: 59
    Projection variance identity: defect and conditional variance both 1/9

These test rational diagonal examples, including unequal
branch probabilities, incomplete revelation and early
stopping, and one elementary projected complex pair.
The proof, not the examples, covers arbitrary 2x2 matrices
and arbitrary probability laws. No numerical gradient
optimization, formal Lean proof or external review is claimed.

**The only main completion gate:** prove (6), or supply
a gap-preserving construction yielding (14) -> 0 for all
periodic gradients, or exhibit an actual strictly positive
D for a certified gradient law. The finite-wave D/TQ
corner work is now explicitly subordinate and suspended.
The all-N case enumeration and polynomial-degree hierarchy
are not main completion strategies. The determinant cost
is a quantitative equivalent problem and its vanishing
has not been proved. In particular the results here do not
claim a finite positive decision procedure or a proof
that unrestricted Morrey is true.
