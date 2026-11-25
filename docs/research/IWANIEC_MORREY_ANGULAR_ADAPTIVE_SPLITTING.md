# Gate 1: angular adaptive splitting, tight hyperplanes, and exact residual geometry

24 November 2026.

**Status: Gate 1 remains OPEN.** The universal positive stress
absorption requested in the roadmap was not obtained in this turn.
The direct heat/polar positivity approaches still lack control of their
mixed term. In particular this note does not assert that a conditional
law produced by splitting a compatible gradient is itself a compatible
gradient.

We instead make constructive progress on the angular law side of G1,
using a freedom absent from ordinary laminate splitting: change
amplitudes and probabilities while preserving all homogeneous energy
moments. For degree two this yields a compact optimization with an exact
classification of the residual types. Every finite angular input is
covered, independently of its number of rays. The ordinary blocked
states whose affine span contains zero can now be split, rather than
being left as terminal traps. This is not a uniform bound on the number
of configurations or a proof that the residuals vanish for gradients.

Two additional results:
* For every p>1, on compact laws supported in an affine hyperplane
  avoiding zero, the homogeneous Jensen tests already imply ALL
  rank-one convex Jensen tests. Thus simply restricting homogeneity
  does not simplify this part of the spatial problem.
* A two-sheeted ordinary blocked law at a nonzero base admits an explicit
  angular split. A different generalized concentration-bearing tight
  state has a strict negative homogeneous RC Jensen gap. These are
  abstract laws/states, NOT counterexamples to Morrey. The examples
  locate exactly what radial freedom does and does not remove.

The arguments below are hand proofs. The accompanying symbolic and
rational checker was actually executed locally. No new Lean theorem,
priority claim, or universal positive stress certificate.

## 1. Angular reweighting does not lose any tests on a tight hyperplane

We first record an extension of the earlier finite-ray
[angular realization theorem](IWANIEC_MORREY_ANGULAR_LAMINATE_REALIZATION.md)
to arbitrary angular measures.

Let V=R^(2x2), S its Frobenius unit sphere, p>1, and A a matrix.
A finite laminate is a finite rank-at-most-one binary splitting tree
rooted at A. Rank-zero splits allow randomization at a common root.
For its leaf law nu define

    mu_nu = (X -> X/|X|)_# (|X|^p nu),

with zero atoms omitted. The set of all such positive finite measures
is convex. For any positive finite angular measure mu, the following
are equivalent:

    F(A) <= integral_S F(u) dmu(u)   for every finite p-homogeneous RC F;

    mu belongs to the weak-* closure of the angular measures of
    finite laminates rooted at A.

The second assertion implies the first directly. For the converse,
strictly separate mu from the closed convex set by a continuous angular
function f. Use the positively p-homogeneous leaf cost G_f(X)=
|X|^p f(X/|X|), G_f(0)=0. Its finite-laminate envelope is bounded below
at A by strict separation and bounded above everywhere by the trivial
tree. Finiteness below at A implies finiteness below at any B:
a four-level coordinate product split at A has B as a designated
leaf of weight 1/16 (split each entry between B_i and 2A_i-B_i).
Append any tree rooted at B there, keeping the other leaves fixed.
Thus an unbounded negative cost at B would give one at A.
The envelope is finite RC by concatenation and p-homogeneous by
scaling trees. It is a continuous separating homogeneous RC
integrand, a contradiction. The weak closure can be realized by a
sequence: impose approximation on the constant test 1 and successively
on a countable dense set of continuous tests. The mass bound then
gives weak-* convergence on the compact sphere.

**Theorem A (tight hyperplane transfer, all p>1).** Let nu be a
compactly supported probability law of mean A, supported on
ell(X)=1 for some linear functional ell. Then

    Jensen for every positively p-homogeneous RC F

is equivalent to

    Jensen for every finite RC F (no growth or homogeneity restriction).

The reverse implication is immediate. For the forward one, choose
finite laminates nu_j rooted at A whose angular p-moment measures
converge weak-* to that of nu. In particular

    integral |ell(X)|^p dnu_j -> 1,    integral ell(X) dnu_j = 1.

Strict convexity of |t|^p implies ell(X)->1 in probability under
nu_j, and uniform integrability of |ell(X)|^p. Explicitly the
nonnegative scalar Bregman difference
    |t|^p - 1 - p(t-1)
vanishes only at 1 and is asymptotic to |t|^p at infinity. Its
mean tends to zero; apply these two properties to obtain the
probability convergence and tail estimate.

If |X|<=R on supp nu, its angular measure is supported on
ell(u)>=1/R. Choose 0<delta<1/R. Weak convergence of angular
measures implies
    integral_{ell(X/|X|)<=delta, X!=0} |X|^p dnu_j -> 0
by the closed-set inequality. On the complementary angular set,
|X|<=|ell(X)|/delta. The scalar uniform integrability just proved
therefore gives uniform integrability of |X|^p under nu_j.
Every weak cluster point is supported on ell(X)=1 and has the
specified angular measure, by passage with uniformly integrable
p-growth continuous tests. Such a law is unique: on that hyperplane
the ray u meets it only at u/ell(u), with probability law obtained
from the angular measure by weighting with ell(u)^p. Thus nu_j
converges weakly to nu, with uniformly integrable p-th moments.

To test an arbitrary finite RC function f, first extend its values
on a compact ball containing supp nu and A by a globally RC
p-growth function. Choose radii R<R'<R'' and a large c>0 so the
convex Q(X)=c(|X|^p-(R')^p) is strictly below f on B_R and strictly
above f on a collar of the radius-R'' boundary. Set g=max(f,Q)
inside B_R'', and g=Q outside. It is locally convex along every
rank-one line, hence globally RC, agrees with f on B_R, and has
p-growth. Passing Jensen for g along nu_j gives the desired
inequality for f. QED.

For gradient laws supported in an arbitrary affine hyperplane,
translate the matrices to make the hyperplane avoid zero if
necessary. Translation preserves compatibility and the unrestricted
RC Jensen test. Consequently a solution of homogeneous G1 at any
one fixed p>1 would already solve the NONhomogeneous RC Jensen
question for every hyperplane-supported gradient law. Theorem A
does not assert that all such gradient laws are laminates.

## 2. Compact angular states at degree two

Now fix p=2. Let v_1,...,v_m be distinct unit matrix directions,
with d_i=det v_i. For any nonzero finite second angular moment
vector w, write T=sum w_i, a=w/T and b=A/sqrt(T). The normalized
data of any probability law of mean A obeying the determinant
moment identity satisfy

$$
a_i\ge0,\quad\sum_i a_i=1,\qquad
\det b=\sum_i a_i d_i,\qquad
b=\sum_i s_i v_i,\quad s_i\ge0,\quad
\sum_i s_i^2/a_i\le1 .
\tag{1}
$$

Use the convention s_i^2/a_i=0 if s_i=a_i=0, infinity if
s_i>0=a_i. The last inequality is Cauchy--Schwarz on each ray,
summing the probability masses of the nonzero rays. Thus (1)
holds for every compatible finite gradient law. It also describes
generalized states: for s_i>0 the radius and probability on ray i
can be chosen as
    r_i=a_i/s_i, theta_i=s_i^2/a_i.
Their mean contribution is s_i v_i and second angular moment a_i.
Any leftover probability is placed at zero. If s_i=0<a_i, this
data instead represents concentration at infinite radius with
zero probability and first moment. Such states must be allowed
in compact limits; they are not asserted to be genuine gradients.

Denote the compact state space by K_D. Compactness follows from
the closed rotated-cone inequalities s_i^2<=a_i t_i with
t_i>=0 and sum t_i<=1. The s variables are bounded, as are b
(with |b|<=1 by Cauchy--Schwarz). Projection from this compact
lift gives compact K_D.

We call a state *solved* if for every finite homogeneous degree-two
RC F,
    F(b)<=sum a_i F(v_i).
This is equivalent to existence of the positive angular stress
of the earlier G1 duality. A state with b=0 is solved by the
complete degree-two origin theorem (determinant lower support).
Likewise if a contains angular mass |b|² at the direction b/|b|,
remove that mass; its remaining angular determinant moment is
zero, and apply the same origin theorem. If |b|=1, equality in
the norm and Cauchy bounds of (1) forces a to be a single atom
at b. Thus a nonsingleton solved state can be replaced by the
atomic states (delta_i,v_i) with weights a_i, strictly increasing
the resolved base second moment from |b|² to 1.

## 3. Exact constructive angular splitting with slack

For a state define
    rho(a,b)=min {sum s_i²/a_i: s>=0, sum s_i v_i=b}.
It is at most one. The minimizer exists and is unique on positive
a coordinates. A split is allowed to use unnormalized child
angular data a^+,a^- with average a. Their base matrices are
b+epsilon H and b-epsilon H for a nonzero rank-one H. For each
child require (1) except that sum a_i^child may differ from one;
the feasibility bound on sum s_i²/a_i^child is still 1.

Normalize a child by dividing its angular data by its total
mass m_child and its base by sqrt(m_child). Use mixture weight
m_child/2. This preserves feasibility and the determinant
identity, as well as the parent angular mixture. Homogeneity
and rank-one Jensen show that the child base source dominates
the parent for every degree-two homogeneous RC F. Moreover

    sum_child (m_child/2) |b_child/sqrt(m_child)|²
          = |b|²+epsilon² |H|².

This is a STRICT positive gain in resolved second moment.

Assume rho<1. In the cone generated by directions with a_i>0
let I be the set of indices that can have strictly positive
coefficient in some conic representation of b. Equivalently
they are the directions in the minimal face containing b.
The equivalence is elementary for a finitely generated cone:
b is in the relative interior of its minimal face; subtract
a sufficiently small positive multiple of any generator in
that face and remain in it. Every conic representation of b
uses only face generators. Even if the cone contains a line,
this relative-interior argument applies. A convex combination
of finitely many representations makes all I coefficients
positive. Mix a sufficiently small amount of this representation
into the slack minimizer. We obtain a strictly slack s with
s_i>0 for all i in I, and s_i=0 outside I.

Let L=span{v_i:i in I}. If L contains a nonzero rank-one H,
choose a coefficient variation k supported on I with
    sum k_i v_i=H.
If at least one positive a_i has d_i!=0, choose a weight
variation h supported on positive a indices satisfying
    sum d_i h_i=cof b:H.
If all those d_i vanish then det b=0. When b!=0 use H=b,
which is itself rank one and belongs to L; when b=0 use any
nonzero rank-one H in L. In either case cof b:H=0 and take h=0.

For small epsilon>0 set

$$
b^\pm=b\pm\epsilon H,\quad
s^\pm=s\pm\epsilon k,\quad
a^\pm=a\pm\epsilon h.
\tag{2}
$$

All coefficients stay nonnegative and the strict norm slack
persists by continuity. The determinant identity holds exactly,
since det H=0 and determinant is quadratic. Thus (2) is the
desired split. No assumption on rank-one connections between
individual original rays is needed.

Conversely, if L contains no rank-one direction, no nontrivial
split of the indicated kind is possible. Indeed both child means
belong to the original conic hull (their positive ray supports
are subsets of the parent's), and their average b is in its
minimal face. They must both lie in that face by the face
property. Their difference is in L.

For an ordinary finite law, all positive angular coordinates
have positive first-moment coefficient. Hence in the slack
case L is the whole span of its rays. If the original law has
nonzero variance and the correct determinant moment, L must
contain a rank-one direction: otherwise the determinant is
definite on L and its centered variance has a strict nonzero
determinant sign, contrary to the determinant identity.
This proves existence of the angular split for every such
ordinary slack law.

## 4. Tightness exactly forces a hyperplane

Suppose rho=1. By the first-order optimality condition for a
strictly convex quadratic on a finite polyhedron, there is a
linear functional ell with

    s_i=a_i (ell(v_i))_+   (a_i>0),
    ell(b)=sum_i a_i (ell(v_i))_+²=1.

For completeness the multiplier assertion follows by applying
the finite-dimensional linear inequality alternative to the
system ell(v_i)=s_i/a_i on positive s coordinates, and
ell(v_i)<=0 on zero s, positive a coordinates. Infeasibility
would give a kernel variation with nonnegative entries at the
zero s coordinates and strictly negative directional derivative
of sum s_i²/a_i, contradicting minimality. The value of the
objective and contraction with b give the two equalities.

Thus the finite part consists of fixed matrices and probabilities

$$
X_i=v_i/\ell(v_i),\qquad
\theta_i=a_i\ell(v_i)^2,\qquad \ell(X_i)=1
\tag{3}
$$

for i with ell(v_i)>0 and a_i>0. Their probabilities sum to one.
All remaining positive angular weights are concentration at
directions with ell(v_i)<=0.

In particular, for an ORDINARY finite law satisfying (1), tightness
holds exactly when its support lies in an affine hyperplane
avoiding zero. Indeed if rho=1, its own first-moment vector must
be the minimizing one; equality in the radial Cauchy bounds
forces one fixed radius per ray, with no zero atom, so (3)
applies to the original law. Conversely ell(X)=1 a.s. implies
ell(b)=1 and sum a_i ell(v_i)_+²=1, hence all feasible first
moment vectors have norm sum s_i²/a_i>=1 by Cauchy. This
characterization uses the normalized law (the normalization
merely rescales the hyperplane).

The tightness relation persists under *every* split with
equal child probabilities as in Section 3. For each child,
Cauchy--Schwarz gives
    (ell(b^child)_+)² <= sum_i a_i^child ell(v_i)_+².
The right sides average to one, and the convex function
(t_+)² gives average left sides at least (ell(b)_+)²=1.
Equality forces ell(b^+)=ell(b^-)=1, since the mean is
positive and the square is strictly convex there. Equality
also forces the child first moments to be a_i^child ell(v_i)_+.
The exact criterion for a tight split is therefore existence
of a vector h supported on positive a coordinates with

    sum h_i ell(v_i)_+²=0,
    H=sum h_i ell(v_i)_+ v_i nonzero rank one,
    sum h_i d_i=cof b:H.

These are linear constraints except for the single rank-one
condition. Conversely they imply that (2), with
s_i^child=a_i^child ell(v_i)_+, gives a feasible split.
When there is no concentration, the radii in (3) cannot
change, and this is exactly the previous ordinary
minor-preserving adaptive split. This is the finite-dimensional
counterpart of Theorem A.

## 5. Global optimal decomposition: complete residual types

**Theorem B.** For every state (a_0,b_0) in K_D, there is a
probability measure Pi on K_D with angular mixture a_0 and

    integral F(b) dPi >= F(b_0)

for every degree-two homogeneous RC F, maximizing
    integral |b|² dPi.

Almost every state at an optimum is either atomic (a=delta_i,
b=v_i) or belongs to one of the following three types.

I. **Tight ordinary hyperboloid trap.** There is no concentration.
The law (3) is a nontrivial ordinary blocked law, supported
in ell(X)=1 and in a two-sheeted determinant quadric within
an affine span of dimension two or three. Both sheets carry
mass. In particular its affine span does not contain zero.

II. **Slack definite-face concentration.** rho<1, the active
mean span L is a determinant-definite two-dimensional space,
and b!=0. All inactive positive angular mass (outside the
minimal conic face of b) has strictly the opposite determinant
sign to L.

III. **Tight definite-variation concentration.** rho=1, the
finite part (3) varies in a translate of a determinant-definite
linear subspace of dimension one or two. All concentration
directions have ell(v_i)<=0, and all have strictly the opposite
determinant sign to that variation subspace.

No claim is made that these residuals are themselves genuine
gradient laws. Their occurrence at an optimum for compatible
input is the unresolved issue.

### Proof

The feasible Pi set is compact: K_D is compact, the angular
mixture constraint and each continuous homogeneous test
constraint are weakly closed, and the trivial Pi=delta_(a0,b0)
is feasible. The objective is continuous. At an optimum any
positive mass of strictly improvable states can be refined,
preserving feasibility by conditioning and integration.
For the two-child refinements this assertion can be made
measurable as follows. Use variables t in [0,1] and two
normalized children z_j=(a_j,b_j) in K_D. Require
    a=t a1+(1-t)a2,
    b=(sqrt(2t)b1+sqrt(2(1-t))b2)/2,
    det(sqrt(2t)b1-sqrt(2(1-t))b2)=0.
These are compact closed constraints in the parent and child
variables, allowing trivial replacements. The objective
gain is continuous. A maximizing child pair and t can be
selected measurably by the standard compact-graph Borel
selection theorem (equivalently here by semialgebraic choice).
Thus strictly positive gain on a positive mass contradicts
optimality. The additional finite atomic refinements below
have explicit weights, with measurable choices of slack,
face, minimizer and multiplier by the same finite-dimensional
semialgebraic selection. Solved states such as b=0 or the
dominance condition of Section 2 can be atomized directly.

A useful further refinement removes any positive inactive
angular subvector c<=a, supported at indices with zero
first moment in the chosen feasible representation, whenever
sum c_i d_i=0. The remaining angular data a-c with the same
b and s still satisfy the determinant and norm constraints.
If its angular mass is positive, normalize it as before,
and append the atom states (delta_i,v_i) with weights c_i.
The new angular mixture is a; its base energy average is
F(b)+sum c_i F(v_i)>=F(b) by the degree-two origin support.
Its resolved second moment has increased by sum c_i>0.
If the remainder has zero mass, b=0 and atomization applies.
Therefore at an optimum no inactive mass can have zero
determinant or mix both determinant signs: one could remove
either a zero-det weight, or suitable positive portions of
two opposite-det weights.

For rho<1 choose the representation of Section 3 positive
on all generators of the minimal face. If L has a rank-one
direction there is a strict split. Otherwise determinant on L
is definite and dim L<=2 (the determinant form on V has
signature (2,2)). We may exclude b=0 by atomization. If dim L=1,
write b=alpha v for alpha>0 and a unit ray v in that face.
The first moment coefficient of v is at least alpha (only
its opposite direction could also occur). The norm bound
then implies a_v>=alpha². The dominance condition of Section 2
solves this state. Thus dim L=2. Write q for determinant with
the sign chosen positive definite on L. Using the q-norm and
Cauchy on the active directions gives
    q(b) <= (sum s_i²/a_i)(sum_active a_i q(v_i))
          < sum_active a_i q(v_i).
The determinant identity forces inactive angular mass of the
opposite sign. All inactive masses have this strict sign by the
previous removal argument. This is II.

For rho=1 take the multiplier and finite law (3). If there is
concentration, the removal argument leaves a single nonzero
determinant sign. Let L0=span{X_i-b: theta_i>0}. Every mean
variation H in L0 can be obtained by perturbing the finite
probability weights with sum zero. In the tight split criterion
this gives the corresponding active h_i; choose one inactive
index with nonzero d_i to enforce the remaining determinant
equation, without affecting the mean or probability variations.
Thus if L0 contains a nonzero rank-one direction we can split.
If L0=0, the active finite part is the single matrix b, and its
angular contribution is |b|² at the direction of b. The residual
has determinant moment zero, so the state is solved. Otherwise
L0 must be definite, of dimension one or two. The centered
finite-part determinant variance is strictly nonzero with that
sign, and the total concentration determinant cancels it.
This gives III.

Finally for tight states with no concentration, the previous
[ordinary blocked-law classification](IWANIEC_MORREY_ADAPTIVE_MARTINGALE.md)
applies directly (or use the exact tight split criterion).
For completeness, center the law at b, let Y_i=X_i-b and
q_i=det Y_i. The feasible mean variation space is
    W={H:(H,0) in span (Y_i,q_i)}.
The lifted span projects onto L0; if it contains a nonzero
vertical vector, W=L0. Otherwise it is a graph of a linear
functional lambda on L0, and W=ker lambda. The nontrivial law
with mean zero and E det Y=0 cannot have determinant definite
on L0; if semidefinite its support lies in the null kernel.
Thus W=L0 or lambda=0 yields a nonzero rank-one direction
and a split. If no split is possible, W is definite, lambda!=0,
and L0 is indefinite of dimension two or three, with one
opposite-sign dimension to W. The restricted determinant form
is nondegenerate: its complement to the definite W is a
one-dimensional opposite-sign line. Completing the square
in det Y=lambda(Y) gives a two-sheeted hyperboloid. Its mean
at Y=0 is a vertex on one sheet, so both sheets must carry
mass: one-sheet support alone would force equality in the
one-dimensional hyperbolic-coordinate bound and concentrate
all mass at that vertex. This is type I, and (3) supplies
the extra affine-hyperplane condition. QED.

This theorem eliminates ordinary slack traps entirely, even
when the original law was blocked. It also explicitly addresses
the concentration degeneracy, rather than assuming compactness
of the set of unbounded radial realizations in second moment.
It does not prove that an optimal decomposition for an actual
gradient avoids I--III. In particular not all generalized states
of type III can be solved, as the example below shows.

## 6. Actual spatial information and examples

### 6.1 Conditional scalar-level splitting

For smooth periodic phi=(phi_1,phi_2), let X=A+Dphi.
For any bounded continuous g(phi_1), periodic integration gives
    integral g(phi_1) Dphi_1=0,
    integral g(phi_1) det Dphi=0.
The first is the integral of a gradient of a primitive. The
second is the pullback of the exact two-form
    g(phi_1) dphi_1 wedge dphi_2 = d(G(phi_1) dphi_2).
These extend to bounded Borel functions of phi_1 by equality
of the signed pushforward measures. Consequently the conditional
laws given phi_1 have mean with first row A_1 and the correct
determinant moment, for almost every scalar level (use conditional
expectation and determinant polarization). Their means form a
rank-one row-plane law, so revealing them gives a positive
rank-one barycenter split, independent of F and p.
This is genuine compatibility information beyond the unconditional
determinant mean. It is not a proof that those conditional laws
are themselves compatible gradients, nor a procedure ensuring
their further refinement to atom states. We could not justify the
spatial absorption of the remaining angular/conditional residuals
with this observation.

### 6.2 Radial reweighting unblocks an ordinary trap

Use diagonal matrix coordinates and nonunit ray generators
(this changes a_i and s_i by the squared norm and norm factors,
respectively, leaving s_i²/a_i invariant). Let

    b=(1,2),
    V1=(0,5/2), V2=(3/2,1), V3=(3,4),
    a=(4/9,4/9,1/9).

These are ordinary probability weights at V_i. Their mean is b
and determinant moment is 2. Centering at b gives the earlier
ordinary trap det Y=tr Y in the diagonal plane; its trace-zero
kernel has negative definite determinant. Thus the ordinary
law is blocked.

The direction matrix V with columns V_i has a null vector k
with sum k<0. The exact script chooses such a vector and
    s=a+k/100,
giving strictly positive entries, the same b and slack
    1-sum s_i²/a_i=4257/125000.
Then choose H=(1,0),
    k' = (-4/15,2/3,0),
    h = (0,4/3,0).
They obey V k'=H and sum d_i h_i=2=cof b:H.
With epsilon=1/10000, the exact two children (2) have positive
coefficients, correct mean and determinant moments, and strict
slack. This is a nonzero angular rank-one split. It does not
assert full angular realization of the example after all steps.

### 6.3 A tight concentration obstruction is genuine

Let b=I, X_±=diag(1±e,1∓e), 0<e<1. Give them ordinary
probability 1/2 each, and add second angular concentration
at the ray -I with nonunit-generator coefficient e²
(and no first moment or probability). The determinant data
sum to 1. For ell(X)=tr X/2 the finite part has ell=1, the
concentration has ell=-1. Hence the state is tight (the
Cauchy bound is saturated). The variation span of its finite
part is the negative-definite determinant line spanned by
diag(1,-1); the concentration has positive determinant.

The classical rectified-product energy
    F([[a,b],[c,d]])=a_+ d_++(b²+c²)/2
is degree two, nonnegative and RC. On a rank-one line in
the region a,d>0 its second derivative is
2 H11 H22+H12²+H21²=(H12+H21)² by det H=0; elsewhere it is
the convex shear quadratic. At transitions the continuous
positive-part product has nonnegative slope jumps, since
the other positive factor is nonnegative. This proves global RC.
At the specified state the finite part has energy 1-e²,
the concentration ray has F(-I)=0, while F(I)=1.
The Jensen gap is exactly -e².

All these data can be normalized as in Section 2 by total
Frobenius second moment. This is a generalized concentration
state, NOT the angular measure of a proved compatible gradient
with the stated base. It shows why the remaining types cannot
be discarded merely by the algebraic determinant condition.

## 7. Verification and disposition

The companion research/audit/angular_adaptive_exact.py was
executed locally with SymPy. Output:

    Blocked ordinary law has exact angular split; moment slack = 4257/125000
    Tight concentration state has exact homogeneous RC gap = -1/16
    Rank-one determinant shift and normalization identities passed.

These are algebra checks and exact examples, not certification
of G1. The compactness, hyperplane transfer and classification
are analytic arguments. The only new positive mechanism toward
G1 in this note is the radial reweighting/splitting and the
elimination of the indicated residuals; it applies to the
entire finite angular input space at degree two. The strongest
spatial statement obtained is the scalar-level conditional
determinant identity. We did not show that the optimized
remaining residuals satisfy that or other necessary spatial
compatibility properties. **G1 remains open for arbitrary
compatible gradients, even at degree two and nonzero bases.**
No new Lean verification. Do not infer a finite exact
classification of actual counterexamples or a successful
universal negative-stress absorption.
