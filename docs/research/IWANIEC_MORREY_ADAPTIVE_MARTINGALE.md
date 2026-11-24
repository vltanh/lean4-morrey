# Input-adaptive martingales: a uniform-filtration no-go and exact geometric terminal traps

23 November 2026. Hand proofs, with executed exact rational regression controls.
**Unrestricted Morrey remains open.** The goal is to sharpen the global
determinant-defect approach, not resume the fixed-wave or polynomial-degree
ladder. No independent human review, novelty clearance or Lean check is claimed.

Start with [the determinant-defect theorem](IWANIEC_MORREY_MARTINGALE_DEFECT.md).
For a compact law nu of mean A it defines D(nu) as the infimum, over finite
binary conditional-expectation experiments, of expected sum of absolute
increment determinants plus half the terminal unresolved variance. It proves
D(nu)=0 iff nu is a laminate, and the quantitative repair bound.
We use the classical bounded prelaminate approximation theorem of
Müller–Šverák cited there, and ordinary continuous martingale theory.
For the projected Beurling stochastic representation literature see
[Bañuelos–Janakiraman](https://www.math.purdue.edu/~banuelos/Papers/Beur_Ahl.pdf).
The arguments and constants in this note are derived here.

## 1. A common filtration cannot work even approximately

Let P be uniform on T², let k=(1,0), l=(0,1), m=k+l, and define
u=exp(2 pi i k·P), v=exp(2 pi i l·P), w=uv=exp(2 pi i m·P).
All three have mean zero and absolute value one.

For ANY finite filtration with trivial initial sigma field, append
one last step revealing P completely (this step need not be binary).
Put U_j=E[u|F_j], V_j=E[v|F_j], W_j=E[w|F_j], and let Delta denote
martingale increments. Then the following exact identity holds:
$$
1=\sum_j E\left[
\overline{\Delta W_j}
(U_{j-1}\Delta V_j+V_{j-1}\Delta U_j)
+\overline{W_j}\Delta U_j\Delta V_j
\right]. \tag{1}
$$
Indeed telescope E[bar W_j U_j V_j], whose initial value is zero
and whose final value is E[bar w uv]=1. Expand Delta(UV) by the
product rule; the terms with a single martingale increment
times a previous-step measurable coefficient have zero mean.
The remaining terms are exactly (1).

Since all conditional character means are in the unit disk,
(1) implies
$$
\sum_j E\big(
|\Delta U_j\Delta V_j|
+|\Delta U_j\Delta W_j|
+|\Delta V_j\Delta W_j|\big)\ge1. \tag{2}
$$

**Theorem A (quantitative obstruction to an input-independent
filtration).** There are twelve fixed smooth periodic real
two-component maps phi_i, each consisting of only two independent
ridge phases, such that EVERY common finite binary filtration
of P satisfies
$$
\sum_{i=1}^{12} C_{\mathcal F}(D\varphi_i(P))\ge1. \tag{3}
$$
Here C_F is the cost of the particular experiment in the definition
of D, including the terminal unresolved variance. In particular at
least one of these fields costs >=1/12 for any common filtration,
although D(law(Dphi_i))=0 for EACH individually.

**Proof.** For every pair p,q among k,l,m and each choice s,t of
real or imaginary part, take the gradient whose first row is
p times part_s(exp(2 pi i p·P)) and second row is
q times part_t(exp(2 pi i q·P)). These are actual smooth periodic
gradients: the scalar row potentials are sin(2 pi p·x)/(2 pi)
or -cos(2 pi p·x)/(2 pi), and similarly for q.
There are three pairs and four part choices, hence twelve maps.
All pair determinants have magnitude one. The determinant of
the conditional matrix increment is therefore, in absolute
value, |Delta part_s U Delta part_t V| for the relevant pair.
Summing over the four choices dominates |Delta U Delta V|,
because the real-imaginary l1 norm dominates complex modulus.
The same holds for the other pairs. Sum (2) to obtain (3)
for the increments including the appended full-revelation step.
Its determinant contribution for each matrix field is bounded
by half the squared residual norm, since |det H|<=|H|²/2.
Thus the original cost with the residual term dominates the
appended-step determinant cost. This proves (3).

Every one of the twelve fields is individually a laminate:
the two distinct nonparallel integer phases are independent
uniform circles (their character map is a surjective torus
endomorphism), and each row ranges in a rank-one linear subspace.
Successive convex Jensen proves its laminate property. QED.

The conclusion allows arbitrary auxiliary randomness, unbounded
binary tree depth, and arbitrary nonlinear or adaptive observations
of P, provided the filtration is COMMON to all twelve inputs.
It is not a failure of individual two-wave Jensen.
Different terminal depths for a common filtration do not help:
extend each to the largest depth; by variance orthogonality and
|det H|<=|H|²/2, this cannot increase its original total cost.
The obstruction survives any sequence of common filtrations.

## 2. Continuous and projected versions of the obstruction

Suppose the conditional phase martingales U,V,W are continuous,
start at zero, and reveal P at the terminal time (an infinite
time limit is allowed). Write [U,V] for the complex bilinear
quadratic covariation, not the positive trace bracket.
Itô's product formula and boundedness of U,V,W give
$$
1=E\int\left(
\bar W\,d[U,V]+V\,d[\bar W,U]+U\,d[\bar W,V]\right). \tag{4}
$$
Thus the sum of expected total variations of these three
complex brackets is >=1. Each complex bracket's variation
is at most the sum of the variations of the four real-imaginary
component covariations. For the twelve actual conditional
gradient martingales from Section 1, the signed determinant
bracket is precisely the corresponding real covariation times
det(p,q). If beta_i denotes its expected total variation,
$$
\sum_{i=1}^{12}\beta_i\ge1. \tag{5}
$$

Here is a quantitative consequence for the previous note's
projected Beurling route, in a common continuous filtration
(e.g. a Brownian filtration, or any one where these phase
conditional martingales are continuous).
For each of the twelve maps let g_i=partial_bar_z phi_i and
h_i=partial_z phi_i=B g_i. Suppose complex square-integrable
continuous martingales L_i,N_i start at zero and satisfy
L_i,infty=g_i(P), E[N_i,infty|P]=h_i(P), with the same
terminal P and the same filtration for all i. Put
$$
\delta_i=E\,TV(d\langle N_i\rangle-d\langle L_i\rangle),
$$
where these angle brackets are the positive complex trace
brackets. Set H_i,t=E[h_i(P)|F_t], E_i,t=N_i,t-H_i,t.
By the projection identity from the preceding note,
E|E_i,infty|²<=delta_i. Orthogonality and the Cauchy–Schwarz
bound for quadratic covariations then give
$$
E\,TV(d\langle N_i\rangle-d\langle H_i\rangle)
\le 2\|h_i\|_2\sqrt{\delta_i}+\delta_i.
$$
In conformal/anticonformal coordinates det X=|h|²-|g|²,
so
$$
\beta_i\le2\delta_i+2\|h_i\|_2\sqrt{\delta_i}.
\tag{6}
$$
For our fields E|Dphi_i|²=(|p|²+|q|²)/2<=3/2 and
E det Dphi_i=0, hence ||h_i||²_2<=3/8.
Combining (5) and (6) gives
$$
\max_i \delta_i>1/300. \tag{7}
$$
Indeed if every delta_i<=1/300, then every beta_i is at most
1/150+sqrt(1/200)<1/12 (square the remaining positive terms),
contradicting (5).
This rules out a common projected stochastic representation
with arbitrarily small absolute bracket mismatch uniformly
over even these twelve inputs. It does not rule out a
different, input-specific stochastic representation for each g.
It does not assert a lower bound on the infimum D of any
of these individual gradient laws.

**Stop rule:** Do not keep trying to tune one universal
heat/linear/common-filtration representation to achieve
vanishing absolute determinant bracket defect for all inputs.
The obstruction is independent of depth and of the choice of
common filtration. A successful direct stochastic construction
must be genuinely input-adaptive, or use a different sufficient
property not excluded by (3)–(7).

## 3. An exact, rather than approximate, continuous representation

**Theorem B.** For ANY compactly supported law nu of planar
matrices, with mean A, the following are equivalent:

(a) nu is a laminate, equivalently D(nu)=0.
(b) There exists a uniformly bounded continuous matrix
martingale M_t, 0<=t<infinity, M_0=A, with terminal limit
M_infty of law nu, such that det M_t is also a martingale.

The determinant martingale property is equivalent to
d[M11,M22]=d[M12,M21]. All path bounds can be chosen in any
closed ball centered at A containing the support of bounded
prelaminate approximants, with a harmless enlargement.

**Proof.** (b) implies (a) by the neutral covariance
decomposition (previous note, Lemma E), Itô for smooth RC
functions on the bounded range, mollification, and terminal
bounded convergence. Equivalently, applying Itô to det
shows its finite-variation drift vanishes, and a PSD
covariance with zero determinant contraction is a sum of
rank-one outer products.

For the reverse take bounded finite-order laminate
approximants nu_n converging weakly to nu, using the
classical compact laminate approximation theorem. Translate
each by the small barycenter error to have mean exactly A,
and fix a ball B_R(A) containing all their supports.
Realize a rank-one binary split by one-dimensional Brownian
motion along the segment from one child mean to the other,
stopped at the endpoints, with unit Frobenius direction.
The hitting probabilities are exactly the split weights
(the coordinate process is bounded and a martingale).
Concatenate these independent stopped motions down the
finite prelaminate tree, and freeze the path at its leaf.
This yields a continuous martingale M^n, staying in B_R(A)
because every tree segment is between conditional averages
of its leaves. Its determinant is a martingale, being affine
on each rank-one segment.

Use the Brownian clock in which the trace of the matrix
quadratic variation has rate one before the leaf time tau_n
and zero afterward. The expectation of tau_n equals
E|M^n_infty-A|²<=R² by the martingale isometry
(or sum the finite expected segment exit times).
BDG gives a constant C independent of n with
E|M^n_t-M^n_s|^4<=C(t-s)^2.
The bounded initial data and this moment estimate give
tightness in the continuous path space with the topology
of uniform convergence on each compact time interval.
Take a subsequential weak limit M (Prokhorov and the usual
Kolmogorov tightness criterion, on increasing time intervals).
It stays in the same closed ball. Both the ordinary and
determinant martingale identities pass to the limit when
tested against bounded continuous cylinder functions at
earlier times: all variables in these identities are
bounded, and finite-time evaluation is continuous.
A monotone class argument yields the identities in the
natural filtration; take its usual augmentation if desired.

It remains to identify the terminal law, which need not
follow just from compact-time convergence. For each n,
P(tau_n>t)<=R²/t. Thus the expectation of any bounded
continuous test of M^n_t differs from its expectation
under nu_n by at most 2||f||_infty R²/t. Pass first
n->infinity at fixed t, then t->infinity. The bounded
martingale limit theorem gives M_infty a.s. and in L²,
so its law is nu. QED.

A deterministic time change t=s/(1-s) gives a continuous
martingale on [0,1], including its a.s. terminal limit.
This theorem shows that seeking an exact input-specific
determinant martingale is not a stronger conjecture than
the original compact laminate assertion. It also enables
a sharp geometric analysis of stalled adaptive splittings.

## 4. Exact adaptive binary observations preserving minors

Let eta be any compact law, mean b, satisfying the single
minor identity
$$
\int\det X\,d\eta=\det b. \tag{8}
$$
Write Y=X-b, q(Y)=det Y; then E Y=0 and E q=0.
Define L=span(supp Y), and
$$
S=\operatorname{span}\{(Y,q(Y)):Y\in\operatorname{supp}(X-b)\}
\subset L\times R,\qquad
V=\{H\in L:(H,0)\in S\}. \tag{9}
$$
Equivalently S is the range of the covariance of the
five-dimensional centered lifted variable Z=(Y,q(Y)).
This is an exact finite-dimensional object for ANY compact
law, without any atom count restriction.

**Lemma C (complete one-step criterion).** An observation
can split eta into two child laws satisfying (8), with
distinct rank-one-connected means, if and only if V
contains a nonzero rank-one matrix.

Necessity: if child mean is b+H, its minor identity and
the determinant polarization formula give E_child q(Y)=det H.
For a rank-one-connected binary split H is rank at most
one, so (H,0) is in S. A positive-weight child has
support in the parent's support, and distinct means
give nonzero H.

Sufficiency is constructive. For rank-one H in V choose
a vector c with Cov(Z)c=(H,0), and put f(Y)=c·Z.
It is bounded and centered, E[Y f]=H and E[q f]=0.
Choose epsilon>0 small enough that |epsilon f|<=1/2,
and set
$$
d\eta_\pm=(1\pm\epsilon f)\,d\eta. \tag{10}
$$
Both are probability laws, each has the SAME support as
eta, their equally weighted mixture is eta, and their
means are b±epsilon H. Since E_± q=0 and det H=0,
the determinant polarization formula proves each child
satisfies (8). This is an exact zero-defect rank-one
binary observation; it reduces conditional unrevealed
variance in expectation by epsilon²|H|². QED.

**Theorem D (classification of nontrivial blocked laws).**
Assume eta satisfies (8), is not a Dirac measure, and
the condition of Lemma C fails. Then:

* d=dim L is either 2 or 3.
* There is a nonzero linear form ell on L such that
  q(Y)=ell(Y) on the entire support, and V=ker ell.
* Up to multiplying q by -1, its restriction to L is
  nondegenerate of signature (d-1,1), and is positive
  definite on V.
* For some C in L with q(C)<0 (in this sign convention),
  the support lies on
  $$
  q(Y-C)=q(C), \tag{11}
  $$
  a two-sheeted hyperboloid. It has positive mass on
  BOTH sheets, while the starting barycenter belongs
  to just one sheet.

**Proof.** The projection S->L is onto. If it has a
nonzero vertical kernel then S=L×R, hence V=L.
Otherwise S is the graph of a linear form ell and
V=ker ell. If V=L, then either q|L has a nonzero
null vector (providing a rank-one direction), or q|L
is definite, which is impossible by E q(Y)=0 and
nontriviality. The same excludes ell=0. More generally
q|L must be indefinite in the blocked case: if
semidefinite, E q(Y)=0 would force the support into
the kernel of the semidefinite form, so it would
vanish on its span L, yielding a rank-one direction
in V (or ell=0).
Because V has no nonzero null vector, q|V is definite.
For the determinant's split signature (2,2) this
implies dim V<=2, and indefiniteness on L gives
2<=dim L<=3. Change sign if necessary to have q|V
positive definite. Its q-orthogonal complement in L
is a line, necessarily strictly negative by indefiniteness.
Thus q|L is nondegenerate of signature (d-1,1).
Use polarization B_q to write ell(Y)=2B_q(C,Y)
for the unique C in L. Since ell vanishes on V,
C is in its q-orthogonal line; C is nonzero and q(C)<0.
Complete the square to obtain (11).

With a negative unit vector e along that line, write
Y-C=v+s e, v in V. Put a=-q(C)>0. The two sheets are
s=±sqrt(a+q(v)). The barycenter Y=0 is at v=0 and
s=±sqrt(a), on one of the sheets. If all mass were
on that sheet, averaging s and using |s|>=sqrt(a),
with equality only at v=0, would force Y=0 a.s.
This contradicts nontriviality. Mass on the opposite
sheet alone is inconsistent with the mean as well.
Both sheets must have positive mass. QED.

For clarity, in this proof changing the sign of q
also changes ell; the identity and the minor-preserving
condition are unchanged. Rank-one matrices remain the
nonzero null vectors.

**Corollary E (every nontrivial blocked law is NOT a laminate).**
Otherwise Theorem B gives a bounded continuous determinant
martingale with this terminal law. Subtract b; its value
at each time is the conditional expectation of its terminal
matrix, so it lies in L, and its determinant is the conditional
expectation of the terminal determinant. The affine constraint
q=ell therefore holds at ALL times (first on rational times
and then by continuity). It stays on (11), starts on one
sheet and cannot reach the other by a continuous path.
The prescribed terminal law has positive mass there,
a contradiction. Hence D(eta)>0.
This is a nonlamination criterion for abstract matrix laws,
not a Morrey counterexample; their realizability as genuine
gradient laws is not asserted.

## 5. Global optimal decomposition: only these traps can remain

This result does not require a finite support or a fixed
number of observations. Let K be any compact set containing
the support of a law nu satisfying (8), and let C_K be the
compact space of probability measures on K satisfying (8).
Write b(eta)=integral X d eta. Consider all probability
measures Pi on C_K satisfying

(i) their mixture is nu (integrate every continuous test
against the conditional law eta and then against Pi);
(ii) b#Pi, the distribution of the conditional barycenters,
is a laminate with mean b(nu).

There is at least one: Pi=delta_nu. The feasible set is
compact in the weak topology. The mixture constraint is
closed by continuity of integration, and the laminate
condition is closed on the common compact convex hull of
K because finite-valued rank-one convex functions are
continuous there.

**Theorem F.** There exists such a decomposition maximizing
$$
J(\Pi)=\int |b(\eta)|^2\,d\Pi(\eta).
$$
For every maximizing Pi, almost every conditional law eta
is either a Dirac measure or a nontrivial blocked law as
classified in Theorem D. Equivalently all unresolved
variance at an optimum is on the two-sheeted traps of
dimension 2 or 3.

**Proof.** Existence follows from compactness and continuity.
If a positive Pi-mass of conditional laws admits the split
of Lemma C, refine each of them by such a split. More
explicitly, the feasible triples (p,eta_1,eta_2), with
0<=p<=1, eta_i in C_K, p eta_1+(1-p)eta_2=eta, and
rank(b(eta_1)-b(eta_2))<=1, form nonempty compact
sections of a closed graph in compact metric spaces.
The continuous payoff p(1-p)|b(eta_1)-b(eta_2)|²
has a maximum at each eta. Its value function is upper
semicontinuous; its maximizing graph is Borel with
nonempty compact sections. The standard Borel measurable
selection theorem for Borel graphs with sigma-compact
sections (Arsenin–Kunugui) supplies a measurable maximizing
triple. This avoids any unproved continuous-choice assumption.

Replace each eta by its chosen mixture. The overall
mixture stays nu and all child laws satisfy (8).
By conditional rank-one Jensen, the new distribution of
barycenters dominates the old one for every RC F and is
therefore still a laminate with the same mean.
The objective J increases by the integral of the
nonnegative payoff, strictly if a positive mass admitted
a nonzero rank-one split. This contradicts maximality.
Lemma C and Theorem D prove the assertion. QED.

The total residual at an optimum is
$$
r(\nu)=\min_\Pi \int\operatorname{Var}(\eta)\,d\Pi(\eta)
=\int |X|^2\,d\nu(X)-\max_\Pi J(\Pi).
$$
It satisfies the exact zero criterion and a useful bound
$$
r(\nu)=0\ \Longleftrightarrow\ D(\nu)=0,\qquad
D(\nu)\le r(\nu)/2. \tag{12}
$$
Indeed r=0 means the conditional laws are Dirac, so the
laminate barycenter law equals nu; conversely if nu is
a laminate, its disintegration into Dirac laws is
feasible. For the bound, couple X~nu to Y=b(eta) by
sampling eta~Pi then X~eta. Thus E[X|Y]=Y.
The law of Y is a laminate, so has D=0. Glue any finite
binary experiment on Y to this coupling, conditionally
independent of X given Y. Its conditional means for X
are exactly those for Y, so all determinant costs
agree. Its squared residual for X is the residual for
Y plus E|X-Y|²=r(nu) by orthogonality. Take experiments
for Y of arbitrarily small cost. This proves (12).

There is also an actual adaptive stochastic interpretation.
By Theorem B, realize the barycenter law by a continuous
neutral martingale and then, conditional on its terminal
mean, sample eta and X from the decomposition. Revealing
the identity of eta adds no change in mean. The resulting
partial-revelation experiment stops at a Dirac or one of
the classified traps, with residual variance r(nu).
This is a compact global existence theorem; it is not an
algorithm guaranteed to compute a maximizing Pi, nor
does it prove that its trapped mass vanishes for gradients.

## 6. What gradient compatibility does and does not give

For an arbitrary smooth periodic phi:T²->R², the initial
law of A+Dphi has mean A and satisfies (8) by the
determinant null Lagrangian. Its support is the continuous
image of the connected torus (Haar has full support),
hence connected. A nontrivial law on a two-sheeted
hyperboloid with positive mass on both sheets has
disconnected support. It follows that:

**Every nonconstant smooth periodic gradient admits a
nontrivial exact rank-one binary observation preserving
the determinant identity, with both conditional laws
equivalent to the original and having the same support.**

Furthermore this can be repeated at every finite
nontrivial node, using the positive likelihood (10),
because connected support and the minor identity persist.
This is not a proof of convergence to full revelation:
likelihood lower bounds can decay with depth, and an
infinite sequence can concentrate on disconnected
subsets. A nontrivial lower-dimensional trap is a
possible terminal obstruction of the method. The
conditional laws in the optimal decomposition need not
themselves be actual periodic gradient laws; the null
Lagrangian moment alone is much weaker.

The **specific global remaining gate** for this approach is
to prove that an actual gradient law admits a decomposition
of Section 5 with r(nu)=0, i.e. the optimal decomposition
can avoid all nontrivial two-sheeted traps, or equivalently
to construct an input-specific determinant-neutral
continuous martingale with full terminal law. This must
use spatial compatibility beyond (8) and connectedness.
Do not restart a ladder in dimension, atom count, wave
count, or degree: the classification of the blocked
geometry is complete, but its probability of occurrence
in an optimal adaptive construction is not controlled.

The abstract traps are nonlaminates by Corollary E, but
no positive r or D for an actual gradient law has been
established. Nor does an arbitrary NONoptimal split
producing such a trap establish nonlamination of the
initial law. The optimization over adaptive choices is
essential.

## 7. Exact regression checks

The standard-library checker
[research/audit/iwaniec_adaptive_martingale_exact.py](../../research/audit/iwaniec_adaptive_martingale_exact.py)
was executed locally and returned:

    64 randomized rational phase filtrations: exact product identity and total defect >= 1 passed
    two exact 2D/3D minor-trap controls and positive-likelihood rank-one split passed

The phase controls use the fourth roots of unity with
auxiliary copies and different filtration depths, verify
(1) exactly and include the residual variance in (3).
The trap controls include the diagonal law on
diag(-1,1/2), diag(1/2,-1), diag(2,2), with weights
4/9,4/9,1/9, and a symmetric three-dimensional analog.
They satisfy det Y=tr Y, equivalently det(Y-I)=1,
with barycenter zero and mass on both sheets; the
trace-zero kernel is determinant-definite. A product
sign control checks the explicit likelihood split.
These computations are regression controls only; all
unbounded quantifiers follow from the hand proofs.

**Status:** the common-filtration approach is ruled out
globally; exact neutral martingale representation and
adaptive terminal-trap classification are proved at
hand level. The universal input-adaptive avoidance
theorem remains open. No new four-wave corner or other
fixed-wave-count case has been pursued.
