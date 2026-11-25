# Quantitative exclusion of all adaptive traps and a global compatibility penalty

23 November 2026. Hand proofs and executed rational regression controls.
**Unrestricted Morrey remains open.** No wave-count or atom-count bound,
isotropy, homogeneity, or polynomial restriction is imposed. No independent
human review, novelty clearance, or Lean verification is claimed.

Start with [the adaptive martingale reduction](IWANIEC_MORREY_ADAPTIVE_MARTINGALE.md):
a compact minor-compatible law admits an optimal decomposition into Dirac
laws and blocked laws, with a laminate distribution of their barycenters.
Every nontrivial blocked law lies on both sheets of a two-sheeted
hyperboloid in affine dimension two or three. The unresolved question is
whether actual planar gradient laws admit an optimal decomposition with
no trapped residual.

**Prior art distinction.** The exclusion of nontrivial symmetric
positive-determinant hyperboloid gradient Young measures is classical,
not a new solution of Morrey. It follows from Šverák's determinant-index
quasiconvexity and is explicitly noted in the introduction of the work
on symmetric Hessian hyperboloids (MPI preprint 2002/68,
https://webdoc.sub.gwdg.de/ebook/serien/e/MPI_Math_Nat/preprint2002_68.pdf).
See also Guerra, *Extremal rank-one convex integrands and a conjecture of
Šverák*, https://doi.org/10.1007/s00526-019-1646-5, for the determinant-index
integrands, and Müller–Šverák, *Convex integration for Lipschitz mappings
and counterexamples to regularity*, Ann. Math. 157 (2003), Lemma 4.1.
The recent general index-constancy theorem of Guerra–Tione is
https://arxiv.org/abs/2506.03906; that deeper result is not required here.
The contribution below is the explicit all-matrix quantitative estimate,
its application to every blocked geometry, a compact-parameter
compatibility penalty, and a precise obstruction to unguarded conditioning.

All norms of individual matrices are Frobenius unless indicated otherwise.
"Gradient law" below means a compactly supported homogeneous gradient
Young measure (including actual bounded periodic affine-gradient laws).
The analytic estimates also apply whenever the generating gradients
converge in law with uniformly integrable squared norms.

## 1. One normal form for EVERY nontrivial blocked law

Let eta have mean b, write Y=X-b, and suppose it is blocked in the
sense of the preceding note. Thus L=span supp Y has dimension 2 or 3,
the determinant restricted to L is nondegenerate Lorentzian up to
sign, and for some C in L with det C != 0,
$$
\det(Y-C)=\det C
$$
on the support. The line through C is the distinguished-sign direction
of the restricted Lorentzian form, and there is positive mass on both
sheets. This includes all the blocked cases, not just symmetric matrices.

Let B_q be the polar bilinear form of q(H)=det H. Its signature on the
whole matrix space is (2,2). The q-orthogonal complement of L contains
a matrix N with determinant of the same strict sign as det C:
if dim L=3 the complement is the remaining one-dimensional direction
of that sign; if dim L=2 its signature is (1,1).
The derivative of q at N is the Frobenius functional cof(N):H=2B_q(N,H).
Let J=[[0,-1],[1,0]] and define R by R^T J=cof N. Then
det R=det N != 0, and for H in L,
$$
J:RH=\operatorname{cof}N:H=0.
$$
Hence RL consists of symmetric matrices. In particular -RC is
symmetric with positive determinant. Changing R to -R if necessary,
B_0=-RC is positive definite.

The affine transformation
$$
T(X)=B_0^{-1/2} R(X-b-C)B_0^{-1/2}
$$
therefore maps the law eta to a compact symmetric law with mean I
and determinant identically one. Indeed det(R(X-b-C))=det(RC)=det B_0,
so the congruence makes the determinant one. The two hyperboloid
sheets now consist of positive and negative definite matrices.
Let w>0 be the probability of the negative definite sheet.

This is an invertible affine map of the type P X Q + B, with both
P and Q invertible; such transformations preserve gradient-law
compatibility, by changing the output and spatial coordinates and
adding an affine map. They also preserve lamination. In particular
the normalized trap has precisely the same qualitative compatibility
question as the original. No uniform bound on the condition number
of T across all traps is asserted.

## 2. An explicit spatial-compatibility inequality for ALL planar gradients

For symmetric S define the determinant-index function
$$
h(S)=\begin{cases}\det S&S\text{ positive definite},\\0&\text{otherwise}.\end{cases}
$$
It is continuous. On the positive definite cone its gradient has
Frobenius norm |S|, and outside its closure it is zero.
Along every line segment the positive definite cone cuts out an
interval, and h joins continuously at its endpoints. Integrating
along that segment proves the useful global estimate
$$
|h(S)-h(U)|\le \tfrac12(|S|+|U|)|S-U|. \tag{1}
$$

For completeness, the classical symmetric quasiconvexity proof
works on any flat periodic torus. If the symmetric base S is not
positive definite, h(S)=0 and the assertion is immediate. Otherwise
let psi be smooth and periodic, and minimize
x -> x^T S x/2 + psi(x) - y·x on R² for any y.
Coercivity gives a global minimum, where Sx+grad psi(x)=y and
S+D²psi(x) is positive semidefinite. The gradient map descends
to the torus with target lattice S times the source lattice.
Its positive-semidefinite derivative locus covers that target.
The area formula (the singular-derivative image has zero area)
therefore gives
$$
h(S)\le \fint h(S+D²\psi).
\tag{2}
$$
By smooth approximation and (1) this also holds for periodic
W^{2,2} potentials. This is the known determinant-index inequality.

Now let X=A+Dphi on any flat two-dimensional torus, and use
normalized volume measure. The periodic Helmholtz decomposition is
phi=grad psi+v+constant, with div v=0. Put
S=sym A, H=D²psi, K=sym Dv. Then H and K have zero means,
$$
E H:K=0,\qquad
\|K\|_2=\|\operatorname{skew}D v\|_2
=\|\operatorname{skew}(X-A)\|_2.
\tag{3}
$$
The first equality follows by integration by parts or orthogonal
Fourier projections. For the norm identity, in each Fourier mode
the solenoidal vector coefficient is perpendicular to its frequency;
the symmetric and antisymmetric parts of its rank-one Fourier
gradient have equal squared norms. Thus sym X=S+H+K and
||S+H||_2<=||sym X||_2.

Apply (2), then (1) and Cauchy–Schwarz, to obtain
$$
\boxed{
h(\operatorname{sym}A)
\le E h(\operatorname{sym}X)
+\|\operatorname{sym}X\|_2
 \|\operatorname{skew}(X-A)\|_2 .}
\tag{4}
$$
This is an all-gradient inequality, not merely a minor identity.
It passes to compact homogeneous gradient Young measures: use
the usual bounded-gradient generation theorem, or affine-boundary
generating sequences extended periodically; (1) and uniform
integrability of squared norms pass the required moments to the
limit. No stochastic conditioning or assumed ordinary convexity
of h is used in this proof.

Equation (4) also applies after ANY affine transformation
P X Q+B with invertible factors; singular factors are included
by continuity. This gives a finite-dimensional family of explicit
necessary compatibility tests for arbitrary gradient laws.

## 3. Quantitative distance from every blocked law to gradient laws

Normalize the blocked law as in Section 1, so Z~eta is symmetric,
det Z=1 a.s., E Z=I, and w=P(Z negative definite)>0. Write
$$
M=(E|Z|^2)^{1/2},\qquad V=E|Z-I|^2,\qquad
T_0=\max_{\operatorname{supp}\eta}|\operatorname{tr}Z|.
$$
Here M>=sqrt(2), T_0>=2, and
h(I)-E h(Z)=w.

**Theorem A.** For every gradient law nu, let d=W_2(eta,nu). Then
$$
w\le (3M+2d)d,\qquad
d\ge\frac{w}{3M+2}
\ge\frac{V}{2T_0(T_0+2)(3M+2)}. \tag{5}
$$
The first inequality has the sharper constant sqrt(2)+2M+2d in
place of 3M+2d; when nu has the same mean I the first term
sqrt(2)+d/2 can be omitted.

**Proof.** Take an optimal coupling Z,X of eta and nu and write
A=E X. Then |sym A-I|<=d,
||sym X||_2<=M+d, and
||skew(X-A)||_2<=||skew X||_2<=d because Z is symmetric.
By (1),
$$
|h(I)-h(\operatorname{sym}A)|
\le (\sqrt2+d/2)d,\qquad
|E h(\operatorname{sym}X)-E h(Z)|
\le(M+d/2)d.
$$
Equation (4) bounds the intermediate gap by (M+d)d.
Sum the three inequalities. Since M>=sqrt(2) we obtain the
first bound in (5). If d<=1 it implies the second; if d>1
that bound is automatic since w<=1 and M>=sqrt(2).

For the last assertion put t=tr Z. Because det Z=1 and Z
is symmetric, |Z-I|²=t(t-2). On the positive sheet t>=2 and
on the negative sheet t<=-2. Since E t=2,
$$
E[1_+(t-2)]=E[1_-(2-t)]\le(T_0+2)w.
$$
Hence V<=2T_0(T_0+2)w. This proves (5). QED.

In the original trap coordinates, divide the right side of (5)
by the operator norm of the linear part of the normalization T
to get a bound on the original W_2 distance to gradient laws.
The bound is positive for every nontrivial trap. It need not
remain uniform as the hyperboloid degenerates or T becomes
ill-conditioned. In particular we do NOT infer a uniform
transition gap from a lower variance bound alone.

For example the earlier diagonal trap centered at zero, with
atoms diag(-1,1/2), diag(1/2,-1), diag(2,2) and probabilities
4/9,4/9,1/9, is normalized by Z=I-X. Then M=2, V=2, w=1/9;
every gradient law is at W_2 distance at least 1/72 from it.
This is an abstract non-gradient law, NOT a Morrey counterexample.

## 4. A global quasiconvex extension theorem and explicit separators

Here is an additional useful way to implement the spatial test.
Let g be continuous on the symmetric matrix space, Hessian-
quasiconvex (Jensen for all periodic scalar Hessians), and satisfy
|g(S)|<=c(1+|S|²). On every compact subset of that space, g can be
uniformly approximated by restrictions of globally smooth
quasiconvex full-matrix functions with bounded Hessians.

**Proof.** First replace g by max(g, L|S|²-B), with L>c and B
large enough that the quadratic is strictly below g on a
neighborhood of the chosen compact set. The maximum preserves
Hessian-quasiconvexity, agrees there with g, and equals the
quadratic outside a large ball. Mollify on the symmetric
matrix space, preserving Hessian-quasiconvexity by averaging
its translated inequalities. The resulting smooth g_0 has a
globally bounded Hessian, say with operator norm K, because it
equals a quadratic outside a compact set. It approximates g
as closely as desired on the original compact set.

For any epsilon>0 define on ALL matrices
$$
G(A)=g_0(\operatorname{sym}A)
+\epsilon|\operatorname{sym}A|^2+C|\operatorname{skew}A|^2,
\qquad C=K/2+K^2/(2\epsilon).
\tag{6}
$$
For the decomposition of Section 2, write a=||H||_2 and
b=||K_{\rm sol}||_2 where K_sol=sym Dv (to distinguish this
matrix field from the scalar Hessian bound K).
Taylor's formula with the lower Hessian bound -K, subtracting
Dg_0(S):K_sol whose integral is zero, shows
$$
E[g_0(S+H+K_{\rm sol})-g_0(S+H)]
\ge -K ab-K b^2/2.
$$
The Hessian-quasiconvexity of g_0 supplies the remaining Jensen
inequality for S+H. By (3) the added quadratic terms contribute
epsilon a²+(epsilon+C)b². Young's inequality
K ab<=epsilon a²/2+K² b²/(2epsilon) gives
$$
E G(A+D\phi)-G(A)\ge
(\epsilon/2)(a^2+2b^2)
=(\epsilon/2)\|D\phi\|_2^2.
\tag{7}
$$
Thus G is globally strongly quasiconvex and has bounded Hessian.
On symmetric matrices in the original compact set, the added
term epsilon|S|² can be made arbitrarily small. QED.

In particular apply the theorem to the classical h of Section 2.
For a normalized trap choose the mollification error <=w/8 on
its support and at I, and choose epsilon V<=w/4. Then the
strongly quasiconvex full-matrix G in (6) has the explicit
strict Jensen deficit
$$
G(I)-E G(Z)\ge w/2.
$$
Composing with the affine normalization gives a full-matrix
quasiconvex separator for every original blocked law.
This proof does not claim every rank-one convex symmetric
integrand is Hessian-quasiconvex.

## 5. A SINGLE compact-parameter compatibility penalty

The preceding inequality gives a way to express the
remaining compatibility issue without a growing list of
wave, support, or polynomial cases.

For any compact law eta and affine T(X)=P X Q+B define
$$
e(\eta,T)=h(\operatorname{sym} E T(X))
 - E h(\operatorname{sym}T(X))
 -\|\operatorname{sym}T(X)\|_2
  \|\operatorname{skew}(T(X)-ET(X))\|_2.
$$
Set
$$
\Delta(\eta)=
\max_{\substack{|P|\le1,\ |Q|\le1,\ |B|\le1}}
\max(0,e(\eta,T)). \tag{8}
$$
There are just 12 real parameters in this compact maximization,
regardless of the law's atom count. It is not claimed that the
maximum can always be computed by a fixed finite algebraic
certificate for arbitrary continuous laws.

**Theorem B.** Delta is nonnegative, continuous on laws with a
common compact support, zero on every gradient law, and STRICTLY
POSITIVE on every nontrivial blocked law.

The maximum exists, and continuity follows from joint continuity
of the moment functions on the compact product of the law and
parameter spaces. Its vanishing on gradient laws follows from
(4) and affine invariance (including singular factors by
approximation). For a blocked law take T from Section 1. It
has e(eta,T)=w>0. Replace P,Q by alpha P,beta Q and B by
alpha beta B for sufficiently small positive alpha,beta.
All parameters now lie in the compact constraint set,
and homogeneity of all the terms in e gives
e(eta,T_scaled)=(alpha beta)^2 w>0. QED.

Let r(nu) be the minimum unresolved variance from the adaptive
decomposition theorem. Denote by Pi its feasible decompositions
into minor-compatible laws with laminate barycenter distribution.
On a fixed compact support these form a compact set. When nu
itself is a gradient law, Pi=delta_nu is a feasible decomposition
with zero average Delta, though it need not be optimal. Define
$$
r_{\rm comp}(\nu)=\min_{\Pi:\int\Delta(\eta)d\Pi=0}
                 \int\operatorname{Var}(\eta)d\Pi(\eta).
\tag{9}
$$
The minimum exists for gradient laws by compactness and Theorem B.
The exact new main target, for ALL gradient laws, is
$$
r_{\rm comp}(\nu)=r(\nu). \tag{10}
$$
Indeed, if (10) holds there is an unconstrained optimal decomposition
having zero average Delta. Its conditionals are Dirac or blocked
by the preceding optimal-decomposition theorem. Theorem B excludes
all nontrivial blocked laws; thus r=0 and nu is a laminate.
Conversely if nu is a laminate, the decomposition into Diracs
is feasible in both problems and both residuals are zero.

The same reasoning proves the following **approximate compatibility
preservation** criterion: it suffices to construct feasible Pi_j
with residuals tending to r(nu) and average Delta tending to zero.
A compactness limit is an optimal zero-penalty decomposition.
No uniform normalization bound and no individual posterior
gradient realization are required.

In particular, a sufficient (potentially stronger) global
construction would be: for every non-Dirac minor-compatible eta
with Delta=0, find a nontrivial rank-one binary split whose
children also have Delta=0. Then the constrained variance
maximizer can always be refined until it is Dirac almost surely.
The compactness and measurable-selection proof in the adaptive
note applies with the additional closed constraint Delta=0.
It is NOT known here that such a split exists; Delta=0 has only
been proved to be necessary for gradient compatibility, not
sufficient for lamination. A proof of this uniform splitting
principle would settle Morrey directly. Do not assume it as a
property of the minor-compatible splits constructed previously.

## 6. Why arbitrary determinant-neutral conditioning cannot suffice

There is an exact example even with a smooth separable periodic
gradient, whose law is a laminate.

Let p(t) be the periodic step function with values -1,1/2,2
on consecutive intervals of lengths 1/3,1/3,1/3. Let q(t)
take the same values on intervals of lengths 4/9,4/9,1/9.
Their means are 1/2 and zero. Smooth both by convolution on the
circle with a nonnegative smooth normalized kernel supported
within radius 1/36. Call the smoothed functions p_0,q_0.
Their means are unchanged; each constant plateau still has
length at least its original length minus 1/18.

The law nu of X=diag(p_0(x),q_0(y)) for independent uniform
circle phases is an actual smooth gradient law at base
A=diag(1/2,0): integrate p_0-1/2 and q_0 periodically in the
two coordinates. It is a laminate by independent rank-one
Jensen in the diagonal directions.

Let eta be the three-atom trapped law of Section 3, centered at
zero, with the earlier probabilities. The plateau lengths give
nu >= alpha eta as measures for alpha=1/9. Explicitly, the
probabilities of (-1,1/2) and (1/2,-1) are at least
(5/18)(7/18)=35/324>4/81; the probability of (2,2) is at least
(5/18)(1/18)=5/324>1/81. Thus the following is a legal binary
observation of X: choose the trap branch with likelihood
alpha eta({X})/nu({X}) on those three atoms and zero elsewhere.
Its conditional law is eta with weight alpha; the other
conditional law is zeta=(nu-alpha eta)/(1-alpha).

Both conditional laws commute with the determinant. For eta
this follows from its exact moments. For zeta its mean is
diag(9/16,0) and its average determinant is zero, since the
parent and trap determinant averages are both zero.
The two child means differ by a NONZERO rank-one matrix.
This is therefore an exact zero-defect, variance-reducing
minor-preserving observation of the type allowed in the earlier
adaptive splitting approach. Yet its trap branch is separated
from every gradient law by at least 1/72 and has Delta>0.

The initial law is a laminate and admits a different optimal
decomposition into Diracs. Hence this is NOT a counterexample
to Morrey, nor to (10). It demonstrates that even initial
smoothness, actual spatial compatibility and a legal nonzero
rank-one split do not guarantee compatibility of its children.
A proof using arbitrary greedy determinant-neutral observations,
without a compatibility-preserving choice, has no justification.

## 7. Verification, conclusion, and stop rule

The exact standard-library checker
[research/audit/iwaniec_trap_compatibility_exact.py](../../research/audit/iwaniec_trap_compatibility_exact.py)
was run locally in Python 3; output:

    2D trap: variance=2, E|X|^2=4, opposite mass=1/9, W2 lower bound=1/72
    3D trap and four nonsymmetric affine normalization controls: passed
    smooth-product plateau mass, exact trapped-branch weights, and rank-one child means: passed

The tests verify the finite moment/normalization algebra and the
explicit smooth plateau example's probability inequalities, not
the analytic theorems by sampling.

**Global progress:** every geometry of terminal obstruction is
now excluded as a gradient law, quantitatively, by a single
explicit spatial compatibility inequality. A compact twelve-
parameter test detects every such trap without a wave-count
or atom-count ladder; full-matrix strongly quasiconvex separators
are also supplied by an extension theorem. These results do not
prove that the conditional laws in an optimal decomposition
retain compatibility.

**Remaining main gate:** construct approximately variance-optimal
determinant-neutral decompositions with vanishing average Delta,
or establish the sufficient uniform Delta-preserving splitting
principle. The latter is one global statement about arbitrary
laws, not an invitation to enumerate finite atom counts.
If it fails, analyze the compatibility-preserving choice for
actual gradients, not another hierarchy of increasingly local
lemmas. No proof of (10), unrestricted Morrey, or genuine
negative compatible-gradient witness is supplied.
