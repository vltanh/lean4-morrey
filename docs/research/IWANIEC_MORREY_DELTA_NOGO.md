# Compatibility penalty is insufficient: an exact global no-go for the proposed splitting principle

23 November 2026. Hand proof and locally executed rational checks.
**Unrestricted Morrey remains OPEN.** The proposed stronger splitting
principle for all minor-compatible Delta-zero laws is FALSE. This is not
a counterexample to Morrey, nor a refutation of the equality of optimal
residuals restricted to actual homogeneous gradient Young measures.

The penalty Delta is defined in
[TRAP_COMPATIBILITY](IWANIEC_MORREY_TRAP_COMPATIBILITY.md).
Write h(S)=det S on positive definite symmetric matrices, and h(S)=0
elsewhere. For T(X)=PXQ+B, the test is
$$
h(\operatorname{sym} E T(X))-E h(\operatorname{sym}T(X))
\le \|\operatorname{sym}T(X)\|_2
      \|\operatorname{skew}(T(X)-ET(X))\|_2. \tag{1}
$$
Delta is the maximum positive violation over the compact parameter
set in that note. The previous proof that Delta is necessary for
gradient compatibility and excludes every nontrivial blocked law
is unaffected. What fails is the stronger proposed sufficiency and
uniform splitting principle.

## 1. Global theorem: a whole covariance neighborhood is invisible to Delta

Identify matrices with R^4 in Frobenius coordinates. Let X have a
compact law of mean A satisfying E det X=det A. Set Y=X-A and
C=E[vec(Y) vec(Y)^T]. Assume
$$
0<\lambda I_4\le C\le \Lambda I_4,\qquad
\kappa=\Lambda/\lambda\le 3/2. \tag{2}
$$

**Theorem A.** For EVERY real P,Q,B, including singular P or Q,
the left side g of (1) satisfies the stronger inequality
$$
g\le \sqrt{1/4+\kappa/2}\,\sqrt{s v},
\quad
s=E|\operatorname{sym}(PYQ)|^2,\quad
v=E|\operatorname{skew}(PYQ)|^2. \tag{3}
$$
Consequently Delta=0. For exactly isotropic covariance the constant
is sqrt(3)/2, giving strict relative slack when s,v>0.
This does not assume spatial compatibility, symmetry, independence,
or any restriction on the support or higher moments.

**Proof.** Let S0=sym(PAQ+B), S=S0+sym(PYQ). If S0 is not positive
definite, h(S0)=0<=E h(S), so (3) holds immediately. Otherwise use
two independent estimates.

First h(S)+|S|^2/2 is convex on the symmetric matrix space. To see
this, restrict to an arbitrary line S(t)=U+tH. The positive definite
part of the line is an interval. Inside it h has second derivative
2 det H>=-|H|^2. Outside, h=0. At a finite endpoint, the one-sided
derivatives of h jump upwards: a continuous nonnegative function
vanishing on the outside has inward derivative >=0 on entry and
outward derivative <=0 on exit. This also covers tangent or
degenerate intersections. Adding the quadratic gives convexity
on the whole line. Ordinary Jensen therefore gives
$$
g=h(S0)-E h(S)\le s/2. \tag{4}
$$

Second, det T=det(sym T)+|skew T|^2/2 in dimension two.
The determinant is affine under translations up to its quadratic
part, and det(PXQ)=det P det Q det X. Thus the minor identity
holds for T(X) even with singular P,Q, and subtracting the skew
mean square yields
$$
E\det S=\det S0-v/2.
$$
Since S0 is positive definite,
$$
g=v/2+E[\det S-h(S)]
\le v/2+E[\det S\,1_{\{S\text{ negative definite}\}}]. \tag{5}
$$
Choose orthonormal u1,u2 diagonalizing PP^T. In this basis a
negative definite S has S_11,S_22<0, whereas (S0)_11,(S0)_22>0.
Hence on the negative definite sheet
$$
0<\det S\le |S_{11}S_{22}|
 \le |(u_1^T PYQ u_1)(u_2^T PYQ u_2)|.
$$
Put a=|P^T u1|^2, b=|P^T u2|^2, c=|Q u1|^2, d=|Q u2|^2.
The covariance upper bound in (2) and Cauchy--Schwarz give
$$
E[\det S\,1_{\{S\prec0\}}]\le\Lambda\sqrt{abcd}.
$$
For the skew part, the coefficient matrices of the two real
linear functionals u1^T PYQ u2 and u2^T PYQ u1 are orthogonal:
their Frobenius inner product factors and contains
(P^T u1)·(P^T u2)=0. Their squared coefficient norms are ad and bc.
Consequently (2) gives
$$
v=\tfrac12 E[(u_1^T PYQ u_2-u_2^T PYQ u_1)^2]
\ge \tfrac{\lambda}{2}(ad+bc)
\ge \lambda\sqrt{abcd}.
$$
No division by a possibly zero factor is necessary.
Combine with (5) to obtain the second bound
$$
g\le (1/2+\kappa)v. \tag{6}
$$
The minimum of the nonnegative right sides of (4),(6) is at most
their geometric mean, yielding (3). Finally
E|sym T(X)|²=|S0|²+s>=s and the skew variance is exactly v.
For kappa<=3/2, the constant in (3) is <=1, proving (1)
for ALL transforms, hence Delta=0. QED.

This is an exact, frequency-free statement, not a test of finitely
many parameter values. It shows that the new penalty has a large
blind region, even with well-conditioned full covariance.

## 2. Explicit eight-atom Delta-zero nonlaminate

Let I be the identity and put
$$
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad
D=\operatorname{diag}(1,-1),\quad
K=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$
For r>1 take the law nu_r with atoms +/-rI, +/-rJ, each
of probability 1/[4(1+r²)], and +/-D, +/-K, each
of probability r²/[4(1+r²)]. The four matrix directions
are mutually orthogonal of norm sqrt(2). The first two
have determinant +1, the last two -1. Direct computation gives
$$
E X=0,\quad E\det X=0,\quad
\operatorname{Cov}(X)=\frac{r^2}{1+r^2}I_4.
$$
Theorem A proves Delta(nu_r)=0 for every r, simultaneously for
all affine transformations.

Consider the classical signed Dacorogna--Marcellini quartic
$$
F_\gamma(X)=|X|^4-2\gamma|X|^2\det X,
\qquad \gamma=9/8.
$$
For clarity, rank-one convexity is proved directly and needs no
assumption about the recent quasiconvexity theorem for this energy.
By left/right proper rotations and homogeneity in the direction,
it is enough to take the unit rank-one direction E11. At
X=[[a,b],[c,d]], its second derivative divided by four is
$$
3a^2+d^2-3\gamma ad+b^2+c^2+\gamma bc
=3(a-\gamma d/2)^2+(1-3\gamma^2/4)d^2
 +(b+\gamma c/2)^2+(1-\gamma^2/4)c^2.
$$
The two remaining coefficients are exactly 13/256 and 175/256,
respectively. Hence the Hessian is nonnegative on every rank-one
direction, proving global rank-one convexity by line integration.

The exact quartic gap is
$$
E_{\nu_r} F_\gamma(X)-F_\gamma(0)
=\frac{4r^2}{1+r^2}
 [r^2(1-\gamma)+(1+\gamma)].
$$
It is negative whenever r²>17. In particular r=5 gives
$$
\boxed{\quad\Delta(\nu_5)=0,\quad
 E F_{9/8}(X)=-50/13<0=F_{9/8}(0).\quad}
$$
Thus nu_5 is not a laminate despite satisfying the determinant
moment and EVERY determinant-index/skew test in the penalty.

The classical rank-one-convexity threshold is 2/sqrt(3).
The recent Bruno--Pasqualotto preprint
[Quasiconvexity for the Dacorogna--Marcellini Energy](https://arxiv.org/abs/2608.06367)
claims quasiconvexity up to this threshold. Under that result
nu_5 is not a homogeneous gradient Young measure. The refutation
of the proposed abstract splitting principle is unconditional
and does NOT require that preprint, or a determination of
whether nu_5 is a gradient Young measure. There is no actual
compatible-gradient witness constructed here.

Even without the recent result, the classical boundedness of the
Beurling transform on L^4 excludes nu_r as a gradient Young
measure for all sufficiently large r: its conformal fourth
moment divided by its anticonformal fourth moment is r².
For bounded periodic gradients at mean zero this ratio is
bounded by the fourth power of the L^4 transform norm (the
periodic version, or extension via affine-boundary generation).
The moment inequality passes to bounded generating sequences.
This also shows that some of the explicit family lie outside
the gradient-law class independently of any new QC theorem.

## 3. Robustness: connected, smooth laws and arbitrary neutral covariances

The counterexample is not a pathology of eight isolated atoms.
Convolve nu_5 with a centered smooth rotationally invariant
compactly supported matrix density of small radius, and mix in
a small amount of a centered radial smooth bump positive on
a ball strictly containing the convolved support. The resulting
compact density has connected support and is smooth and positive
in that ball. All means remain zero, covariances stay isotropic,
and the determinant average is zero (isotropic covariance
annihilates the determinant). The quartic gap remains strictly
negative for sufficiently small smoothing/mixing parameters,
by convergence on a common compact set. If desired rescale
to recover exactly the original isotropic covariance.
Thus even smoothness and connected support combined with
Delta=0 do not imply lamination.

A further moment-only obstruction is useful as a global stop
rule. For ANY positive definite covariance C0 satisfying
the determinant-neutral condition tr(J_det C0)=0, where
J_det=D² det, there exist both compact laminates and compact
nonlaminates with mean zero and covariance exactly C0. Indeed:

* The neutral covariance decomposition in
  [MARTINGALE_DEFECT](IWANIEC_MORREY_MARTINGALE_DEFECT.md)
  expresses C0 as sum R_i R_i^T of rank-one matrix directions.
  The law of a sum of independent fair signed R_i is a
  finite-order laminate with covariance C0.
* Choose 0<beta<lambda_min(C0). Then C0-beta I is still
  positive definite and neutral, since tr J_det=0.
  By the same decomposition choose a fixed finite-order
  laminate with covariance 2(C0-beta I). Mix it with
  equal weight with nu_r scaled by sqrt(2 beta / c_r),
  where c_r=r²/(1+r²). This second law has covariance
  2 beta I; the total covariance is C0 and all means
  are zero. Its quartic expectation tends to -infinity
  as r->infinity, because the scale stays bounded away
  from zero and infinity and the displayed formula
  for the expectation tends to -infinity. The first
  law's quartic expectation is fixed and finite.
  For large r the mixture is therefore a nonlaminate.

This is not an assertion that every finite moment list
is insufficient, nor that covariance can be ignored for
actual gradients. It proves that even fixing the ENTIRE
positive definite neutral covariance cannot resolve
lamination. The obstruction applies in particular to
the large blind region of Theorem A.

## 4. Consequence for the MAIN adaptive splitting gate

Let r be the unrestricted minimum residual and r_comp the
minimum over decompositions with average Delta=0, as in
[TRAP_COMPATIBILITY](IWANIEC_MORREY_TRAP_COMPATIBILITY.md).
The feasible set is compact for a fixed compact support.
For nu_5 the constrained problem is feasible by the
trivial decomposition, since Delta(nu_5)=0.

**Corollary B.** r_comp(nu_5)>r(nu_5)>0.

The second strict inequality follows from nonlamination
and the exact zero criterion for r in the adaptive note.
If r_comp=r, a constrained minimizer would also be an
unconstrained minimizer. The terminal-trap classification
then says its conditional laws are either Dirac or nontrivial
blocked laws. The latter have strictly positive Delta
by the previous trap exclusion theorem and cannot appear
with positive mass in a zero-average-Delta decomposition.
All conditionals would be Dirac, giving r=0, a contradiction.
Compact attainment is essential to this strict conclusion.

In particular the proposed stronger statement
"every non-Dirac minor-compatible Delta-zero law admits a
nonzero rank-one binary split into minor-compatible Delta-zero
children" is FALSE. If it were true, the constrained
variance-maximization proof from the adaptive note (with
the additional closed Delta-zero constraint) would force
all conditionals of a constrained optimizer for nu_5
to be Dirac. The same argument proves the existence of
a non-Dirac constrained-blocked law: at a constrained
optimizer for nu_5, at least one nontrivial posterior
cannot admit such a split. This constrained obstruction
is not the old two-sheeted minor-only trap geometry.

The original equality r_comp=r restricted to ACTUAL
gradient laws is NOT disproved. It remains equivalent
to unrestricted Morrey by the earlier theorem. But it
cannot be deduced solely from minor compatibility and
Delta=0, including all transformed determinant-index
tests and exact second moments, even with a smooth
connected initial law. Additional spatial information
is required; do not try to finish the false stronger
principle by enumerating more posterior supports.

## 5. Verification and disposition

The standard-library checker
[research/audit/iwaniec_delta_nogo_exact.py](../../research/audit/iwaniec_delta_nogo_exact.py)
was executed locally with Python 3, producing:
    8-atom law: mean zero, determinant moment zero, covariance (25/26)I4, quartic gap -50/13; exact SOS coefficients passed
    256 rational affine controls, including singular factors: determinant identity, both gap bounds and strict relative margin passed

These controls check algebra, not the universal transform
quantifier: Sections 1--2 supply that hand proof.
No Lean check, external review or novelty clearance.

**Stop rule and remaining positive task:** abandon the
Delta-only uniform splitting lemma as refuted, rather than
add more isolated fixed-wave cases. A stronger spatially
preserved structure must exclude the entire blind region
of nonlaminates above. At minimum, the new quartic example
shows why one needs information beyond the determinant-index
family. The exact input-adaptive martingale characterization
and quantitative repair remain valid tools; no construction
of a neutral martingale for all actual gradients is supplied.
