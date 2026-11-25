# Homogeneous anisotropic Morrey: the degree-two origin gate and a global quasiconvexity theorem for the Guerra--Kristensen obstruction

24 November 2026. **Research pivot:** retain positive homogeneity and
remove isotropy. The signed homogeneous isotropic theorem for every
p>0 is now formally verified, not a candidate awaiting audit. See
[Theorem A at main 17fd1c3](https://github.com/vltanh/lean4-morrey/blob/17fd1c3a83f0c96fbc25a5d916187290f6fc0098/Morrey/HomogeneousIsotropic/Signed/Main.lean#L355)
and [successful Lean CI](https://github.com/vltanh/lean4-morrey/actions/runs/45424739241).
The user explicitly asked to switch from the stalled nonhomogeneous
isotropic program to anisotropy first.

There are two rigorous positive advances:

1. **Complete degree-two homogeneous ORIGIN theorem**, for arbitrary
   anisotropy and signs, even assuming only rank-one convexity at
   zero (Jensen against finite laminates at zero). A determinant
   lower support exists. All failures are detected by a laminate
   with at most THREE atoms and two rank-one splitting steps.
   This settles the p=2 origin-only homogeneous Morrey question,
   not the all-base problem. It also reduces signed degree-two
   GLOBAL rank-one convex integrands to nonnegative ones by
   subtracting a null Lagrangian.
2. **Global RC iff QC theorem**, at ALL bases, for the entire family
   F([[a,b],[c,d]])=a_+ d_+ + q(b,c), with arbitrary finite q.
   The exact criterion is convexity of q AND q+bc. In particular
   this proves quasiconvexity of the anisotropic nonpolyconvex
   example from Guerra--Kristensen (2022), Proposition 3.7,
   and all its homogeneous powers p>=2. The proof uses one
   scalar half-space projection and a partial minimization
   argument, not rotational invariance or a polyconvex support.
   Even q=(b-c)^2/4, with a degenerate shear penalty, is covered.

These are hand proofs. The elementary symbolic and rational controls
were actually run in the working container. No Lean verification of
these new theorems, independent referee review, or priority claim.
**General homogeneous anisotropic quasiconvexity at every base
remains OPEN.** The origin-only formulation (as used e.g. by Cassese)
is strictly a weaker target. Do not confuse them.

## 1. Exact degree-two origin theorem

Let F:R^(2x2)->R be finite-valued and positively 2-homogeneous.
Then F(0)=0. No evenness, nonnegativity, isotropy, or differentiability
is required.

**Theorem 1.** The following are equivalent:

(i) Every finite laminate with barycenter zero obeys E F>=0.
(ii) Every finite laminate with barycenter zero obtained by at
most two rank-one splitting steps (at most three leaves) obeys E F>=0.
(iii) There exists a real c such that F(X)>=c det X for every X.

When F is continuous, these are also equivalent to quasiconvexity
at zero, and polyconvexity at zero (a touching polyaffine support).
In fact (iii) gives E F>=0 for EVERY integrable law with
E det X=0, without even requiring E X=0.
For a continuous F the statement about quasiconvexity uses the
usual realization of finite laminates as compactly supported
gradient Young laws; for the global RC version of the theorem
no realization theorem is needed.

### 1.1 Rank-one dilution

Assume (ii). If C has rank at most one and F(C)<0, use the
rank-one split
    0 = eps C + (1-eps)(-eps/(1-eps) C),
for 0<eps<1. Its F-expectation is
    eps F(C) + eps²/(1-eps) F(-C)<0
for sufficiently small eps. Thus F>=0 on all rank-deficient matrices.

More generally suppose C is rank deficient and a rank-one
two-point split of C has negative mean energy E<0. Dilute
this split by the very same splitting of zero, then split
the C atom. The resulting laminate has at most three leaves
and energy
    eps E + eps²/(1-eps) F(-C)<0
for sufficiently small eps. Thus every rank-one split with
rank-deficient barycenter has nonnegative mean energy.
The dilution step works for arbitrary positive degree p>1
with eps^p/(1-eps)^(p-1) replacing the second coefficient.

### 1.2 Opposite determinant rays are always rank-one connectable

Fix X,Y with D=det X>0 and det Y=-E<0, E>0.
The polynomial det(X-tY) is positive at t=0 and tends to
minus infinity as t tends to plus infinity, since its
leading coefficient is det Y. Therefore some t>0 satisfies
det(X-tY)=0. These matrices are distinct (their determinant
signs differ), so X and tY are rank-one connected.

Put theta=t²E/(D+t²E). The rank-one segment has affine
determinant, hence its point C=theta X+(1-theta)tY has
determinant zero. By Section 1.1,
$$
0\le\theta F(X)+(1-\theta)t^2 F(Y)
=\frac{D t^2 E}{D+t^2 E}
     \left(\frac{F(X)}{D}+\frac{F(Y)}{E}\right).
$$
The crucial cancellation is the matching degree TWO of
F and the determinant. Thus for EVERY opposite-sign pair,
$$
\frac{F(Y)}{\det Y}\le\frac{F(X)}{\det X}.
$$
Both orientation classes are nonempty and F is finite-valued.
It follows that the interval
$$
\boxed{
\sup_{\det Y<0}\frac{F(Y)}{\det Y}
\ \le\ c\ \le\
\inf_{\det X>0}\frac{F(X)}{\det X}
}
$$
is a nonempty interval with finite endpoints. For either
orientation it gives F>=c det, and rank-deficient matrices
are handled by F>=0 from Section 1.1. This proves (iii).
The implications (iii)=>(i)=>(ii) follow from the determinant
moment identity on laminates. The QC and PC assertions
follow from the null Lagrangian and the standard implication
of quasiconvexity at a base to laminate Jensen there. QED.

The three-leaf bound is sharp for this arbitrary origin
test: F=-|det| passes every one-step zero-base rank-one
split, since its atoms are rank deficient, but fails the
three-atom laminate with masses 1/4,1/4,1/2 at
I, diag(1,-1), diag(-1,0). First split zero into C=diag(1,0)
and -C, then split C into the first two atoms. Its energy
is -1/2. This sharpness concerns the origin TEST, not a
globally RC counterexample.

### 1.3 Consequences for the research program

* For EVERY globally rank-one-convex positively 2-homogeneous F,
  F-c det is globally nonnegative, rank-one convex and
  2-homogeneous. Quasiconvexity at any base is unchanged by
  this subtraction. Thus the signed all-base degree-two
  problem is exactly equivalent to its nonnegative version.
* Even for arbitrary continuous 2-homogeneous F, existence of
  a finite globally RC minorant is equivalent to existence
  of a finite globally QC minorant and to condition (iii).
  Indeed a violating three-atom laminate can be dilated by
  an arbitrary large factor T. Any finite RC minorant G
  would satisfy G(0)<=T² E F -> -infinity, impossible.
  Conversely c det is a finite polyconvex minorant.
  This does not identify the envelopes away from zero.
* This closes the degree-two case of the origin-only question
  called the homogeneous Morrey problem in Cassese,
  [arXiv:2608.03488](https://arxiv.org/abs/2608.03488),
  Section 1.3, in dimension 2x2. We do not claim this
  elementary origin result has not appeared elsewhere.
* For arbitrary degree p>1, any globally RC homogeneous F
  is nonnegative on rank-deficient matrices by rank-one
  convexity on rays. The same opposite-sign joining and
  determinant-balanced averaging shows that it cannot be
  strictly negative at matrices of BOTH determinant signs.
  But the ratio argument for a single constant determinant
  support uses p=2 exactly. For p=1 the known
  Kirchheim--Kristensen theorem gives affine lower supports
  at all rank-deficient bases
  ([arXiv:1505.04654](https://arxiv.org/abs/1505.04654)).
  Degree 0<p<1 is already identically zero without isotropy
  in the verified library. The all-base anisotropic problem
  is not closed for the remaining degrees.

## 2. One scalar half-space projection

We use the scalar projection theorem already formalized
in the pinned lean4-iwaniec dependency,
[Agazzi.lemma4](https://github.com/vltanh/lean4-iwaniec/blob/972c01272b2a573ae58fb43fac47c97196db2cbb/Agazzi/Proof/ScalarProjection/Main.lean).
For a compact convex K in R², p in K, and a periodic
Lipschitz scalar perturbation eta, its L² projection zeta
onto the set C of periodic scalar maps with p+D zeta in K
exists and is unique. The projected affine-plus-periodic
map v=p dot x+zeta satisfies
    Dv=Du or Dv in boundary K a.e.,
where u=p dot x+eta.

We recall two strengthened properties, proved directly from
order preservation (also see the earlier
[projection-max note](IWANIEC_MORREY_NONHOMOG_PROJECTION_MAX.md)).

### 2.1 Order and translation preservation

C is closed under pointwise minimum and maximum, because
their gradients agree with one of the two original gradients
almost everywhere. Consequently the L² projection P is
order preserving. For inputs eta1<=eta2, let zeta_i=P eta_i.
Replacing the two outputs by their pointwise min and max
gives competitors for the same two minimization problems.
Where zeta1>zeta2 the reduction in their sum of squared
distances is
    2(zeta1-zeta2)(eta2-eta1)>=0.
Since each output is already a minimizer, the competitors
must also attain their respective minima. Uniqueness
implies zeta1<=zeta2. Projection commutes with translations
in the independent variables and with addition of arbitrary
constants, by invariance of C and of the objective. It
preserves the integral of the input, by minimizing over
constant shifts of the output.

If u is L-Lipschitz on R² (Euclidean norm), the input
u(x+h) is bounded between u(x)-L|h| and u(x)+L|h|.
On periodic parts these are the inputs eta(x+h)+p dot h
and eta(x) +/- L|h|. Order and translation/constant
equivariance give the same inequalities for v. The
Lipschitz representatives make them valid pointwise for
each h. Hence v is also L-Lipschitz.

In particular, when p_1>=0 choose
    K={r in R²: r_1>=0, |r|<=L+1}.
It contains p, since p is the mean of Du. The artificial
round boundary |Dv|=L+1 is never attained at a differentiability
point of v. Thus the selection theorem yields
$$
\boxed{0\le\partial_1 v\le(\partial_1 u)_+
       \quad\text{a.e.}}
\tag{2.1}
$$
Indeed the projected first derivative is either the
original derivative or zero. This derives a half-space
projection from the compact-constraint theorem; no
unbounded-K version is assumed.

### 2.2 Nonlinear directional sign

For every continuous nondecreasing alpha:R->R and every
fixed spatial direction e, we have
$$
\boxed{\int \alpha(D_e\zeta)\,D_e(\eta-\zeta)\ge0.}
\tag{2.2}
$$
Here the derivatives are of periodic parts, so their
means are zero. A proof needing only the scalar order
property is as follows.

For any eta1,eta2 and scalar h, project
max(eta1,eta2+h). Its output is at least
max(P eta1,P eta2+h), and the projection preserves means.
Subtract the mean of P eta2+h to obtain
$$
\int(P\eta_1-P\eta_2-h)_+
\le\int(\eta_1-\eta_2-h)_+ .
$$
Apply this to eta1=eta(.+t e), eta2=eta and h=t k, divide
by t>0, and let t decrease to zero. Lipschitz difference
quotients converge almost everywhere at differentiability
points and in L¹ by bounded convergence. We get
    int (D_e zeta-k)_+ <= int (D_e eta-k)_+
for every real k. The mean derivatives are equal (zero).
By the hinge-function representation of convex functions
on bounded intervals, this implies
    int Psi(D_e zeta)<=int Psi(D_e eta)
for every finite convex Psi. The same argument works for
every Lipschitz periodic input.

Let eta_lambda=zeta+lambda(eta-zeta) for lambda>=0.
The projection variational inequality shows P eta_lambda=zeta:
the residual has merely been multiplied by a nonnegative
scalar. Apply the convex-order inequality to eta_lambda
and the C¹ convex primitive Psi whose derivative is alpha.
Take the right derivative at lambda=0. The gradients are
bounded uniformly near zero, so differentiation under the
integral is justified. This proves (2.2). QED.

## 3. A global all-base RC iff QC theorem

For any finite function q:R²->R, define
$$
F\begin{pmatrix}a&b\\c&d\end{pmatrix}
=a_+ d_+ + q(b,c),\qquad t_+=\max(t,0).
$$

**Theorem 2.** The following are equivalent:
* F is globally rank-one convex;
* F is globally quasiconvex;
* q(b,c) and q(b,c)+bc are both convex on R².

In particular the conclusion applies to every finite q
satisfying the two convexity conditions, without assuming
any polynomial structure, homogeneity, symmetry in b,c,
or a positive definite Hessian. If q is positively
2-homogeneous, then so is F; convexity of q implies q>=0,
so all positive powers F^(p/2) for p>=2 are QC and
positively p-homogeneous as well.

### 3.1 Necessity of the two convexities

For any direction (beta,gamma) of the off-diagonal
variables, the matrix
    H=[[1,beta],[gamma,beta gamma]]
has rank one. Vary it first at a matrix with a=d=-1.
For sufficiently small line parameter both diagonal entries
stay negative. The restriction of F is exactly q along
the indicated off-diagonal line, so rank-one convexity
gives local convexity at every point of that line. Because
the base b,c is arbitrary, q is convex along the whole line.
Repeat at matrices with a=d=1. There the rectified product
is ad=det X+bc. The determinant is affine on the rank-one
line, so the same argument proves convexity of q+bc.
Both arguments use the elementary fact that a continuous
locally convex function on a real interval is convex.
Continuity of F and hence q follows from finite rank-one
convexity (separate convexity). This proves necessity.

### 3.2 Reduce global Jensen to a centered scalar inequality

Let X=A+Dphi be any periodic compatible Lipschitz
gradient on the unit torus, with entries a,b,c,d and
corresponding base entries a0,b0,c0,d0.

If a0<=0 or d0<=0 then F(A)=q(b0,c0).
The integrand dominates q pointwise, so ordinary convex
Jensen proves the desired inequality. It remains to treat
a0>0,d0>0.

Apply Section 2.1 to the first scalar component u_1
of the affine-plus-periodic map, with p=(a0,b0).
Write the projected row as (r,t)=Dv. Then
0<=r<=a_+, and pointwise r d<=a_+d_+, even when d<0.
The compatible stacked map (v,u_2) has the SAME affine
base A. Its determinant has the usual mean:
    E(r d-t c)=a0 d0-b0 c0.
Consequently
$$
E F(X)-F(A)
\ge E[q(b,c)-q(b_0,c_0)+t c]-b_0 c_0.
\tag{3.1}
$$
This is the essential spatial step. It replaces one factor
of the rectified product by a derivative of an actual
projected scalar potential; there is no pointwise
unjustified replacement by a non-gradient field.

For now suppose q is smooth and both q and q+bc are
uniformly strongly convex. Put
    B=b-b0, C=c-c0, P=t-b0,
so all three variables have mean zero. Define the centered
convex remainder
$$
f(B,C)=q(b_0+B,c_0+C)-q(b_0,c_0)
       -q_b(b_0,c_0)B-q_c(b_0,c_0)C.
$$
Then f is strongly convex with f(0,0)=0,Df(0,0)=0.
The function f(B,C)+BC is precisely the centered remainder
of q+bc, so is also convex and nonnegative. Equation (3.1)
becomes
$$
E F(X)-F(A)\ge E[f(B,C)+P C].
\tag{3.2}
$$

### 3.3 Partial minimization supplies exactly the projection sign

For each real p let y(p) be the unique minimizer of
    y -> f(p,y)+p y .
Existence and uniqueness follow from uniform strong
convexity in y; the linear term does not destroy coercivity.
The first-order condition f_C(p,y(p))+p=0, and
f_CC>0, give a continuously differentiable y by the
implicit function theorem. Set
    alpha(p)=f_B(p,y(p)).
Differentiation gives
$$
\alpha'(p)
=f_{BB}-\frac{f_{BC}(f_{BC}+1)}{f_{CC}},
$$
with derivatives evaluated at (p,y(p)).
Convexity of f and f+BC gives, respectively,
    f_BB f_CC >= f_BC²,
    f_BB f_CC >= (f_BC+1)².
The maximum of these two squares is at least their
average, and that average is f_BC(f_BC+1)+1/2.
Therefore alpha'(p)>=0. In particular alpha is exactly
an admissible directional-sign multiplier in (2.2).

Now the convex tangent inequality for (B,C) ->
f(B,C)+p C at (p,y(p)) gives
$$
f(B,C)+p C\ge f(p,y(p))+p y(p)
                     +\alpha(p)(B-p)
\ge\alpha(p)(B-p),
$$
where the second inequality uses f+BC>=0.
Apply this pointwise with p=P. The variables P and B-P
are the second directional derivatives of the projected
periodic part zeta and its residual eta-zeta, respectively.
The nonlinear projection sign (2.2) gives
    E alpha(P)(B-P)>=0.
Hence (3.2) proves E F(X)>=F(A).

This proof does NOT need independent projections of the
two rows or contraction of a cross-row correlation. It
handles arbitrary nonlinear coupled shear penalties q
by the scalar monotonicity of the partially minimized
tangent slope.

### 3.4 Remove smoothness and strict convexity

A finite convex q is continuous. Convolve it with a smooth
nonnegative compactly supported even mollifier and add
eps(b²+c²). This yields a smooth uniformly strongly
convex q_eps. Since convolution of bc with an even
mollifier equals bc plus a constant, q_eps+bc is also
uniformly strongly convex if q+bc is convex. Thus the
smooth case just proved applies. As eps tends to zero
(together with the mollifier scale), q_eps tends locally
uniformly to q. Passing to the limit in the bounded
gradient Jensen inequality proves the full theorem.
The zero-boundary test convention follows by periodizing
the perturbation. Finally QC implies global RC by the
standard implication, completing the equivalence. QED.

## 4. Exact anisotropic applications

Take q(b,c)=alpha b²+beta c²+gamma bc. The criterion is
precisely
$$
\alpha,\beta\ge0,\qquad
4\alpha\beta\ge\max\{\gamma^2,(\gamma+1)^2\}.
$$
This is an exact all-base RC=QC classification of
the full coupled quadratic shear family, including
degenerate boundary cases. It includes q=(b-c)^2/4,
since q+bc=(b+c)^2/4. In this particular case the
one-projection proof reduces to the elementary identity
    (B-C)^2/4 + P C
      = (C-B+2P)^2/4 + P(B-P),
and the ordinary directional quadratic sign suffices.

Guerra--Kristensen, *Automatic quasiconvexity of homogeneous
isotropic rank-one convex integrands*, Arch. Ration. Mech.
Anal. 245 (2022), 479--500,
[doi:10.1007/s00205-022-01792-2](https://doi.org/10.1007/s00205-022-01792-2),
Proposition 3.7, uses the homogeneous anisotropic example
$$
F_p(X)=\left(a_+d_++\tfrac12(b^2+c^2)\right)^{p/2},
\qquad p\ge2 .
$$
It is rank-one convex but not polyconvex. Theorem 2
proves its global quasiconvexity (apply convex increasing
composition for the power). This is the specific
anisotropic obstruction recorded in the earlier
[P2_SIGNED note](IWANIEC_MORREY_P2_SIGNED.md), not an
arbitrarily selected perturbation of an isotropic core.

Recall the exact corrected minors witness at I, with
weights 1/4,3/8,3/8 and diagonal entries (-2,-2),(4,0),(0,4).
The matrix and determinant means are I and 1, while
all three F_p energies vanish and F_p(I)=1. For any
q obeying the conditions of Theorem 2, the same witness
has F(A)=1+q(0,0) and all atoms have F=q(0,0);
hence Theorem 2 gives nonpolyconvex QC energies for
the whole arbitrary-q family. The same calculation
works at a rank-one base [[1,1],[1,1]] by keeping
the off-diagonal entries b=c=1 in all three atoms.
The mean determinant is then zero, but the Jensen
gap in the lifted minors variables is still exactly 1.
These witnesses are not gradient laws; they do not
contradict Theorem 2. The positive powers of a
nonnegative homogeneous q version retain the strict
witness by monotonicity of the power.

The result is stable under fixed matrix translations,
invertible left/right linear changes, addition of
polyconvex or other known QC integrands, nonnegative
sums, pointwise maxima and locally uniform limits.
Translations include arbitrary rectification thresholds;
positive factors of a_+d_+ are handled by dividing q
by that factor and multiplying the energy back. No
claim is made that such closures generate every
homogeneous anisotropic RC function.

## 5. Status, controls, next task

The exact checker
[origin_and_rectification_exact.py](../../research/audit/origin_and_rectification_exact.py)
was run locally in Python/SymPy, giving:

    Exact determinant-balanced two-stage laminate identities passed.
    Exact weighted shear square-completion, rank-one and non-polyconvex controls passed.
    Exact partial-minimization monotonicity and minimal-shear identities passed.

The symbolic checks do not verify the analytic projection or
the universal rank-one joining argument; the proofs above
are the mathematical justification.

The strongest NEW general conclusion without isotropy is
the full degree-two origin gate and exact global sign
reduction at degree two. The positive all-base proof for
the classical anisotropic non-PC obstruction gives a
new nonpolyconvex QC mechanism using one scalar projection,
including arbitrary nonlinear q. The full anisotropic
positive-homogeneity implication RC=>QC at nonzero bases
remains open. The origin result alone is not sufficient.
A natural next question is whether suitable scalar
projection calibrations can recover touching lower
supports for arbitrary angular profiles; their completeness
has not been established. Do not enumerate shear
polynomial degrees or restrict the target to the examples
in this note. The nonhomogeneous isotropic branch of
the attack is paused, and the signed homogeneous isotropic
theorem is formally CLOSED, not awaiting audit.
