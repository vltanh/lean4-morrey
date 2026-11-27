# An exhaustive fixed-dyadic reduction of unrestricted planar Morrey

27 November 2026. **Hand proofs, not new Lean theorems.** This note reduces
unrestricted finite-valued planar Morrey to one fixed dyadic scaling class,
one fixed base, and a fixed small neighbourhood of that base. It also proves
a separate local-uniform density theorem in arbitrary matrix dimensions
which preserves all orthogonal symmetries, including full planar isotropy.
No publication-priority claim is made.

The main reduction below is exhaustive and uses no isotropy assumption.
It does **not** prove the remaining Jensen inequality. The localized profile
inside one scale period is still arbitrary; a finite exact classification
or a uniform complexity cutoff has not been obtained.

For a concrete single target one may fix dilation 2, relative first-order
error 1/100, gradient Lipschitz bound 202, base I, and test-gradient radius 1/10. An affirmative universal
Jensen theorem for that canonical class would settle unrestricted planar
Morrey. The symmetry-preserving density theorem is a different result: its
period may depend on the approximation, and its counterexamples retain
isotropy when the input has it.

The arguments are self-contained: smoothing and strictification, a smooth
maximum, affine cancellation under translation, and disjoint scaled copies.
The secondary density proof additionally uses Taylor flattening and a slow
logarithmic cutoff. No uncertified research reduction is used as a premise.
The verified homogeneous theorem enters only in Section D8 to explain the
limited information obtained by averaging the remaining scale phase.

## Fixed-period theorem

Fix **any prescribed** number $T>1$, and any prescribed
$0<\eta<1$. The unrestricted finite-valued planar implication
$\mathrm{RC}\Rightarrow\mathrm{QC}$ is equivalent to the same implication
restricted to energies $G:\mathbb R^{2\times2}\to\mathbb R$ with **all**
of the following properties:

1. $G$ is globally $C^{1,1}$, smooth away from the origin, and
   uniformly strongly rank-one convex.
2. $G(TX)=T^2G(X)$ for every $X$. In particular one can fix
   $T=2$ once and for all.
3. $G(-X)=G(X)$, and $G(X)=|X|_F^2$ whenever $\det X\le0$.
4. The following relative $C^1$ estimates hold globally:

   $$
   |G(X)-|X|_F^2|\le\eta |X|_F^2,\qquad
   |DG(X)-2X|_F\le\eta |X|_F.
   \tag{M1}
   $$

5. The full gradient obeys the universal bound $\operatorname{Lip}(DG)\le202$. Section M1.1 proves this quantitative version of the localization.

Thus $(1-\eta)|X|_F^2\le G(X)\le(1+\eta)|X|_F^2$. After smoothing and strictification, the localized smooth witness's Jensen
defect is retained exactly by translation and periodization, before a
positive normalization. The resulting violating test can have positive
determinant almost everywhere and define a bi-Lipschitz deformation.

This is an **exhaustive reduction**, not a proof that these energies are
quasiconvex. The strong rank-one constant is positive but has no asserted
universal positive lower bound. The full Hessian bound 202 is universal.
No bound on higher derivatives or on the number of gradient phases follows.
The relative $C^1$ bounds do not imply a small Hessian perturbation.

The easy implication is restriction of a universal theorem. We prove the
converse by transferring any hypothetical strict counterexample into this
class. No isotropy hypothesis is used. Full continuous isotropy is not
preserved by the translation step; the separate symmetry-preserving density
theorem below addresses that different requirement.

## M1. Smooth strong counterexample with a compact quadratic perturbation

Suppose a finite-valued RC energy has a strict negative Jensen gap for a
bounded gradient test $X(x)=A+Du(x)$, with $\int Du=0$, on a domain of
normalized volume one. Convolution in matrix space preserves rank-one
convexity and converges uniformly on the bounded matrix range. Adding a
sufficiently small positive multiple of $|X|_F^2$ changes the gap by only
that multiple of $\int|Du|_F^2$. Consequently we may begin with a smooth
energy $F$, a number $m>0$, and a strict defect $\delta>0$ such that

$$
D^2F(X)[V,V]\ge m|V|_F^2\quad(\operatorname{rank}V=1),\qquad
\int F(A+Du)-F(A)=-\delta.
\tag{M2}
$$

Choose $B>0$ containing the base and the entire essential test range.
Choose radii $B<r_1<r_2<R$. For a sufficiently large $q>0$, with
$2q\ge m$, the quadratic

$$
h(X)=q|X|_F^2-C,\qquad C=q r_1^2,
$$

lies at least one below $F$ on $|X|_F\le B$, and at least one above
$F$ on the closed collar $r_2\le|X|_F\le R$. Indeed the respective
quadratic coefficients $B^2-r_1^2$ and $r_2^2-r_1^2$ have strict
opposite signs, while $F$ is bounded on the relevant compact sets.

Use a smooth convex maximum $\mathcal M(s,t)$, nondecreasing in each
argument, equal to $\max(s,t)$ whenever $|s-t|\ge1$, and satisfying
$\mathcal M(s+a,t+a)=\mathcal M(s,t)+a$. For example, smooth
$|s-t|$ by a compactly supported even mollifier in
$(s+t+|s-t|)/2$. Set

$$
K(X)=
\begin{cases}
\mathcal M(F(X),h(X)),& |X|_F<R,\\
h(X),& |X|_F\ge R.
\end{cases}
$$

It is smooth because the two definitions agree on a collar. It equals
$F$ on the test ball. Both inputs have the common rank-one curvature
margin $m$; differentiating $\mathcal M$ gives a convex combination
of their second derivatives plus a nonnegative square term. Hence $K$
retains that margin. Equivalently, translation equivariance of
$\mathcal M$ permits subtraction of $m|X|_F^2/2$ before taking the
maximum.

Finally add the constant $C$, which leaves the Jensen gap unchanged:

$$
F_0(X)=K(X)+C=q|X|_F^2+\varphi(X),\qquad
\varphi\in C_c^\infty(B_R).
\tag{M3}
$$

The strict defect is still $-\delta$, and $F_0$ is smooth and
uniformly strongly RC. Its full Hessian is bounded because it is a fixed
quadratic outside a compact set. No inner Taylor flattening, quadratic
polyconvexity theorem, or interpolation between different quadratic
backgrounds is needed.

### M1.1 A universal full-Hessian bound

The fixed-period reduction can additionally require the universal bound
$\operatorname{Lip}(DG)\le202$. The strong rank-one constant remains
positive but is not asserted to have a universal positive lower bound.

First translate the original integrand so that the violating base is zero.
Scale its matrix argument and test together to place the entire test-gradient
range in $B_1$; for example, replace $F(X)$ by $F(sX)/s^2$ and
$u$ by $u/s$, with $s$ sufficiently large. The Jensen gap is
multiplied by $s^{-2}>0$. After smoothing and sufficiently small convex
strictification as above, subtract the affine jet at zero. We now have a
smooth strongly RC energy $F$ with

$$
F(0)=0,\qquad DF(0)=0,\qquad \|Du\|_{L^\infty,F}\le1,
$$

and a strict negative gap. Choose
$a>0$ with $a\ge\sup_{B_4}\|D^2F\|_{\mathrm{op}}$. Taylor's
formula gives, on $B_4$,

$$
|F(X)|\le\tfrac a2|X|_F^2,\qquad |DF(X)|_F\le a|X|_F.
\tag{U1}
$$

Set

$$
q=2a,\qquad h(X)=2a|X|_F^2-8a.
$$

On $B_1$,
$F-h\ge8a-\tfrac52a|X|_F^2\ge11a/2$. On the collar
$3\le|X|_F\le4$,
$h-F\ge\tfrac32a|X|_F^2-8a\ge11a/2$.

Use the smooth maximum with transition width $a$,

$$
\mathcal M_a(s,t)=\frac{s+t+a\Theta((s-t)/a)}2,
\tag{U2}
$$

where $\Theta$ is smooth, even and convex, equals absolute value for
$|z|\ge1$, and satisfies $|\Theta'|\le1$, $0\le\Theta''\le2$.
Such a function is obtained by convolving absolute value with a smooth
even probability density supported on $[-1,1]$ and bounded above by one.
Define $K=\mathcal M_a(F,h)$ on $B_4$, and $K=h$ outside.
The strict collar gaps make the resulting function smooth, equal to $F$
on the test ball and to $h$ near and outside the outer boundary.

On $B_4$, write $\alpha=(1+\Theta'((F-h)/a))/2$. Then

$$
D^2K=\alpha D^2F+(1-\alpha)4aI
 +\frac{\Theta''((F-h)/a)}{2a}
       (DF-Dh)\otimes(DF-Dh).
\tag{U3}
$$

Here $0\le\alpha\le1$, and (U1) gives
$|DF|_F\le4a$, $|Dh|_F\le16a$. Therefore

$$
\|D^2K\|_{\mathrm{op}}
 \le4a+\frac{(20a)^2}{a}=404a.
\tag{U4}
$$

Outside $B_4$ the Hessian is $4aI$, so the same bound holds globally.
The final term in (U3) is positive semidefinite; hence the common strong
rank-one curvature margin of the two inputs is preserved as well.

Now $F_0=K+8a=q|X|_F^2+\varphi$, with $\varphi$ smooth and compactly
supported in $B_4$. Adding the constant changes neither Hessian nor
Jensen gap. Every translated/reflected local patch has exactly the Hessian
of $F_0$, up to an orthogonal pullback; every degree-two scaled patch
has that same Hessian bound. Disjointness of the patches and the argument
at zero in the fixed-period proof give the bound $404a$ for the global
Lipschitz constant of $D\widehat G$. Dividing by $q=2a$ yields

$$
\boxed{\operatorname{Lip}(DG)\le202.}
\tag{U5}
$$

The numerical constant is deliberately elementary, not optimized. It is
independent of the original energy, its negative gap, the prescribed
relative $C^1$ tolerance, and the fixed dilation period.

## M2. Move the perturbation to a thin annulus without changing the defect

Let $B_0=M I$, where $M$ will be chosen sufficiently large, and put
$a=|B_0|_F=\sqrt2 M$. Define an even pair of translated perturbations

$$
\psi(X)=\varphi(X-B_0)+\varphi(-X-B_0),\qquad
H(X)=q|X|_F^2+\psi(X).
\tag{M4}
$$

For $a>R$, the two support balls are disjoint. On the first ball,
writing $Y=X-B_0$,

$$
H(B_0+Y)=F_0(Y)+2qB_0:Y+q|B_0|_F^2.
\tag{M5}
$$

Thus the local energy differs from $F_0$ by an affine function. The
second ball has the analogous formula after $Y=-X-B_0$; reflection
$X\mapsto-X$ preserves rank-one directions. Everywhere else the energy
is $q|X|_F^2$. Smoothness of the compact perturbations and disjointness
therefore preserve the common strong RC margin and a full Hessian bound.

The test shifted to base $B_0+A$, with the same perturbation $u$,
lies wholly in the first ball. Equation (M5) and $\int Du=0$ show
that its Jensen gap for $H$ is **exactly** $-\delta$.

The support of $\psi$ lies in the thin radial annulus

$$
a-R\le |X|_F\le a+R.
\tag{M6}
$$

Taking $M>R$ puts both support balls inside $\mathrm{GL}^+(2)$:
every matrix within Frobenius distance $R$ of $\pm M I$ is invertible
and has the same positive determinant sign as its center.

## M3. Exact periodization at any fixed dilation

The dilation $T>1$ was prescribed before seeing the counterexample.
Increase $M$ until

$$
T(a-R)>a+R.
\tag{M7}
$$

Then all annuli obtained from (M6) by the factors $T^k$,
$k\in\mathbb Z$, are disjoint. Define

$$
\widehat G(X)=q|X|_F^2+
\sum_{k\in\mathbb Z}T^{2k}\psi(T^{-k}X)
\quad(X\ne0),\qquad \widehat G(0)=0.
\tag{M8}
$$

At every nonzero point at most one summand is active, and that summand
contains at most one translated copy of $\varphi$. On its annulus,
$\widehat G(X)=T^{2k}H(T^{-k}X)$; outside the annuli it is the
quadratic background. Thus it is smooth off zero and has a uniform full
Hessian bound there, since two differentiations cancel the factor
$T^{2k}$. It retains the strong rank-one curvature margin.

Reindexing (M8) proves

$$
\widehat G(TX)=T^2\widehat G(X).
\tag{M9}
$$

The original shifted test and its base lie in the $k=0$ annulus.
No other scaled patch intersects that annulus. Consequently its gap for
$\widehat G$ is still exactly $-\delta$: there is **no small-scale
error term** and no limiting argument in the witness transfer.

Evenness is immediate from (M4). All active patches have positive
determinant, so $\widehat G=q|X|_F^2$ on $\det X\le0$.

## M4. Relative first-derivative bounds and regularity at zero

Set

$$
C_0=\|\varphi\|_\infty,\qquad C_1=\|D\varphi\|_\infty.
$$

On an active annulus write $Z=T^{-k}X$, so $|Z|_F\ge a-R$.
Disjointness gives the global estimates

$$
\begin{aligned}
|\widehat G(X)-q|X|_F^2|
 &\le \frac{C_0}{(a-R)^2}|X|_F^2,\\
|D\widehat G(X)-2qX|_F
 &\le \frac{C_1}{a-R}|X|_F.
\end{aligned}
\tag{M10}
$$

They are zero off the active patches. Increase $M$ further until

$$
\frac{C_0}{q(a-R)^2}\le\eta,
\qquad
\frac{C_1}{q(a-R)}\le\eta.
\tag{M11}
$$

The value estimate implies differentiability at zero with derivative
zero. The gradient estimate shows that the derivatives away from zero
converge to that derivative. The uniform Hessian bound away from zero
then gives a globally Lipschitz gradient: integrate along each segment,
splitting it at zero if necessary. Hence $\widehat G\in C^{1,1}$
globally. On rank-one lines through zero its one-sided first derivatives
are both zero, so the strong convexity of the two half-line restrictions
glues with the same margin. This verifies global strong RC, including
the accumulation point of the annuli.

Now set $G=\widehat G/q$. Equations (M9)--(M11) give every property in
the fixed-period theorem, and the exact negative gap becomes
$-\delta/q<0$.

For the additional assertion about the test deformation, choose $M$
also larger than $\|A\|_{\mathrm{op}}+\operatorname{Lip}(u)$. On a
convex reference domain,

$$
v(x)=(M I+A)x+u(x)
$$

satisfies

$$
(M-\|A\|_{\mathrm{op}}-\operatorname{Lip}(u))|x-y|
\le |v(x)-v(y)|
\le(M+\|A\|_{\mathrm{op}}+\operatorname{Lip}(u))|x-y|.
$$

It is therefore bi-Lipschitz onto its image. Its derivative is a
perturbation of $M I$ of operator norm less than $M$, so its
determinant is positive almost everywhere. Its boundary values are the
prescribed affine map because $u$ has zero boundary values. This
finishes the exhaustive counterexample transfer. QED.

## M5. One fixed base and one fixed compact range suffice

For $T=2$, the equivalence can be made stronger. Fix any prescribed
$0<\rho<\min(\sqrt2-1,2-\sqrt2)$, for example $\rho=1/10$.
It is sufficient to prove the Jensen inequality for the canonical energy
class above **at the single base $I$** and only for tests satisfying
$\|Du\|_{L^\infty,F}<\rho$. Every matrix in such a test lies in

$$
B_\rho(I)\subset\{X:1<|X|_F<2,\ \det X>0\}.
\tag{M12}
$$

To prove completeness of this fixed-base criterion, first translate the
matrix argument of the hypothetical original counterexample, so that its
base is zero. The preceding construction is then performed with $A=0$.
Choose $B_0=2^K I$, where the integer $K$ is large enough to meet
every separation and relative-closeness budget, and also
$2^{-K}\|Du\|_{L^\infty,F}<\rho$. The shifted violating base is exactly
$2^K I$. For the same final energy $G$, discrete scaling gives

$$
\int G(I+2^{-K}Du)-G(I)
  =2^{-2K}\left[\int G(2^K I+Du)-G(2^K I)\right]
  =-\frac{2^{-2K}\delta}{q}<0.
\tag{M13}
$$

Thus the violating test can always be moved into one prescribed small
ball around one prescribed base, inside the fixed annulus $1<|X|_F<2$.
For example, fixing $T=2$, $\eta=1/100$, $\rho=1/10$, and
$\operatorname{Lip}(DG)\le202$ gives one concrete exhaustive target;
none of these parameters needs a ladder.

The equivalence is universal over all energies in the canonical class.
It does not say that checking these annular tests for one particular energy
certifies that energy at all other bases and ranges: the counterexample
conversion may change the integrand.

This does not contradict local small-amplitude positivity for an individual
smooth strongly RC energy: the constructed energy changes with $K$,
and its Hessian continuity scale need not have a uniform lower bound.
Nor is (M13) an accuracy-independent finite enumeration of gradients or
integrands. It is an exact reduction of the universal inequality.

For a general fixed $T>1$, the same annulus statement follows by choosing
$|B_0|_F=((1+T)/2)T^K$ and then scaling the shifted test by $T^{-K}$.
The base can likewise be fixed at $((1+T)/(2\sqrt2))I$ after the initial
matrix-argument translation. All test values then lie in $1<|X|_F<T$
for sufficiently large $K$.

### Optional finite symmetry extension

The same construction can impose any prescribed **finite** group
$\Gamma$ of orthogonal linear maps of matrix space that preserve rank-one
directions. Replace the two patches in (M4) by
$\sum_{g\in\Gamma}\varphi(g^{-1}X-B_0)$. Choose a generic nonzero
$B_0$ outside the fixed spaces of all nonidentity elements, then scale
it until its finite orbit balls are disjoint. Every local piece is a
rank-one-preserving orthogonal pullback of $F_0$, plus an affine
function; the identity patch retains the witness. All centers have the
same norm, so (M7)--(M11) work unchanged. For determinant-preserving
groups choose the generic center in $\mathrm{GL}^+(2)$ and sufficiently
large to retain the determinant-positive support assertion. If a group
reverses determinant sign, that support assertion is omitted.

This finite-group construction does not extend by simply replacing the
finite sum with a continuous rotation average: the patches would overlap,
and exact preservation of the localized negative gap would be lost.

### What the reduction settles, and what it does not

It is sufficient to settle **one fixed dyadic scaling class**, arbitrarily
close to the quadratic energy in the relative $C^1$ sense, to settle
unrestricted planar Morrey. Increasing periods, growth exponents, or
symmetry orders is not required for this equivalence. The remaining
integrands still carry arbitrary smooth local matrix dependence inside
one period; the construction does not produce a finite list of cases.

The origin regularity is deliberate. A twice differentiable-at-zero
function satisfying $G(TX)=T^2G(X)$, with $T>1$, must be exactly a
quadratic form: apply its Taylor expansion to $T^{-k}X$ and multiply by
$T^{2k}$. Thus imposing global $C^2$ regularity on this reduced
class would discard the possible nonquadratic counterexamples. The
globally $C^{1,1}$, smooth-off-zero statement avoids that invalid
restriction.


## D. Symmetry-preserving density in arbitrary dimensions

### D1. Statements and conventions

Let $\mathbb M=\mathbb R^{m\times n}$, with $m,n\ge1$, and write
$r(X)=|X|_F$. All functions in the main statement are finite-valued on the
whole matrix space. A function is **uniformly strongly rank-one convex with
margin $\mu>0$** if

$$
 X\longmapsto F(X)-\frac\mu2|X|_F^2
$$

is rank-one convex. For a smooth function this is equivalent to
$D^2F(X)[V,V]\ge\mu|V|_F^2$ for every rank-one $V$.
The constants in this note may depend on the function and the requested
approximation accuracy; no uniform margin or period is asserted over the
whole cone.

**Theorem D1 (density with discrete degree-two scaling).** For every finite
rank-one convex $F:\mathbb M\to\mathbb R$, there are affine functions
$\ell_j$, positive integers $N_j$, and functions $P_j$ such that

$$
 \ell_j+P_j\longrightarrow F
 \quad\text{locally uniformly on }\mathbb M,
 \qquad
 P_j(2^{N_j}X)=2^{2N_j}P_j(X).                    \tag{1}
$$

Each $P_j$ is globally $C^{1,1}$, smooth away from zero, and uniformly
strongly rank-one convex. It satisfies $P_j(0)=DP_j(0)=0$ and bounds

$$
 |P_j(X)|\le C_j|X|_F^2,\qquad
 |DP_j(X)|\le C_j|X|_F.                          \tag{2}
$$

If $F$ is invariant under an orthogonal linear group acting on matrix
space, the approximants and affine terms can be chosen invariant under the
same group. In particular all left/right rotational isotropy present in the
input is preserved. The statement does not assume isotropy.

For a bounded domain $\Omega$, an affine base $A$, and a Lipschitz
test $u$ with zero boundary trace or periodic boundary conditions, use the
normalized Jensen gap

$$
 J_F(A,u)=\fint_\Omega F(A+Du)\,dx-F(A),
 \qquad \fint_\Omega Du\,dx=0.                  \tag{3}
$$

**Theorem D2 (strict-witness reduction).** If $J_F(A,u)<0$ for any finite
rank-one convex $F$ and bounded-gradient test, then a function $P$
having every property of $P_j$ in Theorem D1 also has a strictly negative
gap for the same base and test. Any orthogonal symmetry of $F$, including
planar isotropy, can be retained.

Consequently the following two universal implications are equivalent:

1. Every finite isotropic rank-one convex function on
   $\mathbb R^{2\times2}$ is quasiconvex.
2. Every globally $C^{1,1}$, smooth-off-zero, uniformly strongly rank-one
   convex isotropic function satisfying (1) for some positive integer
   $N$, together with (2), is quasiconvex.

This is an exhaustive reduction: a strict counterexample anywhere in the
original class would occur in the displayed discrete-scaling class. It is
not an assertion that this class has been proved quasiconvex.

### D2. Smoothing and a strict rank-one margin

Finite rank-one convex functions are locally Lipschitz. Indeed, their
restrictions to coordinate lines are convex, since a coordinate matrix has
rank one. The elementary local bounds for separately convex functions on
nested coordinate boxes bound their one-dimensional slopes; telescoping
coordinate increments gives a Lipschitz bound on each smaller box. In
particular convolution with a smooth compactly supported mollifier is
well-defined and converges locally uniformly.

Let $\rho_\varepsilon$ be a nonnegative smooth radial mollifier on the
Euclidean matrix space, of integral one. Then

$$
 F_\varepsilon(X)=\int F(X-Y)\rho_\varepsilon(Y)\,dY
$$

is smooth and rank-one convex: integrate the rank-one convexity inequality
for the translates $F(\cdot-Y)$. Radiality of the mollifier preserves
every orthogonal symmetry of $F$.

Adding $\eta r^2$, with $\eta>0$, gives a smooth function $S$
with rank-one curvature at least $2\eta|V|^2$. On any prescribed compact
set this addition and smoothing can both be made arbitrarily small.
For a strict negative test, smoothing changes its gap by at most twice the
uniform error on its matrix range. The quadratic addition changes the gap
by exactly

$$
 \eta\fint_\Omega|Du|_F^2\,dx.
$$

Thus a sufficiently small choice retains strict negativity. This uses an
actual bounded compatible gradient, without replacing its law by moments.

Subtract the affine first-order Taylor polynomial

$$
 \ell(X)=S(0)+DS(0):X,
 \qquad f=S-\ell.
$$

Then $f(0)=Df(0)=0$, and neither rank-one curvature nor Jensen gaps
change. If $S$ is invariant under an orthogonal group, differentiating
its invariance at zero shows that $\ell$ is invariant too. Set

$$
 Q(X)=\frac12D^2f(0)[X,X].                       \tag{4}
$$

The quadratic form $Q$ inherits the strict rank-one curvature margin and
all the symmetries. In general dimensions it need not be convex; the proof
needs only its rank-one curvature. No polyconvexity theorem for quadratic
forms is used here.

### D3. Flattening exactly to the quadratic jet near zero

Write $f=Q+R$. Taylor's theorem gives, on a sufficiently small ball,

$$
 |R(X)|\le B r^3,\quad |DR(X)|\le B r^2,
 \quad \|D^2R(X)\|\le B r.                     \tag{5}
$$

Choose a smooth radial cutoff $\zeta_\delta$ which is zero for
$r\le\delta$, one for $r\ge2\delta$, and takes values in
$[0,1]$. Its first and second derivatives are bounded by constants
times $\delta^{-1}$ and $\delta^{-2}$. Define

$$
 f_\delta=Q+\zeta_\delta R.
$$

The difference $f_\delta-f=(\zeta_\delta-1)R$ is supported in
$r\le2\delta$. The product rule and (5) show

$$
 \sup_X\|D^2(f_\delta-f)(X)\|\le C B\delta,
 \qquad \sup_X|f_\delta-f|\le C B\delta^3.     \tag{6}
$$

The cutoff is constant on a neighbourhood of zero, so these are statements
about smooth functions there as well. Taking $\delta$ sufficiently
small absorbs the Hessian perturbation in the existing strict rank-one
margin and makes the uniform error as small as required. Henceforth rename
this function $f$ and choose $\mu>0$ so that both $f$ and $Q$
have rank-one curvature at least $\mu|V|^2$. We now have

$$
 f=Q\quad\text{on }r\le r_0                   \tag{7}
$$

for some $r_0>0$, with any chosen strict negative test still negative.

### D4. A smooth quadratic exterior and a bounded full Hessian

The following elementary gluing step avoids assuming a global Hessian bound
for the original function. Fix $R>r_0$ containing the compact set or
test range to be retained. Choose

$$
 M\ge\sup_{r\le2R}|f(X)|,
 \qquad h(X)=q r^2-C,\qquad C=qR^2+M+2.
$$

Take $q$ sufficiently large that $2q\ge\mu$ and
$\tfrac54qR^2\ge2M+4$. Then

$$
 h\le f-2\quad(r\le R),\qquad
 h\ge f+2\quad(3R/2\le r\le2R).               \tag{8}
$$

Let $\Theta$ be a smooth convex regularization of $|t|$, equal to
$|t|$ for $|t|\ge1$, with $|\Theta'|\le1$, and put

$$
 \mathcal M(a,b)=\tfrac12(a+b+\Theta(a-b)).
$$

Such a $\Theta$ is obtained by convolving $|t|$ with a smooth even
probability density supported in $(-1,1)$. The map $\mathcal M$ is
convex, nondecreasing in each argument, equals the maximum when the two
arguments differ by at least one, and satisfies
$\mathcal M(a+t,b+t)=\mathcal M(a,b)+t$.

Define $\widehat f=\mathcal M(f,h)$ for $r<2R$, and
$\widehat f=h$ outside. By (8) these definitions coincide on a
neighbourhood of the gluing boundary, and $\widehat f=f$ on $r\le R$.
It is a smooth function with bounded full Hessian: only a compact region
differs from the quadratic $h$.

It retains the margin $\mu$. On a rank-one line, subtracting
$\mu r^2/2$ from both inputs and using translation equivariance of
$\mathcal M$ reduces this assertion to the convex, coordinatewise
nondecreasing composition of two convex functions. Outside the gluing
region the same margin holds for $h$. Equivalently one can inspect the
pointwise rank-one Hessian of the smooth glued function.

Every operation in this step preserves the orthogonal symmetries. In
particular $\widehat f$ remains equal to the original quadratic $Q$
near zero; its exterior quadratic need not have the same coefficient.

### D5. Returning to the same quadratic through a slow logarithmic cutoff

Set $W=\widehat f-Q$. Its Hessian is globally bounded, and
$W(0)=DW(0)=0$. Choose $K<\infty$ with

$$
 \|D^2W\|\le K,
 \qquad |DW(X)|\le Kr,
 \qquad |W(X)|\le\tfrac K2r^2.                 \tag{9}
$$

The last two bounds follow by integrating the Hessian along segments from
zero. Let $\chi:\mathbb R\to[0,1]$ be smooth, equal to one on
$( -\infty,0]$ and zero on $[1,\infty)$, and put

$$
 C_1=\|\chi'\|_\infty,\qquad C_2=\|\chi''\|_\infty.
$$

For $R_*\ge R$ and a length $L>0$, define

$$
 \omega(X)=\chi\!\left(\frac{\log(r/R_*)}{L}\right)
 \quad(X\ne0),\qquad
 V(X)=Q(X)+\omega(X)W(X),                       \tag{10}
$$

with $\omega=1$ near zero. Thus $V=\widehat f$ on
$r\le R_*$, and $V=Q$ on $r\ge R_*e^L$.

For $X\ne0$, the Euclidean identities for $\log r$ give

$$
 |D\omega|\le\frac{C_1}{Lr},\qquad
 \|D^2\omega\|\le
   \frac1{r^2}\left(\frac{C_1}{L}+\frac{C_2}{L^2}\right).
                                                               \tag{11}
$$

The Hessian of (10) is the convex combination of $D^2Q$ and
$D^2\widehat f$, plus the error

$$
 2D\omega[Z]DW[Z]+W D^2\omega[Z,Z].
$$

By (9)--(11), the absolute value of this error is at most

$$
 \boxed{
 K\left(\frac{5C_1}{2L}+\frac{C_2}{2L^2}\right)|Z|_F^2.
 }                                                            \tag{12}
$$

Choose $L$ large enough that the coefficient in (12) is at most
$\mu/2$. For rank-one $Z$, the main convex combination has curvature
at least $\mu|Z|^2$. Therefore $V$ has margin $\mu/2$ globally.
It is smooth, preserves all the symmetries, and is unchanged on the chosen
test range. Crucially,

$$
 V=Q+\Psi,
 \qquad\Psi\in C_c^\infty(\mathbb M),
 \qquad\operatorname{supp}\Psi\subseteq\{r_0\le r\le r_1\},
 \qquad r_1=R_*e^L.                              \tag{13}
$$

This is a compact **annular** perturbation of the same quadratic on both
sides. A nonconvex $Q$ causes no difficulty: its strict rank-one margin
is exactly the margin needed in the convex-combination calculation.

### D6. Disjoint scale periodization

Choose an integer $N\ge1$ so large that, with $T=2^N$,

$$
 T>r_1/r_0.
$$

Define

$$
 \boxed{
 P(X)=Q(X)+\sum_{k\in\mathbb Z}T^{2k}\Psi(T^{-k}X),
 \qquad P(0)=0.
 }                                                            \tag{14}
$$

The closed annuli $[T^kr_0,T^kr_1]$ are disjoint. At most one summand
is nonzero at any nonzero matrix, and on every compact subset away from
zero only finitely many annuli occur. The function is smooth there. On a
copy annulus it equals

$$
 Q(X)+T^{2k}\Psi(T^{-k}X)=T^{2k}V(T^{-k}X),       \tag{15}
$$

and between annuli it equals $Q$. Smoothness across their boundaries
follows from smooth compact support of $\Psi$. In (15) the two chain
rule factors cancel the prefactor, so

$$
 D^2P(X)=D^2V(T^{-k}X)
$$

on each copy. Thus both the full Hessian bound and the strict rank-one
margin are independent of the annulus index. The same properties hold for
the quadratic pieces.

On the compact original annulus, $|V(X)|/r^2$ and $|DV(X)|/r$ are
bounded. Scaling (15) gives the bounds (2), so $P$ is differentiable at
zero with derivative zero, and its gradient is continuous there. The
bounded Hessian away from zero makes this gradient globally Lipschitz:
integrate on a line segment avoiding zero, or split a segment that passes
through zero and pass to the endpoint limit. Hence $P\in C^{1,1}$.

To check strong rank-one convexity across the origin, subtract
$\mu r^2/4$. The resulting function is convex on every rank-one
interval avoiding zero. Its one-sided derivatives at zero are both zero
by (2), so the two convex restrictions glue. This proves the global margin
$\mu/2$, not only an almost-everywhere Hessian assertion.

Finally, shifting the summation index in (14) and using the degree-two
homogeneity of $Q$ gives

$$
 P(TX)=T^2P(X).                                   \tag{16}
$$

All symmetries are retained. Generally the Hessian oscillates through
infinitely many copies as $X\to0$, so $C^2$ regularity at zero is
neither needed nor asserted.

#### D6.1 The exact approximation error on the original test ball

The central copy $k=0$ gives exactly $V=Q+\Psi$. Every positive
copy starts beyond $Tr_0>r_1$, and hence beyond the test range in
$r\le R_*$. Negative copies can occur near zero and must be counted.
Writing $M_\Psi=\|\Psi\|_\infty$, on that test ball

$$
 |P(X)-V(X)|
 \le M_\Psi\sum_{k=-\infty}^{-1}T^{2k}
 =\frac{M_\Psi}{T^2-1}.                         \tag{17}
$$

Consequently

$$
 |J_P(A,u)-J_V(A,u)|
 \le\frac{2M_\Psi}{T^2-1}.                      \tag{18}
$$

If the gap of $V$ is $-\delta<0$, choose $N$ still larger so
the right-hand side of (18) is less than $\delta/2$. The same actual
gradient test then has negative gap for $P$. No exact equality of gaps
has been assumed: the small inner copies are controlled by (17).

### D7. Completion of the density and equivalence statements

For Theorem D1, prescribe approximation on the ball of radius $j$, with
error tending to zero, for example $1/j$. In Section D2 choose smoothing
and strictification errors smaller than one third of this tolerance. Keep
the affine Taylor term $\ell_j$. Choose the flattening radius in
Section D3 to make its uniform error smaller than another third. Sections
D4--D5 leave the prescribed ball unchanged. Choose $N_j$ in Section D6
so that (17) is smaller than the remaining third. Then

$$
 \sup_{|X|\le j}|\ell_j(X)+P_j(X)-F(X)|\le1/j.
$$

Every structural assertion of Theorem D1 was proved above. The periods,
Hessian bounds and strict margins may vary with $j$.

For Theorem D2, use sufficiently small errors throughout to retain the
strict original gap, and then apply (18). The affine term has zero Jensen
gap by (3), so it may be omitted from the final counterexample. Equivalently,
local uniform convergence and affine cancellation in Theorem D1 imply that
an eventual approximant retains any fixed strict negative gap.

The equivalence in Section D1 now follows by contraposition. Its converse
direction is immediate because the discrete-scaling class is contained in
the class of finite isotropic rank-one convex functions. This is a true
reduction of the entire original class, with no preassigned growth,
homogeneity, or gradient support-size hypothesis.

#### D7.1 Optional planar isotropic normalization

For planar isotropy under independent proper rotations, invariance under
$-I$ gives $Df(0)=0$. The invariant quadratic forms are exactly

$$
 Q(X)=a|X|_F^2+b\det X.
$$

For example, the conformal and anticonformal coordinates transform by
independent planar rotations, so their two squared norms span the invariant
quadratic forms. Strict rank-one curvature gives $a>0$, since the
determinant is affine on rank-one lines. Subtracting $b\det$ from the
periodized function changes neither the rank-one margin nor its Jensen
gaps, and preserves (16). Thus the isotropic planar counterexample can be
chosen with the background $a|X|_F^2$ if desired. The general-dimensional
proof did not need this classification or a determinant subtraction.

### D8. The remaining phase gate and the limitation of averaging

Let $P$ be a planar isotropic function obtained above, with period
$T=e^\tau$. Its average over a full logarithmic scale period is

$$
 H(X)=\frac1\tau\int_0^\tau e^{-2s}P(e^sX)\,ds.  \tag{19}
$$

Every integrand in this average is isotropic and rank-one convex. By
(16), the normalized integrand is periodic in $s$; shifting the
integration interval proves that $H(tX)=t^2H(X)$ for every $t>0$.
Thus $H$ is continuously homogeneous of degree two. The repository's
verified
[degree-two isotropic theorem](../HomogeneousIsotropic/README.md)
proves that $H$ is polyconvex and hence quasiconvex.

For a fixed bounded compatible test define

$$
 j(s)=e^{-2s}J_P(e^sA,e^su).                       \tag{20}
$$

Both the affine base and the test map are scaled in this formula. Equation
(16) gives $j(s+\tau)=j(s)$. Fubini on the bounded range swept out by
one finite period gives the exact identity

$$
 \frac1\tau\int_0^\tau j(s)\,ds=J_H(A,u)\ge0.   \tag{21}
$$

This proves a nonnegative **mean** phase gap. It does not prove that
$j(s)\ge0$ at every phase. A continuous periodic function can have
negative values and a nonnegative mean; rank-one convexity would have to
supply an additional spatial or analytical argument excluding this
possibility for (20). No such argument is supplied here.

The new target is exhaustive: prove quasiconvexity for all these
discretely degree-two homogeneous isotropic functions, with every allowed
period, or produce a certified negative member. Unlike a log-polynomial
extension, an affirmative result for this class would settle the whole
finite-valued isotropic implication.

### D9. What the reduction does not claim

The period in this symmetry-preserving construction depends on the compact
annulus and the tolerated gap error. It can always be chosen $2^N$, but
this proof supplies no universal bound on $N$ and no reduction to a
single fixed period while preserving full isotropy. Compressing logarithmic
radii is not a justified substitute: such a nonlinear matrix change does
not preserve rank-one lines. Averaging several phases can lose the strict
negative gap, as (21) makes explicit.

In isotropic planar coordinates the energy is represented by a profile on
the compact cylinder

$$
 \left(\frac{\det X}{|X|_F^2},\
       \log|X|_F\bmod\log T\right),
 \qquad -\tfrac12\le\frac{\det X}{|X|_F^2}\le\tfrac12.
$$

Smoothness of the matrix function imposes the usual compatibility at the
conformal endpoints; no arbitrary endpoint profile is silently declared
admissible. The profile remains a function, not a bounded list of
parameters, and a gradient test can visit arbitrarily many scaled annuli.
The cylinder representation therefore does not constitute a finite exact
decision procedure or a stopping bound for computation.

The new localization and periodization arguments are hand mathematics.
They have not been connected to a new Lean endpoint. Unrestricted planar
Morrey, including its unrestricted nonhomogeneous isotropic case, remains
open in this research workspace.

## Exact checks and formal status

The companion [exact checker](../../research/audit/discrete_scaling_exact.py)
checks the cutoff Hessian identities, the general quadratic translation
identity, period reindexing, support-separation budgets, and relative value
and derivative estimates. It also checks exact Jensen cancellation on an
actual compatible finite-state sawtooth control. Its finite algebra checks
support the displayed identities; the arbitrary-function localization,
regularity, and universal-equivalence arguments are the hand proofs above.
They have not been assembled into a new Lean endpoint.
