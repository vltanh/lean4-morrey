# Full-matrix half-space projection and anisotropic quasiconvex gluing

24 November 2026. The target is removing isotropy while retaining
positive homogeneity. This note establishes a new spatial projection
mechanism, not restricted to scalar row constraints. It yields
quasiconvex gluing across any full-rank linear gradient functional
and explicit nonnegative anisotropic nonpolyconvex quasiconvex
integrands for EVERY p>1. A separate quantitative estimate extends
the degree-two origin theorem to arbitrary sufficiently strongly
elliptic anisotropic profiles near degree two.

These are hand proofs with executed symbolic/rational algebra
checks, not new Lean theorems. The homogeneous isotropic theorem
and the signed Burkholder inequalities used below are already
formally verified on main at 17fd1c3. No independent referee review
or publication-priority claim. The general homogeneous anisotropic
all-base implication remains OPEN.

## 1. Full-matrix half-space projection via an elliptic obstacle

Let X=A+Dphi on the normalized unit flat two-torus, where phi is
a periodic Lipschitz R²-valued map. Fix an invertible real 2x2
matrix B. Write ell(X)=B:X for the Frobenius inner product.
Suppose a0=ell(A)>0.

**Theorem A.** There exists a compatible gradient Z=A+D zeta,
with zeta periodic and in W^(1,q) for every finite q>1, such that

    ell(Z)>=0, and Z=X or ell(Z)=0 almost everywhere.

Moreover, if e is any spatial direction,

$$
\int Ze\cdot (X-Z)e=0,\qquad
\int |Xe|^2=\int |Ze|^2+\int |(X-Z)e|^2.
\tag{1}
$$

Let J=[[0,-1],[1,0]] and define omega_B(X)=J:(B^(-1)X).
Then

    omega_B(Z)=omega_B(X) a.e.

For every finite convex function psi on the real line,

$$
\int\psi(\ell(Z))\le\int\psi(\ell(X)).
\tag{2}
$$

In particular the theorem treats divergence constraints (B=I),
which involve both rows and cannot be reduced to a single scalar
row constraint. The projected gradient need not be bounded in
L-infinity; the W^(1,q) conclusion suffices for polynomial-growth
energies. No Lipschitz regularity of this vector projection is
claimed.

### 1.1 Construct the pressure

Put f=ell(X)=a0+div(B^T phi), so f is bounded and has positive
mean a0. Minimize over periodic rho in H¹, rho>=0, the obstacle
functional

$$
\mathcal I(\rho)=\tfrac12\int |B\nabla\rho|^2+\int f\rho .
$$

This functional attains its minimum. Indeed, because B is
invertible, the first term bounds a positive multiple of
the squared gradient norm. Decomposing f into its mean and
zero-mean part and using Poincare gives a lower bound of the form

    c ||D rho||_2² - C ||D rho||_2 + a0 E rho,

with c>0. Nonnegativity of rho gives E rho>=0. A bounded
sublevel thus bounds its mean and its H¹ norm. The cone
rho>=0 is weakly closed and the functional is weakly lower
semicontinuous, so the direct method applies.

Set

    zeta=phi-B grad rho,
    f_v=a0+div(B^T zeta)
       =f-div(B^T B grad rho).

Initially zeta is only in L² and f_v is a distribution.
First variation in any smooth nonnegative direction gives
f_v>=0 as a distribution. Variation along scaling rho by
1+t, for small t of either sign, gives

$$
\langle f_v,\rho\rangle
=\int f\rho+\int |B\nabla\rho|^2=0.
\tag{3}
$$

Here the pairing is the H^(-1),H¹ pairing on the torus.

### 1.2 Identify the projection and gain regularity

The set
    C={eta in L²(T²,R²): a0+div(B^T eta)>=0 in distributions}
is nonempty (it contains zero), closed, and convex. If eta
belongs to C, then

$$
\int(\phi-\zeta)\cdot(\eta-\zeta)
=-\langle a_0+\operatorname{div}(B^T\eta)-f_v,\rho\rangle
\le0.
$$

The first distribution in the pairing is nonnegative and
belongs to H^(-1); its pairing with nonnegative rho is
nonnegative by approximation of rho with nonnegative smooth
periodic convolutions in H¹. Equation (3) removes the second
term. Hence zeta is exactly the Hilbert-space L² projection
of phi onto C.

This projection is nonexpansive and commutes with translations,
since C does. For any displacement h,
    ||zeta(.+h)-zeta||_2 <= ||phi(.+h)-phi||_2.
The difference quotient characterization of H¹ now gives
zeta in H¹. Thus B grad rho=phi-zeta belongs to H¹, and
invertibility of B gives rho in H². In particular f_v=ell(Z)
is an L² function, nonnegative almost everywhere.

By (3), f_v=0 almost everywhere on {rho>0}.
On {rho=0}, the gradient of rho vanishes almost everywhere.
Applying the same standard Sobolev zero-set derivative property
to each component of grad rho (which is H¹) shows
D²rho=0 almost everywhere on {rho=0}.
Therefore

    Z=X-B D²rho,
    Z=X a.e. on {rho=0},
    ell(Z)=0 a.e. on {rho>0}.

This proves the exact selection statement. It also gives
f_v=f or f_v=0 pointwise, and consequently
div(B^T B grad rho)=f-f_v is bounded.

By the usual constant-coefficient elliptic L^q estimate on the
torus, rho is in W^(2,q) for every finite 1<q<infinity.
Equivalently the Fourier symbols for its second derivatives
are (up to the sign convention) k_i k_j/(k^T B^T B k)
on nonzero modes, the standard bounded L^q elliptic multipliers.
This gives the asserted W^(1,q) regularity of zeta. Its
mean gradient is unchanged by the periodic correction.
No nonlinear obstacle regularity beyond H¹ projection
and this linear elliptic estimate is required.

### 1.3 Exact energy decomposition and invariants

Integrating by parts twice, or using smooth periodic
approximation in H¹ and H², gives for every constant e

$$
\begin{aligned}
\int Ze\cdot (X-Z)e
&=\int D_e\zeta\cdot B\nabla D_e\rho\\
&=\int \operatorname{div}(B^T\zeta)D_{ee}\rho\\
&=\int f_v D_{ee}\rho=0.
\end{aligned}
$$

The constant affine terms integrate to zero. The final
product vanishes because f_v=0 on {rho>0} and D²rho=0
on {rho=0}. Expanding the square proves (1).

The matrix B^(-1)(X-Z)=D²rho is symmetric, so its contraction
with the skew matrix J is zero. This proves the pointwise
omega_B invariant.

To prove (2), set S={rho>0}. On its complement f_v=f, on S
f_v=0, and the two functions have equal means a0. Therefore
int_S f=0. If S has positive measure, ordinary Jensen gives
int_S psi(f)>=|S|psi(0). Outside S the two integrands agree.
The zero-measure case is immediate. QED.

The same construction works for ell(X)>=t with arbitrary
constant threshold t<ell(A), by replacing f with ell(X)-t.
Equation (1) is unchanged, and the conditional mean of
ell(X) on S is now t. We need only threshold zero below.

## 2. A quasiconvex gluing theorem

Fix B invertible as above. Let Q0 be any finite energy of the form

$$
Q_0(X)=\operatorname{tr}(X N X^T)+\gamma\det X
 +L:X+c+\psi(\ell(X))+\chi(\omega_B(X)),
\tag{4}
$$

where N is symmetric positive semidefinite, gamma and c
are arbitrary constants, L is a constant matrix, and psi,chi
are finite convex scalar functions of at most polynomial growth.
This is a convex function plus a determinant term, hence QC.
The class can also be transformed by arbitrary fixed invertible
changes of target coordinates. In particular it can accommodate
a positive definite target metric by transforming both the
constraint matrix and the energy.

Let Q1 be any continuous QC integrand with polynomial growth.
More generally it suffices for Q1 to be defined and QC for
tests staying within the closed half-space ell>=0, with
polynomial growth there. Assume only the boundary domination

    Q1(X)<=Q0(X) whenever ell(X)=0.

Define

$$
G(X)=
\begin{cases}
\max\{Q_0(X),Q_1(X)\},&\ell(X)>0,\\
Q_0(X),&\ell(X)\le0 .
\end{cases}
\tag{5}
$$

**Theorem B.** G is continuous and globally quasiconvex.

Proof. Continuity across the interface follows from the
boundary domination. At a base A with G(A)=Q0(A),
the pointwise inequality G>=Q0 and QC of Q0 prove Jensen.
Otherwise ell(A)>0 and G(A)=Q1(A). Use Theorem A for X and
its projection Z. Where ell(Z)>0, Z=X, so
G(X)-Q0(X)>=Q1(Z)-Q0(Z). Where ell(Z)=0, the same inequality
follows from G>=Q0 and boundary domination. Thus everywhere

    G(X)>=Q0(X)+Q1(Z)-Q0(Z).

Integrate. By diagonalizing N and using (1) on each
eigenvector, the quadratic term in Q0 contracts.
The determinant and affine terms integrate to their base
values for both compatible gradients. In dimension two the
determinant identity is valid in W^(1,2) by smooth approximation.
The psi term contracts by (2), and the chi term is unchanged
pointwise. Hence E Q0(X)>=E Q0(Z). Quasiconvexity of Q1 gives
E Q1(Z)>=Q1(A). To justify this for the projected field,
smooth the periodic part zeta by convolution, which preserves
the half-space constraint when needed. Convergence in
W^(1,q) for q at least the polynomial growth degree and
q>1 gives convergence of the energies in L¹ by continuity
and uniform integrability. This proves
    E G(X)>=E Q1(Z)>=Q1(A)=G(A).
The zero-boundary test convention follows by periodizing
the perturbation. QED.

This is a full-matrix half-space version of the earlier
row-projection calibration, with an exact skew invariant
and nonlinear convex contraction of the active constraint.
It allows arbitrary known QC branches Q1, not just
quadratic or homogeneous ones. Nonnegative sums, maxima,
and locally uniform limits of the resulting finite QC
energies remain QC. We do NOT assert that these closures
generate the entire homogeneous anisotropic RC cone.

## 3. Anisotropic nonpolyconvex QC examples for every degree p>1

Write the conformal and anticonformal coordinates as z,w,
so s=|z|+|w|, det X=|z|²-|w|², and

    Re z=(X11+X22)/2,
    Im z=(X21-X12)/2.

Take B=I. The constraint ell is the trace, while omega_B
is twice Im z. Therefore functions of Im z are unchanged
under the full-matrix projection.

### 3.1 Every p>=2: a determinant branch

Set Q0=|Im z|^p and Q1=(det X)_+^(p/2). Both are QC:
the first is convex and the second is convex as a
function of the determinant. On the trace-zero plane
z is purely imaginary, so det X<=|Im z|² and Q1<=Q0.
Theorem B gives the nonnegative positively p-homogeneous
QC energy

$$
G_p(X)=
\begin{cases}
\max\{|{\rm Im}\,z|^p,(\det X)_+^{p/2}\},&
       {\rm tr}\,X>0,\\
|{\rm Im}\,z|^p,&{\rm tr}\,X\le0.
\end{cases}
$$

For p=2 this is precisely
    (X21-X12)²/4 + det(sym X) 1_{sym X positive definite}.
Indeed det X-(X21-X12)²/4=det(sym X), and a symmetric
2x2 matrix with positive trace and positive determinant
is positive definite.

For EVERY p>=2 the corrected three-atom minors law
already used in the Guerra--Kristensen example shows
nonpolyconvexity at I:

    weights: 1/4, 3/8, 3/8
    matrices: -2I, diag(4,0), diag(0,4).

The mean is I and the mean determinant is 1. All atoms
have Im z=0, and either nonpositive trace or determinant
zero, hence all have G_p=0. But G_p(I)=1.
This is a minors-compatible law, not a gradient law;
it contradicts polyconvexity, not QC.

### 3.2 Every 1<p<2: a signed Burkholder branch

The following gluing construction works for all p>1.
Use the already formally verified signed Burkholder energy

$$
B_p(X)=s^{p-2}(|1-2/p|s^2+\det X),\qquad B_p(0)=0 .
$$

For a fixed x=|z|>=0 and y=|w|>=0, its expression for
p>=2 is (2/p)((p-1)x-y)(x+y)^(p-1), while for 1<p<=2
it is (2/p)(x-(p-1)y)(x+y)^(p-1).
In the first case the y derivative is
    2 (x+y)^(p-2)((p-2)x-y),
so the maximum over y>=0 is attained at (p-2)x.
In the second case the derivative is
    -2(p-1)y(x+y)^(p-2),
and the maximum is attained at zero.
Thus globally B_p(X)<=M_p |z|^p with

    M_p=2/p                          for 1<p<=2,
    M_p=2(p-1)^(p-1)/p               for p>=2.

Use Q0=M_p |Im z|^p and Q1=B_p in (5). On trace zero
the boundary domination follows exactly from this
bound. The resulting integrand H_p is nonnegative,
p-homogeneous, QC, and anisotropic (H_p(I)>0=H_p(-I)).

It is not convex for any p>1. In fact set
    k>max(p-1,1/(p-1)),
    A1=diag(-1/2+k,-1/2-k),
    A2=diag(1-k,1+k).
Both are symmetric. A1 has negative trace, so H_p(A1)=0.
For A2, z=1 and |w|=k, so B_p(A2)<0 and H_p(A2)=0.
Their midpoint is I/4, with strictly positive energy.

For 1<p<2 this even proves failure of polyconvexity
by an explicit four-atom repair of the minors. The two
matrices above have mean A=I/4 and mean determinant
Dbar=5/8-k²<0 (choose k>1). Given 0<eps<1, place mass
(1-eps)/2 on each Ai/(1-eps), and mass eps/2 on each
of tI and -tI, where

    t²=(1/16-Dbar/(1-eps))/eps>0.

The mean is A and the mean determinant is det A=1/16.
The two rescaled Ai retain zero energy by homogeneity,
as does -tI. The remaining expectation is
    (eps/2)(|1-2/p|+1)t^p,
which tends to zero as eps tends to zero because
p<2 and t²=O(1/eps). For sufficiently small eps it
is strictly less than H_p(A)>0. This is an exact
minors Jensen counterexample, not a violation of QC.

Together Sections 3.1 and 3.2 produce nonpolyconvex
nonnegative anisotropic QC integrands at all exponents
p>1. For 1<p<2 this construction directly uses the
verified signed Burkholder result in a non-isotropic
way. No claim of priority for individual examples
or the gluing mechanism is made.

## 4. Auxiliary all-profile quantitative extension near degree two

The previous
[anisotropic origin theorem](IWANIEC_MORREY_ANISOTROPIC_ORIGIN_RECTIFIED.md)
proves F>=c det for every finite positively 2-homogeneous RC F.
The following exploits it and the verified signed Burkholder
inequalities for arbitrary angular dependence near degree two.

Let p>1 and let F be positively p-homogeneous and C² away
from zero. Assume the rank-one Hessian bound on the Frobenius
unit sphere is D²F(X)[H,H]>=m|H|² for rank-one H, with m>=0.
Let M be the supremum of the full Hessian operator norm on
that sphere. Set

$$
m'=m-M|p-2|\frac{3p+1}{p(p-1)},\qquad
K(p)=\frac{|p-2|}{p}+\frac{2^{|p-2|/2}-1}{2}.
$$

If m'>=0, every compatible bounded zero-base gradient X obeys

$$
\int F(X)\ge
\left(\frac{m'}2-\frac{2M K(p)}{p(p-1)}\right)
          \int |X|_F^p .
\tag{6}
$$

In particular for ANY fixed positive ellipticity ratio
m/M, the coefficient is positive on some open exponent
interval about two. No closeness to isotropy, angular
polynomial degree, or sign hypothesis is required.
The interval depends on the ellipticity ratio, so this
does not establish arbitrary signed origin QC for p!=2.

Proof. Set r=|X|_F and G=r^(2-p)F. This is continuous,
2-homogeneous, and C² away from zero. On r=1, put
theta=2-p. The exact Hessian identity is

$$
D^2G[H,H]=D^2F[H,H]+2\theta(X:H)DF:H
  +\theta F|H|^2+\theta(\theta-2)F(X:H)^2 .
$$

Euler's identities give ||DF||<=M/(p-1) and
|F|<=M/(p(p-1)) there. Therefore the absolute
value of the Hessian correction is bounded by
M|p-2|(3p+1)/(p(p-1)) times |H|².
By degree-zero homogeneity of the Hessian, G has
rank-one Hessian lower bound m' everywhere off zero.
G-(m'/2)r² is globally RC: its rank-one line
restrictions have nonnegative second derivative off
zero, and on lines through zero the first derivative
extends continuously through zero by degree two.

Apply the degree-two origin theorem to that function.
For some c,
    G(X)>=(m'/2)r²+c det X.
Test this at I/sqrt(2) and diag(1,-1)/sqrt(2);
their determinants are respectively +/-1/2, and the
bound on |F| there yields |c|<=2M/(p(p-1)).
Multiplication by r^(p-2) gives the lower bound
F>=(m'/2)r^p+c d r^(p-2), with zero values understood
at X=0.

Since the signed reflected Burkholder energies are QC,
at zero they give
    |E d s^(p-2)| <= |p-2|/p E s^p,
where s=||X||op. Also s<=r<=sqrt(2)s and |d|<=r²/2.
It follows pointwise that
    |d| |r^(p-2)-s^(p-2)|
    <= (2^(|p-2|/2)-1) r^p/2.
The estimate holds for p<2 by reversing the powers and
for p>=2 by 1-2^(-(p-2)/2)<=2^((p-2)/2)-1.
Adding the two estimates gives
    |E d r^(p-2)| <= K(p) E r^p.
This proves (6). QED.

For p=2 the result recovers the strict origin margin m/2.
Equation (6) is not the desired general anisotropic
all-base theorem and is not intended as an exponent
ladder. The primary advance of this note is the
full-matrix half-space projection and gluing theorem.

## 5. Verification and status

The checker
[full_matrix_halfspace_exact.py](../../research/audit/full_matrix_halfspace_exact.py)
was actually executed in the working container. It verified the
two Burkholder derivatives, the skew and determinant-symmetric
identities, the common Fourier symbol in the orthogonality
calculation, the lifted minors witnesses, and the exponent
demotion coefficients. The PDE projection proof is the analytic
argument in Sections 1--2, not inferred from the finite controls.

**Remaining gate:** prove arbitrary homogeneous anisotropic
RC=>QC at every base. The full-rank half-space construction
offers a new class of spatial calibrations, with both a
nonlinear scalar contraction and an exact preserved skew
quantity. We have not proved a representation of arbitrary
angular profiles by its gluing operation. The signed origin
problem for unrestricted p!=2 and the nonzero-base degree-two
problem remain open. No new Lean theorem or general closure
is claimed. The formally verified homogeneous isotropic
theorem remains closed.
