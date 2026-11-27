# Gate 1: explicit spatial cofactor cancellation and a uniform negative-stress budget

24 November 2026. The remaining homogeneous anisotropic Morrey gate is
to construct a PSD angular stress with zero cofactor trace for every
compatible gradient. We work directly on spatially induced stresses.
This note is **not another finite angular approximation or an assumed
classification of integrands**.

**New results.**
* An exact exchange of two PSD stresses, induced by the spatial heat
  flow, cancels the cofactor defect and preserves the original angular
  equation. Both exchanged stresses have the same action on ALL
  homogeneous Hessian tests; one is rank-one generated. This gives
  an explicit signed correction solving both linear requirements of
  Gate 1, for arbitrary compatible fields and every p>1.
* The corrected signed stress has a constructive decomposition into
  positive rank-one generated stresses S_+ and S_-. The negative mass
  is at most (sqrt(2)-1) times the original heat-stress mass, uniformly
  over every field, exponent and base. At p=2 the coefficient improves
  to (sqrt(3)-1)/2. The bounds use actual compatibility and integration
  by parts, not only determinant moments.
* A weighted spatial Hessian estimate then gives a global Jensen
  theorem for arbitrary angular profiles with a controlled contrast
  of their rank-one Hessian curvatures. At p=2 the admissible ratio
  of upper to lower curvature is 2+sqrt(3); in fact at this degree
  the constant-curvature-bound theorem needs no homogeneity at all.

**Status:** Gate 1 is NOT closed. The exchange cancels the cofactor
trace exactly but does not necessarily preserve positivity. The
negative-stress bound is not a contraction iteration: no theorem
absorbs or eliminates that negative measure in general. The
contrast theorem does not cover arbitrary RC integrands; uniform
strictification cannot enforce its contrast bound with vanishing
error. Hand proofs, actual symbolic checks, no new Lean verification
or claim of novelty. The signed homogeneous isotropic result remains
formally verified.

## 1. A PSD spatial starting stress

Let X=A+Dphi be a bounded periodic compatible field on the flat
two-torus with normalized area one, and let phi_s=exp(s Delta)phi.
Take phi to have zero mean. Write

    X_s=A+Dphi_s,
    B_ij=partial_ij phi_s in R²,
    g=B_11+B_22=Delta phi_s,
    H_j=partial_j X_s.

All formulas below for fixed s>0 involve smooth periodic maps.
For a C² angular function f let F(X)=|X|^p f(X/|X|), F(0)=0,
where p>1 and the norm is Frobenius. Let Q(X)=D²F(X) for X!=0.

Let \mathcal D_p denote the linear angular stress operator defined
in [ANGULAR_CURVATURE_STRESS](IWANIEC_MORREY_ANGULAR_CURVATURE_STRESS.md):
    <f, \mathcal D_p M> = integral_{S³} Q(u):dM(u).
Let C be the linear cofactor operator on real 2x2 matrices.

Define the spatial PSD tensor and weight

    M_h(s,x)=H_1 tensor H_1+H_2 tensor H_2,
    omega(s,x)=|X_s|^(p-2).

In integrals with derivatives of X_s, define the weighted tensor
to be zero on {X_s=0}: for each s the spatial derivative of
X_s vanishes a.e. on this zero set. We use the following convention
for pushing a spatial tensor T(s,x) onto the angular sphere:

    [T] = integral_0^infinity integral_T²
               omega(s,x) T(s,x) delta_(X_s/|X_s|) dx ds.

Thus [T] denotes a matrix-valued measure, not a scalar energy.
Time intervals can also be restricted, with the same notation
and indicated limits. Every tensor below is bounded in norm
by a constant times |D²phi_s|², so these measures are finite
by the energy estimate in Section 1.1.

For heat flow,

    d/ds integral F(X_s) = - integral Q(X_s):M_h(s,x).

Since X_s converges uniformly to A as s->infinity and
to X in L^p as s->0, this gives the PSD starting stress

$$
\boxed{
M=[M_h]\succeq0,\qquad \mathcal D_p M=\sigma,
}
\tag{1}
$$

where sigma is the angular p-moment difference of X and A.
Its trace mass is

    T = integral omega |D²phi_s|² dx ds.

This M is another possible starting stress in place of the
straight-line Taylor stress of the preceding note. There is no
assumption that it has zero cofactor trace.

### 1.1 Finiteness and the singular exponent range

Set J_p=integral |X|^p-|A|^p,
    c_p=p min(1,p-1), d_p=p max(1,p-1).

The Hessian of |X|^p away from zero lies between
c_p |X|^(p-2) I and d_p |X|^(p-2) I. To justify the
heat computation for 1<p<2, first use the smooth convex
radial functions P_eps(X)=(|X|²+eps²)^(p/2).
Their Hessians have lower bound c_p (|X|²+eps²)^((p-2)/2) I.
The exact smooth heat identity and monotone convergence of this
weight as eps decreases to zero give c_p T<=J_p. Zero-set
derivatives are zero a.e., as above.

For p>=2 use boundedness of X_s, the smooth heat identity
for |X|², and passage to the radial energy by dominated
convergence. Thus T is finite for all p>1.

For arbitrary smooth angular f, ordinary convolution of F
with a compact smooth mollifier gives smooth energies and
converges locally uniformly. Their Hessians are bounded by
a constant times (|X|+eps)^(p-2) when 1<p<2: away from zero
this follows by homogeneity and the support of the kernel,
and on the radius-2eps ball it follows by integrating the
locally integrable bound O(|X|^(p-2)) after scaling.
At nonzero X these bounds are dominated by a constant times
|X|^(p-2). For p>=2 use boundedness of X_s and integrability
of |D²phi_s|². Therefore all the heat identities and spatial
integration-by-parts identities below pass to the original
F by dominated convergence. The weighted tensors vanish a.e.
at X_s=0, so no separate Hessian value at zero is needed.
In particular, for the radial energy we also obtain

$$
\boxed{c_p T\le J_p\le d_p T.}\tag{2}
$$

For p=2, T=J_2/2 exactly. All these conclusions hold for
periodic Lipschitz phi by the heat-flow limits just used,
without assuming that its initial spatial Hessian is bounded.

## 2. Exact cofactor cancellation by a spatial PSD exchange

The same derivative of the energy can be calculated by the
first variation and one spatial integration by parts:

    d/ds integral F(X_s)
      = integral DF(X_s):Dg
      = - integral sum_(a,b,i,j)
                     Q_(ai,bj)(X_s) g_a (B_ij)_b.

Here a,b index target coordinates and i,j spatial coordinates.
The derivative of X in the spatial direction i has component
partial_i X_bj=(B_ij)_b. By the symmetry of Q, the spatial
signed tensor in this identity is

$$
S_{ai,bj}=\tfrac12\{g_a(B_{ij})_b+g_b(B_{ij})_a\}.
\tag{3}
$$

It is symmetric in i,j AND a,b. Consequently C:S=0 pointwise:
the only cofactor terms pair (1,1) with (2,2) and (1,2)
with (2,1), with opposite signs, and those two entries
of S are equal.

By the two exact energy identities,

$$
\boxed{\mathcal D_p[S]=\sigma,\qquad C:[S]=0.}\tag{4}
$$

This solves the two linear requirements of Gate 1 by explicit
spatial integration by parts. It does not establish [S]>=0.

The following algebra gives an important more precise form of
the correction. Use column-block notation: [a,b] denotes a 2x2
matrix with columns a,b in R². Define

    P=(B_11-B_22)/2, R=B_12,
    T_1=[g/2,0], T_2=[0,g/2],
    V_1=[P,R], V_2=[R,-P].

Then H_1=T_1+V_1 and H_2=T_2+V_2. Let

    G=T_1 tensor T_1+T_2 tensor T_2,
    V=V_1 tensor V_1+V_2 tensor V_2.

Both G,V are PSD and C:G=0, since T_1,T_2 have rank at
most one. Expanding the column blocks in (3) gives

$$
\boxed{S=M_h+G-V.}\tag{5}
$$

For example the upper-left block of S is sym(g tensor B_11);
the lower-right block is sym(g tensor B_22); the off-diagonal
block is sym(g tensor B_12). Expanding the right-hand side
gives precisely these three blocks. In particular C:V=C:M_h.

The two first-variation formulas agree for EACH s>0 and
EVERY angular f, and so (5) implies the exact PSD exchange:

$$
\boxed{
\mathcal D_p[G]=\mathcal D_p[V],\qquad
C:[G]=0,\qquad C:[V]=C:M.
}
\tag{6}
$$

The equation is even valid with any bounded measurable weight
depending only on heat time s in the integrals defining [G],[V],
because the spatial integration-by-parts identity holds at
each s (with the justifications of Section 1.1). No angular
weight may be inserted into (6) without another proof.

In the angular equation the entire positive deviatoric
Hessian stress [V] can thus be exchanged for the positive,
cofactor-free trace stress [G]. This is more than merely
subtracting the pointwise cofactor component: the exchange
lies in the kernel of the angular Hessian operator for all
tests, exactly because X_s is an actual compatible field.

But subtracting [V] from M may spoil positivity, since
M_h consists of the squares of T_j+V_j rather than
independent squares of T_j and V_j. The cross terms are
not separately PSD. For example, for a fixed theta,
    M_theta=M+theta([G]-[V])
retains the correct angular source and has cofactor trace
(1-theta) C:M. Its positivity is guaranteed if
theta[V] <= M+theta[G] in PSD measure order.
We have not proved this domination for theta=1 or any
uniform positive theta over all fields. This is the missing
part of the exchange approach. The heat energy need not
be monotone for general polyconvex energies, so there is
no basis for asserting pointwise PSD of S.

## 3. Constructive balanced signed decomposition with a uniform budget

Although positivity is missing, (3) admits a rank-one
directional decomposition with an explicit global negative
mass bound. It involves no eigenvalue decomposition on the
angular sphere or assumption on the number of field values.

Let n be uniform on the spatial unit circle. Define

    b(n)=sum_ij B_ij n_i n_j,
    v(n)=4 b(n)-g.

The circle fourth-moment identity is
    E_n n_i n_j n_k n_l
      =(delta_ij delta_kl+delta_ik delta_jl+
        delta_il delta_jk)/8.
It implies E_n n_i n_j v(n)=B_ij. Hence

$$
S=\mathbb E_n\,\operatorname{sym}
       ((g\otimes n)\otimes(v(n)\otimes n)).
\tag{7}
$$

For fixed n, the symmetric target matrix
    W(n)=(g tensor v(n)+v(n) tensor g)/2
has eigenvalues (g dot v(n) +/- |g| |v(n)|)/2.
It is the difference W_+-W_- of its PSD positive and
negative spectral parts. The map a->a tensor n is an
isometric embedding of the target into matrix space,
with rank-one image. Embedding these two parts by this
map, averaging in n, and pushing forward with the heat
weight gives positive measures S_+,S_- on S³ such that

$$
[S]=S_+-S_-,\qquad S_\pm\succeq0,\qquad C:S_\pm=0.
\tag{8}
$$

The positive and negative parts are continuous functions
of the target symmetric matrix, so this construction is
measurable and causes no eigenvector selection issue.
Both are rank-one generated, not just cofactor-free in
total mass.

Let
    U=integral omega |g|² dx ds,
    W=integral omega |B_ij-(delta_ij/2)g|² dx ds
       (sum over i,j).
The orthogonal trace/deviatoric decomposition gives
    T=U/2+W,  0<=U<=2T.
By circle moments,
    E_n g dot v(n)=|g|²,
    E_n |v(n)|²=|g|²+4 sum_ij |B_ij-(delta_ij/2)g|².
The trace of S is |g|². Thus, writing N=tr S_-(S³),
we have the exact trace difference and the Cauchy bound

$$
\begin{aligned}
\operatorname{tr}S_+(S^3)&=U+N,\\
N&=\tfrac12\int\omega\,\mathbb E_n
                    (|g|\,|v(n)|-g\cdot v(n))\,dx\,ds\\
 &\le\tfrac12\{\sqrt{U(4T-U)}-U\}.
\end{aligned}
\tag{9}
$$

If T=0, the stress is zero. Otherwise set z=U/T in [0,2].
The maximum of (sqrt(z(4-z))-z)/2 over this interval is
sqrt(2)-1, attained at z=2-sqrt(2). For example square
the desired upper bound, using
    (z+2(sqrt(2)-1))²-z(4-z)
      =2(z-(2-sqrt(2)))².

**Theorem A (universal signed repair).** For every bounded
compatible gradient, arbitrary base and p>1, there are
explicit positive cofactor-free stresses S_+,S_- with

$$
\boxed{
\mathcal D_p S_+=\sigma+\mathcal D_p S_-,\qquad
\operatorname{tr}S_-(S^3)\le(\sqrt2-1)\,T
                         \le\frac{\sqrt2-1}{c_p}J_p .
}
\tag{10}
$$

At p=2 there is an improved budget

$$
\boxed{\operatorname{tr}S_-(S^3)
        \le\frac{\sqrt3-1}{2}\,T
        =\frac{\sqrt3-1}{4}\,J_2 .}
\tag{11}
$$

Indeed the unweighted periodic Hessian identity
    integral |D²phi_s|²=integral |Delta phi_s|²
follows by two integrations by parts, componentwise.
Therefore U=T when p=2, and (9) gives (11).

This is a uniform actual-spatial construction of a balanced
signed solution, with a quantified price for making it
positive: add the positive curvature source D_p S_-.
That source is generally a distribution on S³, not necessarily
the angular moment difference of another compatible law at
the same base. Hence the strict numerical coefficient in
(10) is NOT a proof of an iterative contraction of the
original problem. In particular one cannot repeat the
same theorem on this residual as if it were a gradient
distribution, nor subtract S_- from S_+ without proving
measure domination or a replacement gauge.

## 4. A weighted trace/deviatoric estimate for every exponent

We can give the positivity budget in terms of U, the
trace of the balanced signed stress, as well as T.
This uses compatibility again, beyond the circle algebra.

**Lemma.** With the same notation, for every p>1,

$$
\boxed{
U\ge k_p T,\qquad
k_p=
\begin{cases}
(p-1)^2,&1<p\le2,\\
4/(p+2),&p\ge2.
\end{cases}}
\tag{12}
$$

The two constants agree at p=2. No assumption on det X_s,
orientation, symmetry or angular range is imposed.

**Proof.** First fix positive eps and use the smooth spatial
weight omega_eps=(|X_s|²+eps²)^((p-2)/2). For each s,
write T_eps(s)=integral omega_eps |B|² and
U_eps(s)=integral omega_eps |g|². Integrate by parts once
in each of the expressions. Periodicity of the full affine
gradient X_s makes the computation legitimate even though
the affine map itself need not be periodic. The third
derivative terms cancel, leaving

    U_eps(s)-T_eps(s)
      = integral sum_j partial_j omega_eps
                 [sum_(a,i) X_ai (B_ij)_a -sum_a X_aj g_a].

Let
    Z_eps(s)=integral omega_eps sum_j
       (X_s:partial_j X_s)^2/(|X_s|²+eps²),
    L_eps(s)=integral omega_eps sum_j
       (X_s:partial_j X_s)(X_s e_j dot g)/
                         (|X_s|²+eps²).
Differentiating the weight gives exactly

    U_eps(s)-T_eps(s)=(p-2)(Z_eps(s)-L_eps(s)).

Cauchy--Schwarz gives
    0<=Z_eps(s)<=T_eps(s),
    |L_eps(s)|<=sqrt(Z_eps(s) U_eps(s)).
For the second inequality use |X_s^T g|² <= |X_s|² |g|².
Drop the argument s for these scalar inequalities.

If p>=2, complete the square:
    Z-L>=Z-sqrt(Z U)>=-U/4.
Thus (1+(p-2)/4) U>=T, giving U>=4T/(p+2).
If 1<p<2,
    U-T>=-(2-p)(T+sqrt(T U)).
For T>0 put a=sqrt(U/T); then
    a²+(2-p)a-(p-1)=(a-(p-1))(a+1)>=0.
Since a>=0, U>=(p-1)²T. The zero case is immediate.

These inequalities hold for each eps and s. Integrate
in s and let eps decrease to zero. For p<2 use monotone
convergence and zero-set derivatives; for p>=2 use
boundedness and the integrable unweighted Hessian energy.
This proves (12). QED.

Combined with (9), for U>0,

$$
\boxed{
N\le r_p U,\qquad
r_p=\tfrac12(\sqrt{4/k_p-1}-1).
}
\tag{13}
$$

At p=2 this is precisely (sqrt(3)-1)/2. For p>=2,
r_p=(sqrt(p+1)-1)/2. If U=0, (12) forces T=0.

## 5. A positive all-base consequence for general angular profiles

Let F be any finite positively p-homogeneous function smooth
off zero, p>1. Assume the rank-one curvatures on the unit
sphere obey

    0<m<=D²F(u)[H,H]<=L

for every unit u and every unit rank-one H. This is an
acoustic curvature bound, not a bound on the full Hessian,
nor a perturbation around an isotropic integrand.
By the rank-one generated construction (8),

    J_F=integral Q:d(S_+-S_-)
        >=m (U+N)-L N
        =m U-(L-m)N
        >=[m-r_p(L-m)] U.

Consequently if L/m<=1+1/r_p, the Jensen inequality holds
for EVERY base and EVERY bounded compatible gradient.
More precisely,

$$
\boxed{
J_F\ge\frac{k_p}{d_p}\,[m-r_p(L-m)]\,J_p
\quad\text{when }m-r_p(L-m)\ge0 .
}
\tag{14}
$$

Here (2) and (12) were used only after ensuring the
coefficient is nonnegative. At degree two,
the contrast threshold is 2+sqrt(3), and the estimate is

$$
\boxed{
J_F\ge \frac{(L+m)-\sqrt3(L-m)}4\,
                     \int |D\varphi|^2 .
}
\tag{15}
$$

**Nonhomogeneous consequence at degree two:** suppose F is
any C² function on all real 2x2 matrices with the same
constant global rank-one Hessian bounds m,L (not weighted
by |X|). Use the spatial identities (3),(7) directly
without pushing to the angular sphere, with weight one.
The identical unweighted Hessian calculation proves (15).
Thus this contrast theorem has no homogeneity assumption.
It also needs no sign, rotational symmetry, bounds on the
number of waves, or small-gradient assumption.

This result only uses elementary circle moments, heat flow
and integration by parts. It is not asserted to be a new
optimal curvature-contrast threshold. In the homogeneous
problem, strictification by adding eta |X|^p guarantees a
positive lower bound on curvature, but does not generally
force L/m below the stated threshold as eta decreases to
zero. So (14) cannot be passed to the entire homogeneous
cone using the earlier regularization alone.

## 6. Disposition and exact remaining work

We explicitly constructed a spatially derived kernel correction
    N_exchange=[G]-[V]
that preserves the angular equation and cancels its entire
cofactor trace, for every original compatible field. The
resulting tensor need not be PSD. Its rank-one generated
negative measure admits a uniform global budget, but is
not shown to tend to zero.

The central unresolved task is now **positive absorption of
that negative stress**, or another spatial correction using
the same exact exchange identity. For example a positive
cofactor-free stress dominated by S_+ and having the same
angular source as S_- would finish the correction, but
existence is not established. It is invalid to regard the
negative-stress mass bound as a geometric contraction with
no operation producing the next compatible residual.

The companion [heat_exchange_exact.py](../../research/audit/heat_exchange_exact.py)
was actually executed in the working container:

    Heat exchange, cofactor cancellation and trace identities passed.
    Exact directional decomposition and angular second/fourth moment identities passed.
    Negative-mass bounds and ellipticity contrast constants passed.

The analytic heat, weighted integration and spectral
decomposition proofs are given above. These symbolic checks
only verify their algebra. Gate 1 remains OPEN; no new Lean
result. The earlier verified homogeneous isotropic theorem
is unchanged.
