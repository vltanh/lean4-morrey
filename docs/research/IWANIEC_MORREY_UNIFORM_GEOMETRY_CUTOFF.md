# Uniform finite-accuracy geometry via separated frequency bands

24 November 2026. **This is the missing law-side finite-accuracy reduction.** The previous [degree-free finite-data theorem](IWANIEC_MORREY_DEGREE_FREE_FINITE_FILLINGS.md) handled the entire integrand cone at a fixed finite vertex geometry, but did not bound the geometry. Here a frequency separation, localization, and relative-energy extraction argument bounds the geometry independently of the original witness.

For each rational 0<epsilon<=1 we give a computable finite set of rational periodic PL maps, on one fixed square mesh, and a computable positive threshold Delta(epsilon). If ANY normalized globally RC energy and ANY bounded compatible gradient have gap <=-epsilon, then some map in this set has gap <=-Delta for a normalized globally RC energy. Combining the earlier degree-free data repair with this theorem gives one finite rational optimization that either certifies a genuine unrestricted counterexample or proves the uniform estimate J> -epsilon on the original normalized class. Neither the original frequency scale nor number of distinct scales, triangles, or energy polynomial degree enters the cutoff.

**Limits:** the bound is for prescribed positive accuracy, not exact zero. The constants below are deliberately conservative and astronomically large. The finite optimization has not been enumerated or solved at this scale. This is not a practical solver or an unrestricted Morrey proof, and no new Lean verification, independent review, or priority claim is made. Exact Fourier multiplier and parameter controls were executed in Python. A brief literature check found related computational Morrey work, e.g. Voss et al., [Numerical approaches for investigating quasiconvexity](https://doi.org/10.1007/s00332-022-09820-x), but is not a complete novelty review.

## 1. Normalization and precise theorem

Use Frobenius norms on matrices and the corresponding Euclidean tensor norms. Let K denote all finite globally RC f on R^(2x2) with
    f(0)=0,   |f(X)-f(Y)|<=|X-Y|_1,
where the 1-norm is the sum of the absolute values of all four entries. In particular each f is Frobenius-Lipschitz with constant <=2. Work on the area-one flat torus.

Every possible strict counterexample to planar Morrey can be put in K, with base zero and ||Dphi||_infty<=1. Indeed translate and scale the original matrix energy and periodic perturbation to achieve the gradient bound. On the ball of radius 3 shift the energy to be nonnegative. Replace it there by its maximum with c(|X|_F-2) and extend by this barrier outside. Choose c so large that the barrier strictly dominates at radius 3. Convexity on every rank-one line glues by the strict boundary margin. The result agrees with the shifted original energy on radius 1 and has exterior c(|X|-2). Every coordinate line is convex with asymptotic slopes ±c, so its Lipschitz constant in that coordinate is <=c. Divide by c and subtract its value at zero. The strict sign is preserved. This is also a special case of the [fixed class normalization](IWANIEC_MORREY_SIGNED_TRACE_FOLD_TRANSFER.md).

**Theorem A.** For rational 0<epsilon<=1, there are explicit computable rational Delta>0 and integer n, and a finite family V_epsilon of rational two-component periodic PL maps on the common n by n square grid with each square cut along the same diagonal, such that:
    if some f in K and periodic Lipschitz phi with ||Dphi||_infty<=1 obey
        int f(Dphi)-f(0)<=-epsilon,
    then for some u in V_epsilon and some F in K,
        int F(Du)-F(0)<=-Delta.
The selected map and F may differ from the original; in particular the final F is translated/rescaled and extended on a fixed finite witness range. This is counterexample extraction, not approximation of every original gradient law by a low-frequency law. The exact mesh and nodal value range are chosen before the original integrand or gradient is known.

## 2. Uniform smoothing of the whole integrand class

Put d=epsilon/128. For one variable use the probability kernel
    rho_d(t)=15/(16d) (1-(t/d)^2)^2 for |t|<=d,
             0 otherwise.
Use its tensor product in four matrix coordinates. It is nonnegative and C^1 with integrable weak second derivatives. Its first derivative has L1 norm <2/d and second derivative L1 norm <=15/d^2, by integration of the displayed polynomial (no endpoint delta since its first derivative vanishes at the endpoints).

Convolving f gives smooth enough F_s: C^3, globally RC, still coordinate-Lipschitz one, with
    |F_s-f|<=4d,
    sup ||D^2 F_s||op <= M=16/d,
    sup ||D^3 F_s||op <= T=256/d^2.
Indeed the weak first coordinate derivatives of f are bounded by 1. Each partial second derivative of the convolution is bounded by 2/d, and each partial third derivative by 16/d^2. Taking arbitrary Euclidean unit tensor arguments gives the constants above via the l1 bounds <=2 on each matrix argument. Continuity of these derivatives follows from L1 kernel translation continuity against the bounded weak first derivatives. Convolution preserves RC by averaging its translated rank-one inequalities. Subtracting a constant has no effect on the argument.

Replace phi by a sufficiently high product Fejer convolution. Its derivative is a trigonometric polynomial X of mean zero, still with ||X||_infty<=1 by positivity of the Fejer kernel, and converges in L2. Choose the approximation so that its F_s gap changes by <=epsilon/16, using the Lipschitz constant. Smoothing the energy changes the gap by <=8d=epsilon/16. Thus we start with a smooth finite Fourier field satisfying
    J_s(X)=int [F_s(X)-F_s(0)] <= -7 epsilon/8.
No bound on the initial Fejer cutoff is required.

For convenience set
    R(B,H)=F_s(B+H)-F_s(B)-DF_s(B):H.
Taylor's integral formula gives the three global estimates
    |R(B,H)| <= (M/2)|H|^2,
    |R(B,H)-R(B',H)| <= (T/2)|B-B'| |H|^2,
    |R(B,H)-R(B,K)| <= M(|H|+|K|)|H-K|.
The last follows by integrating the H-derivative, which has norm <=M|H|. These bounds are independent of B and remain valid even if intermediate low-frequency sums have large amplitude.

## 3. Positive frequency partition with sparse discarded gaps

In one space dimension let Fejer_n have Fourier multiplier (1-|k|/n)_+, and let V_n=2 Fejer_(2n)-Fejer_n. Its multiplier is
    v_n(k)=max(0,min(1,2-|k|/n)).
Its convolution L1 operator bound is 3. In two dimensions put P_i=V_(2^i) tensor V_(2^i), for integers i>=0, and D_0=P_0, D_i=P_i-P_(i-1) for i>=1. These are Fourier multipliers. All D_i multipliers are nonnegative, their sum is one, and each P_i has L1 operator bound 9. For i>=1 a nonzero multiplier D_i(k) requires
    2^(i-1)<|k|_infty<2^(i+1).
Only the zero-mean frequencies are needed.

Choose a positive integer K (retained band length) and g (gap length), and periodically discard g consecutive indices out of each K+g, with an offset modulo K+g. The average discarded multiplier at each k over all offsets is g/(K+g); it lies in [0,1]. Hence its mean square is <=g/(K+g). By Parseval choose ONE offset with discarded field Y satisfying
    ||Y||_2^2 <= g/(K+g) ||X||_2^2.
The retained blocks are consecutive retained indices a_j,...,b_j of length at most K, with g indices between successive blocks. Keep zero blocks in the ordering until beyond the support of X. For the first block b_1<K+g, including an initial possibly partial block.

Write
    G_j=sum_(i=a_j)^b_j D_i X,   w_j=sum_(i=a_j)^b_j D_i phi,
    E_j=||G_j||_2^2.
The underlying phi here is the already smoothed, mean-zero periodic potential. Each G_j=Dw_j. The block multipliers are nonnegative and sum to <=1, so sum_j E_j<=||X||_2^2<=1. Each block operator is the difference of two P's (or one P), giving ||G_j||_infty<=18. Its support is in
    ell_j<=|k|_infty<u_j,   ell_j=2^(a_j-1) if a_j>=1, else 1,
    u_j=2^(b_j+1),
with u_j/ell_j<=2^(K+1), and u_1<=2^(K+g). All w_j are mean zero and
    ||w_j||_2<= E_j^(1/2)/(2pi ell_j),   ||DG_j||_2<=16 u_j E_j^(1/2).
These follow directly from the support and Parseval.

Choose a dyadic lambda=2^(-s), s>=1, and g=2s+1. For j>1,
    u_(j-1)/ell_j<=lambda^2.
Since successive u_j increase by at least a factor two,
    u_i/ell_j<=lambda^2 2^(-(j-1-i)) for i<j.
For the partial sum L_j=sum_(i<j) G_i, Fourier orthogonality yields
$$
\left|\int DF_s(L_j):G_j\right|
\le \sqrt{2}M\sum_{i<j}(u_i/\ell_j)\sqrt{E_i E_j}.
$$
In detail, project DF_s(L_j) onto frequencies |k|_infty>=ell_j (only these pair with G_j). Its L2 norm is <=||D[DF_s(L_j)]||_2/(2pi ell_j), by Parseval, and this derivative is bounded by M||DL_j||_2. Use the support estimates for the latter. The j=1 term vanishes since G_1 has mean zero. Summing using 2sqrt(E_i E_j)<=E_i+E_j and the geometric bounds on u_i/ell_j gives
    sum_j |int DF_s(L_j):G_j| <=4 M lambda^2 sum_j E_j.
This is the essential summability: there is no factor counting the number of bands.

The original gap of X differs from the gap of sum G_j by at most 2sqrt(g/(K+g)).

## 4. Localizing every band on an intermediate scale

For j>1 take m_j=lambda ell_j, an integer: ell_j is dyadic with a_j-1>=g, while s<g. Thus m_j/ell_j=lambda and u_(j-1)/m_j<=lambda. Partition the torus into m_j by m_j equal squares (with a shift chosen below).

We need slow variation of L_j, not a bound on its value. For trigonometric polynomials use the ordinary one-dimensional Bernstein inequality in each spatial variable, applied also to scalar projections of a matrix-valued polynomial. It gives ||partial_k G_i||_infty<=2pi u_i ||G_i||_infty. Summing over earlier blocks (sum u_i<=2u_(j-1)), the oscillation of L_j within any cell is at most 2048 lambda. For example, using pi<4 and sqrt(2)<2, the gradient bound is <=576 u_(j-1) and the diameter <=2/m_j. This verifies the deliberately loose constant.

Let 0<theta<1/4 be a fixed relative boundary width. On each square C choose the same scaled cutoff chi: zero on the boundary with zero first derivative, equal to one farther than theta/m_j from the boundary. It can be the product of four one-variable transitions p(t)=3t^2-2t^3 on [0,1], extended by 0 below and 1 above, with arguments the scaled distances from the four sides. Because opposite boundary transitions do not overlap,
    0<=chi<=1,  |Dchi|<=16 m_j/theta,
    |D^2chi|<=64 m_j^2/theta^2
a.e., in Euclidean norms. Choose a translation of this square grid so that
    int_boundary_layers |G_j|^2 <=4 theta E_j.
A uniform translation has this bound in expectation, by Fubini and the boundary-layer area fraction. Such a shift therefore exists; the shift is allowed to depend on the input band.

Let B_C=L_j at the center of C, and let H_j on each C be D(chi w_j). If lambda<=theta/16 then
    ||H_j||_2 <=(1+16lambda/theta)sqrt(E_j)<=2sqrt(E_j),
where the norm sums the cell integrals. Indeed use H_j=chi G_j+w_j tensor Dchi and the low-frequency Poincare estimate for w_j above. On the boundary layers,
    int |H_j|^2 <= 8theta E_j +512 lambda^2/theta^2 E_j.
Since H_j=G_j off the layers, the remainder estimates of Section 2 and the slow variation bound give
$$
\left|\int R(L_j,G_j)-\sum_C\int_C R(B_C,H_j)\right|
\le [1024 T\lambda +M(6\theta+256\lambda^2/\theta^2)] E_j.
$$
The base replacement error uses T |L_j-B_C| |G_j|^2/2; the boundary replacement error uses M/2 times the sum of the two squared norms on the layers. This proves the estimate without evaluating any conditional gradient law. Each local perturbation is itself an actual compact-boundary gradient.

Rescale each C to a unit square, with the potential multiplied by m_j to preserve its gradient. Call it U_C. Since chi and its first derivative vanish at the boundary, U_C extends periodically in W^(2,2). The cell area weights m_j^(-2) recover exactly the original integrals. The Hessians satisfy the aggregate bound
$$
\left(\sum_C m_j^{-2}||D^2 U_C||_2^2\right)^{1/2}
\le [16 u_j/m_j+32/\theta+64\lambda/\theta^2]\sqrt{E_j}.
$$
Expand D^2(chi w_j), use the cutoff bounds and the two Fourier norm estimates, and divide by m_j. Here u_j/m_j<=2^(K+1)/lambda.

For j=1 there is no low field or boundary issue: use the single original periodic potential w_1, B=0, of Hessian norm <=16 u_1 sqrt(E_1). Hence ONE uniform aggregate Hessian constant, valid for all blocks, is
    H0=16*2^(K+g+2)/lambda +32/theta+64/theta^2.
The first band also satisfies the preceding gradient norm bound. The errors and all these norms are weighted by E_j, not the number of cells or bands.

## 5. A fixed periodic mesh with relative L2 gradient error

Here is an explicit finite-element approximation avoiding any unproved uniform approximation of arbitrary Lipschitz gradients. For any periodic W^(2,2) map U and square integer n>=16 (a perfect square is convenient), put t=n^(-1/2)<=1/4. Average U by the normalized box kernel on [-t,t]^2, periodically, producing U_t. The elementary translation estimate for W^(1,2) functions and Cauchy-Schwarz give
    ||DU_t-DU||_2 <= sqrt(2)t ||D^2 U||_2,
    ||D^2 U_t||_infty <= ||D^2 U||_2/(2t).
The latter uses the L2 norm 1/(2t) of the normalized box. These convolved derivatives are continuous (L2 translation continuity), so the ordinary nodal interpolation is legitimate.

Interpolate U_t on the fixed n by n periodic square grid with a common diagonal. On each triangle each column of the interpolated gradient is the slope along a horizontal or vertical edge of length 1/n. Its difference from the corresponding derivative of U_t anywhere on that triangle is bounded by sqrt(2)/n times the Hessian sup norm, using the fundamental theorem along the edge. Combining the columns gives Frobenius error <=2/n times that norm. Thus the periodic PL interpolant U_h obeys
    ||DU_h-DU||_2 <= (sqrt(2)t+1/(nt)) ||D^2 U||_2
                    <=3 ||D^2 U||_2/sqrt(n).
This is a relative H2-based estimate, not an assumption that the original arbitrary X has uniformly controlled H2 norm.

Choose zeta>0, zeta<=1, and n so that 3H0/sqrt(n)<=zeta. Over the local maps of each band the aggregate gradient error is <=zeta sqrt(E_j). Their aggregate gradient norm after approximation is <=(2+zeta)sqrt(E_j). The R estimate gives an energy error per band bounded by
    M(4+zeta)zeta E_j.
The first band obeys this bound too.

Each local mesh map is periodic and its mean gradient is zero. Consequently its Jensen gap at B_C equals the integral of R(B_C,DU_h), since the linear term integrates to zero.

## 6. Explicit finite extraction

Set theta=zeta=epsilon/[1024(M+1)]. Choose lambda=2^(-s) by increasing s from 1 until all these rational inequalities hold:
    lambda<=theta/16;
    4M lambda^2<=epsilon/32;
    1024 T lambda<=epsilon/32;
    M(6theta+256lambda^2/theta^2)<=epsilon/32.
Existence follows since 6Mtheta<epsilon/32 and the other quantities tend to zero as lambda tends to zero. Let g=2s+1 and K=ceil(1024 g/epsilon^2); then 2sqrt(g/(K+g))<=epsilon/16. Also M(4+zeta)zeta<=epsilon/32.

One explicit mesh size without ever writing a huge exponent in floating point is this:
    D=ceil(log2(1/theta)), Z=ceil(log2(1/zeta)),
    L=max(K+g+s+6,5+D,6+2D)+2,
    n=2^(2(L+Z+2)).
These integer logarithms can be found by rational comparisons with powers of two. Since H0<=2^L and 3H0/sqrt(n)<= (3/4)2^(-Z)<=zeta, the required fixed mesh bound holds.

Telescope the smoothed gap along the partial sums L_j:
    J_s(sum G_j)=sum_j [int DF_s(L_j):G_j + int R(L_j,G_j)].
Apply the linear-term, localization, and mesh-error estimates from Sections 3--5. Let J_loc be the sum of all periodic mesh Jensen gaps at the frozen bases, weighted by their original cell areas, with weight one for the first band. The sum of all these error bounds is <=epsilon/8, because sum E_j<=1. The discarded gap error is <=epsilon/16. The initial smoothed witness satisfies J_s(X)<=-7epsilon/8. Therefore
    J_loc <=-epsilon/2.
At the same time the weighted sum of squared L2 gradient norms of all the mesh maps is <=(2+zeta)^2 sum E_j<=9. Thus some local mesh map U with nonzero gradient L2 norm a obeys
    int F_s(B+DU)-F_s(B) <= -(epsilon/32) a^2.
Indeed if every such gap were larger than -epsilon a^2/32 the weighted sum would be >-9epsilon/32, a contradiction. A zero-gradient periodic map has gap zero and cannot invalidate this argument.

Importantly the selected local gap is measured relative to its own gradient energy. There was no need to lower-bound a or to bound the number of frequency bands. Absolute per-band tolerances would not have been sufficient.

Normalize U by a and subtract its value at one mesh vertex. Then ||DU/a||_2=1. On each triangle the gradient is constant and the triangle area is 1/(2n^2), hence ||DU/a||_infty<=sqrt(2)n. Define the new globally RC function
    f_hat(Y)=[F_s(B+aY)-F_s(B)-a DF_s(B):Y]/a^2.
It has f_hat(0)=0, Df_hat(0)=0 and global Hessian bound M. The normalized map has f_hat Jensen gap <=-epsilon/32. Neither a nor B needs a bound.

Return to K with uniform loss as follows. Let r=2n, D0=2 M r^2, c=(4M+1)r. On |Y|<=2r the function f_hat+D0 lies in [0,4 M r^2]. Inside this ball set G=max(f_hat+D0,c(|Y|-r)), outside use the barrier. Its strict dominance at radius 2r gives globally RC G by rank-one line gluing, and on radius r it equals f_hat+D0. As in Section 1 the linear exterior bounds each coordinate Lipschitz constant by c. Therefore F=(G-D0)/c belongs to K, and its gap on U/a is <=-epsilon/(32c).

Finally put
    Delta=epsilon/(64c),   h=Delta/(16n).
All normalized nodal values have Euclidean norm <=2n after the additive normalization (Lipschitz bound sqrt(2)n times square diameter). Round their two coordinates to h Z with error <=h, consistently on the periodic mesh, retaining the value zero at the chosen vertex. Use the finite set V_epsilon of all periodic nodal assignments from h Z intersect [-2n-1,2n+1], with this value fixed. On each triangle each gradient entry changes by <=2 n h, hence its matrix 1-norm change is <=8 n h=Delta/2. The F in K is 1-Lipschitz in this norm, so the final gap is <=-2Delta+Delta/2<=-Delta.

All parameters depend only on epsilon. This proves Theorem A.

## 7. Combine with exact finite data repair

The earlier [degree-free data repair](IWANIEC_MORREY_DEGREE_FREE_FINITE_FILLINGS.md), Theorem 2, applies to any finite rational set S0 of test slopes and zero in a bounded cube. For all maps in V_epsilon take S0 to be the union of their slopes and zero. All nodal entries have absolute value <=2n+1, so the slopes have entry bounds <=2n(2n+1); the cube radius 8n^2+8n is more than enough. Use the earlier repair with tolerance Delta/2. Its finite rational LP data polytope has two properties:
1. restrictions of every F in K are feasible;
2. every feasible energy vector has a genuine globally RC extension in K matching each sampled test slope up to Delta/4, with exact normalization at zero.

Minimize the sampled energy gap over V_epsilon and this polytope. This is a finite rational optimization, for example enumerate the finite nodal assignments and solve a rational LP for each, or combine them by binary selectors and exact linearization. The data variables are bounded by the Lipschitz constraints relative to zero; the optimum m_grid exists and is rational. Flat zero is among the tests.

**Theorem B (finite certificate alternative at each tolerance).** Run this one finite optimization:
* If m_grid<=-Delta/2, the repaired globally RC energy and the selected actual rational periodic PL gradient have Jensen gap <=-Delta/4. This is a genuine counterexample. If desired, rescale the gradient and matrix integrand to restore the original gradient bound one, preserving the strict sign.
* If m_grid>-Delta/2, then for EVERY f in K and EVERY periodic Lipschitz phi with ||Dphi||_infty<=1, the Jensen gap is >-epsilon.

Proof of the second conclusion: a hypothetical gap <=-epsilon gives by Theorem A a test in V_epsilon and F in K of gap <=-Delta. Its data are feasible, so m_grid<=-Delta, a contradiction. The first conclusion follows from the explicit data repair and the positive triangle area weights summing to one. QED.

This is a uniform **finite-accuracy bound on BOTH sides of the unrestricted problem**, not just the earlier fixed-geometry integrand approximation. If Morrey is true, every one of these finite computations returns the second outcome. If it is false, every sufficiently small epsilon must return the first outcome. These statements do not supply an accuracy-independent decision procedure: the true case still requires a proof at zero, or a uniform exact gap-amplification theorem. The proof does not claim that the finite computation approximates the worst normalized gap to an additive tolerance if it returns a negative witness; the extracted energy and amplitude change, and the negative threshold may be much smaller than epsilon.

## 8. Verification, scope, and next gate

The exact companion [multiscale_constants.py](../../research/audit/multiscale_constants.py) was actually executed. It checked the rational V_n multipliers' nonnegativity, support and partition, the discarded-gap average inequality for integer frequencies in [-16,16]^2, and all explicit parameter budget inequalities at six rational tolerances. It printed:
    Exact multiplier positivity, support, partition, and gap-average checks passed.
    All explicit parameter and error-budget checks passed. No finite mesh was enumerated.
For example epsilon=1 already gives log2(n)=153888, and epsilon=1/10 gives log2(n)=19456360. These constants are conservative theoretical effectivity, not a proposed practical enumeration. The analytic frequency localization and extraction argument, not those finite checks, prove the uniform quantifiers.

No new Lean theorem or independent human validation. The prior negative results about arbitrary conditioning, determinant moments, common filtrations, sampled LH and finite positive grids do not imply or refute this construction: each localized band uses an actual periodic/zero-boundary potential, the relative L2 budget, and a genuine globally RC repair.

**Next gate:** a uniform exact gap-amplification or zero-defect argument, or a substantially sharper constructive estimate that makes a meaningful fixed-accuracy computation practicable. There is no proved positive lower bound on the size of a normalized violation if any exists. Do not equate arbitrary prescribed tolerance with exact positivity, or treat an unexecuted enormous optimization as a closed case. Unrestricted planar Morrey remains open.
