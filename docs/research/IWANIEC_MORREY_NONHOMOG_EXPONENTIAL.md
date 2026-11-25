# Uniform exponential quasiconvexification of arbitrary strongly rank-one-convex isotropic energies on bounded gradient ranges

24 November 2026. **Positive all-base, all-gradient integral Jensen theorem for a scalar reparametrization of arbitrary nonhomogeneous isotropic energies.** No fixed exponent, wave count, or spectral-profile subclass in the hypothesis on F. The exponential parameter is chosen uniformly over ALL bases and ALL compatible gradient tests in a given bounded matrix ball. In fact the reparametrized energy satisfies a strict quadratic Jensen estimate.

This is a hand proof using published set and transition-layer theorems. It does not use the candidate signed homogeneous proof, the vector projection, or heat descent. No new Lean verification, independent refereeing or publication-priority claim. The original F need not equal its exponential reparametrization; **general isotropic Morrey is NOT proved**. The question of removing the amplification remains open.

## 0. Literature clarification and exact inputs

The support-level implication RC sets => QC sets for disconnected compact SO(2)xSO(2)-invariant subsets of real 2x2 matrices is already known: S. Heinz, *Quasiconvexity equals rank-one convexity for isotropic sets of 2x2 matrices*, WIAS Preprint 1637 (2011), Theorems 7.2 and 7.3,
https://www.wias-berlin.de/publications/wias-publ/run.jsp?number=1637&template=abstract&type=Preprint&year=2011 .
The previous [SPECTRAL_COMPONENTS](IWANIEC_MORREY_SPECTRAL_COMPONENTS.md) note gives a different proof at rank-deficient bases using truncated determinants, but its supremal Jensen conclusion is not a new general-set theorem. Heinz's result covers all bases. His theorem concerns sets, not integral Jensen for arbitrary functions.

We use the following three established results:
* Conti, De Lellis, Müller and Romeo, *Polyconvexity equals rank-one convexity for connected isotropic sets in M^(2x2)*, C. R. Math. 337 (2003), 233--238, Theorem 2.1, https://doi.org/10.1016/S1631-073X(03)00333-9 : a compact connected isotropic lamination-convex set is polyconvex.
* Heinz, op. cit., Theorems 7.2--7.3: every compact isotropic lamination-convex set equals its rank-one convex and quasiconvex hulls.
* Ball and James, *Incompatible sets of gradients and metastability*, https://arxiv.org/abs/1407.5929 (2014 preprint), Remark 6 and Theorem 14. Remark 6 records the planar Kirchheim--Székelyhidi incompatibility criterion: two disjoint compact sets are incompatible if the rank-one convex hull of their union is the disjoint union of their individual rank-one convex hulls. Theorem 14 gives, for incompatible compact K1,K2, on the unit cube and with p=2, constants delta0>0,gamma>0 such that for 0<delta<delta0 and u in W^(1,2), writing E_i={Du in N_delta(K_i)} and T the complement of E_1 union E_2,
  int_T (1+|Du|_F²) >= gamma min(|E_1|,|E_2|).
  Here N_delta is the closed delta-neighborhood. A cube is an admissible C-connected domain. We take delta small enough that the two neighborhoods are disjoint.

These statements were checked in the cited sources. Only the two-set transition theorem is needed, regardless of the number of connected components in a sublevel set.

## 1. Main theorem

Let F:R^(2x2)->R be C² and SO(2)xSO(2)-isotropic. Suppose it is uniformly strictly rank-one convex on every bounded matrix ball: for each finite radius r, there is m_r>0 such that
    D²F(X)[H,H]>=m_r |H|_F²
whenever ||X||op<=r and H has rank one. It is enough to have this hypothesis on a neighborhood of the bounded range used in the theorem.

**Theorem (uniform exponential quasiconvexification).**
For every R<infinity there exist lambda_R>0 and kappa_R>0 such that for every lambda>=lambda_R, every base A with ||A||op<=R and every compatible periodic Lipschitz gradient X=A+Dphi with ||X||op<=R almost everywhere, on the normalized unit torus,
$$
\boxed{
\int \frac{\exp(\lambda(F(X)-F(A)))-1}{\lambda}
\ \ge\ \kappa_R\int |X-A|_F^2.
}
\tag{1}
$$
The same holds for Lipschitz tests with affine boundary data. The parameters do not depend on A, phi, support size, amplitude ratios, or oscillation frequencies within the chosen ball. In particular exp(lambda F) is strongly quasiconvex on this bounded gradient range.

The uniformity in A is proved last. We first build a strong Jensen inequality at an arbitrary fixed A, using a slightly larger gradient bound.

## 2. Spectral coordinates and sublevel component

Write the conformal and anticonformal parts of X as z,w in C, with x=|z|,y=|w|. Then
    ||X||op=x+y,  |X|_F²=2(x²+y²),  det X=x²-y².
Every isotropic F is F(X)=f(x,y). The function f extends to a C² function of real x,y by evaluating F at the matrices with real z=x,w=y; it is even in each variable. By proper rotations we may assume the prescribed A has z=x0>=0,w=y0>=0, real.

Set c0=F(A), and define the smooth invariant nonnegative penalty
$$
\psi(X)=p_{x_0}(|z|^2)+p_{y_0}(|w|^2),\qquad
p_a(t)=
\begin{cases}(t-a^2)^2,&a>0,\\ t,&a=0.\end{cases}
$$
It vanishes exactly on the SO(2)xSO(2) orbit O_A of A. In the real spectral variables its Hessian at (x0,y0) is diagonal with entry 8a² if a>0 and 2 if a=0. It is positive definite in those two variables, even at a conformal endpoint.

Fix R strictly larger than ||A||op and a further radius R'>R. For sufficiently small epsilon>0, F_e=F-epsilon psi is still uniformly strictly RC on the closed operator-norm ball of radius R', because psi has bounded Hessian there. Put
$$
K'=\{X:\|X\|_{\rm op}\le R',\ F_e(X)\le c_0\},\qquad
K=\{X:\|X\|_{\rm op}\le R,\ F(X)\le c_0\}.
$$
Both are compact isotropic lamination-convex sets, and K is a subset of K'. Let C be the connected component of K' containing A. It is compact, isotropic, lamination convex, and hence polyconvex by the first literature theorem. In particular O_A is contained in C.

We record two elementary facts:
1. If B in K intersection C is not on O_A, then F_e(B)<c0 and ||B||op<R'. Thus a full matrix neighborhood of B lies in K', and, being connected and containing B, in C.
2. Write M(X)=(X,det X). If a full matrix neighborhood of B is in C, M(B) belongs to the interior in R^5 of conv M(C). Indeed the lifts of B plus/minus small rank-one coordinate matrices give four independent pairs of opposite tangent directions at M(B), and the averages of the lifts of B plus/minus t I and B plus/minus t diag(1,-1) give the opposite pure fifth directions (0,+/-t²). Their convex hull contains a five-dimensional neighborhood of M(B).

The point M(A) is on the boundary of conv M(C). Otherwise polyconvexity of C and continuity of M would imply a neighborhood of A in C, contradicting strict RC on a rank-one line through A, since F_e(A)=c0 and F_e<=c0 on C. Thus a nonzero supporting functional exists. In particular there is a nontrivial polyaffine P0=k+linear(X)+c det X such that P0(A)=0 and P0<=0 on C. At every B in K intersection C off O_A it is strictly negative, by facts 1 and 2.

For a polyaffine P0 its isotropic supremum over proper left/right rotations is
$$
\overline P_0(X)=k+\beta |z|+\gamma |w|+c\det X,\quad\beta,\gamma\ge0.
$$
It still touches at A and is <=0 on C; it is strictly negative on K intersection C off O_A because the entire compact orbit of such a B consists of interior points as in fact 1. The supremum formula follows from independent rotation of z,w. We use this supporting functional to build a QC calibration in the next section, adjusting the determinant multiplier slightly where necessary. At zero we use a different quadratic calibration.

## 3. A calibration with a strict local Jensen margin at EVERY base

Let w_F(X)=F(X)-F(A) (the subscript distinguishes it from the anticonformal coordinate). Write
    H_lambda(t)=(exp(lambda t)-1)/lambda.
This function is convex, increasing, H_lambda(0)=0, H_lambda'(0)=1 and H_lambda''(0)=lambda. For every fixed real t, H_lambda(t) is nondecreasing in lambda>0: use the secant slope of the convex exponential along the positive lambda-axis. Also H_lambda(t)>=t.

We construct a globally QC calibration P(X) with P(A)=0, and lambda0>0, eta0>0, and a spectral neighborhood U of O_A such that
$$
H_{\lambda_0}(w_F(X))-P(X)\ge \eta_0 |X-A|_F²\quad(X\in U),
\tag{2}
$$
and
$$
P(X)<0 \quad (X\in (K\cap C)\setminus\{A\}).
\tag{3}
$$
The point A itself, rather than its entire orbit, is exceptional in (3). In the cases with nonzero moduli the strictness on other orbit points follows from the orientation gap below.

### 3.1 Noncritical bases, including noncritical conformal endpoints

Suppose DF(A) is nonzero. Work first in the spectral variables. At x0,y0>0, the profile of the isotropic supporting functional is smooth. At y0=0,x0>0 we show gamma=0: the implicit local level curve F_e(x(y),y)=c0 has x(y)=x0+O(y²), by evenness in y and nonzero x derivative. The curve for small y>=0 is connected to A and belongs to C. Thus gamma y+O(y²)=overline P0(x(y),y)<=0, forcing gamma=0. At x0=0 the same argument gives beta=0. So overline P0 is differentiable in full matrix space near A in these cases as well.

The gradient of P0 at A is a positive multiple of DF(A), since P0<=0 on the local sublevel with a regular boundary F_e=c0 and Dpsi(A)=0. To see the multiple is not zero, if DP0(A)=0 then exactly P0(A+H)=c det H. If c!=0, choose a direction H with DF(A):H<0 and c det H>0; such a direction exists since either determinant-sign cone is open, symmetric under H->-H, and a nonzero linear functional cannot vanish on that cone. Small positive multiples lie in the sublevel component C, contradicting P0<=0. If c=0 the polynomial would be identically zero, which is impossible for a nonzero supporting functional on the minors lift. Since P0 and its isotropic supremum agree at A, their gradients agree there. Normalize the functional by a positive scalar so that the spectral gradients of f and overline P0 agree at (x0,y0).

For every spectral vector v tangent to the regular level (df(v)=0), differentiate twice along a C² local level curve of F_e=c0 with initial derivative v. The curve lies in C (one may use real signed y or x at an endpoint, since the corresponding coefficient gamma or beta is zero and f is even). The isotropic support has a maximum at A along this curve, and its first derivative agrees with df_e. Therefore
$$
D^2(f-\overline P_0)[v,v]\ge \epsilon D^2\psi[v,v]>0\quad(v\ne0).
$$
Here D² is the Hessian in the real spectral variables, evaluated at the base. The penalty Hessian is positive definite as computed in Section 2. The Hessian of H_lambda(w_F) in those variables at A is D²f+lambda df tensor df. Increasing lambda thus makes D²(H_lambda(w_F)-overline P0) positive definite: the tangent restriction is strictly positive, and the additional square in the nonzero normal direction absorbs its cross terms. This is a two-dimensional quadratic-form argument (complete the square in tangent and normal coordinates).

We also need strictly positive norm coefficients for every NONZERO base modulus. If x0,y0>0, the strict RC inequality along the direction with imaginary conformal and imaginary anticonformal components of equal length gives
    f_x/x0+f_y/y0>0.
Since the normalized support has matching gradient, the left side equals beta/x0+gamma/y0. At least one coefficient is positive. If either is zero, alter c by a sufficiently small amount d, and simultaneously replace beta by beta-2d x0, gamma by gamma+2d y0, and adjust the constant to preserve value at A. The new isotropic polynomial differs from the old by exactly
$$
d[(x-x_0)^2-(y-y_0)^2].
$$
Choose the sign of d so both norm coefficients become strictly positive. At a conformal base x0>0,y0=0, gamma stays zero, and if beta=0 choose a small negative d making beta positive. The reflected case is identical. In each case the value and spectral first jet are unchanged, and the strict radial Hessian obtained above persists for sufficiently small d. Choose d also small enough to retain the strict negativity of the original support on the compact subset of K intersection C outside a fixed small spectral neighborhood of O_A. This is possible with a FIXED local neighborhood: the strict radial Hessian at the base and continuity give a common positive lower bound on a sufficiently small neighborhood for all sufficiently small d. The resulting radial Taylor lower bound and H_lambda(t)<=0 for t<=0 give strict negativity on K intersection C inside this spectral neighborhood, except on the orbit.

Now choose P to be the actual polyaffine function with real aligned coefficients:
$$
P(X)=k+\beta\operatorname{Re}z+\gamma\operatorname{Re}w+c\det X,
$$
with the modified, normalized coefficients. It is globally QC and touches at A. Its isotropic upper envelope is the modified spectral support. In the spectral neighborhood, Taylor's theorem gives
$$
H_{\lambda_0}(w_F(X))-\overline P(X)
   \ge \eta_1[(x-x_0)^2+(y-y_0)^2]
$$
for some eta1>0. Moreover
$$
\overline P(X)-P(X)
 =\beta(x-\operatorname{Re}z)+\gamma(y-\operatorname{Re}w).
$$
For x0>0, |z-x0|²=(x-x0)²+2x0(x-Re z), and beta>0; for x0=0 the first radial square is already |z|². Use the same identities for w. Since |X-A|_F²=2(|z-x0|²+|w-y0|²), these inequalities give (2). They also give strict negativity on other points of the orbit because the positive coefficients force both nonzero complex parts to have the base phases at equality. Together with the preceding compactness argument this proves (3).

### 3.2 All nonzero critical bases

If x0,y0>0 then DF(A)=0 is impossible: the strictly positive rank-one Hessian in the imaginary direction used above would be f_x/x0+f_y/y0=0. Thus a nonzero critical base is conformal or anticonformal. Reflect if necessary and take x0=r>0,y0=0. Let a=f_xx(r,0) and b=f_yy(r,0). Strict rank-one convexity in conformal/anticonformal coordinates implies b>0 and a+b>0: use, respectively, an imaginary conformal and real anticonformal rank-one direction, or two real parts of equal speed. The mixed derivative f_xy vanishes by evenness in y.

If a>0, choose epsilon small so that the spectral Hessian of F_e at (r,0) is positive definite. Its local sublevel F_e<=c0 consists exactly of the orbit. The orbit is a relatively open and closed subset of K', hence is C. In this case choose any k_*>0 small enough that k_*<b/2, and set
    overline P(x,y)=k_*[y²-(x-r)²].
If a<=0, choose epsilon small so that a_e=a-epsilon psi_xx<0, b_e=b-epsilon psi_yy>0. The local sublevel has points (r+xi,0) on both sides, and (r+xi,t|xi|) for a fixed sufficiently small t>0 and both signs of xi, all connected to the base along those rays for small xi, by the strict negative quadratic Taylor term. For the isotropic envelope of the lifted supporting functional in Section 2, the first pair forces beta+2cr=0, and the latter forces gamma=0. Its value at (r,0) is zero, so it is exactly c[(x-r)²-y²], with c<0 (beta>=0, and otherwise the functional is identically zero). Scale by a positive constant to obtain
    overline P(x,y)=k_*[y²-(x-r)²],  max(0,-a/2)<k_*<b/2.
Such k_* exists by b>0 and a+b>0. The strict inequality (3) off the orbit in C follows from the original supporting functional and positive scaling; for a>0 there are no such off-orbit points.

In either case the actual polyaffine calibration is
    P(X)=2k_* r Re z - k_* det X - k_* r².
Its isotropic envelope is the prescribed polynomial. The spectral Hessian of f-overline P at (r,0) is diag(a+2k_*,b-2k_*), positive definite, with equality of value and gradient. Thus (2) follows by Taylor, H_lambda(t)>=t, and the phase identity, using the positive coefficient 2k_* r of Re z. The orientation gap gives strictness on the orbit except at A, proving (3). Reflection handles the anticonformal case.

### 3.3 The zero base

At zero, isotropy and C² Taylor give
    F(X)-F(0)=a |X|_F²+b det X+o(|X|_F²),
with a>0 by strict RC; the quadratic invariance follows from independent conformal and anticonformal rotations. Choose epsilon small enough that the analogous coefficient a_e=a-epsilon/2 for F_e is still positive (here psi=(|X|_F²)/2). There are no nonzero rank-one matrices in K', since F_e is even and strictly convex on every rank-one line through zero.

If C contains nonzero matrices, they all have the same determinant sign. Otherwise take two of opposite signs, balance their determinant moments by a convex combination, and use independent rotations and averaging in their two complex parts to give their law a small nonzero rank-one barycenter: the conformal and anticonformal average moduli can each be chosen to be the same arbitrarily small positive number, since each of the two total available moduli is positive. This is a correct-minors probability measure supported on C. Polyconvexity of C would place the nonzero rank-one barycenter in C, a contradiction. Moreover C connected and containing zero and another point must have nonzero points arbitrarily close to zero. The Taylor bound for F_e shows that such low-energy points require b!=0 and determinant sign opposite b. Hence this sign holds throughout C minus zero.

Choose eta>0 small and put P(X)=b det X+eta |X|_F². It is globally QC. The Taylor bound for F gives (2) on a neighborhood of zero with a strict quadratic margin. For nonzero points in C sufficiently near zero the Taylor bound for F_e gives b det X<=-a_e |X|_F²/2, so choose eta<a_e/2. On the remaining compact portion of C, if nonempty, b det X<0 with |det X|/|X|_F² bounded away from zero; reducing eta ensures (3). If C={0} there is no additional constraint. This proves the claim at zero.

## 4. A compact two-phase partition, even with infinitely many components

We need to extend (2),(3) over the full bounded test ball, not merely a neighborhood of the base. We first record how to isolate C by clopen unions of components in K'.

For X write s=||X||op, delta=det X/s (zero at zero) and I(X)=[|delta|,s]. The compact set T(K')=union of I(X) has real connected components J. The connected components of K' correspond to these J. Here is a short proof. The fiber of matrices whose interval contains a fixed radius r is path connected: rotate both matrices to have identical first column of norm r, and join by their rank-one segment, retaining r in their intervals. Rotations are connected paths. The compact graph of pairs (X,r) with r in I(X) intersection a fixed J is connected, since its projection to connected J has connected fibers (a disconnection into compact pieces would disconnect their images). Its matrix projection is the component corresponding to J. Conversely a connected matrix subset cannot meet distinct interval components, by continuity of s. This proves the correspondence.

Let J be the interval component corresponding to C. At an interior endpoint of J in the range of T(K') there are gap radii outside T(K') arbitrarily close on the exterior side, unless J already reaches the corresponding extreme of T(K'). Choose such gap radii on both sides (omitting a side at an extreme). Their spectral band defines a compact union K1 of components including C, and a complementary compact union K2 in K'. By bringing the gap radii to the endpoints, K1 can be made arbitrarily close to C: otherwise a sequence in these shrinking bands bounded away from C would have a cluster point with its interval in J. Both K1,K2 are isotropic and lamination convex, since a rank-one segment in K' is connected. In particular they and their union are QC and RC sets by Heinz's theorem. K2 may be empty.

Choose the band sufficiently close to C that P is strictly negative on (K intersection K1) outside the spectral neighborhood U of (2). This follows from compactness and (3), because the exceptional point A is in U. Shrink U if necessary before choosing the band; it may be taken to be a spectral ball about the orbit. The estimate (2) also gives strict negativity on (K intersection U) minus A, since H_lambda(w_F)<=0 there.

If K2 is nonempty, the two-set planar incompatibility criterion gives incompatibility of K1 and K2, since the three rank-one convex hulls are exactly K1, K2, and their disjoint union. Apply the Ball--James theorem with p=2. Choose a fixed delta>0 sufficiently small so the closed neighborhoods N_delta(K1), N_delta(K2) are disjoint and the transition-layer estimate holds. We may shrink delta further below.

## 5. Integral comparison on the whole bounded ball

Use the sets E_i={x:X(x) in N_delta(K_i)}, and T the complement of E1 union E2. Write alpha=|E1|, beta=|E2|, t=|T| (the spatial cube has measure one). We first show that there is a constant L_T<infinity such that
$$
\beta\le L_T t .
\tag{4}
$$
Indeed K2 is a compact QC set and A is outside it. There is a continuous globally QC function q with q(A)>max_{K2} q. For delta small enough the strict separation remains on N_delta(K2) intersection the radius-R test ball, say q<=q(A)-k with k>0. If this intersection is empty, beta=0 is immediate. Otherwise q is bounded above on the test ball, by Q>=q(A). Jensen gives
    q(A)<=E q<=beta(q(A)-k)+(1-beta)Q.
Hence 1-beta>=k/(Q-q(A)+k)=b0>0. The Ball--James inequality, since |X|_F²<=2R², gives t>=gamma/(1+2R²) min(alpha,beta). If t>=b0/2 then beta<=2t/b0; otherwise alpha=1-beta-t>=b0/2, and min(alpha,beta)>=(b0/2)beta. This proves (4), e.g. with
    L_T=max(2/b0, 2(1+2R²)/(gamma b0)).
The functions q and constants do not depend on the test gradient.

Also there is h>0 with w_F(X)>=h on the transition region within the radius-R ball. Indeed the compact set in that ball with distance >=delta from K'=K1 union K2 is disjoint from K, which contains every point with w_F<=0 in that ball. Thus the continuous w_F has strictly positive minimum there (if empty, t=0). This argument is important: use the enlarged sublevel for incompatibility but the original sublevel for the positive-energy gap.

We now choose a small eta>0 and increase lambda, both independently of the particular test. On the spectral neighborhood U, (2) implies H_lambda(w_F)>=P+eta|X-A|_F² for all lambda>=lambda0 if eta<=eta0. On the compact part of the test ball outside U and in N_delta(K1), every point with w_F<=0 belongs to K intersection K1 (it belongs to K' and cannot belong to K2 if delta is less than their distance), and P is strictly negative there. Choose eta still smaller so P+eta|X-A|_F² remains strictly negative on that compact low set. By compactness H_lambda(w_F)>=P+eta|X-A|_F² on the whole indicated portion for sufficiently large lambda: near the low set the left side is at least -1/lambda, and away from a neighborhood of it w_F is bounded below by a positive number, so H_lambda tends to infinity uniformly. Consequently
$$
H_\lambda(w_F(X))-P(X)-\eta|X-A|_F²\ge0\quad\text{on }E_1.
$$

Everywhere on the test ball the same left side is bounded below by -D for a finite D independent of lambda>=1, since H_lambda>=-1 and P+eta|X-A|_F² is bounded. On T the energy gap h>0 makes the left side at least D L_T for sufficiently large lambda. Integrate on the three regions and use (4). This gives
$$
\int H_\lambda(w_F(X))\ge
\int P(X)+\eta\int|X-A|_F² -D\beta+D L_T t
\ge\eta\int|X-A|_F² .
$$
The last inequality uses quasiconvexity of P and P(A)=0. This proves the strict integral Jensen estimate at the fixed base for all sufficiently large lambda and all bounded compatible gradients. If K2 is empty, there is no transition-layer argument: the strict negativity on all low points away from U and compactness prove the comparison directly on the full test ball by taking a sufficiently large lambda.

## 6. Uniformity over ALL bases on the bounded range

We have proved the fixed-base estimate on every bounded gradient range containing that base in its interior. Apply it at each A in the radius-R ball, using the larger gradient bound R+1. Fix an associated lambda_A and eta_A>0. In terms of E_lambda(X)=exp(lambda F(X)), the estimate is
    int E_lambda(A+Dphi)-E_lambda(A)
      >=lambda exp(lambda F(A)) eta_A int |Dphi|_F².
The strict inequality is stable under small changes of the base at this fixed lambda. Indeed the linear Taylor terms in Dphi vanish on integration. The difference between the Jensen deficits at bases A and B is bounded by
    (1/2) omega(|A-B|) int |Dphi|_F²,
where omega is a modulus of continuity of D²E_lambda on a slightly larger compact matrix ball. This is Taylor's integral formula along the segment from each base to its test gradient. If ||B+Dphi||op<=R and |A-B| is small, both gradient ranges are covered by the bound R+1 used at A. Thus all B in a neighborhood of A have a strict Jensen margin with the same exponent lambda_A (reduce the margin by half, and normalize it by lambda_A exp(lambda_A F(B)), which is bounded above in that neighborhood).

These neighborhoods form an open cover of the compact ball of bases. Take a finite subcover, lambda_R the maximum of the finitely many lambda_A (and 1), and kappa_R the minimum of their positive normalized margins. For lambda>=lambda_R, H_lambda(w_F)>=H_lambda_A(w_F) pointwise, including negative w_F. Thus the same normalized lower bound holds for all bases and all fields. This proves (1).

## 7. Uniform weighted integral Jensen for the ORIGINAL energy

Let M=osc_{||X||op<=R} F. If M=0 there is no Jensen deficit (and for R>0 strict RC excludes M=0). For M>0 and lambda=lambda_R,
$$
l=\frac{1-e^{-\lambda M}}{\lambda M}>0,\qquad
u=\frac{e^{\lambda M}-1}{\lambda M}.
$$
On -M<=w<=M, the elementary exponential bounds give
    H_lambda(w)<=u w_+ - l w_- .
Using (1) yields the uniform weighted integral estimate
$$
\boxed{
\int (F(A)-F(X))_+
+\frac{\kappa_R}{l}\int |X-A|_F²
\le e^{\lambda_R M}\int(F(X)-F(A))_+ .
}
\tag{5}
$$
It holds for the same arbitrary F and ALL base matrices, including zero and every rank-one base, with a single constant for the whole ball. This is genuinely a weighted Jensen statement rather than a supremal statement. It also implies Jensen at every base A for the continuous convex increasing piecewise-linear reparametrization
    w -> C_R w_+-w_-,  C_R=exp(lambda_R M),
centered at F(A), and the stronger smooth exponential result (1) uses ONE common function exp(lambda_R F) across the entire ball.

The constant in (5) need not equal 1 in this proof. Uniform finiteness is not the desired unweighted Morrey inequality. The theorem proves no universal finite lambda over unbounded gradient ranges, no quasiconvexity of F without the reparametrization, and no result for arbitrary anisotropic F. For tackling unrestricted isotropic Morrey one can restrict without loss to smooth uniformly strictly RC energies by invariant mollification and adding vanishing positive quadratics, but the constants above may depend on those perturbations. They cannot simply be passed to a limit or sent to one.

## 8. Disposition and next task

The symbolic checker
[nonhomogeneous_exponential_exact.py](../../research/audit/nonhomogeneous_exponential_exact.py)
was executed with Python/SymPy, confirming the spectral penalty Hessians, the determinant-multiplier shift preserving the first jet, the critical conformal support, and the phase-deficit identity. The proof of the global theorem is analytic; no numerical test is used as a substitute.

**Positive progress:** arbitrary smooth strictly RC isotropic F, with no homogeneity and arbitrary signed energies, admits a single smooth increasing convex reparametrization that is strongly QC uniformly on each bounded gradient range. The proof handles every base and uses actual compatible-gradient transition costs. The earlier fixed-witness eventual power inequality is much weaker: its exponent was allowed to depend on the witness. Here the exponent is chosen BEFORE the test gradient, simultaneously for every base on the compact ball.

**Next positive target:** sharpen the comparison to recover the original energy, e.g. quantitative control of the transition cost and of the local support curvature without exponential amplification. We have not shown that the threshold lambda_R can tend to zero or the factor in (5) can tend to one. Do not misstate this as closure of general isotropic Morrey. Do not return to fixed projection/heat descent or enumerate restricted curvature subclasses. Audit of the signed homogeneous candidate remains separate.
