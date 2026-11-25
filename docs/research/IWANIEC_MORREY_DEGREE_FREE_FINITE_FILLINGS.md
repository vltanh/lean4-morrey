# Positive degree-one graphs and a degree-free finite integrand optimization

24 November 2026. This continues [integer fillings](IWANIEC_MORREY_INTEGER_FILLINGS.md) without making a sequence of particular integrands the main problem.

**New unrestricted reductions.** Positive projected triangles suffice for strict-negative existence; their integer multiplicities are automatically binary, and the number of chosen triangles is bounded by twice the number of distinct projected vertices minus six. For EVERY fixed finite rational vertex set, one finite rational optimization over discrete energy data and these graph fillings gives two-sided bounds, at arbitrary prescribed positive accuracy, on the worst Jensen gap over the ENTIRE globally rank-one-convex Lipschitz-normalized class. No polynomial-degree or SOS-cone restriction on the integrand is needed for this theorem. An explicit mollification, curvature repair and linear-tail gluing constructs a genuine globally RC energy from feasible discrete data. The constants are conservative and the resulting uniform net is very large.

**Executed computational results.** A separate tractable joint polynomial/geometry MILP, exact rational branch-and-bound replay, and exact boundary enumerator were implemented. The latter certifies every one of 32 and 1,142 fillings in two fixed vertex controls by exact rank-one merges, hence for ALL RC integrands. The numerical joint quartic search found no negative witness. A larger generic graph merge stress test did not finish in its 25-second budget; it is not evidence of a violation. The full uniform discrete-data net of the theorem below was NOT enumerated or solved.

**Status:** hand proofs and executed finite controls; no new Lean theorem, independent review, proof of unrestricted Morrey or finite cutoff on the vertex geometry. This is a systematic finite-accuracy interface for the unrestricted integrand side, not a proof that the geometry side terminates.

## 1. Positive fillings are genuine graphs, and are binary

Let Q=(0,1)^2. Translate the affine base to zero, so the prescribed oriented boundary is the four edges of the horizontal square in R^2_y x R^2_w. Fix a finite rational vertex set V containing its four corners and with all projected coordinates in closed Q. A candidate triangle is a nondegenerate oriented triangle with vertices in V and strictly positive projected area a_t. Its graph slope is the rational matrix X_t=L(xi_t)/a_t, in the mixed-minor notation of the earlier note. Each unordered triple has at most one such orientation.

**Lemma 1.** If nonnegative integer triangle counts n satisfy the exact oriented edge-incidence equation B n=b (the four oriented boundary edges), then every selected multiplicity is one. The chain is the graph, almost everywhere, of a continuous piecewise-affine Lipschitz map on Q with zero boundary values. At most 2N-6 triangles are selected, where N is the number of distinct projected vertices in V.

Proof: project the chain onto the y-plane. The boundary equation implies that the projected top-dimensional integer current has multiplicity one in Q and zero outside: subtract the square, and its boundary vanishes, so the difference has constant signed density on the whole plane, and compact support forces the constant to be zero. All projected contributions here are positive. Therefore almost every point of Q belongs to exactly one projected triangle interior, counted with multiplicity. No two selected triangle interiors overlap, and every selected multiplicity is one. There are no negative or vertical sheets.

The BV signed-trace formula of [integer fillings](IWANIEC_MORREY_INTEGER_FILLINGS.md), applied with this absence of vertical sheets, gives a single-valued trace whose distributional gradient is exactly X_t on each projected triangle interior, and zero outside Q after extension by the flat graph. It belongs to W^(1,infinity) since there are finitely many slopes. Equivalently, one may use Stokes face by face and the exact edge-incidence equation to verify the weak derivative. The Lipschitz representative agrees with each affine triangle map on its closed projected triangle. Hence at any used projected vertex, there is only one possible used height. The trace is zero on the boundary by its extension, and the energy of ANY finite continuous matrix integrand is exactly sum_t a_t n_t F(X_t). No fold penalty or polynomial-growth extension is needed for these positive competitors.

For the count, the angles of every selected projected triangle sum to pi. The total of these angles at an interior projected vertex is at most 2pi, at a noncorner boundary vertex at most pi, and at the four corners at most pi/2. This follows from disjoint triangle interiors, also allowing possible hanging nodes on edges. Thus pi sum n_t <= 2pi(N-4)+4(pi/2), proving the claimed bound. QED.

Conversely rational PL graph approximations with a flat boundary collar give such chains, with the four unsplit boundary edges. Any strict negative actual periodic witness can be converted by the ordinary affine-boundary cutoff and rational PL approximation into one of these positive rational fillings. The earlier folded BV reduction also converts any strict negative canonical integer filling to an actual graph, so positive fillings are sufficient for the strict-negative question. We do NOT assert a cost-nonincreasing replacement using the same finite vertex set, nor preservation of the extra full-area penalty by signed-trace smoothing.

## 2. Exact finite boundary enumeration and all-integrand certificates

For fixed V, the binary search has the following complete geometric recursion, independent of the integrand. Select an unmet oriented edge of the residual b-Bn; branch on every still compatible triangle with that oriented edge. Prune intersecting projected interiors, inconsistent heights at a common projected vertex, total projected area exceeding one, and depth exceeding 2N-6. If a nonzero residual remains, any feasible completion contains a remaining triangle with the requested edge orientation. This proves completeness by induction on a fixed putative completion. Selecting the edge with fewest available triangles is only a search ordering. Overlap tests can use the rational separating-axis test for two planar triangles. Memoizing the selected subset does not affect completeness. A zero residual implies total projected area one by Stokes. Exact rechecking of each output uses all edge coefficients and the full bivector mean.

For a filling with weights a_t, a sequence of exact rank-one merges of its atomic law is a certificate for every RC F. Replace (p,X),(q,Y) with (p+q,(pX+qY)/(p+q)) if det(X-Y)=0, first aggregating equal atoms. Jensen is valid at every step; ending at (1,0) proves the desired inequality. This is a sufficient certificate, NOT a necessary condition for a laminate. In particular failure of bottom-up merges is not a Morrey counterexample; the search may need splitting atom weights, auxiliary states, or a completely different proof.

The exact enumerator was actually executed on two rational vertex controls (all allowed heights and all compatible triangulations of those finite vertex sets, not one fixed triangulation):

| Control | Vertices | Distinct projections | Admissible candidate triangles | Complete fillings | Distinct gradient laws | Exactly certified fillings |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small | 10 | 6 | 52 | 32 | 21 | 32 |
| four | 16 | 8 | 328 | 1142 | 661 | 1142 |

Both inputs use zero base and Frobenius gradient bound one. The exact recursion visited 98 and 3793 partial states respectively. All outputs were independently boundary-checked and every merge checked by rational arithmetic. These are finite regression controls, not an exhaustive reduction of all geometries. No inference is drawn from the separate generic-graph merge timeout.

## 3. An unrestricted Lipschitz normalization

Write |X|_1 for the sum of absolute values of the four entries. Let K be all globally finite RC f with f(0)=0 and |f(X)-f(Y)|<=|X-Y|_1 for all X,Y. Every strict counterexample to Morrey can be sought in K: the fixed-class normalization of [signed trace](IWANIEC_MORREY_SIGNED_TRACE_FOLD_TRANSFER.md) gives a globally RC W with Frobenius-norm linear exterior. Its restriction to any coordinate line is convex with asymptotic slopes ±1, so its coordinate Lipschitz constants are one. Consequently W-W(0) belongs to K, and has the same gap. The normalization permits arbitrary original energy and base. The original gradient bound can be taken as 1/2 there; the results below allow an arbitrary rational r>=1 covering the witness slopes.

We use this slightly enlarged class K rather than imposing the exterior equality of the previous normalization. It is complete for counterexamples and has simpler rational Lipschitz constraints. If K has no negative Jensen gap on all positive fillings, unrestricted Morrey follows.

## 4. Quantitative repair of finite Lipschitz and rank-one midpoint data

**Theorem 2.** Given rational r>=1 and rational tolerance 0<epsilon<=1, there is a predetermined finite rational set of sample matrices and a predetermined finite list of rank-one midpoint constraints, independent of the original integrand or gradient law. Adjoin any finite set S0 of rational matrices in the cube [-r,r]^4, including 0. Let S be their union with the samples. If real data w_s, s in S, satisfy w_0=0, all pairwise Lipschitz inequalities |w_s-w_t|<=|s-t|_1 and the prescribed midpoint inequalities, then there exists an actual globally RC F in K such that

    |F(s)-w_s| <= epsilon/2 for every s in S0.

Conversely restriction of every F in K is feasible data. Thus the finite constraints provide an explicitly repairable OUTER approximation of the entire unrestricted integrand class, not just a sufficient inner cone or curvature sampling.

### 4.1 Explicit parameters and sample geometry

Set
    eta=epsilon/(16r), c=1+eta, D=16(r+1), R=(D+4)/eta,
    delta=epsilon/64, kappa0=epsilon/(16R^2),
    tau=min(1,kappa0 delta^2/100),
    h=min(1,kappa0 tau^2/80).

All are positive rational. Take all grid bases Y in h Z^4 within [-R-delta-h,R+delta+h]^4. For each take all u',v' in h Z^2 within [-1-h,1+h]^2. Include Y and Y±tau(u' tensor v') in S. Impose
    w(Y+tau H')+w(Y-tau H')-2w(Y)>=0,
    H'=u' tensor v'.
The rank-zero case is harmless. Together with S0 and all pairwise Lipschitz constraints this is a finite rational LP description of w. No smoothness or polynomial representation of the unknown f is imposed.

### 4.2 Extend, then obtain a uniform approximate midpoint inequality

Use the McShane extension
    f0(X)=min_{s in S}(w_s+|X-s|_1).
It is globally 1-Lipschitz in |.|_1 and matches every w_s by the pairwise inequalities. In particular f0(0)=0 and |f0(X)|<=|X|_1. It need not be RC.

Let X be in [-R-delta,R+delta]^4 and H=u tensor v be any Frobenius-unit rank-one direction, with |u|=|v|=1. Round the coordinates of X,u,v to the respective grids with error <=h in each coordinate. Then |X-Y|_1<=4h and
    |H-H'|_1 <= |u-u'|_1 |v|_1+|u'|_1 |v-v'|_1 <=12h,
since h<=1. Lipschitz comparison with the exact sampled midpoint inequality gives
$$
f_0(X+\tau H)+f_0(X-\tau H)-2f_0(X)
\ge -(16+24\tau)h\ge-40h.
$$
This bound is uniform in ALL directions and bases in the indicated cube.

### 4.3 Smooth and repair the rank-one Hessian

Use the normalized one-dimensional kernel
    rho_delta(t)=(15/(16 delta))(1-(t/delta)^2)^2 for |t|<=delta,
                 0 otherwise.
It is nonnegative, C^1, with integrable weak second derivative. Its integral is one, ||rho_delta'||_1=15/(8 delta)<2/delta, and ||rho_delta''||_1<=15/delta^2. The last estimate follows from |−4+12s^2|<=4+12s^2 on [-1,1]; there is no endpoint derivative jump. Take the product kernel in four coordinates and g=f0*rho_delta^(tensor 4). Then |g-f0|<=4delta. For any Frobenius-unit H,
    ||D_H f0||_infty<=|H|_1<=2,
    ||D_H^2 rho_delta^(tensor 4)||_1<=64/delta^2.
The second estimate sums the sixteen partial derivatives using |H|_1^2<=4; each partial has L1 norm <=16/delta^2. Differentiating the convolution in the weak sense, followed by continuity from L1 kernel translations, gives a continuous third directional derivative of g bounded in absolute value by 128/delta^2. In particular ordinary second directional differentiation and the third-order Taylor estimate are legitimate.

The approximate midpoint inequality averages under this kernel for every X in [-R,R]^4. Comparing the symmetric second difference at step tau with its second derivative gives, for every unit rank-one H,
$$
D^2g(X)[H,H]\ge-40h/\tau^2-43\tau/\delta^2.
$$
Indeed the sum of two third-order Taylor remainders divided by tau^2 is at most (128/3) tau/delta^2. Put kappa=40h/tau^2+43tau/delta^2. The chosen parameters give kappa<=kappa0. Thus
    g1(X)=g(X)-g(0)+(kappa/2)|X|_F^2
is rank-one convex on the entire cube [-R,R]^4 by the rank-one line second-derivative test. There
    -|X|_1-8delta <= g1(X) <= |X|_1+8delta+2kappa R^2.

### 4.4 Globalize without losing the Lipschitz normalization

Let B(X)=c|X|_1-D. On the boundary of the large cube,
    B-g1 >= eta R-D-8delta-2kappa R^2 >=4-epsilon/4>0.
On [-r,r]^4 the barrier is strictly below g1: B<=8r-16(r+1), whereas g1>=-4r-8delta. Define
    G=max(g1,B) on [-R,R]^4, and G=B outside.
The strict uniform boundary margin ensures continuity and local convexity on every rank-one line through the interface. The maximum of the two convex line restrictions is convex inside; the restriction outside is that of the convex barrier. Therefore G is globally RC. It equals g1 on [-r,r]^4 and G(0)=0.

On any coordinate line the convex restriction of G has asymptotic slopes ±c, since G agrees with B at large norm. Its secant slopes lie between those values. Changing matrix entries one at a time proves |G(X)-G(Y)|<=c|X-Y|_1 globally. Thus F=G/c belongs to K. For s in S0 use |w_s|<=4r and the mollification bound to conclude
$$
|F(s)-w_s|\le 8\delta+2\kappa r^2+4r\eta
\le \epsilon/8+\epsilon/8+\epsilon/4=\epsilon/2.
$$
This proves Theorem 2. Every operation is explicit (min of finitely many Lipschitz cones, convolution with fixed compact polynomial kernel, a quadratic repair, max and linear exterior). The construction is not a mere sampled-Hessian heuristic: the derivative and gluing bounds are part of the certificate. The uniform net is deliberately conservative; no claim of computational practicality or efficient dimension dependence is made.

## 5. One finite rational optimization covers ALL integrands at fixed geometry

For a fixed finite rational V, let S0 consist of 0 and all permitted triangle slopes X_t in [-r,r]^4; include every slope, not just those in one candidate filling. Denote the true worst normalized gap by
    m_* = inf {sum_t a_t n_t F(X_t): F in K, n a positive feasible integer filling}.
By Lemma 1 the graph variables are binary and sum a_t n_t=1. There is a flat feasible filling, so m_*<=0. Use the finite data polytope of Theorem 2 in place of F, and minimize
    sum_t a_t n_t w_(X_t)
over the same binary geometry and that polytope. This is a finite rational MILP: each product of a binary n_t and a bounded continuous w_(X_t) has an exact linearization. All bounds |w_s|<=|s|_1 are rational. Alternatively enumerate the finite graph choices and solve rational LPs. The optimum m_grid exists, and exact rational computation (rather than reliance on a floating solver) is possible by enumeration of feasible vertices or exact LP algorithms.

Restriction of a genuine F gives m_grid<=m_*. At a minimizing discrete pair, Theorem 2 supplies a genuine globally RC F whose error in its graph integral is <=epsilon/2, since area weights sum to one and F(0)=w_0=0. Therefore
$$
\boxed{m_{\rm grid}\le m_*\le m_{\rm grid}+\epsilon/2.}
$$
If the exact lower bound is nonnegative, ALL rank-one-convex integrands satisfy Jensen for this finite geometry (normalization handles any potential witness from an arbitrary RC energy; for a particular finite range use the linear-tail normalization and vertical rescaling, or the same construction of a bounded-deficit extension without changing the sign). If m_grid<−epsilon/2, the explicit repaired energy and selected positive filling are an actual strict planar counterexample. In between, the approximation does not decide exact zero.

This is more than a fixed polynomial/SOS search or a two-sided convergence assertion of unknown rate on the integrand side. At EVERY fixed vertex geometry, one explicit finite optimization achieves any prescribed positive accuracy over the entire normalized cone. For arbitrary bounded finite rational gradient data the same repair gives the analogous single LP estimate without geometry variables. However, the theorem does NOT bound the vertex set, heights, triangulation complexity or normalized magnitude of a possible counterexample away from zero. It is still not a finite exact decision of Morrey.

## 6. Practical joint search and exact lower bounds: executed controls

The uniform net in Section 4 is too large to enumerate with the present computational budget. A separate practical inner search jointly varies geometry and all coefficients of a quartic polynomial (including cubic and quadratic terms) in a fixed finite rational dictionary of globally LH-SOS factors. Affine and determinant gauges are omitted. At degree four the homogenized LH form has degrees (2,2,2) in (t,X),u,v, with 20 basic degree-(1,1,1) factors. The dictionary uses monomials, pair sums/differences, the exact sharp P2 factors, signed row/column permutations and transposition, and selected translated factors. There are 64 energy coefficients and 443 distinct rational square factors. The LP identities enforce h(P)=sum_j lambda_j q_j^2 with lambda_j>=0, l1 coefficient sum <=1 and Gram trace <=1. These last two bounds only normalize the cone. The dictionary is a restricted sufficient RC class, not the whole cone.

The MILP simultaneously chooses all positive triangles, at most one height per projected vertex, and the energy. Each face cost is a rational linear function of the energy coefficients. With the l1 coefficient budget, its absolute value is bounded by the largest absolute area-weighted monomial coefficient, so the binary-times-cost epigraph is exact. The explicit angle bound from Lemma 1, exact edge constraints, area and all five nonconstant minors constraints are included. No floating result is accepted as a positive lower bound.

For a numerical candidate, resolve the fixed-chain energy LP, rationalize the polynomial and nonnegative square weights, and compute the exact coefficient residual R=h(P)-sum lambda_j q_j^2. On the three unit spheres |R|<=||R||_1 (sum of absolute coefficients). The polynomial
    P_fixed=P+(||R||_1+margin)(|X|_F^2/2+|X|_F^4/4)
with rational margin>0 has a globally strictly nonnegative rank-one Hessian, because the radial Hessian dominates (1+|X|^2)|H|^2. After exact edge and mixed-minor checks, evaluate the same polynomial on the rational slopes with rational weights. This is a genuine negative-certificate format if the final gap is strictly negative; rounding alone cannot create one.

For finite positivity one can also use a proof tree of exact rational LP bounds. Put every row in the form Gx<=b with exact rational variable bounds l<=x<=u. For any rational y<=0,
    min c·x >= y·b + sum_j min((c-G^T y)_j l_j, (c-G^T y)_j u_j).
This follows by multiplying inequalities by their nonpositive multipliers, then minimizing the residual linear term over the box. An approximate numerical dual is only a suggestion; evaluate the displayed bound exactly. For infeasible nodes a Phase-I LP relaxes every inequality by a common t>=0; an explicit finite upper bound for t is obtained from worst row violations over the box. A strictly positive rational lower bound for min t certifies infeasibility. Branch on a free binary variable at each unclosed node, checking both children. A replay checker verifies every rational leaf bound and every disjunction, without calling a solver.

Actual executed results:
- small instance: numerical joint optimum 0; exact candidate gap nonnegative after repair. The final reproducible ordered-row exact proof tree has 121 nodes (60 branches, 61 lower-bound leaves), every weakest leaf bound exactly 0. Exact replay completed, and tests with deliberately corrupted rational bounds and signs rejected earlier regenerated certificates.
- four instance: 30-second joint MILP timed out with incumbent about −2.72e−13 and floating lower bound −0.08745. The fixed-chain LP gave zero, the exact radial repair gave positive gap 845657/41943040000000000. That numerical output does not certify the finite optimum. The exact geometric enumeration in Section 2 subsequently closed this entire finite vertex instance, for every RC integrand.
- Both independent exact enumeration runs completed. No strict negative actual gradient was found. A separate 20-triangle generic-map merge attempt hit its time budget; the result supplies no theorem.

The scripts, inputs and reports are preserved in the accompanying reproduction materials. These are actual finite tests of the new simultaneous search and exact replay; they are not evidence that all unrestricted geometries are laminates. The full degree-free finite-data optimization is a proved construction, not an executed large-grid campaign.

## 7. Remaining global gate

The outstanding mathematical step remains on the law/geometry side: a universal positive decomposition, or a uniform effective finite vertex reduction that preserves the possible strict negative gap. Do not resume an endless list of vertex counts, and do not declare Morrey solved by the finite controls. The next attempt should use the binary positive graph geometry and exact degree-free integrand repair to design a uniform mechanism or a genuine negative witness. No new Lean certification or priority claim. Unrestricted planar Morrey remains open.
