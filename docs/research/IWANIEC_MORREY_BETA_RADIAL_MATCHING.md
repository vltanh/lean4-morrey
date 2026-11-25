# Direct improvement of the universal C11 Morrey margin by radial matching

24 November 2026. Return directly to the scalar beta_* of [R16](IWANIEC_MORREY_C11_OPTIMAL_MARGIN.md).

**Result (hand proof): -58/125 <= beta_* <= 0**, improving the previous -99/200 from [R17](IWANIEC_MORREY_COFACTOR_DUALITY.md). It holds for arbitrary globally C11 rank-one convex planar energies, all bases and all periodic W1,2 tests. The only special quasiconvexity input is the pinned verified truncated determinant; none of the later contact-law, stationary-lift, inner-shear or envelope-pinching arguments is needed.

The requested self-improving inequality beta_* >= theta beta_* with theta<1 is still unproved. This is a strict numerical improvement on the original global scalar, not a normalized gap amplifier, exact-zero proof, counterexample, or new Lean theorem. A small floating scalar-parameter exploration helped choose constants; the proof covers the entire continuum analytically. The exact arithmetic companion was executed.

## 1. Exact radial Taylor-kernel estimate

Normalize F(0)=DF(0)=0, Lip DF<=1, using Frobenius norms. For X and t>0,

    |F(tX)/t²-F(X)| <= |X|² |t-1|/(t+1).                (1)

Indeed h(s)=F(sX) has absolutely continuous derivative, |h''|<=|X|² a.e., and h(0)=h'(0)=0. Thus h(r)/r²=int K_r(s) h''(s) ds on the positive half-line, where K_r(s)=(r-s)_+/r² has mass 1/2. For 0<a<=b the two kernels cross at ab/(a+b) on their common support. The positive triangle of K_a-K_b has twice-area (b-a)/(b+a), so their L1 distance is exactly that value. This gives (1); the scalar estimate is sharp given only the second derivative bound, not necessarily under all additional planar RC constraints.

Also F(R)>=0 for rank R<=1, and F(X)>=-|det X|: decompose X=R+S into its orthogonal rank-one singular summands, and use F(X)>=F(R)+DF(R):S>=-|R||S|. No sign restriction on F is assumed.

## 2. Opposite-orientation pair estimate

Take nonsingular X,Y with d_X=det X>0 and d_Y=det Y<0. Let s_X,s_Y be their larger singular values and ell_X,ell_Y their smaller singular values. The polynomial det(X-tY) has a positive root t, since its constant term is positive and its leading coefficient negative. Every such root satisfies ell_X/s_Y<=t<=s_X/ell_Y: outside the interval a norm estimate shows invertibility and the corresponding orientation, by homotopy to X or -tY.

Put
    p=min(s_X/ell_X,s_Y/ell_Y), q=max(s_X/ell_X,s_Y/ell_Y),
    v=|log(s_X/s_Y)|, k=p+1/p.
Then 1<=p<=q and |log t|<=v+log q. The rank-one segment between X and tY has a singular mean with weights proportional to t²|d_Y| and d_X, respectively, because determinant is affine on the segment. Rank-one Jensen and nonnegative F at that mean give
    F(X)/d_X+F(tY)/(t²|d_Y|)>=0.
Scale the whole join by 1/t for a second inequality
    t² F(X/t)/d_X+F(Y)/|d_Y|>=0.
Using (1) in the better of the two, and |X|²/|d_X|=s_X/ell_X+ell_X/s_X, gives
$$
\frac{F(X)}{d_X}+\frac{F(Y)}{|d_Y|}
\ge-\min\{2,k\tanh((v+\log q)/2)\}.                      (2)
$$
The cap 2 is the elementary determinant bound. These rank-one joins are used only to compare pair energies. We do not assert that collapsing or rescaling portions of the original gradient law preserves compatibility.

## 3. One scalar inequality on the entire continuum

Set c=58/125, lambda=1/10. For all q>=p>=1, v>=0,
$$
\min\{2,(p+1/p)\tanh((v+\log q)/2)\}
\le c(p+1/p+q+1/q)+\lambda(v-(p+q)/2-2\log2).           (3)
$$
Proof. Write k=p+1/p, B(k)=sup_(z>=0)[min(2,k tanh(z/2))-lambda z], and G(q)=c(q+1/q)-lambda(q/2+log q). Substitute z=v+log q; it suffices that
    B(k)+lambda(p/2+2 log2)<=c k+G(q).

Case p<=5/4. B is nondecreasing and k<=41/20. Dropping the cap gives an upper bound for B(41/20) at y=tanh(z/2)=sqrt(37/41):
    (41/20)y-lambda log((1+y)/(1-y)).
The rational estimates 949/1000<y<19/20, exp(18/5)<1949/51 and log2<7/10 imply B(k)<127/80. Hence the left side is strictly less than 127/80+(1/10)(5/8+7/5)=179/100. On the other side log q<=q-1 and AM-GM give
    G(q)>=[(c-3lambda/2)q+c/q+lambda]
         >=2 sqrt(c(c-3lambda/2))+lambda.
The square root is greater than 381/1000. With k>=2, the right side exceeds 2c+2(381/1000)+lambda=179/100.

Case p>=5/4. For q>=p, G'(q)=c(1-1/q²)-lambda(1/2+1/q)>0, by c(1-16/25)>lambda(1/2+4/5). It suffices to set q=p and prove
    2c k-B(k)-lambda(p+log p+2log2)>=0.                  (4)
The maximizing y=tanh(z/2) for B is min(sqrt(1-2lambda/k),2/k). On the uncapped branch B'(k)=sqrt(1-2lambda/k)>=sqrt(9/10)>2c, so the left side of (4) decreases as p increases. There is one transition k=lambda+sqrt(lambda²+4), greater than k at p=5/4. It suffices to verify the capped branch including that transition.

On the capped branch B(k)=2-lambda log((k+2)/(k-2)). Inequality (4) becomes H(p)>=0 with
    H(p)=2c(p+1/p)-2-lambda p-lambda log(4p(p-1)²/(p+1)²).
In fact H>0 on all p>1. Its derivatives are
    H'(p)=2c(1-1/p²)-lambda(1+1/p+4/(p²-1)),
    H''(p)=4c/p³+lambda/p²+8lambda p/(p²-1)²>0.
Rational evaluation gives H'(147/100)<0<H'(149/100), and |H'(37/25)|<1/1000. The minimum lies inside that bracket. At p0=37/25 the logarithm argument equals 5328/24025. Since exp(3/2)<24025/5328,
    H(p0)>2c(p0+1/p0)-2-lambda p0+3lambda/2=1141/462500.
The tangent inequality at p0 bounds the minimum below by 1141/462500-1/100000=9091/3700000>0. This proves (3) globally. All rational and exponential estimates are checked by the companion script via rational Taylor sums and geometric upper bounds on the positive tails.

## 4. Integrate with genuine gradient compatibility

For an actual bounded mean-zero periodic gradient X put S=int ||X||op², E=int |X|². By the determinant null Lagrangian int det X=0. The determinant-weighted positive and negative measures on log s, s=||X||op, have common mass m=(1/2)int |det X|. Omit terms of zero determinant. If m=0, the nonnegative rank-one restriction already gives Jensen. Otherwise use the [logarithmic transport estimate](IWANIEC_MORREY_WEIGHTED_SPECTRAL_TRANSPORT.md), also derived in R17 Section 6.1:
    W1(mu_+,mu_-)<=S/2+2m log2.                            (5)

Briefly, the verified quasiconvex truncated determinant at each radius r and its reflected version imply
    |int_(s<=r) det X + int_(s>r)(r/s) det X|
        <=int_(s>r) r(s-r).
In log radius the left side is the absolute CDF difference of the measures smeared by negative unit-mean exponential noise. The integral of the right side in dr/r is S/2. Shift the smearing by log2 (the median of that noise's absolute scale); transporting each original measure to its smeared law costs at most m log2. The one-dimensional CDF formula and triangle inequality prove (5). All log first moments are finite for bounded gradients by the determinant weight. This is precisely the step using actual compatibility rather than only the determinant moment.

Lift an optimal log-radius coupling to a coupling pi of the determinant-weighted matrix measures, using disintegration on the radii. Its integral of v is W1. Denote the nonsingular and singular contributions to E,S by E_nz,E_0 and S_nz,S_0. Since |det X|=s_X ell_X,
    int (p+1/p+q+1/q) d pi=E_nz,
    int (p+q) d pi=S_nz.
Also E_0=S_0 and F>=0 there. Integrate (2) and (3) and apply (5):
$$
\begin{aligned}
-\int F(X)&\le\int\min(2,k\tanh((v+\log q)/2))\,d\pi\\
&\le cE_{\rm nz}+\lambda(W_1-S_{\rm nz}/2-2m\log2)\\
&\le cE_{\rm nz}+\lambda S_0/2\le cE.
\end{aligned}
$$
Approximate arbitrary W1,2 periodic gradients by smooth convolutions, using the quadratic growth and Lipschitz derivative for integral convergence. Translation to any base A, affine subtraction and scaling by M=Lip DF now give
$$
J_F(A,u)\ge-(58/125)M\int|Du|^2.                           (6)
$$
Thus beta_*>=-58/125. The upper bound zero follows by choosing the zero energy.

For a strong LH margin m0, F-(m0/2)|X|² is RC with Hessian bound M-m0: decompose an arbitrary matrix into orthogonal rank-one singular summands, reflect one summand, and use the sum of the two Hessian quadratic forms to bound the original Hessian below by (2m0-M)I. Apply (6) to the subtracted energy:
    J_F >= [m0/2-(58/125)(M-m0)] E.
In particular QC holds whenever m0/M>=116/241 (strict strong QC for strict inequality). This is a sufficient condition on arbitrary anisotropic energies, not a reduction of all possible counterexamples to that condition ratio.

## 5. Exact-zero target remains open

The determinant transport budget in (5) is independent of beta_*. Consequently the calculation gives a better absolute bound, NOT beta_* >= theta beta_* with theta<1. Applying the strong-margin corollary to the critical energy F-2 beta_* Q, Q=|X|²/2, only recovers the same bound. A genuine compatible residual decomposition or another normalization-preserving inequality is needed. The previous N18 local-collapse counterexample prevents simply declaring the matched pair residual a gradient law. No new equivalent reformulation or auxiliary gate is being counted as exact-zero progress.

The companion beta_radial_exact.py was actually executed: SHA-256 fe332136b42b43224919ae9926ef3953275e5140a052a480e8783a762e88b9b2; Git blob c0beea338216e7e3e1027181fe7bf1099577d360. All rational budgets and twenty exact Taylor-kernel controls passed. The scalar proof covers the full continuum rather than a sampled grid. No huge finite-mesh optimization, independent analytic review, Lean validation, or unrestricted proof was performed.
