# Joint gradient-stress Hamiltonian flow: a rigorous 4x2-to-2x2 transfer test

24 November 2026. Unrestricted exact-zero attack after [cofactor duality](IWANIEC_MORREY_COFACTOR_DUALITY.md). This note uses the verified higher-dimensional negative results in a new way: the Hamiltonian is permitted to be rank-one convex on 4x2 matrices, not just a planar determinant or a planar convex function.

**Hand results.**
1. Every globally C11 rank-one convex Hamiltonian on 4x2 matrices generates a short-time nonlinear flow preserving rank-one convexity of **every** globally C11 planar rank-one convex integrand. The same flow preserves quasiconvexity if both the input and the Hamiltonian are quasiconvex. There are explicit safe time, Hessian, ellipticity and relative energy bounds. The old determinant-stress shear is a special case.
2. A strictly negative higher-dimensional Jensen gap on the joint gradient/cofactor-stress field of a planar QC equality state would give a genuine planar counterexample. More generally, a finite rational jet test compares the initial planar gap, the joint Hamiltonian gap, and a rigorous second-order error. It requires no numerical integration of the flow.
3. At equality the joint lift of ANY compact planar laminate is a 4x2 laminate. Thus an already known laminate cannot furnish a spurious higher-dimensional transfer. Hypothetical extremizers of the universal relative margin obey an additional necessary inequality for EVERY normalized 4x2 RC Hamiltonian.

**Limits:** this does not produce the requisite joint field, nor a universal contradiction at a critical near-equality sequence. It is a new concrete higher-dimensional counterexample route, not an implication from the existence of any 3x2/4x2 counterexample. The exact arithmetic verifier was executed on a deliberately misleading negative-first-derivative control and rejects the transfer; 27 exact tangent curvature controls also passed. No difficult higher-dimensional Hamiltonian campaign, strict negative planar witness, Lean verification or independent mathematical review. A brief prior-art search found related Hamilton-Jacobi convexity and rank-one geometric-flow work (e.g. https://users.math.msu.edu/users/yanb/rank-1-flow.pdf), but no exhaustive priority audit or novelty claim is made.

## 1. Hamiltonian graph flow and uniform time interval

Let X,p be planar matrices, with the Frobenius norm, and C X=cof X. In row-major vectorization C is a symmetric orthogonal involution; det X=(1/2)X:C X. Let K be a real-valued energy on 4x2 matrices, identified with pairs of planar matrices. Define
    k(X,p)=K([X; C p]),
where the semicolon stacks rows. Suppose Lip DF<=M, Lip DK<=N with M>=0, N>0, globally. At first take both functions smooth; the C11 case follows below.

Use the Hamiltonian system
    dX/dt=-k_p(X,p),   dp/dt=k_X(X,p)
with initial data (X_0,p_0)=(A,DF(A)). The canonical vector field is globally N-Lipschitz on R^8, since it is an orthogonal transformation of Dk. The graph projection A->X_t(A) is globally bi-Lipschitz on the explicit interval
    0<=t<=T0=1/[4N(1+M)].
Indeed for two trajectories the difference of their displacements differs from zero by at most (exp(Nt)-1) times the initial distance. Restricted to the initial gradient graph, the first-component displacement therefore has Lipschitz constant at most (exp(Nt)-1)(1+M)<=2Nt(1+M)<=1/2. The map is identity plus a contraction in the Lipschitz seminorm, hence has a globally defined inverse with Lipschitz constant at most two.

Define the evolved energy by its action along these characteristics:
    F_t(X_t(A))=F(A)+integral_0^t [k(X_s,p_s)-p_s:k_p(X_s,p_s)] ds.
Differentiating the action with respect to A gives DF_t(X_t(A))=p_t(A): the variation of the integrand is exactly the time derivative of p_s:delta X_s by the characteristic equations. Consequently at a fixed matrix argument Y,
    partial_t F_t(Y)=k(Y,DF_t(Y)).
The gradient Lipschitz bound is
    Lip DF_t<=L=2(1+M),
since the stress displacement has the same bound 1/2 and the inverse graph projection is 2-Lipschitz. The flow is thus a genuine globally defined classical Hamilton-Jacobi solution before the first possible folding of the characteristic graph. We do not make a claim about continuation after this interval or about weak solutions after shocks.

## 2. Rank-one convexity is invariant under the joint RC Hamiltonian

**Theorem A.** If F is RC on 2x2 matrices and K is RC on 4x2 matrices, then every F_t on the above interval is RC on 2x2 matrices. If F has a uniform positive LH margin m, then F_t has margin at least
    m exp(-N(2+3L)t).
There is no sign assumption on the Hamiltonian and no assumption that K is QC.

Proof for smooth functions. Along a characteristic let H=D²F_t(X_t), a symmetric 4x4 matrix. Differentiating the equations of variation of the graph gives the Riccati identity
    dH/dt=k_XX+k_Xp H+H k_pX+H k_pp H.
Equivalently, for any matrix R,
    R:(dH/dt) R = D²K(X_t,Cp_t)[(R,C H R),(R,C H R)].       (1)

The special planar fact is the Finsler decomposition H=c C+P with P>=0 whenever H is nonnegative on the C-null cone, i.e. the rank-one cone. Its non-strict version and proof by elementary PSD separation are recorded in [cofactor duality, Section 2.1](IWANIEC_MORREY_COFACTOR_DUALITY.md). At a unit rank-one R with zero curvature one has P R=0 and hence C H R=cR. The stacked matrix (R,cR) is rank one in 4x2. Therefore the right-hand side of (1) is nonnegative at every null LH direction, by RC of K on 4x2. This is exactly the tangent-cone invariance that requires the planar Finsler lemma.

For completeness, justify the invariance even at a nonsmooth boundary of the cone. Put ell(t)=min_{rank R=1, |R|=1} R:H R along the characteristic. It is locally Lipschitz and, at almost every t, its derivative is the derivative along a minimizing R (equivalently use the elementary one-sided min derivative rule on the compact set of R). The symmetric matrix Hbar=H-ell I is nonnegative on the rank-one cone, with zero curvature at R. Thus (R,C Hbar R) is rank one. The Euclidean norm difference from (R,C H R) is |ell|, while the respective norms are <=1+2L and <=1+L, because |ell|<=L. By the Hessian bound N for K, (1) gives
    ell'(t)>=-N(2+3L)|ell(t)|.
The negative part satisfies a Gronwall inequality and starts at zero. It is therefore always zero. Once ell>=0, the same inequality gives ell(t)>=ell(0) exp(-N(2+3L)t). This proves both assertions, using the rank-one line second derivative criterion.

For globally C11 F,K, convolve each in its matrix variables with smooth compactly supported probability kernels. This preserves their respective RC hypotheses and gradient-Lipschitz bounds; a strong LH margin is preserved as well. Their gradients converge uniformly on compact subsets. The globally Lipschitz characteristic flows, their uniformly bi-Lipschitz first projections and the actions then converge uniformly on compact sets to those of the original F,K. The resulting limit is C11 with the same bound L: the gradients are the limits of the characteristic stress fields, using inverse projection continuity. RC and strong RC pass to locally uniform limits. This proves Theorem A with exactly the stated safe interval.

**Sharper Hessian growth.** The same Riccati identity also gives ||dH/dt||<=N(1+||H||²). Hence, as long as the following angle is <pi/2,
    Lip DF_t<=tan(arctan M+Nt).
This follows by the scalar differential comparison for the upper right derivative of the operator norm, then by smooth approximation for C11. We will use this only near t=0 in Section 6.

The stress-only determinant Hamiltonian k(X,p)=det p has constant p and X_t=X_0-t C p_0; its action is F(X_0)-t det p_0. This is precisely the previous T_(-t) cofactor shear. The mixed null Hamiltonian k=-X:p yields X_t=exp(t)X_0, p_t=exp(-t)p_0, F_t(Y)=F(exp(-t)Y): relative curvature and gap merely rescale. Thus the new transformation genuinely permits more than these null flows, but does not pretend that simple scaling amplifies the normalized defect.

## 3. Quasiconvex Hamiltonians preserve quasiconvexity

Let the relative margin beta(F) be the infimum of the periodic Jensen gap divided by the squared L2 gradient norm over all bases and nonzero compatible gradients. Periodic W1,2 maps may be used for globally C11 functions because of quadratic-growth continuity. Similarly define gamma(K) for 4x2 energies. Recall the orthogonal decomposition of periodic planar matrix fields into constants P0, zero-mean gradients P, and zero-mean rowwise solenoidal fields Q. C maps Q onto P, by the Fourier rank-one identity.

**Theorem B.** If gamma(K)>=0, then on the safe interval
    beta(F_t)>=exp(-c t) beta(F) + gamma(K)(1-exp(-c t))/c
whenever beta(F)>=0, where c=4N(1+L). In particular F QC and K QC imply F_t QC. If K is strongly QC, the flow actually yields a positive quantitative QC margin at positive times. The claim is forward preservation, not backward preservation for a general K.

Proof for smooth energies. Fix a characteristic base B_t=X_t(A) and a mean-zero actual periodic gradient U, with E=int |U|²>0. Put
    p^0_t=DF_t(B_t), p^U_t=DF_t(B_t+U), q_t=p^U_t-p^0_t,
    W^0_t=(B_t,C p^0_t), W_t=(U,C q_t).
Define
    j(t)=[int F_t(B_t+U)-F_t(B_t)]/E.
As the base follows the characteristic velocity -k_p(B_t,p^0_t), the affine p term cancels in the derivative. The affine X term integrates to zero. Consequently
    j'(t)=int [K(W^0_t+W_t)-K(W^0_t)-DK(W^0_t):W_t]/E.     (2)
All base matrices at time t are reached by some A. Thus beta(t)=beta(F_t)=inf j(t). Since ||q_t||_2<=L sqrt(E), the derivative in (2) is bounded in absolute value by N(1+L)²/2. All the j's and hence beta(t) are uniformly Lipschitz in t. The estimates justify differentiation for W1,2 tests by dominated convergence (or first for bounded tests and approximation).

We need genuine spatial compatibility in (2) at a near minimum, not for arbitrary p fields. Fix the endpoint t, and take a sequence of bases and tests whose j(t) tends to beta(t). The energy H=F_t-beta(t)|X|² is globally QC by the definition of beta(t); its derivative bound is <=2L. On the Hilbert space of all affine-base periodic gradient fields Z, the functional
    I(Z)=int H(Z)-H(mean Z)
is nonnegative with derivative Lipschitz constant at most 4L. The descent lemma gives ||grad I(Z)||²<=8L I(Z). Apply it at B_t+U, and divide by E along the near-minimizing sequence. The affine-base gradient formula is exactly
    ||P0 q_t||_2 + ||P q_t-2 beta(t)U||_2 = o(sqrt(E)).
In particular, with W_c=(U,C Qq_t), W_c is an actual zero-mean 4x2 gradient, and
    ||W_t-W_c||_2 <= [2|beta(t)|+o(1)] sqrt(E).
This is where the 4x2 Hamiltonian is useful; we have two compatible 2x2 fields simultaneously. No minimizer is assumed to exist.

The same W_c can be used at all earlier times s sufficiently close to t, at their own joint bases W^0_s. Indeed the differentiated Hamilton-Jacobi equation at the moving base gives
    d q_s/ds =
        k_X(B_s+U,p^U_s)-k_X(B_s,p^0_s)
        +D²F_s(B_s+U)[k_p(B_s+U,p^U_s)-k_p(B_s,p^0_s)].
The global Hessian bounds give
    ||q_s-q_t||_2<=D(t-s) sqrt(E),  D=N(1+L)².
This estimate is independent of the base magnitude or gradient amplitude. The joint base is allowed to move arbitrarily; no uniform bound on its velocity is needed. Since W_c is compatible, its Bregman integral for K at ANY base is >=gamma(K)||W_c||_2²>=gamma(K)E. For the change from W_c to W_s use the C11 remainder bound
    |R_K(B,V)-R_K(B,V')|<=N(|V|+|V'|)|V-V'|.
The L2 norms of W_s and W_c are <=(1+L)sqrt(E). In (2) this gives
    j'(s)>=gamma(K)-2N(1+L)[D(t-s)+2|beta(t)|+o(1)].
Integrate from s to t and pass to the near-minimizing sequence at t, noting j(s)>=beta(s). The result is
    beta(t)>=beta(s)+[gamma(K)-c|beta(t)|](t-s)
                      -N(1+L)D(t-s)².                      (3)
At almost every differentiability time, take s->t from below. Then beta'(t)>=gamma(K)-c|beta(t)|. When beta(0)>=0 and gamma(K)>=0 the negative part stays zero by Gronwall. The resulting inequality beta'+c beta>=gamma(K) proves the claimed formula. The case N=0 is just an affine Hamiltonian/translation and is unnecessary for the nontrivial conclusion.

For C11 F and K with their stated nonnegative margins, smooth both as in Section 2. Convolution preserves QC, and also preserves the relative lower margins by averaging their translated Jensen inequalities. The smooth proofs have common safe time and constants. The evolved energies converge locally uniformly with common C11 bounds. Pass first on bounded-gradient tests, then extend to W1,2 tests. This completes Theorem B.

Thus the joint RC/QC evolution is controlled by the corresponding higher-dimensional convexity concept, not just an abstract positivity assumption on a pointwise Hessian. The available 4x2 RC non-QC energies are precisely the Hamiltonians for which this argument cannot simply invoke Theorem B.

## 4. A finite jet certificate for producing a planar counterexample

This is the constructive consequence, requiring only the RC hypotheses of Theorem A, not QC of K.

Given an actual planar periodic gradient U with base A, put p_A=DF(A). Translate and subtract affine tangents so the initial F and K have value and gradient zero at their respective bases:
    Fhat(X)=F(A+X)-F(A)-p_A:X,
    Khat(X,Z)=K([A+X; C p_A+Z])-K([A; C p_A])
              -DK([A; C p_A]):[X;Z].
These recenterings preserve RC and global derivative-Lipschitz bounds. Apply the flow to Fhat,Khat; its base zero stays fixed (both derivatives and values are zero there). Set
    E=int |U|², j0=J_F(A,U)/E,
    W=(U,C[DF(A+U)-p_A]),
    d0=int Khat(W)/E.
Here d0 is the joint BREGMAN gap, not necessarily Jensen against a compatible law when the original energy has a positive gap.

From (2) at t=0 and the time derivative bound for q_t, the relative gap of the evolved planar integrand obeys the exact estimate
$$
\boxed{\quad
\left|J_{Fhat_t}(0,U)/E-j_0-t d_0\right|
\le B t^2,\quad B=N^2(1+L)^3,\quad 0\le t\le T_0.
\quad}                                                     (4)
$$
Indeed the integrand derivative differs from its initial Bregman value by at most 2N(1+L)D t in normalized integral, by the preceding L2 bound, and integration in time gives B t². Smooth approximation gives the same estimate for C11 data, preserving initial values and gradients in the limit. The field U is not changed at all in this test.

**Corollary C (negative transfer).** If for any rational safe time t>0
    j0 + t d0 + B t² < 0,
then the evolved Fhat_t is a genuine globally RC planar energy violating QC on the original compatible gradient. In particular if j0=0 and d0<0, take any sufficiently small positive t with B t<-d0.

If the input F is QC and j0=0, the Hilbert stationarity identity in Section 3 is exact: mean DF(A+U)=DF(A) and the stress has vanishing zero-mean compatible projection. Hence W is a genuine compatible 4x2 gradient, with the correct base and zero mean. In this equality situation the affine term in the Khat average integrates to zero, so d0 is an ordinary higher-dimensional Jensen gap. A known higher-dimensional counterexample on exactly such a lifted law would therefore produce a new planar counterexample.

For positive j0, the strict test can still succeed, but a merely negative d0 does NOT suffice. It must pay the initial gap and the quantitative second-order error. In particular the simple scaling null Hamiltonian has negative derivative when applied to a positive quadratic planar energy and cannot yield a negative evolved gap. The exact regression control below exercises this distinction.

The repository has verified higher-dimensional RC/non-QC energies in [Sverak](../Sverak/README.md) and [Cassese](../Cassese/README.md); a 3x2 energy can be composed with any linear row map from 4x2 without losing RC. These are legitimate choices of K after bounded-Hessian extension. Their original witnesses are not automatically of the constitutive graph form W. No such realization is claimed.

### 4.1 Exact bounded-Hessian extension of polynomial inputs

The test (4) is a finite rational criterion for polynomial data. A globally RC polynomial P need not have bounded Hessian, but it can be replaced by a globally C11 RC function agreeing EXACTLY in value and first derivative with P plus a constant on any fixed compact witness range.

This construction works for any d x 2 matrix space. Take an integer r>=1 with the base and all tested matrices in the ball B_r, put R=2r, and bound |P|, |DP| and ||D²P|| on B_R by rational numbers B0,G0,H0 (the sum of absolute polynomial coefficients at entrywise radius R suffices, applying it to each derivative and summing). On B_R put U=P+B0+1, so 1<=U<=2B0+1. Let
    a=(2B0+3)/(3r²),   V=a(|X|²-r²).
Use the convex C11 smooth maximum
    smax(U,V)=(U+V+chi(U-V))/2,
    chi(s)=|s| if |s|>=1, (s²+1)/2 otherwise.
It is nondecreasing in each argument, equals the actual maximum when |U-V|>=1, and preserves RC by convex composition along every rank-one line. On B_r, V<=0 so smax=U. At the outer sphere V=2B0+3, hence V strictly dominates U by more than the smoothing width. Define the extension as this smooth maximum inside B_R and V outside. The strict collar makes the gluing C11 and globally RC. A rational global derivative-Lipschitz bound is
    M_P=max(H0,2a)+(G0+2aR)²/2,
by the Hessian product rule, 0<=chi''<=1 a.e., and |chi'|<=1. The bound remains valid after affine recentering. The shift constants cancel from all gaps.

Given rational polynomial F and K, a rational periodic PL gradient is a finite rational list of slopes with rational weights. All initial polynomial values and first derivatives, hence j0,d0 and the bounds M,N above, can be checked with rational arithmetic. Choose any rational t in the certified interval (or minimize the quadratic upper bound on [0,T0]). A strict negative upper bound proves existence of a globally C11 RC negative planar energy through the analytic flow construction. There is no need to approximate the evolved integrand by a polynomial or integrate a numerical ODE to certify the sign. The construction is a sufficient test, not a completeness assertion about low-degree polynomial inputs.

The exact standalone [joint_hamiltonian_gap.py](../../research/audit/joint_hamiltonian_gap.py) implements this direct certificate format. It requires rational polynomial coefficients and exact direct LH-SOS identities after rank-one substitution in 2x2 and 4x2, constructs actual periodic PL slopes from rational nodal data, checks the exact mean/determinant identities, evaluates the joint Bregman gap, computes the extension bounds and checks (4). Other exact RC certificate types or the known higher-dimensional theorems can also be used analytically; they are not implemented by this particular checker.

## 5. Universal lifting theorem for equality laminates

**Theorem D.** Let nu be a compactly supported planar laminate with mean A, and F any globally C11 planar RC function. If
    int F(X) dnu=F(A),
then the joint law of (X,C DF(X)) is a laminate on 4x2 matrices, with barycenter (A,C DF(A)).

Proof. First apply the laminate inequality after translating every matrix by the same h. The resulting nonnegative gap has value zero at h=0, so differentiability gives int DF(X) dnu=DF(A). For any globally C11 RC K on 4x2, the Fhat_t from Theorem A remains planar RC. The gap of Fhat_t on the translated nu is nonnegative for all small t, and its initial value is zero. The derivative formula (4) applies to this fixed compact probability law (its proof used only a zero mean and L2 estimates, not spatial compatibility). Therefore the joint Bregman gap for K is nonnegative. Its affine correction integrates to zero by the mean identity. For an arbitrary finite RC K on 4x2, first glue a convex linear-growth tail beyond a large compact ball, exactly preserving K on the joint law and base, as in the earlier unrestricted normalization, then convolve to obtain globally C11 RC functions converging uniformly on that compact set. Pass Jensen to the limit. This is the asserted laminate inequality for every finite RC K. QED.

In fact (4) proves a quantitative version for near equality. If nu is a compact laminate and J_F/E=j0>=0, then every globally C11 RC K on the joint space satisfies
    d0>=-j0/t-Bt   for every 0<t<=T0.
For j0 small enough that sqrt(j0/B)<=T0, optimize to get d0>=-2 sqrt(B j0). At equality take the limit t->0. The same estimate for an actual gradient law, if violated, produces a genuine planar counterexample by Corollary C. This gives a concrete certificate threshold, not a claim that every nonlaminate lift can be separated with a uniformly large gap.

The result treats every laminate, including those not described by a fixed-depth splitting tree. It explains why lifting an already settled planar laminate cannot automatically turn one of the higher-dimensional counterexamples into a planar counterexample.

## 6. Additional necessary inequality at a hypothetical universal extremizer

Let beta_*=-b be the universal normalized margin from [C11 optimal margin](IWANIEC_MORREY_C11_OPTIMAL_MARGIN.md), with b>=0. Take any extremizing sequence F_j, U_j with Lip DF_j<=1, F_j(0)=DF_j(0)=0, ||U_j||_2=1, and int F_j(U_j)->-b. For every sequence of 4x2 RC globally C11 K_j with Lip DK_j<=1 and value/gradient zero at zero, we obtain the necessary condition
$$
\boxed{\liminf_j \int K_j(U_j,C DF_j(U_j))\ge-2b.}           (5)
$$
Indeed apply Theorem A and (4) with the uniform safe interval, L=4 and B=125. The sharper Riccati Hessian bound and universal definition give
    int (F_j)_t(U_j)>=-b tan(pi/4+t)
for every sufficiently small fixed t>0. Compare this with the upper bound in (4), take liminf in j, then divide by t and take t->0. The derivative of tan at pi/4 is two. This proves (5) even when K_j is selected adaptively for the extremizing sequence.

The critical QC energies H_j=F_j+b|X|² have near-zero Jensen gaps and asymptotically compatible stress lifts (see cofactor duality). The joint field in (5) is NOT asserted to be compatible; its lower block differs from the critical compatible lift by -2b C U_j. Thus (5) supplies an additional exact constraint on the whole constitutive graph. It would contradict an explicit higher-dimensional Hamiltonian gap with liminf strictly below -2b in the same normalization. We have no proof of such a violation or of its impossibility. In particular it is not a gap-amplification theorem.

## 7. Actual verification and disposition

Executed exact script [joint_hamiltonian_exact.py](../../research/audit/joint_hamiltonian_exact.py), SHA-256 6082c1782026f572a8cbd24bb183ed82bf4dde0bd9c11eb63347812094bb9d88: verified the cofactor and canonical symplectic identities, the Riccati formula, 27 exact rational null-direction/4x2 rank-one curvature controls, the determinant-stress specialization and null scaling. An initial SymPy structural-equality check for a rational-symbolic scaling formula was corrected to check the simplified difference; the final run passed.

Executed exact [joint_hamiltonian_gap.py](../../research/audit/joint_hamiltonian_gap.py), SHA-256 0db47566ecff1df139d6b45ce54b9d68af789aaa62c9e2642c888491b5627ed7, on F=det+|X|²/4 and the mixed null Hamiltonian K(X,Z)=-X:C Z. The rational periodic 2x2 grid control has E=8, initial planar gap 2 and joint Bregman gap -4. The exact flow criterion correctly does NOT report a negative witness. A corrupted joint LH-SOS identity was rejected. This is an executed soundness regression, not a negative search over the verified Cassese or Sverak Hamiltonians. The polynomial bound and flow estimates are conservative; no numerical claim of efficient detection.

The principal next mathematical attack is the constitutive-graph test of Corollary C or the exact necessary condition (5), using genuinely higher-dimensional RC Hamiltonians, rather than another finite-mesh or integrand-subclass ladder. The general invariance and transfer theorem are proved here at hand level, but the requisite negative joint gap or a universal critical-state rigidity argument remains missing. No new Lean theorem or unrestricted Morrey resolution.
