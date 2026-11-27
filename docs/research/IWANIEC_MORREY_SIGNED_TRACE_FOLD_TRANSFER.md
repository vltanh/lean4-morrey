# Signed sheet traces: a folding-safe graph transfer, commuting envelopes, and a fixed unrestricted normalization

24 November 2026. **Unrestricted research, after compactification.** The previous [graph-bivector note](IWANIEC_MORREY_PARAMETRIC_COMPACTIFICATION.md) stopped at the need to handle noninjective chart changes. Here a signed sheet trace constructs an actual compatible gradient for *every* folded planar projection with invertible affine base, not a conditioning of its matrix law. The trace need not be Lipschitz, but its gradient is in L^1 and linear-growth quasiconvexity is sufficient.

Three results:
- A general folding-safe extension of any continuous energy between a finite sublinear function and that function minus a constant. It preserves both rank-one convexity and quasiconvexity, with QC interpreted on ALL parametrized periodic surfaces in R^4, and commutes exactly with both envelopes. Negative parametrized-surface witnesses can be converted into genuine graph witnesses with no increase in the scaled energy.
- Every strict unrestricted planar counterexample can be transferred to **one fixed compact class of rank-one convex integrands** with Frobenius-norm exterior, bounded deficit one, base zero, and gradients of norm at most 1/2. Thus the energy class used in the folding-safe transfer is complete for the unrestricted problem. There is no symmetry or homogeneity restriction on the original energy.
- The old flat-region E is fully quasiconvex, including folded and sign-changing determinant tests, by a sharper version of the signed-sheet argument for the known truncated determinant. This closes the remaining benchmark from the reset. It is not a new subclass ladder.

**Status:** analytic hand proofs. Exact mixed-minor, Piola, three-sheet and flat-profile algebra controls were executed in Python/SymPy. No new Lean proof, independent mathematical review or claim of priority. No unrestricted Morrey proof or accuracy-independent finite decision bound. The new transfer eliminates the folding issue for a canonical complete extension class *conditional on QC of the chart energy*: it does not infer QC from RC. Universal positivity of the compact curvature stress is still open.

Classical Shield inversion on GL+ and envelope commutation for invertible maps are known (Ball, 1977; e.g. Voss et al., https://doi.org/10.1007/s00332-022-09827-4, Section 6). The usual orientation-preserving formulation does not directly justify inversion through folds. The argument below uses the signed area formula and Piola cancellation instead. No exhaustive priority search for the trace/penalty theorem is claimed.

## 1. Signed trace across an arbitrary folded projection

Let U=(y,w):R^2 -> R^4 with
    y(x)=B x+psi(x), w(x)=D x+eta(x),
where B,D are real 2x2 matrices, psi,eta are smooth and Z^2-periodic, and det B>0. Initially assume det Dy is nonzero a.e. (the assumption will be removed in all integral conclusions). The map y is proper, since B is invertible and psi bounded, and has degree one by the proper homotopy from y to Bx. Almost every target point z is a regular value by Sard. Its inverse image is finite by properness and local invertibility. Write x_i(z) for all inverse branches at such a value and s_i=sgn det Dy(x_i). Then
    sum_i s_i=1.
In particular the number of positive branches is exactly one more than the number of negative branches.

Define a vector map on the regular values by
    v(z)=sum_i s_i w(x_i(z)).
The branch set at z+Bk is the translate by k of the branch set at z, with the same signs, for k in Z^2. Therefore
    v(z+Bk)=v(z)+Dk
almost everywhere. Local L^1 integrability follows from the area formula: for a compact target set K, integral_K |v| is at most integral_(y^{-1}(K)) |w(x)| |det Dy(x)| dx, finite by properness.

**Theorem A (signed trace gradient).** v is locally W^(1,1), and
$$
\boxed{Dv(z)=\sum_{x_i:y(x_i)=z}s_i\,Dw(x_i)(Dy(x_i))^{-1}}
$$
a.e. The periodic part v(z)-DB^(-1)z belongs to W^(1,1) on the target torus. Its mean gradient is DB^(-1).

**Proof.** For a smooth compactly supported scalar test chi on target space, the signed area formula yields
    int v_j(z) partial_k chi(z) dz
      = int w_j(x) det Dy(x) partial_k chi(y(x)) dx
      = int w_j(x) sum_l adj(Dy)_(l k) partial_l(chi o y)(x) dx.
The adjugate identity and chain rule prove the second equality even at singular derivatives. The columns of adj(Dy) have divergence zero (Piola identity, directly equality of mixed derivatives in dimension two). Integrating by parts gives exactly
    - int (Dw adj(Dy))_(j k)(x) chi(y(x)) dx.
Since det Dy is nonzero a.e., the unsigned area formula rewrites this as
    - int chi(z) sum_i (Dw adj(Dy))_(j k)(x_i)/|det Dy(x_i)| dz.
The displayed derivative is locally integrable: its absolute integral on K is bounded by integral_(y^{-1}(K)) |Dw adj(Dy)|. This proves W^(1,1) and the formula. In particular no unaccounted boundary distribution on a fold occurs. The mean derivative follows by the periodicity already proved. QED.

There is an exact integrated identity on the target cell Q_B=B[0,1)^2. For integrable branch costs g(x) periodic in x, the unsigned area formula on a fundamental domain gives
    int_Q g(x)|det Dy(x)| dx = int_(Q_B) sum_i g(x_i(z)) dz.
On the right use ALL lift preimages in R^2. Indeed apply the area formula over preimages of Q_B and translate domain lattice cells back to Q; periodicity and target lattice translation tile Q_B. Equivalently use the induced map between the two flat tori. The signed trace formula is invariant under these translations.

**Remove degeneracy for integral conclusions.** For a periodic Lipschitz U use trigonometric-polynomial approximations of its periodic parts, e.g. convolution by product Fejer kernels, preserving affine base and a uniform gradient bound, and converging in W^(1,p) for each finite p. Then det Dy is real analytic and has integral det B>0, hence its zero set has measure zero. The previous construction applies to each approximant, and continuous integrands on bounded original derivative ranges pass to the limit. We do not assert that the trace of the original map has an absolutely continuous derivative if its critical set has positive area. This distinction is essential.

## 2. A universal penalty allowing graph-coordinate folds

Use the notation of [parametric compactification](IWANIEC_MORREY_PARAMETRIC_COMPACTIFICATION.md). On the cone of simple bivectors let a=xi12, b=xi34 and L(xi)=[[-xi23,xi13],[-xi24,xi14]], so a b=det L(xi). For a parametrized U=(y,w),
    a=det Dy, L= Dw adj(Dy), b=det Dw.
In the chart a>0, xi=a m(L/a), where m(X)=(1,X12,X22,-X11,-X21,det X).

Let C be any finite sublinear function on real 2x2 matrices (convex, positively 1-homogeneous; not necessarily even). Let W be continuous, and suppose for a finite M>=0
$$
C(X)-M\le W(X)\le C(X)\quad\text{for every }X.
$$
Define the canonical oriented extension
$$
\boxed{
\Phi_W(\xi)=
\begin{cases}
a W(L/a),&a>0,\\
C(L)-2M a,&a\le 0.
\end{cases}}
\tag{1}
$$
It is continuous, finite and positively 1-homogeneous on the whole simple cone, including zero: on a>0 it is between C(L)-Ma and C(L). The constant 2M is an explicit sufficient fold penalty, not a claim of optimality.

Here parametric quasiconvexity means
    integral_Q Phi(partial_1 U wedge partial_2 U) >= Phi(U0 e1 wedge U0 e2)
for every affine-plus-periodic Lipschitz map U:R^2->R^4 of every affine base U0. This is an integral statement on single-valued parametrized maps, not a theorem about all integral currents, arbitrary multivalued graphs or arbitrary measures of bivectors.

**Theorem B.** (1) is line-convex on the simple cone iff W is rank-one convex. It is parametrically quasiconvex iff W is quasiconvex in the ordinary matrix sense.

### 2.1 Rank-one convexity

On a>0 every simple line yields the usual perspective of a rank-one segment in matrices. More explicitly, two points xi_i=a_i m(X_i) with positive a_i on a simple line have det(X1-X2)=0 (wedge polarization). The matrix quotient L/a on their segment is the weighted average of X_i with weights proportional to a_i. Apply RC of W. On a<=0 the extension is the restriction of the globally convex function C(L)-2Ma. On a>0 this convex function is a lower bound for Phi_W and equals it on a=0. Thus restrictions glue convexly along any crossing line: the right-hand slopes at the interface dominate those of the common convex lower bound, while the other half coincides with it. Lines lying in a=0 are covered by C(L). A line through zero is also covered by this argument when a is nonzero along it; alternatively the two half-line slopes are ordered because Phi_W(xi)+Phi_W(-xi)>=C(L)+C(-L)+Ma>=0 for a>=0. The reverse implication follows by restriction to m(X) along rank-one lines. QED.

### 2.2 Parametric quasiconvexity — arbitrary folds

Suppose W is QC. Its at-most-linear absolute growth permits the usual QC inequality for periodic W^(1,1) perturbations: approximate them by smooth periodic convolutions with gradients converging in L^1. Continuity and the linear growth bound give convergence of the energies by uniform integrability (or a subsequence and Vitali). The result also holds on any fixed lattice cell using the ordinary periodic/domain equivalence, or using tiling and a large-cell cutoff before the W^(1,1) approximation.

For affine base U0=(B;D) with det B<=0, the ambient convex function C(L)-2Ma touches Phi_W at the base and lies below it everywhere. The mean of every 2x2 minor of DU equals the corresponding base minor. Consequently convex Jensen proves the result at this base, including det B=0.

For det B>0 first use the analytic approximants of Section 1. At a regular target value z, denote
    T_i=Dw(x_i)(Dy(x_i))^(-1).
By the signed trace formula
    Dv(z)=sum_positive T_i - sum_negative T_i.
Under unsigned change of variables the original energy density on this fiber becomes
    S(z)=sum_positive W(T_i) + sum_negative [C(-T_i)+2M].
If there are k negative branches there are k+1 positive branches. If k=0, S(z)=W(Dv(z)) exactly. If k>=1, the bounded-deficit and sublinear inequalities give
$$
\begin{aligned}
S(z)&\ge\sum_+ C(T_i)+\sum_- C(-T_i)+(k-1)M\\
&\ge C(Dv(z))+(k-1)M\\
&\ge W(Dv(z)).
\end{aligned}
$$
All these quantities are integrable on Q_B: the original energy is bounded on the smooth original derivative range, and the trace derivative is L^1. Apply QC of W to the W^(1,1) trace with affine base DB^(-1), then change back:
    integral_Q Phi_W(partial_1 U wedge partial_2 U)
      >= integral_(Q_B) W(Dv)
      >= det B W(DB^(-1))
      = Phi_W(U0 e1 wedge U0 e2).
Now pass the original bounded-gradient approximants to the limit. No global inverse has been assumed. The converse is obtained by U(x)=(x,Ax+phi(x)), whose a is always one. QED.

This supplies an actual law operation at an arbitrary folded chart: for a smooth analytic original map, the integral gap for Phi_W is bounded below by the gap of a genuine signed-trace gradient, scaled by det B. Even when W is not QC, a strict negative parametrized-surface witness yields a strict negative ordinary graph witness after W^(1,1) approximation, since the same fiber inequality does not require QC. The negative-sheet penalty pays for branch merging, not for a conjectured rank-one splitting. It is an inequality for a special *extension* of arbitrary W, not a universal pointwise comparison for an arbitrary preexisting Phi.

**Nonnegative version.** When C>=0, add the bivector-linear term M a to (1). On a>0, Phi_W+Ma>=C(L)>=0; on a<=0 it equals C(L)-Ma>=0. Neither line convexity nor parametric Jensen gaps change by this addition. Thus the extension also lies in the nonnegative compact cone of the previous note.

### 2.3 Exact commutation of envelopes

For any continuous W with the stated bounds (whether RC/QC or not), define RW and QW as the pointwise suprema of globally finite RC and QC minorants of W. These envelopes are finite, since the convex lower bound C-M is admissible and W<=C. They are respectively RC and QC: a supremum preserves each Jensen inequality, and finiteness of RC gives continuity. In particular RW,QW obey the same bounds with the SAME C,M.

Define the parametric envelopes on the simple cone by suprema of continuous, positively 1-homogeneous line-convex and parametrically QC minorants. Restricting any such minorant to m(X) gives a corresponding ordinary minorant of W. On a>0 homogeneity therefore bounds it by a RW(L/a) or a QW(L/a), while on a<=0 it cannot exceed the original Phi_W there. Theorem B gives admissible parametric minorants Phi_RW and Phi_QW attaining these bounds everywhere. Hence
$$
\boxed{\mathcal R\Phi_W=\Phi_{RW},\qquad \mathcal Q\Phi_W=\Phi_{QW}.}
$$
The penalty and exterior C are unchanged. Thus allowing arbitrary folded parametrized surfaces does not change the graph quasiconvex envelope for this canonical extension. This is an exact all-energy statement under the bounded-deficit normalization, not a polynomial-order approximation.

## 3. Exact reduction of unrestricted Morrey to a single fixed compact class

The preceding transfer is sufficiently general to cover every potential unrestricted counterexample. In fact the following quantitative normalization is elementary.

**Theorem C.** Unrestricted finite-valued planar Morrey is equivalent to Jensen at base zero for every globally RC W satisfying all three conditions
$$
|X|_F-1\le W(X)\le |X|_F,\qquad
W(X)=|X|_F-1\ \text{if } |X|_F\ge3/2,\qquad
\|D\varphi\|_{L^\infty(F)}\le1/2.
$$
The last inequality is a restriction on the periodic gradient witness, not on the integrand. There is no exponent, angular symmetry or finite-wave hypothesis. The class of energies in the first two conditions that are RC is compact in the global uniform metric and uniformly Lipschitz with constant sqrt(2).

**Proof.** Given a strict counterexample (F,A,phi), translate and rescale the matrix argument to obtain a globally RC f_0 with a negative gap at zero witnessed by a periodic gradient bounded by one. Explicitly choose r>=max(1,ess sup|Dphi|), use f_0(Y)=F(A+rY) and phi/r. Add a constant to f_0 to obtain f>=0 on the closed Frobenius ball of radius 3. Let K=max on that ball f. Choose c>K+1 and define
    W0(X)=max(f(X),c(|X|_F-2))   for |X|_F<3,
          c(|X|_F-2)            for |X|_F>=3.
The barrier strictly dominates f at the interface, hence W0 is continuous and RC globally (on rank-one lines local convexity glues). It equals f on the witness ball, so has the same strict gap. Define
    S=sup_X (W0(X)-c |X|_F),    M=2c+S.
Then 0<=S<=K, since W0(0)=f(0)>=0 and outside the ball W0-c|X|=-2c. Moreover W0>=c(|X|-2). Thus
    c|X|-M<=W0(X)-S<=c|X|,
and equality with the lower bound holds outside radius 3.

Put lambda=M/c>=2 and W(X)=(W0(lambda X)-S)/M. It obeys the first two claimed inequalities, since 3/lambda<=3/2. Its gap at zero for phi/(r lambda) is the original strictly negative gap divided by M; the gradient bound is <=1/2. This proves the exact reduction; the converse is immediate.

For the Lipschitz assertion, on any unit rank-one line the two-sided norm-growth bound and ordinary convexity put every secant slope between -1 and 1, by comparison at positive and negative infinity. Decompose an arbitrary matrix difference into its two rank-one SVD terms; the change of W is bounded in absolute value by the nuclear norm of the difference, hence by sqrt(2) times the Frobenius norm. All such W coincide outside the fixed radius 3/2. Uniform boundedness on that ball, the Lipschitz bound, and closedness of all RC inequalities imply compactness by Arzela-Ascoli. QED.

Apply Theorem B to this single compact class with C=Frobenius norm and M=1. Every hypothetical unrestricted counterexample now has an exact nonnegative homogeneous extension
    Psi_W(xi)=a W(L/a)+a if a>0,
               |L|_F-a if a<=0,
which is line-convex and has a negative ordinary graph test. For this family the QC envelope in the graph chart is exactly the parametric QC envelope across all affine bases and folds. In particular one can work on a fixed compact angular domain with a fixed negative-chart formula, rather than inventing an independent homogeneous problem in each degree.

This normalization does not bound the oscillation complexity of the witness or the magnitude of a possible negative gap away from zero. Compactness alone supplies no effective finite exact decision. In particular it is not legitimate to assert that proving positivity for one fixed epsilon-net proves the conjecture. The next global problem is to exploit this fixed geometry to obtain a universal compatible-gradient Jensen mechanism (or a strict certified negative pair).

## 4. A sharper fold inequality for the verified truncated determinant

Let z(X) be the conformal part, s=operator norm, d=det X, and delta=d/s at nonzero X (zero at zero). The verified QC input is
    L0(X)=d(X) if s<=1,
            2|z(X)|-1 if s>1.
Write C0(X)=2|z(X)|=s+delta, a finite sublinear seminorm. For s<=1,
    C0-L0=s+(1-s)delta.
Since -s<=delta<=s, this lies between s^2 and 2s-s^2, hence in [0,1]. Outside the ball C0-L0=1. Thus Theorem B applies to L0 with C=C0,M=1 and negative sheet penalty 2. In particular the entire GL(4) orbit of the resulting continuous simple-cone integrand yields QC matrix energies: a linear change P of U preserves the class of actual affine-plus-periodic parametrizations, and its bivector action is exterior square Lambda^2 P. Restrict back to ordinary graphs. This produces known-QC generators with genuine variable projective chart changes, much larger than just translations and left/right changes in matrix space. It does not prove they generate every RC integrand.

For the *natural* truncated determinant extension (penalty 1, not 2),
    Phi_L^nat(xi)=a L0(L/a) if a>0,
                  C0(L)-a if a<=0,
a stronger fiber inequality holds when the second projection w has nonnegative determinant a.e. For a positive branch, det T_i>=0 in that case, and L0(T_i)>=0: inside the unit ball this is obvious, outside C0(T_i)>=s(T_i)>1. The negative branch cost C0(-T_i)+1 is at least one. If there are k>=1 negative branches, then S(z)>=1. On the other hand for any number of branches, the deficit bound L0>=C0-1 and subadditivity give
    S(z)>=C0(Dv(z))-1.
If s(Dv)>1, the latter is exactly L0(Dv). If s(Dv)<=1, L0(Dv)=det Dv<=1, so the former bound suffices when k>=1. When k=0 the energy is exactly L0(Dv). This proves the required pointwise comparison. For a particular w=x no approximation of w is needed, so the nonnegative-determinant hypothesis is retained in analytic approximations of y.

**Important limit:** the penalty-one proof does not apply to arbitrary w, since positive projection branches can have negative det T_i. The penalty-two version above is valid with no such assumption. The penalty-one pointwise comparison can fail for arbitrary fiber data: two positive T_i=J,-J, J=diag(1,-1), and one negative T_i=0 give sum of costs -1 but trace gradient zero with L0(0)=0. This is an algebraic illustration of the missing hypothesis, not a parametrized or planar counterexample.

## 5. Complete all-base quasiconvexity of the original flat-region example E

Consider the graph swap of the natural extension, now as a matrix energy
$$
H(X)=
\begin{cases}
1,&\delta(X)\ge1,\\
2|z(X)|-\det X,&\delta(X)<1 .
\end{cases}
$$
It is continuous, since s+delta-d=1 at delta=1. At any positive-det base A, apply the preceding sharper signed-trace argument to U(x)=(u(x),x), u=Ax+phi, so y=u and w=x. Here the base of the second projection is I, det Dw=1 everywhere. On a positive sheet the original cost H(X)/d(X) is L0(X^(-1)), because s(X^(-1))=1/delta(X); on a negative sheet H(X)/|d(X)|=C0(-X^(-1))+1, since the conformal norm of the planar adjugate equals that of the original matrix. These are exactly the fiber costs above. Thus
    integral_Q H(Du) >= det A L0(A^(-1)) = H(A)
for every analytic affine-plus-periodic u with det A>0, and then every bounded periodic Lipschitz gradient by approximation. There is no sign condition on det Du. If det A<=0, H coincides at A with the globally PC minorant 2|z(X)|-det X; H dominates this minorant everywhere because on delta>=1 the difference is (s-1)(delta-1)>=0. This proves H is globally QC at every base.

Now recall
    E(X)=0 on delta>=1,
         (1-delta)(s-(1+delta)/2) on |delta|<=1,
         -2d on delta<=-1.
As recorded in the prior flat contact note, E+1>=H everywhere with equality on delta>=1. In the central sector the difference is (1-delta)^2/2; in delta<=-1 it is 1-delta-s(1+delta)>=0. Thus at every expansive positive-orientation base E has the touching QC minorant H-1. At every central-sector base |delta(A)|<=1 use the convex-plus-null-Lagrangian support C_h(X)-d(X)-1/2 from [FLAT_CONTACT_RESOLUTION](IWANIEC_MORREY_FLAT_CONTACT_RESOLUTION.md), where C_h=s+h(|delta|) and h(t)=t^2/2 for t<=1, t-1/2 otherwise. Its convexity follows as the supremum of (1-k) op norm+k nuclear norm-k^2/2, 0<=k<=1. It touches throughout that sector and lies below E everywhere. Finally E(JX)=E(X)+2det X for the reflection J=diag(1,-1), so the result at expansive negative-orientation bases follows by reflection and determinant cancellation.

**Corollary D.** The entire finite nonhomogeneous isotropic energy E in the reset's hard flat-region example is quasiconvex on real 2x2 matrices, at every base and for arbitrary planar Lipschitz gradient tests. Its anisotropic homogeneous blow-up E2 was already closed by the previous translated-kernel proof. This uses a folded-map compatible trace, not an unsupported vector-valued contact-set assertion. The older support-class impossibility theorem concerned its specified generators/operations, not the present graph-swap QC construction.

## 6. Next universal gate and verification

The signed trace is an exact geometric operation for arbitrary folded charts. It resolves the inverse obstruction for the canonical bounded-deficit extension and, with the sharper branch budget, for the natural graph swap H. We have not obtained a positive curvature stress for arbitrary line-convex Phi on the compact section. An unrestricted proof cannot assume that an arbitrary transformed energy obeys the branch budget (in particular the exact degree count alone does not control nonlinear determinants of sums). The compact normalization in Section 3 permits working with a fixed complete energy class, but Theorem B still needs QC of W to give QC of its extension. We do not use that implication in reverse to assume the desired answer.

A promising next route is to use the new all-chart QC kernels (penalty two) in a genuinely global support or positive-stress argument on S^2 x S^2. The earlier affine-L support-cone no-go does not automatically apply to these projective generators. Conversely their completeness is not proved. Any such next attempt must preserve the entire class in Section 3 and supply the missing all-law inequality; no further isolated benchmark class is an active completion gate.

The accompanying [exact checker](../../research/audit/signed_trace_exact.py) was actually run using Python and SymPy. It verifies the mixed-minor relation L=Dw adj(Dy), Piola cancellation, the flat-sector identities, and a rational three-sheet folded degree-one example (trace derivative 7/6 on the triple region, integrated truncated-determinant lower bound 10/9 versus affine value 1). These are algebra controls, not independent verification of the analytic proof. No Lean validation of the new theorems or resolution of unrestricted Morrey is claimed.
