# Degree-one integer fillings: unrestricted BV trace and an exact integer-programming certificate

24 November 2026. This is a law-side advance, not an additional class of integrands. The previous [signed-trace theorem](IWANIEC_MORREY_SIGNED_TRACE_FOLD_TRANSFER.md) used smooth parametrizations and removed singular projections by analytic approximation. Here we allow **arbitrary compact integral 2-currents with the prescribed degree-one flat boundary**, including vertical faces, singular projections, multiple sheets, junctions, and arbitrary topology. The signed trace is BV, and the vertical faces pay exactly for the singular derivative.

Consequences:
* The exact ordinary cell infimum for EVERY continuous bounded-deficit chart energy equals the infimum over integer polyhedral fillings of one flat boundary with projection confined to the base square, for its canonical fold-penalized extension. Without confinement, strict-negative existence remains equivalent. Thus this geometry is complete for unrestricted Morrey after the earlier fixed-class normalization. No global invertibility or smooth parametrization is required.
* For fixed rational vertices and a certified RC energy, counterexample discovery becomes a **linear objective in integer triangle multiplicities with exact boundary incidence equations**. An optional arbitrarily small area term bounds the integers at each finite level. Strict negative fillings yield genuine planar graph witnesses by an explicit BV smoothing estimate. An exact boundary and interval-energy verifier is implemented.
* A concrete rational control shows an integrality gap of at least 1/10 between the real-coefficient relaxation and the integer filling optimum for an already verified quasiconvex kernel. The new approach must preserve degree one with integer multiplicity. Dropping integrality would force the false RC=>PC conclusion.

These are hand proofs, with an actually executed exact rational boundary/energy control. No new Lean proof, independent review, claimed unrestricted solution, or finite exact mesh cutoff. No MILP campaign discovering a negative filling is claimed.

## 1. Prior art and the geometric boundary of the method

Burago–Ivanov (2004), *Gaussian images of surfaces and ellipticity of surface area functionals*, and De Rosa–Lei–Young, *Construction of fillings with prescribed Gaussian image and applications*, Arch. Ration. Mech. Anal. 249 (2025), https://arxiv.org/abs/2401.10858 (Theorems 1.1, 1.5, 1.8, Proposition 3.2), establish that real-coefficient fillings, and Lipschitz multigraphs with unbounded multiplicity, can approximate general positive tangent-plane measures with the correct simple bivector mean. The ellipticity criterion for those enlarged competitors is polyconvexity. This is not ordinary Morrey. The real/integer distinction is already central in that work. De Gennaro–De Rosa, https://arxiv.org/abs/2510.24610, show that the approximation requires unbounded multigraph multiplicities; fixed multiplicity does not suffice. Burago–Ivanov also proved the special two-dimensional Busemann–Hausdorff area density has a convex extension (GAFA 2012, https://doi.org/10.1007/s00039-012-0170-y); it cannot generate the whole non-PC cone merely by convex closure.

The present deduction uses the earlier specific signed trace and penalty, not a claim that arbitrary graph-QC parametric integrands are elliptic for all integer surfaces. We prove the equality for one complete canonical extension class. No exhaustive priority audit of the BV trace argument or of integer optimization for this exact class has been performed.

## 2. Integer current signed trace including the singular derivative

Let Q=(0,1)^2 and A be any real 2x2 matrix. Let G_A be the oriented graph of y->Ay over Q, and T a compactly supported integral 2-current in R^4=R^2_y x R^2_w with boundary ∂T=∂G_A. In particular T can be a finite oriented triangle chain with signed integer coefficients. The proof only uses Stokes and the area formula; it does not assume the current is a graph or a single parametrized disk.

Extend T by adding the affine graph outside Q, obtaining a locally integral current S with ∂S=0 and coinciding with the full affine graph off a compact set. For the oriented unit simple tangent bivector xi of S, write
    a=xi12, L=[[-xi23,xi13],[-xi24,xi14]],
as in the [parametric compactification](IWANIEC_MORREY_PARAMETRIC_COMPACTIFICATION.md). Integrals over S below include its nonnegative integer multiplicity and oriented tangent; equivalently use each signed sheet with its multiplicity. Projection pi(y,w)=y is proper on the relevant supports locally, since S is flat outside a compact set.

**Degree:** pi#S is the oriented Lebesgue-plane current of multiplicity one. Indeed it is a locally finite top-dimensional current with zero boundary, so its signed density is constant by the distributional derivative equations. Outside a compact set that density equals one. By the unsigned area formula, for almost every y the nonvertical sheets have a finite positive count n_+(y) and negative count n_-(y), counted with integer multiplicities, and
    n_+(y)-n_-(y)=1.
Only the a!=0 part contributes to these counts. The projection of the a=0 part is Lebesgue-null by the area formula (up to a current-mass null set, which has no effect here).

Define v(y) to be the sum of the w-coordinates on the positive sheets minus their sum on the negative sheets. Locally integrable follows from the area formula applied to |w||a|, finite over compact projected sets. For any compact target test chi,
    int v_j chi dy = S(w_j chi(y) dy1 wedge dy2).
For derivative index 1 apply Stokes to w_j chi dy2, and for index 2 to -w_j chi dy1. Boundary terms vanish, giving the distributional identity
$$
\boxed{Dv=\pi_\#(L(\xi)\,\|S\|).}
$$
The mixed-minor component with column 1 is dw_j wedge dy2; column 2 is dy1 wedge dw_j. The notation on the right means a pushforward of a matrix-valued measure with the oriented L density, not the pushforward of the mass measure alone. It is locally finite since |L| is bounded on the unit bivectors. In particular v is BV_loc and v(y)=Ay outside a compact set.

For a nonvertical sheet at a.e. y let X_i=L_i/a_i. The absolutely continuous part of Dv is
    Z(y)=sum_positive X_i - sum_negative X_i.
This follows from changing variables with Jacobian |a_i|, hence L_i/|a_i|=sgn(a_i)X_i. The singular part is exactly the pushforward of the L density on the vertical part a=0. It is a finite matrix-valued measure locally. It may have cancellations, and it is not discarded. No statement that v is W^(1,1) for an arbitrary current is necessary.

For a polyhedral chain, the same proof can be read without general current machinery: Stokes on each affine triangle cancels internal edge terms because the boundary incidence equation is exact. Nonvertical triangles project affinely, vertical triangles project to lines or points; the resulting v is piecewise affine on the arrangement of all projected edges, with possible jumps. This is the computational case.

## 3. Full bounded-deficit envelope identity

Let C be a finite sublinear function on real 2x2 matrices, and W continuous with C-M<=W<=C for some finite M>=0. Use the earlier canonical extension
    Phi_W(xi)=a W(L/a) if a>0,
              C(L)-2Ma if a<=0.
As proved in the [signed-trace note](IWANIEC_MORREY_SIGNED_TRACE_FOLD_TRANSFER.md), it is continuous, positively 1-homogeneous on simple bivectors, and line convex iff W is RC. The following comparison needs neither RC nor QC.

Choose a large square Omega containing Q and all the non-flat support of the projected extension S strictly in its interior. Then
    E_Phi(S over Omega)<=E_Phi(T)+(|Omega|-1)W(A).
Equality holds for the termwise sheet representation. If overlapping oppositely oriented portions cancel as currents, the inequality follows since Phi_W(xi)+Phi_W(-xi)>=0: this follows directly from sublinearity C(L)+C(-L)>=0 and the bounded deficit with the negative-sheet penalty. The upper bound, not equality, suffices.
For almost every target y the nonvertical energy after area change of variables is
    F_y=sum_positive W(X_i)+sum_negative [C(-X_i)+2M].
If no negative sheet occurs, there is exactly one positive sheet and F_y=W(Z). Otherwise k=n_->=1, n_+=k+1. By sublinearity and the bounds,
    F_y >= sum_positive C(X_i)+sum_negative C(-X_i)+(k-1)M
        >= C(Z)+(k-1)M >= W(Z).
This is where integrality matters: k is either zero or at least one. Fractional positive sheets with no negative sheet need not give the desired Jensen inequality.

For the vertical part the cost is C(L), and sublinearity gives
    int C(dD^s v/d|D^s v|) d|D^s v| <= int_{a=0} C(L) d||S||.
For completeness, any finite sublinear C is the support function of a nonempty compact convex set of linear functionals. Testing the pushforward measure with continuous fields valued in that set and taking the supremum proves the stated total cost inequality, including possible cancellation. It is also the usual integral triangle inequality for a sublinear function of a vector measure. We obtain
$$
E_\Phi(T)+(|\Omega|-1)W(A)
\ \ge\
\int_\Omega W(Z)\,dy+\int_\Omega C(dD^sv/d|D^sv|)\,d|D^sv|.
\tag{1}
$$

Now smooth the actual trace, not the original chain. Put g=W-C, so -M<=g<=0 and g is continuous. Extend v-Ay periodically on Omega (it vanishes near the boundary), and convolve with a nonnegative symmetric smooth mollifier rho_epsilon. Then v_epsilon=Ay near the boundary for sufficiently small epsilon, and its gradient is (Dv)*rho_epsilon with periodic interpretation of the affine gradient. Sublinearity and Fubini give
    int_Omega C(Dv_epsilon) <= int_Omega C(Z)+int_Omega C(dD^sv/d|D^sv|)d|D^sv|.
By differentiation of measures, Dv_epsilon -> Z a.e.; in particular the singular measure contributes zero at a.e. Lebesgue point in this limit. Bounded convergence of g gives int g(Dv_epsilon)->int g(Z). Hence
$$
\limsup_{\epsilon\downarrow0}
\int_\Omega [W(Dv_\epsilon)-W(A)]
\le E_\Phi(T)-W(A).
\tag{2}
$$
No weak lower semicontinuity of W or unproved Morrey implication was used.

**Explicit polyhedral error.** If T is a finite triangle chain, include every projected triangle edge (and projected degenerate segment) in a finite list of line segments of total length ell and count N. For y farther than epsilon from this list the signed trace is affine on the convolution ball, so g(Dv_epsilon)=g(Z) exactly. Elsewhere the possible increase is <=M. For a mollifier supported in the epsilon ball, the total exceptional area is bounded by 2 epsilon ell+N pi epsilon^2. Therefore the right side in (2) has an explicit additive error at most M(2 epsilon ell+N pi epsilon^2), for epsilon small enough to keep the perturbation away from the boundary. A rational choice using pi<4 suffices to preserve any certified strict negative gap. The derivative may become large near jumps, but the smoothed map is a genuine smooth compact-boundary gradient. No assumption that the final gradient remains in the previous normalized ball is needed to refute QC.

**Theorem A (exact confined equality and unrestricted strict-negative equivalence).** Let q_W(A) be the infimum of integral_Q W(A+Dphi) over Lipschitz zero-boundary perturbations on Q (area Q=1). Then
$
\boxed{
q_W(A)=\inf\{E_{\Phi_W}(T):T\text{ compact integral 2-current},\ \partial T=\partial G_A,\ \pi(\operatorname{supp}T)\subset\overline Q\}
}
\tag{3}
$
and this equals the infimum over finite integer polyhedral fillings with the same boundary and projection confinement. Graph competitors give the upper bound, and smooth compactly supported tests approximate their energies, followed by PL approximation. In the confined case v=Ay outside Q. Smooth on an epsilon-expanded square whose area tends to one, apply (1)-(2) there, and rescale to Q preserving the gradients; dividing by the square's area tending to one proves the reverse inequality. Rational polyhedral competitors suffice for rational A by rational PL approximation with a flat boundary collar.

Without confinement, (2) gives the exact strict-negative equivalence:
    exists compact integral filling T with E_Phi(T)<W(A)
    iff there exists a genuine affine-boundary gradient with strictly negative Jensen gap at A.
Indeed choose a large square Omega containing the perturbation and rescale it to Q. Its gap is divided by |Omega|, but its strict sign is preserved. A negative graph is already a filling. We do not assert an undiluted equality of cell infima for unconfined fillings. This distinction is important. QED.

In fact every compact confined filling (not necessarily polyhedral) has the same comparison. Graphs with gradients approximated on a square by smooth then PL maps give the reverse inequality. The cell infimum is finite, since W>=C-M and the convex recession function has Jensen. All steps are for arbitrary continuous W with the stated recession bounds. For unrestricted Morrey apply the fixed-class normalization in the previous note; this does not require new symmetry assumptions.

## 4. A genuinely different finite search: integer triangle fillings

Choose a finite rational vertex set V in R^4 containing the four vertices of G_A, with rational A. Use every nondegenerate oriented triangle with vertices in V, with one reference orientation per unordered triple. Introduce nonnegative integer variables n_t^+,n_t^- giving copies in the two orientations. Let B be the signed edge-triangle incidence matrix (entries 0,+1,-1), and b the four-edge oriented boundary of the unit graph square. The exact compatibility constraint is
    B(n^+-n^-)=b.
This defines an integer polyhedral chain, not a matrix-law moment relaxation. Overlapping triangles and cancellations do not invalidate the comparison: the termwise sum of costs bounds the current's energy after cancellation whenever Phi(xi)+Phi(-xi)>=0, as is true for the canonical extension with C>=0, or directly use the signed sheet copies in the BV trace and Stokes proof. No manifold or triangulation-topology constraint is needed.

If xi_t is the oriented area bivector, i.e. half the wedge of its two edge vectors, put
    Psi(xi)=Phi_W(xi)+M a+eta |xi|, eta>0
with C>=0, as in the fixed normalized class. This is strictly positive for every nonzero simple xi and homogeneous. The term M a is linear in the bivector and integrates to M over every filling with the specified boundary. The Euclidean area term is nonnegative and its total is >= |m(A)| by the full oriented bivector mean identity (Stokes applied to each coordinate 2-form). Thus a strict negative gap for Psi implies a strict negative gap for Phi_W. The search is now
$$
\min_{n^\pm\in\mathbb N_0}\sum_t[n_t^+\Psi(\xi_t)+n_t^-\Psi(-\xi_t)]
\quad\text{s.t. }B(n^+-n^-)=b .
$$
The baseline is Psi(m(A)). The flat square is feasible with two triangles.

If all vertex coordinates have common denominator q, each nonzero xi has a component of magnitude at least 1/(2q^2), so each copy costs at least eta/(2q^2). A rational upper bound U on the flat energy bounds the sum of all multiplicities of every competing chain with cost <=U by 2q^2 U/eta. This is an explicit finite search bound **at this vertex level**, independent of a parametrizing map. For rational polynomial-tail energies the individual costs are algebraic; exact enumeration or rational interval bounds can certify a strict gap. An ordinary floating MILP can discover candidates, but its feasible/optimal status is not a mathematical certificate without exact boundary and cost checks. Nothing here gives a finite universal vertex-grid cutoff.

For the negative direction this is complete over rational vertices and rational certificate data. The [global certificate hierarchy](GLOBAL_CERTIFICATES.md) gives a strict rational-polynomial RC counterexample with a rational PL witness whenever Morrey is false, using smooth approximation and a strictification. Apply the earlier radial linear-growth extension: choose rational r<R enclosing the witness strictly inside radius r, shift the polynomial by a rational constant to make it nonnegative there, and choose rational c>0 so that the barrier c(|X|-r) strictly dominates the shifted polynomial on |X|=R. Set W0=max(P,c(|X|-r)) inside, barrier outside. Rank-one convexity glues on all rank-one lines by the strict boundary margin. If B0 is a nonnegative rational coefficient bound for |P| on radius R, W=W0-B0 obeys C-M<=W<=C with C=c|X| and M=cr+B0. It retains the same gap on the witness. Convert the periodic test to a rational PL compact-boundary test by the standard large-cell cutoff and rescaling, preserving the strict gap. Triangulate with rational vertices (a flat boundary collar can retain just the four corners). Its graph supplies a finite feasible integer chain with strict Phi gap. Choose rational eta>0 sufficiently small so the positive area correction retains the gap. The parameters are all enumerable and the exact global LH certificate can be replayed. Thus no counterexample is excluded by this search representation.

**What is different from the old nodal searches:** for a fixed integrand the geometry is a linear cost with integer compatibility constraints, allowing arbitrary faces and singular projections. The unknown nodal coordinates need not be optimized nonconvexly. All actual gradient witnesses are included by density over vertex sets. The BV trace is the soundness bridge back to single-valued planar maps. This is not a proof that arbitrary minor-compatible data are realizable.


### 4.1 Uniform geometric budget at any prescribed violation size

This additional bound applies to the entire fixed normalized class from the signed-trace theorem, not a particular energy or mesh. Write C(X)=|X|_F, M=1, A=0. Suppose a witness has gradient Frobenius norm <=1/2 and gap <=-epsilon, epsilon>0. The graph area satisfies
    |m(X)|^2=1+|X|^2+det(X)^2 <= (1+|X|^2/2)^2 <=(9/8)^2.
Thus its area excess is at most 1/8. Take eta=4epsilon (or a nearby positive rational number <=4epsilon). The new penalized gap is <=-epsilon/2. A strict witness can be placed on the unit square with affine boundary by periodic tiling, cutoff and arbitrarily small scaling/error, keeping the same bound up to an arbitrarily small margin. For example begin with any witness gap <=-epsilon, choose eta=2epsilon to leave spare error for that conversion; area-penalized negativity survives. Translation of the periodic potential by a constant and the gradient bound allow a fixed bounded ambient box for the original graph, after cutoff and scaling.

For a strict negative integer filling with eta>0,
    E_Psi(T)<Psi(e12)=W(0)+1+eta<=1+eta.
Since Psi(xi)>=|L(xi)|+a_-+eta|xi|, this implies
$
\int |L|\,d\|T\|+\int a_-\,d\|T\|+\eta\,\operatorname{Mass}(T)<1+\eta.
$
In particular Mass(T)<(1+eta)/eta and the excess number of negative projection sheets, integrated with respect to projected area, is bounded independently of mesh. The same bound is valid for the termwise mass of a certified chain. Its trace has total variation bounded by the mixed-minor budget (for confined projection at zero base), since Dv is the pushforward of L. This supplies a priori search constraints for every normalized potential violation of a fixed size. It bounds total area and weighted sheet count, NOT the number of small triangles or topology; a mass bound alone gives no energy-continuous finite lattice approximation for an unknown non-QC energy.

## 5. Exact integrality-gap benchmark: do not relax to real coefficients

Take the verified QC truncated determinant L0 as W, with C0=2|z| and M=1. The prior signed-trace note proves C0-1<=L0<=C0. Set
    Psi(xi)=Phi_L0(xi)+a+(1/16)|xi|.
The degree-one integer filling theorem, together with QC of L0 at 0, gives E_Phi(T)>=0 for every integer filling of the unit horizontal square. The linear a term is one, and the area term is at least 1/16. Thus its exact integral filling optimum is 17/16, attained by the flat square.

Take D=diag(1,-1), and the rational law with atoms
    D,-D,2I,-2I
of weights 2/5,2/5,1/10,1/10. Its mean and determinant moment are zero. For the angular area law put weights theta_i |m(X_i)| on the oriented unit bivectors m(X_i)/|m(X_i)|. Its bivector barycenter is e12. The L0 values are (-1,-1,3,3); the area norms are (2,2,5,5). Hence its Psi energy is exactly
    1-1/5+(1/16)(13/5)=77/80.
All four directions have rational slopes. Proposition 3.2 of De Rosa–Lei–Young (arXiv:2401.10858) constructs rational-coefficient polyhedral fillings of that same unit square approximating this angular area law in total variation. Theorem 1.1 identifies the relaxed infimum as well. It follows that the real-coefficient filling infimum is at most 77/80, so the integral optimum exceeds it by **at least 1/10**. The result uses the already verified L0 theorem, the new BV trace comparison, and the cited real-filling theorem.

Thus some sufficiently rich real-coefficient finite polyhedral fillings have negative Psi gap for a KNOWN QC W. Rational vertices can be obtained by consistently approximating each vertex after common triangulation and holding the boundary collar fixed, preserving the strict gap by continuity. No specific finite LP instance attaining 77/80 is constructed here. A failed real LP inequality or a negative high-degree filling divided by its degree is not a planar counterexample. The actual integer degree-one boundary is a nonnegotiable constraint. The arithmetic moment and energy identities were checked exactly with Python fractions.

## 6. Verification and next gate

The new [integer filling verifier](../../research/audit/integer_filling_exact.py) checks:
* exact rational coordinates, nonzero integer multiplicities, exact four-edge graph boundary, nondegenerate triangles, and the integrated simple-bivector mean;
* the verified truncated L or convex norm-minus-one controls, and a rational polynomial glued to a linear-growth tail after replaying the existing global LH certificate;
* rigorous rational square-root intervals via integer square root, and unpenalized and area-penalized energy gap intervals.

The actually executed default control is a flat square plus the oriented boundary of a rational tetrahedron, with three positive, one negative and two vertical faces. Its unpenalized gap is exactly 3/8 for truncated L. A flipped face and a fractional multiplicity were both rejected. The rational real-versus-integer gap control of Section 5 was also executed. The separate finite discovery driver integer_filling_search.py was run on the eight-vertex truncated-L control, with 102 oriented nondegenerate triangle variables and the rigorous multiplicity cap 3232. HiGHS returned objective 1.01, and exact verification gave unpenalized and penalized gaps both zero, with the two flat faces. This is a successful pipeline control, not a proof of lower bounds for new energies. No difficult-candidate MILP campaign, full rational-polynomial-tail replay, universal stress positivity or negative filling has been established.

**Remaining research target:** derive a uniform lower bound on the degree-one integer filling objective from line convexity, or find one globally RC integrand with a certified strict negative integer filling. The earlier angular positive-stress formulation remains equivalent, but this new formulation supplies an exact geometric optimization route with a genuine compatibility constraint. Try integer-valid inequalities or a constructive triangle simplification preserving the boundary, rather than endlessly increasing triangle counts. The explicit relaxation gap explains why an ordinary linear dual calibration cannot be the universal proof. There is no known accuracy-independent vertex, multiplicity, or triangle-count bound, and the unrestricted conjecture stays open.
