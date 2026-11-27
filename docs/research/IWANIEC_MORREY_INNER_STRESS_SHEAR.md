# Maximum-defect contact measures and an exact inner-stress shear amplifier

24 November 2026. This attacks the rigidity gate after [quadratic-tail critical states](IWANIEC_MORREY_QUADRATIC_TAIL_CRITICAL.md). It changes the contradiction setup from critical stabilization (a possibly diluted sequence with relative gap tending to zero) to the maximum positive quasiconvex-envelope defect of one fixed smooth strongly RC energy.

**Hand results.**
1. Any hypothetical planar Morrey counterexample gives one fixed smooth uniformly strongly RC energy with quadratic exterior, a maximum-defect base, and a compact homogeneous gradient Young measure on its full six-row stationary lift. Its first block is supported entirely at envelope contact points a definite distance from the base. Thus there is NO absolute-variance dilution in this alternative. The stress means match the affine base, except that the energy-momentum block has an exact nonzero scalar shift. Exclusion of this shifted base from the full-lift gradient Young measure hull is equivalent to unrestricted Morrey for the stated complete energy class.
2. The energy-momentum block gives a new nonlinear **inner-stress shear**. Its exact local contact transformation preserves smooth uniform rank-one convexity on a common ball throughout a safe chart interval, in either time direction. No truncation or infinitesimal Hessian repair is needed within that chart. The transformation is different from the earlier outer cofactor shear; it acts on domain coordinates.
3. On the maximum-defect law, the positive gap magnitude D is transformed EXACTLY to D/(1-tD), on an actual compatible gradient law. The Hessian at the recentered affine base is unchanged. The entire lifted law transports, including the shifted energy-momentum mean. This is an absolute defect amplifier, not just a negative first-variation test.

**Remaining limitation.** The admissible chart time is controlled by the Hessian and witness-radius bounds, not just by D. An iteration approaching the pole t=1/D is not justified; chart folding, curvature growth and the extension normalization remain possible obstacles. In particular an increase in the absolute defect with unchanged *base* Hessian does not imply an increase in the universal Hessian-normalized relative deficit. No contradiction, strict negative planar witness, exact universal gap separation, or new Lean theorem is claimed. The algebra script was actually executed. These are hand proofs pending independent review. No exhaustive novelty claim; the cell-formula/gradient-Young-measure background and inner-variation conservation law are standard.

## 1. Exact bounded contact law at a maximum defect

Suppose a strict counterexample exists. By the smooth quadratic-tail extension in [the preceding note](IWANIEC_MORREY_QUADRATIC_TAIL_CRITICAL.md), we can choose a fixed smooth F with that negative witness, with Lip DF<=M<infinity, and exactly quadratic exterior
    F(X)=lambda |X|²/2+c+V(X), lambda>0, V smooth compactly supported.
We can additionally make F uniformly strongly RC: before extension add a sufficiently small positive quadratic preserving the strict gap; choose the tail curvature sufficiently large and use a smooth convex maximum. Subtraction of a common smaller quadratic commutes with the maximum, so its rank-one lower margin is preserved.

Let q=QF be the ordinary quasiconvex envelope, given by the cell formula
    q(A)=inf_u int F(A+Du)
over bounded periodic Lipschitz perturbations (unit-area torus). We use the usual periodic/domain equivalence and the quasiconvex-envelope cell formula for continuous finite energies with quadratic growth; the standard patching proof in [cofactor duality, Section 4](IWANIEC_MORREY_COFACTOR_DUALITY.md) applies here. The infimum is finite since F is bounded below by a quadratic minus a constant. Translating the same perturbation at every base shows q is M-semiconcave: the infimum of the concave functions int F(A+Du)-M|A|²/2 is concave. In particular q is continuous. No assertion of an attained cell minimum is required.

Let supp V be contained in B_r and |V|<=B. For |A|>r and V(A)=0,
    J_F(A,u)>= [lambda/2-B/(|A|-r)²] int |Du|².
Indeed nonzero V(A+Du) requires |Du|>=|A|-r, and the quadratic Jensen gap is lambda/2 times the variance. Hence F=q outside a fixed ball. The continuous nonnegative defect F-q attains a positive maximum D at some A.

Recenter at A and subtract the affine tangent:
    f(X)=F(A+X)-F(A)-DF(A):X.
This preserves RC, M, and the gap D; f(0)=Df(0)=0, Qf(0)=-D, and f-Qf<=D globally. Apply the scalar clipping theorem from the quadratic-tail note to a cell minimizing sequence at A BEFORE recentering. Its energy cannot increase and remains above q(A); its base stays A, and its gradients are uniformly bounded by a fixed radius. Thus after recentering there are actual mean-zero periodic compatible gradients X_j with |X_j|<=L and
    int f(X_j) -> -D.
They have a uniform positive variance: |f(X)|<=M|X|²/2 gives liminf int |X_j|²>=2D/M.

There is a stronger support exclusion. The concave function Qf(X)-M|X|²/2 has a supporting hyperplane at zero. Its slope is zero because it is touched there from below by f(X)-D-M|X|²/2, which is smooth with derivative zero. Therefore
    Qf(X)<=-D+M|X|²/2,
    f(X)-Qf(X)>=D-M|X|².                                  (1)
By quasiconvexity of Qf and the minimizing property,
    0<=int(f-Qf)(X_j)<=int f(X_j)+D ->0.
Take a subsequence of the probability laws of X_j converging on B_L. The limiting law is a homogeneous gradient Young measure, has mean zero and int f=-D, and is supported on {f=Qf}. Every point of that support satisfies
    |X|²>=D/M                                             (2)
by (1). In particular the limiting law is genuinely nontrivial, with no atom at the recentered base. This is not merely the earlier relative weighted measure that allowed a vanishing absolute variance. We changed the contradiction setup, and do not claim that all critical stabilized near-equality sequences can be undiluted.

We use the standard meaning of a homogeneous gradient Young measure: it can be generated by gradients with an affine boundary and arbitrarily fine oscillations. A weak limit of the spatial laws of uniformly bounded periodic affine-base gradients has this property, by fine periodic replication and cutoff to affine boundary, followed by diagonalization. Equivalently it satisfies Jensen for all quasiconvex test energies. See the gradient-Young-measure background in Voss et al., Numerical Approaches for Investigating Quasiconvexity in the Context of Morrey's Conjecture, https://doi.org/10.1007/s00332-022-09820-x, Section 6, and the original Kinderlehrer–Pedregal characterization. We will construct bounded actual gradients for the larger lift rather than infer compatibility from its minors.

## 2. Full lift with an exact vertical energy-momentum offset

Write p_j=Df(X_j), T_j=f(X_j)I-X_j^T p_j, C=cof and J=[[0,-1],[1,0]]. Put j_j=int f(X_j)+D, so j_j>=0 and j_j->0. All fields are uniformly bounded. Let P0,P,Q be the Fourier projections onto constants, zero-mean compatible gradients, and zero-mean rowwise solenoidal fields. The outer and inner variation estimates of the preceding full-lift and quadratic-tail notes apply at this minimum, with a changed constant energy reference.

For the outer equation, the Hilbert functional
    I(Z)=int f(Z)-f(mean Z)+D
on the subspace of all affine-base compatible fields is nonnegative by maximality of D. Its gradient is 2M-Lipschitz; at X_j its value is j_j. The descent lemma gives
    ||Pp_j||² + |mean p_j|² <=4M j_j.
The subtraction of f(mean Z) is important: mere minimization at the single base would not give the mean-stress identity. The inequalities extend to W1,2 tests by the quadratic growth and Lipschitz derivative.

For the inner equation, transport X_j by a periodic smooth domain diffeomorphism x->x+t xi(x), with mean base zero retained. The transported energy is at least Qf(0)=-D. Use the same second derivative bound 64 M int |X_j|² as in the full stationary lift note, but apply it to the nonnegative functional with constant D added. This gives
    |int T_j:Dxi| <=12 sqrt(M j_j int|X_j|²) ||Dxi||_infty.
The Lipschitz truncation argument in the quadratic-tail note (here ordinary absolute errors suffice) yields ||P T_j||_2->0, using bounded T_j. The linear domain transformations X_j B are also actual gradient tests on the transformed torus; for all invertible B their energy is at least -D, then extend by continuity to every B. The function B->int f(X_j B)+D is nonnegative with derivative Lipschitz constant <=M int |X_j|². Descent at I gives
    |int X_j^T p_j|² <=2M j_j int |X_j|².
Since int f(X_j)->-D, it follows that
    mean T_j -> -D I.                                    (3)

The cofactor rotation maps rowwise solenoidal fields to compatible gradients, and T_j J has the same property up to its mean. Therefore the six-row graph
    W_f(X)=[X; C Df(X); (f(X)I-X^T Df(X))J]
evaluated at X_j is L²-close to genuine gradients with affine mean [0;0;-D J]. We may enforce exactly this mean by adding a constant to the projected fields. The scalar bounded-replacement lemma of the preceding note, row by row on the zero-mean parts, makes all these genuine six-row fields uniformly bounded, without changing X_j and with error tending to zero. In this use the target rows are centered at their prescribed affine means; no claim is made that the raw Fourier projection is bounded in L-infinity.

Their weak limiting law is precisely the pushforward of the first-block measure by W_f, by continuity and the L² approximation on fixed compact sets. Hence:

**Theorem A (exact shifted-base characterization).** If Morrey is false, some smooth uniformly strongly RC f (after recentering the quadratic-tail energy) has a compact homogeneous gradient Young measure supported on its full six-row constitutive graph, with barycenter
$$
\boxed{\bar W=[0;\,0;\,-D J],\qquad D>0.}                  \tag{4}
$$
Its first block is supported on {f=Qf}, away from zero by (2), and int f=-D. This is a shifted base, not the graph value W_f(0)=[0;0;0].

Conversely if such a law exists for any finite smooth globally RC f with f(0)=Df(0)=0, even without the contact or separation property, its first-block gradient Young law gives a Morrey counterexample. In fact the mixed minors of X and C p in the six-row law imply int X:p=0: since both blocks have zero mean, all row-pair minors between them have zero mean, which is equivalent to the integrated row inner products of X and p vanishing. Trace the energy-momentum mean identity to get 2 int f-int X:p=-2D, so int f=-D. The standard generation of the first-block law, or a periodic bounded generating sequence, then gives a strict negative actual gradient gap. Thus excluding (4) on this complete normalized class is exactly the remaining rigidity target.

This formulation retains actual spatial compatibility and the support condition. Replacing the six-row homogeneous gradient Young measure by just its correct-minors moment constraints would be a strictly weaker problem; no completeness of that relaxation is asserted.

## 3. Inner-stress shear: exact contact transformation

For any smooth planar f set p=Df(X) and T=f I-X^T p as above. Define
    B_t(X)=I+t C T(X),    d_t(X)=det B_t(X),
    Y=Psi_t(X)=X B_t(X)^(-1),
    g_t(Y)=[f(X)+t det T(X)]/d_t(X).                       (5)
These formulas are used only on a regular chart where B_t is invertible and X->Y is a smooth diffeomorphism onto its image. This transformation is induced by changing the independent variables using the energy-momentum stress. It is not the earlier outer shear X+t C Df(X).

The exact transformed gradient and inner stress are
$$
\boxed{
p_t(Y)=Dg_t(Y)=\frac{p(X)B_t(X)^T}{d_t(X)},\qquad
T_t(Y)=\frac{T(X)+t\det T(X)I}{d_t(X)}.
}                                                         \tag{6}
$$
In particular
    C p_t=C p B_t^(-1),
    C T_t=C T B_t^(-1),
    T_t J=T J B_t^(-1).
The identity X^T p commutes with T and B_t^T follows from T=f I-X^T p and B_t^T=I+t adj T. This proves the formula T_t=g_t I-Y^T p_t once the derivative formula holds. The cofactor identities follow by multiplying out the two-dimensional adjugates.

Here is a direct proof of the derivative formula and rank-one preservation that does not rely on a global Hamiltonian continuation. Consider the contact Hamiltonian on independent variables (X,z,p)
    k(X,z,p)=-det(z I-X^T p)=-z²+z X:p-det X det p.
At fixed initial X, the rational formulas (5),(6) give a characteristic
    dot Y=-Y C T_t=-k_p,
    dot g=-g²+det Y det p_t=k-p_t:k_p,
    dot p_t=-p_t T_t=k_X+k_z p_t,
where k and its derivatives are evaluated at (Y,g,p_t). For the last identity use p_t Y^T p_t=(Y:p_t)p_t-det(p_t) C Y. The first two follow by differentiating d_t=1+t tr T+t² det T. These are identities of the rational expressions before assuming any derivative property of the transformed function. For a variation of the initial X the contact one-form residual
    alpha=delta g-p_t:delta Y
satisfies dot alpha=k_z alpha, by differentiating the characteristic equations and canceling terms. Initially alpha=0 by p=Df. Hence alpha=0 at every regular time; the derivative formula in (6) holds. Also at fixed Y,
    partial_t g_t(Y)= -det T_{g_t}(Y).
This is the exact contact evolution, with no integration error or auxiliary curvature repair.

The transforms compose additively in time within their common regular charts: B_s^{new}=I+s C T_t=B_(t+s) B_t^(-1). Substituting in (5),(6) gives the same energy and stress as a single time t+s. Both positive and negative times are allowed while the charts are regular. Nothing here guarantees regularity for all times.

### 3.1 An explicit safe local chart

Assume f(0)=Df(0)=0, Lip Df<=M, M>0. Choose R>0. On B_R, |Df(X)|<=M R, |f(X)|<=M R²/2,
    |T(X)|<=2MR²,    ||DT(X)||<=4MR.
Use Frobenius norms and their induced operator norms. For |t|<=1/(100MR²), B_t is within 1/2 of identity and has positive determinant, with ||B_t^(-1)||op<=2. Differentiating Psi_t gives
    D Psi_t[V]=V B_t^(-1)-X B_t^(-1) t C DT[V] B_t^(-1).
Therefore
    Lip_(B_R)(Psi_t-id)<=20 |t| M R²<=1/5.
Since Psi_t(0)=0, the map is injective on B_R and its image contains B_(3R/4): solve X=Y-(Psi_t(X)-X) by contraction on the closed ball, where for |Y|<=3R/4 the right side stays strictly inside B_R. The inverse is smooth on that common ball by the inverse function theorem. The formulas define g_t there for every time in the stated interval.

### 3.2 Preserve uniform rank-one convexity along the whole safe chart

Let H=D²g_t(Y) along a characteristic. Differentiate the contact Hamilton-Jacobi equation twice, and include dot Y=-k_p to cancel the D³g term. For a fixed direction R1 one gets the exact contact Riccati identity
$$
R_1:\dot H R_1=
D^2 k[(R_1,p_t:R_1,H R_1),(R_1,p_t:R_1,H R_1)]
+k_z H[R_1,R_1].                                         \tag{7}
$$
The derivatives of k here are ambient derivatives in (X,z,p). At a unit rank-one R1 with zero LH curvature for an RC Hessian H, use the planar Finsler lemma H=c C+P, P>=0, to obtain H R1=c C R1. The first derivative of T along the ambient vector in (7) is
    delta T=(p_t:R1)I-R1^T p_t-Y^T H R1.
Multiplying by J, its rows have the common row direction of R1, as in the full-lift note; hence det(delta T)=0. The second ambient directional derivative of T is -2R1^T H R1=0 because R1^T C R1=det(R1) I=0. Thus the first term of (7), a second derivative of -det T, is zero, and so is its second term. The cone tangent derivative is EXACTLY ZERO, not merely nonnegative. This holds for either sign of time.

To justify preservation on the entire regular compact chart, let ell(t)=min_{unit rank-one R1} H[R1,R1]. It is locally Lipschitz, and a.e. its derivative is obtained at a minimizing direction. Replace H by H-ell I to evaluate the ambient second derivative at a rank-one convex Hessian with a null direction. The preceding identity makes that term zero. Since k is polynomial and all X,g,p,H stay bounded on the compact regular family of characteristics from B_R, the change in (7) is at most C0|ell| for a uniform finite C0. Such boundedness of H follows directly from the derivative formula and the uniform inverse derivative bound on Psi_t. Gronwall, forward or backward, proves preservation of nonnegative LH curvature, and for initial strong margin m>0 gives ell(t)>=m exp(-C0|t|). The usual rank-one line criterion on the convex output ball gives local RC there. If needed, take closed balls strictly inside the stated chart; this avoids any endpoint issue in differentiating the inverse. No unproved smoothness of an evolved envelope is used.

Moreover g_t(0)=0, Dg_t(0)=0 and
    D²g_t(0)=D²f(0).                                     (8)
Indeed p=O(|X|), f=O(|X|²), T=O(|X|²), Psi_t(X)=X+O(|X|³) and g_t(Psi_t(X))=f(X)+O(|X|⁴). The exact equality of base Hessians follows.

For any compact witness range strictly inside this output ball, extend g_t globally as smooth strongly RC, with exactly quadratic exterior, by the same smooth convex maximum and strict collar gluing as in Section 1. Such gluing changes the energy only by an additive constant on the chosen witness ball (including zero). The global derivative Lipschitz bound of this extension can depend on t and the chosen ball; (8) does not bound that global norm.

## 4. Exact amplification on the maximum-defect law

Take the law of Theorem A, with first-block measure nu supported on B_L, full lift W_f, mean [0;0;-DJ]. In particular
    int f dnu=-D, int T dnu=-D I, int det T dnu=D².        (9)
The last identity is the determinant null Lagrangian of its third compatible block (det J=1).

Choose R>=8 max(1,L), and |t|<=1/(100MR²). All the pointwise charts above are regular. We show that the first-block law transported with the appropriate area weight is still a genuine homogeneous gradient Young measure, not merely a correct-minors measure. Use the bounded six-row compatible approximants from Section 2, with exact affine mean. Rotate the third two rows by J^T on the left to obtain actual compatible two-row matrices S_j, with mean -D I and S_j-C T(X_j)->0 in L². Here J^T(T J)=C T. In constructing the bounded replacement choose each centered row radius twice the bound of the corresponding row of C T(X_j)+D I. Since |T(X_j)|<=2ML² and D<=ML²/2, each such radius is at most 5ML² (or enlarge the bound slightly if necessary for approximation). Consequently ||S_j||op<=10ML². The estimate also holds in the limit and can be enforced by using a fixed larger R. The precise constants are not important but the uniform derivative bound is.

Let y_j(x) be the affine-plus-periodic map with derivative
    G_j=I+t S_j,
whose affine part is (1-tD)I. For these t, ||t S_j||op<=1/2 uniformly, so y_j is globally bi-Lipschitz, orientation preserving (identity plus a Lipschitz contraction), and is a bijection between the two flat tori. Let the three original compatible pairs of potentials be transported by composition with y_j^(-1). Their derivative on the target is the original stacked gradient multiplied on the right by G_j^(-1), by the Lipschitz chain rule. Since inverses and determinants vary Lipschitzly on this fixed compact regular matrix range, in the original coordinates those transported fields are L²-close to
    [X_j; C p(X_j); T(X_j) J] B_t(X_j)^(-1)
     = W_(g_t)(Psi_t(X_j)),
using (6). The first block has norm <=2L<=R/4, including the actual transported test, so the global extension of g_t can match all these values. The second and third block mean are now zero and -D J/(1-tD), respectively; this follows by transporting the affine parts of the potentials. The first block still has mean zero. A uniform spatial rescaling of the target square torus to unit size, and the corresponding potential rescaling to preserve gradients, gives ordinary periodic test maps.

The resulting exact limiting first-block probability law is
$$
d\nu_t(Y)= (\Psi_t)_\#\left(\frac{d_t(X)}{(1-tD)^2}\,d\nu(X)\right).
\tag{10}
$$
This follows by the area formula for the actual y_j and the L² approximation; the denominator is the area of the affine target fundamental cell. It is also verified algebraically by int d_t=1+t tr(mean T)+t² int det T=(1-tD)². The transported full lift is a genuine homogeneous gradient Young measure with the just-computed means. Thus, by (5) and (9),
$$
\boxed{
\int g_t\,d\nu_t=\frac{-D+tD^2}{(1-tD)^2}
=-\frac{D}{1-tD}.}
\tag{11}
$$
Since g_t(0)=0 and its smooth strongly RC global extension agrees up to a constant on the witness range, (11) is a strict negative Jensen gap on that law. A bounded generating gradient gives a strict actual witness as well. For positive safe t this defect magnitude is strictly larger than D; its derivative at zero is D². Negative safe t reduces it. This is an exact statement about the exhibited gap at the recentered base, not an equality assertion for the transformed global maximum envelope defect. That maximum is at least D/(1-tD).

The transformed six-row mean is exactly [0;0;-D/(1-tD) J]. Hence the shifted-base characterization persists under this regular shear; no repeated re-maximization is necessary to establish its algebraic composition as long as the single original chart remains regular. There is no need for the original measure to be attained by one minimizer.

## 5. What the amplifier does and does not prove

The pole in (11) occurs at t=1/D. A proof that the chart could remain regular and the global energy/gradient normalization be controlled up to a fixed fraction of that time, with constants independent of D, would be an important further advance. We have not proved it. The safe interval is of size 1/(MR²), while D/(MR²) can be arbitrarily small in the present reasoning. The pointwise coordinate map may fold or become singular well before the pole; the Hessian of g_t away from zero can grow through the inverse derivative. Local gluing does not control the normalized global Hessian either. It is therefore invalid to divide (11) by the unchanged BASE Hessian and claim a uniform bound for the universal relative-margin problem, or to iterate the Möbius formula across an unproved regular chart interval.

This is a different exact operation from the previous outer cofactor shear, which preserved the sup envelope gap. At a hypothetical maximum defect the inner shear amplifies the exhibited absolute gap, while retaining the actual full-lift compatibility. The maximum-defect setup also removes absolute variance dilution by (2), rather than assuming the original critical stabilization has nondiluted near-minimizers. The next exact target can now be formulated on a compact, support-separated, shifted six-row law with no unknown concentration tail. Exclude (4) using genuine compatibility and contact geometry, or find a valid normalization-preserving continuation/amplification mechanism. Neither is established here. Do not resume finite-mesh enumeration or assume an unlimited regular time interval.

## 6. Verification

The companion [inner_stress_shear_exact.py](../../research/audit/inner_stress_shear_exact.py) was executed locally with Python/SymPy. Four rational polynomial-jet controls check the exact transformed gradient, action, stress, contact characteristic equations, cofactor identities and additive composition. A symbolic null rank-one calculation checks that the contact Hessian derivative is zero on the LH boundary. Exact symbolic mean and defect identities and rational chart budgets also passed. These are algebraic controls only, not an independent review of the analytic proof or a constructed planar counterexample. No Lean verification or unrestricted solution.

## 7. Inverse-coordinate transport and the missing contraction

27 November 2026. The following are exact identities for an actual change
of independent variables. They record its interaction with stationary
energies and martingale dilations, and a compatible test on which every
nontrivial constant linear shear increases the Dirichlet energy. They do
not prove the fixed-period Jensen assertion R29, improve the universal
margin, or exclude all inverse-coordinate methods.

### 7.1 The positive chart, its weights, and the full stress

Use row Jacobians, the Frobenius inner product, and distinguish the
cofactor matrix $CZ=\operatorname{cof}Z$ from the adjugate
$\operatorname{adj}Z=(CZ)^T$. Let $u$ be a periodic Lipschitz map on
the unit-area planar torus, $X=Du$, and let $B$ be a constant real
$2\times2$ matrix. If
$$
 |t|\,\|B\|_{\rm op}\|X\|_{L^\infty,\rm op}<1,
$$
then $y=x+tBu(x)$ is a globally bi-Lipschitz degree-one change of
coordinates. Put
$$
 Q_t(Z)=I+tBZ,\quad \Delta_t(Z)=\det Q_t(Z),\quad
 \Psi_t(Z)=ZQ_t(Z)^{-1}.
$$
The transported potential $u_t=u\circ y^{-1}$ satisfies
$$
 Du_t(y(x))=\Psi_t(X(x)),\qquad dy=\Delta_t(X)\,dx.
$$
In two dimensions the useful polynomial identity is
$$
 \boxed{\ \Delta_t(Z)\Psi_t(Z)
       =Z+t\det Z\,\operatorname{adj}B.\ }                 \tag{12}
$$
Also $\Psi_t^{-1}=\Psi_{-t}$ on the corresponding matrix charts.
Since $\int X=0$ and $\int\det X=0$, one has
$\int\Delta_t(X)=1$. Thus the transported gradient law uses precisely
the probability weight $\Delta_t(X)$, with no extra normalization.

For a $C^2$ energy $f$ define, on that chart,
$$
 f_t(W)=\det(I-tBW)\,
        f\!\left(W(I-tBW)^{-1}\right).
$$
Then
$$
 f_t(\Psi_t(X))=\frac{f(X)}{\Delta_t(X)},\qquad
 \int f_t(Du_t)-f_t(0)=\int f(X)-f(0).                    \tag{13}
$$
The original Jensen gap is preserved exactly. For a rank-one matrix
$V$, writing $L=I+tXB$ and $Q=I+tBX$, its curvature is
$$
 D^2f_t(\Psi_t(X))[V,V]
 =\frac{D^2f(X)[L V Q,L V Q]}{\Delta_t(X)}.               \tag{14}
$$
Indeed, along a rank-one line in $W$, both
$\det(I-tBW)$ and $W-t\det W\,\operatorname{adj}B$ are affine.
The usual one-dimensional perspective differentiation gives (14).
The direction $LVQ$ remains rank one, so RC is preserved within the
positive chart. This does not furnish a global finite extension with
the original derivative-Lipschitz bound.

The full stress also has an exact transport formula. Let
$p=Df(X)$, $T=f(X)I-X^Tp$, and let $p_t,T_t$ denote the corresponding
quantities for $f_t$, evaluated at $\Psi_t(X)$. Direct differentiation
and the two-dimensional cofactor identities give
$$
\begin{aligned}
 p_t&=\frac{L^T(pQ^T-tf(X)B^T)}{\Delta_t(X)},&
 T_t&=\frac{TQ^T}{\Delta_t(X)},\\
 Cp_t&=(Cp-t\,\operatorname{adj}B\,CT)Q^{-1},&
 CT_t&=CTQ^{-1}.                                        \tag{15}
\end{aligned}
$$
These formulas retain the energy-momentum block. With the earlier
rotation convention, $CT=J^T(TJ)$, so using $CT$ instead of $TJ$
only applies a constant left rotation to that compatible block.

### 7.2 Stationarity identifies a first-order term, not its sign

The transported Dirichlet energy is
$$
 E_t=\int |Du_t|^2
 =\int\frac{|X+t\det X\,\operatorname{adj}B|^2}
                {1+t\operatorname{tr}(BX)+t^2\det B\det X}.
                                                               \tag{16}
$$
Consequently
$$
 E'_0=\int\left[|X|^2\operatorname{tr}(BX)
                    -2X:XBX\right].                    \tag{17}
$$
For $B=I$, (16) also simplifies to
$$
 E_t=\int
       \frac{|X|^2-2\det X}
            {1+t\operatorname{tr}X+t^2\det X},
$$
using $\int\det X=0$.
At a fixed matrix argument the generator of the energy transformation
is
$$
 k_B(X,f,p)=p:XBX-f\,\operatorname{tr}(BX).                \tag{18}
$$

Here is the exact stationary cancellation that can legitimately be
used. Suppose $H=f+b|\cdot|^2$ is QC at zero and $u$ attains equality
in its Jensen inequality. No attainment assertion for the universal
margin is being made. Differentiating the energy of $H$ under the
actual changes $x\mapsto x+tBu(x)$, in both signs of $t$, gives
$$
 0=\int\left[H(X)\operatorname{tr}(BX)-DH(X):XBX\right],
 \qquad
 \boxed{\ \int k_B(X,f(X),Df(X))=bE'_0.\ }               \tag{19}
$$
This follows directly from (17) and $DH=Df+2bX$. It identifies the
first-order correlation term; it does not imply $E'_0=0$ or cancel
the derivative of the normalized deficit.

For clarity, suppose additionally that global RC extensions matching
the transported witness range have derivative-Lipschitz bounds $M_t$,
with $M_0=1$ and a derivative at zero. Such extensions with this
normalization behavior are an additional hypothesis, not a consequence
of the local chart. If the initial gap is $-bE_0$, its negative
Hessian-normalized quotient is
$$
 \frac{-bE_0}{M_tE_t},\qquad
 \left.\frac{d}{dt}\frac{-bE_0}{M_tE_t}\right|_{t=0}
       =b\left(M'_0+\frac{E'_0}{E_0}\right).              \tag{20}
$$
Thus a negative sum in (20) would give a gain. Equations (13) and (19)
alone give no sign for that sum. The available extension argument
supplies no favorable first-order estimate for the global
derivative-Lipschitz bound.

### 7.3 The conditional determinant defect in an optimal dilation

The next calculation applies to any centered martingale coupling
$(X,Y)$ with $\mathbb E[Y\mid X]=X$ and
$\mathbb E\det X=\mathbb E\det Y=0$, and in particular to an optimal
dilation whenever these chart hypotheses hold. Write $R=Y-X$ and
$$
 e(X)=\mathbb E[\det R\mid X],\qquad \mathbb E e=0.
$$
For a probability interpretation assume a bounded common chart with
$\Delta_t(Y)>0$; in particular this holds for sufficiently small
$t$ if $X,Y$ are bounded. An unbounded optimal target is not thereby
placed in a positive chart at any fixed nonzero $t$.

Reweight the joint law by $\Delta_t(Y)$ and send $Y$ to
$\Psi_t(Y)$. Its total mass is one. From (12) and
$\mathbb E[\det Y\mid X]=\det X+e(X)$, the new marginal weight and
conditional barycenter are exactly
$$
\begin{aligned}
 w_t(X)&=\Delta_t(X)+t^2\det B\,e(X),\\
 m_t(X)&=
 \frac{X+t(\det X+e(X))\operatorname{adj}B}{w_t(X)},\\
 m_t(X)-\Psi_t(X)&=
 \frac{t\,e(X)\operatorname{adj}B\,(I+tBX)^{-1}}{w_t(X)}.
                                                               \tag{21}
\end{aligned}
$$
The conditional determinant defect of this reweighted coupling is
also explicit:
$$
 \mathbb E_t\!\left[
       \det(\Psi_t(Y)-m_t(X))\mid X\right]
       =\frac{e(X)}{w_t(X)^2}.                            \tag{22}
$$
To check (22), the conditional mean of $\det\Psi_t(Y)$ is
$(\det X+e)/w_t$. Subtract $\det m_t$; the numerator reduces to
$e$ by the two-dimensional determinant expansion.

For a finite rank-one tree contained in the positive chart, the
weighted projective image is again a rank-one tree: replace a child
weight $\theta_i$ by
$\theta_i\Delta_t(Y_i)/\Delta_t(Y_{\rm parent})$.
The determinant weight and the numerator in (12) are affine on each
rank-one segment, and the projective image preserves the rank-one
connection. This explains the laminate side of the calculation within
such a chart. It does not supply a global transport theorem for an
unbounded optimal target.

In particular, if $B$ has rank one, the source weight agrees exactly
with the actual spatial weight $\Delta_t(X)$, but the conditional
mean still differs by
$$
 m_t(X)-\Psi_t(X)
       =\frac{t\,e(X)\operatorname{adj}B}{\Delta_t(X)}.
$$
Such a scalar field times a fixed rank-one matrix need not be a
gradient. The martingale constraint for the actual transported
gradient therefore requires a further compatible repair. Neither
(21) nor (22) constructs that repair or proves it has favorable cost.

There is an explicit compatible-source control in which even the
correct-minor condition fails after this conditional correction.
Take $X=\operatorname{diag}(a,b)$, with independent uniform signs, and
$Y=\operatorname{diag}(2s,2r)$ with conditional probabilities
$$
 \mathbb P(s,r\mid a,b)
   =\frac{4+2as+2br+(ab+a)sr}{16}.
$$
They are nonnegative, $\mathbb E[Y\mid X]=X$, and the marginal of
$Y$ is the uniform product law on $\operatorname{diag}(\pm2,\pm2)$,
hence a laminate. Here $e(X)=a$, with zero global mean.
For $B=\operatorname{diag}(1,0)$ and $t=1/4$, all target
Jacobian weights are positive. The corrected barycenter and its
source weights are
$$
 m_t(X)=\operatorname{diag}
    \left(\frac{a}{1+ta},\,b+\frac{ta}{1+ta}\right),
 \qquad \frac{1+ta}{4}.
$$
This law is centered, but
$$
 \mathbb E_t\det m_t(X)=\frac{t}{1-t^2}=\frac4{15}>0,
$$
so it cannot be a centered periodic gradient law. The coupling is
**not optimal**: its source is already a laminate and has optimal
dilation cost zero. This is a control on the proposed transport rule,
not a countermodel to optimality in P20/P21 or to Morrey.

### 7.4 An actual gradient on which every constant shear raises the energy

Let $\tau$ be the periodic triangular function with derivative $+1$
on the first half-period and $-1$ on the second, and set
$u(x_1,x_2)=(\tau(x_1),\tau(x_2))$.
Its gradient is $X=\operatorname{diag}(a,b)$, with independent,
equiprobable $a,b\in\{-1,1\}$. This is an actual compatible
two-level laminate and $E_0=2$.

For each atom put $\delta=ab$, $\ell=aB_{11}+bB_{22}$, and
$d_{a,b}=1+t\ell+t^2\delta\det B$. Since $X$ is orthogonal,
$$
 \frac{|X+t\delta\,\operatorname{adj}B|^2}{d_{a,b}}
   =2+
     t^2\frac{|B|^2-2\delta\det B}{d_{a,b}}.
$$
Hence the exact energy change is
$$
 \boxed{\ E_t-2=\frac{t^2}{4}
     \sum_{a,b=\pm1}
        \frac{|B|^2-2ab\det B}{d_{a,b}}>0\ }              \tag{23}
$$
for every nonzero $B$ and nonzero safe $t$, for example
$|t|\|B\|_{\rm op}<1$.
All denominators are positive. Each numerator is nonnegative because
$2|\det B|\le |B|^2$, and the two determinant-sign numerators cannot
both vanish unless $B=0$. In particular
$$
 E_t=2+t^2|B|^2+O(t^3).
$$
For a conformal or anticonformal $B=\lambda O$, $O\in O(2)$, the
formula specializes to
$$
 E_t=\frac{2}{1-t^2\lambda^2}
 \qquad (|t\lambda|<1).
$$
Thus compatibility alone does not make a constant inverse-coordinate
shear decrease Dirichlet energy. This control has no negative RC
Jensen gap; it does not exclude a method that uses additional
correlations of an extremal energy, its stress, and its gradient.

### 7.5 Exact checks and remaining implication

The companion [inverse_transport_exact.py](../../research/audit/inverse_transport_exact.py)
checks the projective numerator and inverse, cofactor versus adjugate
conventions, full-stress transport, polynomial-jet chain rules and
rank-one curvature, the stationarity algebra, conditional moment and
determinant-defect formulas, and the all-$B$ triangular-gradient
control. Symbolic identities are checked with SymPy and finite
couplings with exact rational arithmetic.

These checks certify the displayed finite algebra, not a universal
extension bound, an optimal compatible repair, or QC for the R29 class.
The remaining issue is a favorable global normalization or another
genuine compatible operation using energy-stress correlations. No
unrestricted Jensen proof, improved universal bound, or Lean
declaration is asserted.
