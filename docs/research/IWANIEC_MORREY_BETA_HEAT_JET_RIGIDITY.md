# Strictness of the acoustic margin and an exact limitation of the full quadratic-jet relaxation

24 November 2026. Direct continuation of [P15](IWANIEC_MORREY_BETA_ACOUSTIC_HEAT.md), keeping the original normalized universal relative margin beta_*.

**Results (hand proofs).**
1. For globally C11 planar RC energies with Lip DF<=1, the inequality beta_* >= -1/8 from P15 is strictly improvable. The proof uses the simultaneous action of the two exact heat stresses on the Hessian of the SAME integrand. Local saturation in P15 forces a special acoustic projector Hessian and a strictly negative discrepancy between the two heat actions. This is inconsistent with their integrated equality. A conservative explicit bound is beta_* >= -1/8+10^(-38) (Section 3); the quantitative constant is not optimized. The strictness proof requires the full Hessian bound, not just the rank-one sandwich of P15.
2. There is an exact rational artificial jet distribution attaining cost -1/10 in the strengthened relaxation with the full Hessian bound, local RC, all componentwise constant-coefficient quadratic Hessian covariance identities, and all constant-target-matrix/spatial-index weighted heat identities (Section 4). Thus these algebraic conditions alone cannot establish exact zero. This is not a compatible gradient, a single integrand's jet distribution, a counterexample to Morrey, or a bound on beta_* in the other direction.

**Disposition.** No self-contraction beta_*>=theta beta_* was obtained. Attempts to interpret the signed heat residual as a smaller compatible gradient test remain unjustified. We should not spend another series of turns optimizing this finite-dimensional algebraic relaxation: a stronger ingredient involving the common constitutive integrand or actual compatibility of the evolving fields is necessary. No new Lean theorem, independent review, numerical counterexample, or priority claim. The companion exact script was actually executed; the strictness proof is analytic.

## 1. Two exact heat actions and local equality characterization

For smooth F and u, use the notation of P15: X_s=A+Du_s, u_s=exp(s Delta)u; B_ij=partial_ij u_s in R², g=sum_i B_ii, H=D²F(X_s). Write B^a for the symmetric spatial Hessian matrix of target component a. Define the matrix-valued heat stresses on R4 (with Frobenius-vectorized planar matrices)
    M_h=sum_(k=1,2) H_k tensor H_k, H_k=D partial_k u_s,
    S_(ai,bj)=(g_a B^b_ij+g_b B^a_ij)/2.
We reserve H for the integrand Hessian, not H_k. The two heat identities give
    int_space H:M_h=int_space H:S
for each s>0, by integration by parts. Their time-space integrals equal the Jensen gap J_F. Also int_space |B|²=int_space |g|² and int_time,space |B|²=E/2, where E=int|Du|².

Let G=|g| and W=|B|²-|g|²/2. At each point rotate the target so g=(G,0); if G=0 the signed action is zero. For G>0 write
    B^1=G I/2+P, B^2=Q
with P,Q symmetric trace free, so W=|P|²+|Q|². In row-major matrix coordinates let A be the first diagonal target block of H, K its upper-right target block, B0=(K+K^T)/2. Put
    x=tr(A)/2, y=tr(B0)/2, A_d=A-xI, B_d=B0-yI,
    U=(A_d,B_d), Z=(P,Q).
For a unit spatial n the acoustic matrix is PSD and <=I, since H is RC and ||H||op<=1. The proof of P15 gives
    |A_d|²<=2x², |B_d|²<=2x(1-x).
Set e=2x-|U|²>=0 and local excess
$$
\delta=H:S+W/2=\tfrac12|Z+G U|^2+\tfrac12G^2 e\ge0.       (1)
$$
We now characterize equality using the full Hessian bound.

For G=0, equality requires W=0. For G>0, equality gives Z=-G U and e=0. If W=0, then U=0 and x=0. To treat W>0, diagonalize A by a spatial orthogonal change. Equality |A_d|²=2x² implies A=diag(2x,0), with 0<x<=1/2. Write B0=[[y+z,w],[w,y-z]]. For a direction n maximizing the trace-free quadratic form of B_d, the perpendicular-direction inequality is saturated. In detail, let a=n^T A n, a'=n_perp^T A n_perp, b=n^T B0 n, b'=n_perp^T B0 n_perp, and k²=z²+w². The nonnegative defects a-a²-b², a'-(a')²-(b')² from the acoustic contraction satisfy
    x(1-x)-k² = (a-a')²/4+y²+
                [(a-a²-b²)+(a'-(a')²-(b')²)]/2.
Thus y=0. The acoustic bound at n=e2 now gives z=0 because a(e2)=0. Hence w²=x(1-x). For n=(h,sqrt(1-h²)), acoustic nonnegativity and the upper bound give 4w² h²(1-h²)<=2x h². Let h->0: since x>0, this forces x>=1/2, hence x=1/2 and |w|=1/2. Reflect the second target coordinate if needed to take w=1/2.

Now A=diag(1,0). The norm bound on H implies H e_11=e_11 (a unit coordinate vector with quadratic value one). Therefore K_11=K_12=0, and the symmetric off-diagonal entry of B0 being 1/2 implies K_21=1. The columns of H indexed by e_12,e_21 then have their full norm budget spent on that off-diagonal entry, so all other entries in those columns vanish. The final diagonal entry H_(22,22) must equal one: at n=(1,1)/sqrt(2) the acoustic first row is (1/2,1/2); PSD contraction implies the second diagonal entry is 1/2 (the first diagonal entry of K_acoustic-K_acoustic² is zero, so its first row vanishes). This fixes H_(22,22)=1. Thus in these bases H is exactly the transpose operator T on planar matrices. In addition Z=-GU fixes
    B^1=G diag(0,1), B^2=[[0,-G/2],[-G/2,0]],
    W=G².
Direct contraction gives H:S=-G²/2 and H:M_h=-3G²/4.

In the W=0 equality case, both H:S and H:M_h vanish: B^1=GI/2 and B^2=0, so their actions are G²x and G²x/2. Consequently, at ALL equality states, including the zero jet,
$$
\delta=0\quad\Longrightarrow\quad
\Delta:=H:M_h-H:S=-W/4.                                 (2)
$$
This is the essential new local rigidity statement. It uses ||H||op<=1, and makes no claim about the existence of actual fields with those local jets.

## 2. Strict global improvement

At each nonzero jet normalize B (and hence g,P,Q) by dividing by sqrt(G²+W); H stays unchanged. The local normalized state space, with symmetric H, ||H||op<=1, RC of its quadratic form, symmetric B^a and G²+W=1, is compact in finite-dimensional Euclidean space. No choice of a continuous rotation field is needed; the preceding calculations are invariant under the orthogonal basis changes made separately at each point.

Weight the time-space measure by (G²+W)/(3E/4), since (3) of P15 gives int G²=E/2 and int W=E/4. The normalized state laws are probability measures with mean W=1/3, mean Delta=0, and
    mean delta = (J_F+E/8)/(3E/4).
If the previous universal constant could be approached, compactness of probability measures on this state space would yield a limit law of mean delta=0, W=1/3 and Delta=0. Since delta>=0 and continuous, the limiting support would satisfy (2), hence its mean Delta=-1/12, a contradiction. This proves a uniform strict improvement on -1/8 for the normalized full-Hessian class. Smooth convolution of the matrix energy and periodic gradient preserves the global Hessian bound and RC, and passage to W1,2 gradients is justified by the quadratic-growth bound as in P15. Thus the result covers exactly the original beta_* normalization.

For example, an equivalent compact minimum determining a strict improvement is the minimum of mean delta over probability measures on the stated local state space with mean W=1/3 and Delta=0. It is attained and positive. This is a finite-dimensional moment relaxation (the three expectations can be represented by at most four states via Caratheodory); it is not a characterization of the actual heat-flow problem. We do not use it as an exact-zero reduction.

## 3. An explicit conservative strictness budget

For reproducibility the compactness proof can be quantified very crudely without optimizing the relaxation. Keep the local normalization G²+W=1. Call a state good if W>=1/100 and delta<=eps, with eta=10^(-16), eps=10^(-36). We show Delta<=-W/8 on every good state.

By (1) or the square completion in P15,
    |G sqrt(x)-sqrt(W/2)|<=sqrt(delta).
Thus G>=1/16 and x>=1/256 on a good state. Equation (1) gives e<=512eps<eta². Diagonalize A=diag(a,b), a>=b>=0. The first acoustic defect 2x²-|A_d|²=2ab is <=e, so b<=128eta². Write B0 as in Section 1. The perpendicular-direction defect identity there gives |y|<=eta. The acoustic inequality at e2 gives |y-z|<=sqrt(b), so |z|<=13eta. Consequently
    w²>=x(1-x)-170eta².
For n=(±sqrt(eta),sqrt(1-eta)), average the two squared acoustic off-diagonal entries to cancel the odd cross term. The inequality b(n)^2<=a(n) yields
    4w² eta(1-eta)<=a eta+b,
    4w²<=(a+128eta)/(1-eta)<=a+260eta.
Since a<=2x, it follows that x(1/2-x)<=66eta. As x>=1/256, x>=1/2-17000eta. Also x< =1/2+64eta² since a<=1 and b<=128eta². In particular
    a>=1-35000eta,
    1/2-10^9 eta²<=|w|<=1/2.
The latter uses x(1-x)=1/4-(x-1/2)², the lower bound on w² and w²<=x(1-x). Reflect the second target component to take w nonnegative.

By the full norm bound on H its e_11 column has off-diagonal norm <=sqrt(1-a²)<=sqrt(70000eta)<10^(-5). In particular |K_12|<10^(-5). Since K_21=2w-K_12>=1-2*10^(-5), the e_21 column's norm bound gives |H_(21,21)|<7/1000.

Write the trace/deviatoric split of the ordinary spatial heat derivatives:
    H_1=T_1+V_1, H_2=T_2+V_2,
    T_1=[g/2,0], T_2=[0,g/2],
    V_1=[[P_11,P_12],[Q_11,Q_12]], V_2=V_1 J,
    J=[[0,-1],[1,0]].
The last sign convention follows from P,Q trace free and symmetric. These paired deviatoric matrices have total squared norm W; the pair construction is an isometry from (P,Q) with its Frobenius norm. Define Gstress=sum T_i tensor T_i and Vstress=sum V_i tensor V_i. Expanding gives
    S=M_h+Gstress-Vstress,
    Delta=H:Vstress-H:Gstress, H:Gstress=G²x/2.
The reference pair V_ref=(-GI/2,-GJ/2) corresponds to Z_ref=-G U_ref where U_ref=(diag(1/2,-1/2),[[0,1/2],[1/2,0]]). The bounds on a,b,z,w and x just proved imply |U-U_ref|<10^(-11). Equation (1) gives |Z+GU|<=sqrt(2eps), so the pair distance to V_ref is <=10^(-10). Since the norm of V_ref is G, and of V is sqrt(W), both <=1, the difference of their quadratic actions is <=2*10^(-10).

For the reference pair, using the full Hessian bounds above,
    4 (H:Vstress_ref)/G²
        = a+H_(22,22)+2K_12+b+H_(21,21)-2K_21
        <= 7/1000+6*10^(-5)+128eta² < 8/1000.
Consequently H:Vstress<=0.002G²+2*10^(-10), while H:Gstress>=0.24G². With G>=1/16 this gives Delta<=-0.23G². The reference pair distance gives sqrt(W)<=G+10^(-10), hence W<=1.5G². In particular Delta<=-W/8 at every good state, as asserted.

For any state, good or bad, Delta<=W since H:Vstress<=W and H:Gstress>=0. Use the weighted probability law of Section 2. Since mean Delta=0 and mean W=1/3, the total W on bad states is >=1/27 (integrate -W/8 on good and W on bad). The subset W<1/100 contributes at most 1/100 to that total, and W<=1 on the rest. Hence the probability of delta>eps is at least 1/27-1/100. Therefore
$$
J_F/E\ge -1/8+(3/4)(1/27-1/100)10^{-36}
         >-1/8+10^{-38}.
$$
This is an intentionally very loose explicit version of the uniform strictness theorem, not a useful numerical optimization. In particular it is not evidence of proximity to zero.

## 4. Exact no-go control for quadratic jet constraints

The stronger relaxation still allows a substantial negative value even when the entire componentwise covariance tensor is imposed, and when the weighted heat identity is imposed for every constant target matrix and each pair of spatial indices.

For an actual smooth compatible field at fixed s, periodic integration by parts gives, for all target indices a,b and spatial indices i,j,k,l,
    int B^a_ij B^b_kl = int B^a_ik B^b_jl.                (3)
For every constant real 2x2 target map L and spatial indices k,l it also gives
    int H[D partial_k u_s, L D partial_l u_s]
      = int sum_(a,b,i,j) H_(ai,bj) (L B_kl)_a B^b_ij.  (4)
For (4), write the first integrand as partial_k(DF(X_s)):L D partial_l u_s. Integrate in k, then use commutation of partial derivatives and integrate in i. The Hessian chain rule yields the right side. This uses the same constitutive Hessian and spatial field. It is linear in L and bilinear in the two spatial directions. Equations (3) are all constant-coefficient second-moment symmetries of the Hessian components (including the ordinary trace identity), and (4) includes both scalar heat contractions when summed on k=l with L=I. We do not claim these exhaust nonlinear or variable-coefficient integration identities.

Start with two artificial equal-weight states, both with g=e1. State 0 has H=0, B^1=I/2, B^2=0. State 1 has
    B^1=diag(0,1), B^2=[[0,-1/2],[-1/2,0]],
    H=(4T+C)/5,
where T is the transpose operator and C the cofactor involution in row-major matrix coordinates. Its eigenvalues are 1,3/5,3/5,-3/5; its LH curvature at a tensor product a tensor n is (4/5)(a dot n)^2. Thus both states satisfy all local curvature and Hessian-norm constraints. The contractions in state 1 are H:S=H:M_h=-2/5, while in state 0 they are both zero. The mean |B|² and |g|² are both one. In particular the normalized heat cost, divided by twice the mean |B|², is -1/10.

Symmetrize each state independently by all signed permutation matrices in target and domain (8 choices each, so 128 equally weighted states counting duplicates). If the matrices of these transformations are U,R, let B'^a=sum_b U_ab R B^b R^T and H'=O H O^T for the orthogonal matrix-space map O:X->U X R^T. The covariance and curvature inequalities transform correctly; |B|²,|g|²,H:S,H:M_h are invariant scalars. The script checks exactly every identity (3) on the 128 states (all 64 index combinations), and every identity (4) for the four elementary L and four pairs k,l (16 combinations). Hence all identities hold by linearity. One can also see the mechanism directly: target signed permutations eliminate mixed covariances and equalize the diagonal component identities, while spatial signed permutations eliminate odd-index terms. The weighted discrepancy in (4), as a functional of the constant target map and spatial pair, averages under independent conjugations to a multiple of the product of traces; that multiple is zero by the scalar equality of the two contractions. The exact enumeration avoids assuming additional rotational symmetry of the fields.

This is an artificial rational state distribution, not an actual pair (H(X_s),D²u_s) on any torus, and no claim is made of reconstructing it by one smooth integrand. Its role is precise: a lower bound using ONLY these local curvature constraints and these listed constant-coefficient quadratic identities cannot give a nonnegative heat cost in general. In particular adding the componentwise covariance and all the constant-target weighted identities to P15 does not resolve the self-contraction. A proof needs constraints stronger than this relaxation. The artificial cost does NOT imply beta_*<=-1/10.

## 5. Verification and stop rule

Executed research/audit/beta_heat_jet_exact.py with Python/SymPy in the working container. SHA-256 f61a0826491721d7c29d3a67c5b517d52ea28d39978acbcf5f1574241b6bea6a; Git blob 47491f8140a4a268b76b0b5e4b0089b9f3c5fee5. The rational spectrum and rank-one identity, 128-state covariance and weighted identities, exact contraction values and conservative rational stability budgets all passed. The analytic strictness arguments are hand proofs; the arithmetic script alone does not certify them.

The requested beta_* self-contraction remains open. The strongest new conclusion is the strict lower bound above and the exact barrier to proving zero from the listed second-order constraints alone. This rules out the idea that the missing ingredient is merely the omitted constant-coefficient identities. A further step must genuinely exploit joint constitutive/spatial structure, or construct a compatible residual operation. Neither has been obtained. Do not treat progressively tighter negative bounds as an exact-zero mechanism.
