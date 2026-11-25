# Fold-safe Young-measure projective transfer and exact combined-shear chart criterion

24 November 2026. Continuation of [maximum-defect laws and the inner-stress shear](IWANIEC_MORREY_INNER_STRESS_SHEAR.md). This attacks the two regularity obstructions separately, rather than assuming that the local amplification formula can be iterated.

**New results (hand proofs).**
1. For any compact homogeneous gradient Young measure of a stacked (2+m)-by-2 field (G,V), a strictly positive determinant of G on its support suffices for the projective pushforward (G^{-1},VG^{-1}), with determinant weights, to be a compact homogeneous gradient Young measure. Generating maps need not be injective or have positive Jacobian everywhere. Signed inverse traces, degree one, vanishing bad-fiber mass and Lipschitz truncation yield actual bounded generating maps. This removes the spatial small-Lipschitz-perturbation assumption of the previous amplification theorem.
2. The inner-stress chart derivative has an exact Hessian pencil formula. The outer cofactor shear leaves T unchanged, and combining it with the inner shear gives a single auxiliary scalar s. For a strongly RC energy the cofactor-weighted Hessian has two positive-type and two negative-type eigenvectors. At a physical positive-determinant chart the combined action is locally strongly RC **if and only if all four pencil denominators have the same nonzero sign**. The identity branch uses the positive sign. This reduces matrix-space regularity to pointwise scalar inequalities, affine in s for a fixed t.
3. A nonperturbative sufficient continuation theorem uses these inequalities on an input ball, together with a boundary-radius condition. No continuous-in-time chart, derivative-smallness condition on the inner shear, or actual inverse of each generating map is required. Whenever the certificate holds, the entire shifted law transports and the defect is exactly D/(1-tD).
4. A rational two-orientation quadratic control shows why strict positivity of the physical Jacobian is not by itself a matrix-space regularity theorem, even allowing an auxiliary outer shear. The first curvature fold on the identity branch is an upward curvature blow-up. This example is NOT a maximum-defect stationary law or a Morrey counterexample.

**Remaining blocker:** no proof that a maximum-defect law admits such a chart for a fixed fraction of the pole, or that its transformed curvature/range normalization stays bounded. The result is not a uniform normalized amplifier or an unrestricted proof. The proposed feasibility test is exact in principle for semialgebraic input jets; no optimization over hypothetical maximum-defect laws was performed. Algebra controls were executed locally. No new Lean theorem, independent mathematical review or priority claim. Related orientation-preserving Young-measure work includes Astala–Faraco, https://doi.org/10.1017/S0308210500002006, and Benešová–Kampschulte, https://doi.org/10.1137/151006056. We give a direct signed-trace proof for the stacked field and do not claim novelty of the general inverse-measure concept.

## 1. A projective law transfer without injective generating maps

Let nu be a compact homogeneous gradient Young measure on matrices with 2+m rows and 2 columns, written (G,V), where G has two rows. Assume det G>=delta>0 on supp nu. Denote their means by G0,V0. The determinant minor identity implies det G0=int det G dnu>=delta.

**Theorem A.** The probability law
$$
\boxed{\quad
\widetilde\nu=(G,V\mapsto (G^{-1},VG^{-1}))_\#
                  \left(\frac{\det G}{\det G_0}\nu\right)
\quad}
\tag{1}
$$
is a compact homogeneous gradient Young measure, with means G0^{-1}, V0 G0^{-1}. Every constant row combination, or any sub-block, of this field is again a genuine homogeneous gradient Young measure. The two extra rows G^{-1} may be omitted if they are not needed.

Proof. Use a bounded periodic affine-base generating sequence (y_j,v_j) on the area-one square torus, with mean derivatives G0,V0. If starting from the affine-boundary characterization, periodize the perturbations. Conversely a law obtained on any fixed affine lattice can be generated on the usual unit square by fine-scale repetition, cutoff to affine boundary, and diagonalization. This uses the usual equivalence between spatial laws of bounded affine-periodic gradients and homogeneous gradient Young measures. Approximate each periodic perturbation by a trigonometric polynomial with errors tending to zero in W1,2, retaining a common gradient bound by positive Fejer convolution. This retains the same limiting law. Since det Dy_j is real analytic and its mean is det G0>0, its zero set is Lebesgue-null.

For abbreviation put G_j=Dy_j, V_j=Dv_j. Define the bad source set E_j={det G_j<delta/2}; its measure tends to zero by convergence of the bounded laws. All Jacobians and all components of adj G_j are uniformly bounded; thus
    integral_(E_j) |det G_j| ->0.
The target torus is the fixed lattice G0 Z², of area det G0. The induced map has degree one. Equivalently the lift y_j:R²->R² is proper with degree one, and preimages of a target value translated by G0 k correspond by source translation by k. For almost every regular target value z let x_i(z) be all lift preimages; they are finitely many, with signed count one. Use the signed trace of the augmented map w_j(x)=(x,v_j(x)):
    a_j(z)=sum_i sign(det G_j(x_i)) w_j(x_i).
The signed trace theorem of [fold transfer](IWANIEC_MORREY_SIGNED_TRACE_FOLD_TRANSFER.md), or its proof applied to each of the 2+m scalar components, gives a_j in W1,1_loc and
    Da_j(z)=sum_i sign(det G_j(x_i)) [I;V_j(x_i)] G_j(x_i)^{-1}.
It is affine-plus-periodic with affine derivative [I;V0]G0^{-1}. In particular this statement does not assume a globally defined single inverse branch. For clarity the distributional derivative follows by integrating a scalar test through the signed area formula and integrating by parts against adj G_j; Piola cancellation gives the numerator Dw_j adj G_j. Almost-everywhere nonsingularity permits its conversion back by the unsigned area formula. The previously proved formula works unchanged for any number of output rows.

Let B_j be the image of E_j in the target torus, enlarged by the null set of critical values. By the unsigned area formula
    |B_j|<=integral_(E_j)|det G_j| ->0.
For z outside B_j there are only good positive sheets, so degree one gives exactly ONE sheet. There the trace has derivative [I;V_j]G_j^{-1} with a common bound, since det G_j>=delta/2 and G_j,V_j are bounded. Good source sheets mapping into B_j also have vanishing total source measure: their count is <=1+n_-(z), where n_- counts negative sheets; all negative sheets come from E_j. Thus
    |{x outside E_j : y_j(x) in B_j}|
       <=(2/delta)(|B_j|+integral_(E_j)|det G_j|) ->0.
All sets and integrals here can be interpreted in the two fundamental tori; the signed count and area formula follow equivalently by summing translated lift cells.

On B_j the signed trace derivative may have very large norm. But the absolute integral of that derivative there is bounded by
    integral_(y_j^{-1}(B_j)) |[I;V_j] adj G_j| ->0,
by the preceding source-measure estimate and the uniform cofactor bound. Thus no L1 derivative mass is hidden in the disappearing folded fibers. This is stronger than merely discarding their target measure.

Subtract the affine part of a_j, obtaining a periodic W1,1 map on the target lattice. Its derivative is bounded by a constant C0 outside B_j, and its L1 norm on B_j tends to zero. The periodic Hardy–Littlewood maximal estimate and the Sobolev pointwise Lipschitz inequality give the following fixed-radius truncation: choose a fixed threshold L>2(C0+1), enlarged by the dimension/lattice constants if needed. The set where the maximal function of the derivative exceeds L has measure o(1), since its bounded portion is <=C0 and its remaining L1 norm is o(1). On the good set of Lebesgue points the periodic map has a fixed Lipschitz bound; extend each real component by McShane on the flat torus. The extension's derivative agrees a.e. on that good set (Sobolev locality), and is uniformly bounded everywhere. Add the same affine part back. The resulting a_j^b are genuine uniformly bounded affine-base gradients; the set where they differ in derivative from the signed trace has measure o(1). This truncation is not an assertion that the original inverse trace had an L2 gradient on all fibers.

For any continuous test function on the output compact derivative range, its averaged value on Da_j^b differs by o(1) from its integral on the single-good-sheet target region, because both the repaired gradient and the derivative on that region are bounded. Change variables on this region by the area formula. The discarded source set has measure o(1), and on the remaining source det G_j>=delta/2. A continuous cutoff in det G_j extending the weighted projective test below delta/2 permits passage to the original Young measure. The resulting normalized limit is exactly (1), since the target fundamental cell area is det G0. The uniform boundedness and affine periodicity of the repaired maps prove the homogeneous gradient Young-measure assertion, not just the moment identities. QED.

The argument uses strict positivity on the LIMITING support, not positivity of every generating G_j and not global bi-Lipschitz invertibility. No conclusion is asserted for a support containing singular matrices with positive mass or mixed determinant signs. At a vanishing base area the statement cannot be used.

## 2. Exact differential of the inner-stress chart

We use the notation of [inner-stress shear](IWANIEC_MORREY_INNER_STRESS_SHEAR.md). Recenter f(0)=Df(0)=0, let p=Df(X), H=D²f(X), T=f I-X^T p, C=cof as a symmetric linear involution on four matrix entries. Set
    B=I+t C T,
    a=1+t(f-X:p), b=1+t f,
    d_X=det X, d_p=det p, d=det B,
    L=a I+t X p^T.
The two-dimensional adjugate identity gives
    B=a I+t p^T X,    det L=det B=a b+t² d_X d_p.
At any X where d!=0 the inner chart's value, gradient candidate and action are
    Y=X B^{-1}, Z=C p B^{-1}, g=(f+t det T)/d.
Here Z is the cofactor of the transformed stress, not the stress itself. Define the invertible rank-one-preserving linear map
    Acal[R]=L^{-1} R B^{-1}.
It obeys Acal^* C Acal=C/d² since det(Acal[R])=det(R)/d².

**Exact derivative pencil**
$$
\begin{aligned}
D_X Y&=\mathcal A\,(aI_4+t\,d_X C H),\\
D_X Z&=\mathcal A\,(b C H-t\,d_p I_4).
\end{aligned}
\tag{2}
$$

Proof. In a direction R, d a=-t X:HR and
    dB=-t (X:HR) I+t(HR)^T X+t p^T R.
Use (X:HR)I-(HR)^T X=adj X C(HR), with adj X=(C X)^T. Also Y=L^{-1}X and Z=L^{-1}Cp; these identities follow by multiplying on the left by L and on the right by B, and Cp p^T=d_p I. Consequently
    I-t Y p^T=a L^{-1},
    Y adj X=d_X L^{-1},
    I+t Z adj X=b L^{-1},
    Z p^T=d_p L^{-1}.
Differentiate X B^{-1} and Cp B^{-1}, substitute these four identities, and obtain (2). No inverse of the matrix-space chart has been used.

The action satisfies the differential identity dg=(C Z):dY on the entire set d!=0, EVEN if D_X Y is singular. Indeed p_t=CZ=p B^T/d. With N=f+t det T, one has N I-p^T X=T^T B and dB=t C dT. Differentiating N/d and using these equalities shows
    dg=(df+t CT:dT-N tr(B^{-1}dB))/d
      =(df-tr(p^T X B^{-1}dB))/d=p_t:dY.
This algebraic proof does not require continuity of a regular characteristic from time zero.

## 3. Outer and inner shears commute and reduce chart search to one scalar

The outer shear from [cofactor duality](IWANIEC_MORREY_COFACTOR_DUALITY.md) acts by X->X+s Cp, f->f+s det p, retaining p. The identity (Cp)^T p=(det p)I proves that T is unchanged. Hence the two shears commute algebraically wherever their charts exist.

More importantly, the combined formulas make sense even if an intermediate inner chart has folded in matrix space:
$$
\begin{aligned}
Y_s&=(X+s C p)B^{-1},\\
Z_s&=C p B^{-1},\\
g_{t,s}(Y_s)&=\frac{f+t\det T+s d_p}{d}.
\end{aligned}
\tag{3}
$$
Where the combined map X->Y_s is regular and single-valued on an output chart, its derivative satisfies C Dg_(t,s)=Z_s. This follows from dg=p_t:dY above and d(det p_t)=p_t:C dp_t, since det p_t=d_p/d. Thus the combined differential identity holds before taking any chart inverse, just as (2) does. The new energy-momentum tensor remains (T+t det T I)/d, because the outer shear changes neither the inner stress nor its cofactor.

By (2) define the scalar affine functions of a real spectral parameter mu:
    P(mu)=a+t d_X mu,
    Q(mu)=b mu-t d_p,
    P_s(mu)=P(mu)+s Q(mu).
They depend on X and t, suppressed in the notation. Then
    D_X Y_s=Acal P_s(CH),
    D_X Z_s=Acal Q(CH).
At a regular chart point the exact transformed cofactor-Hessian is
$$
\boxed{
C D^2 g_{t,s}(Y_s)
 =\mathcal A\,Q(CH)P_s(CH)^{-1}\,\mathcal A^{-1}.
}
\tag{4}
$$
This is not just an infinitesimal Riccati equation. In particular the matrix-space chart can be tested using the original first and second derivatives of f at X.

### 3.1 Exact rank-one curvature criterion

Suppose f has a positive LH margin. The planar Finsler lemma gives H=c C+P0, P0 positive definite (apply the lemma to H-m I first). Hence CH=c I+C P0 is diagonalizable over the reals: C P0 is similar to the symmetric P0^(1/2) C P0^(1/2). There are two eigenvalues mu_- below c with C-negative type eigenvectors, and two eigenvalues mu_+ above c with C-positive type eigenvectors, counted with multiplicity. Indeed for an eigenvector v of C P0 of nonzero eigenvalue lambda, v^T P0 v=lambda v^T C v, so its C-norm has the sign of lambda. Distinct eigenvalues give C-orthogonal eigenvectors, and each repeated eigenspace has definite C sign; choose a basis with C-norms ±1. Thus for each negative-type / positive-type pair, mu_+>mu_-.

In this basis a C-selfadjoint operator defines a strongly RC Hessian exactly when its smallest positive-type eigenvalue is strictly above its largest negative-type eigenvalue. To see this, a C-null vector has equal squared coordinate sums in the two types; the quadratic Hessian form is the difference of the two weighted sums. Necessity follows by taking one C-unit eigenvector of each type with equal coefficient. This argument is valid also in the transformed basis Acal v, which rescales all C-norms by the same positive number d^-2.

For the fractional function m_s=Q/P_s one has the exact cross-type difference
$$
m_s(\mu_+)-m_s(\mu_-)
 = \frac{d(\mu_+-\mu_-)}
        {P_s(\mu_+) P_s(\mu_-)}.                           \tag{5}
$$
The identity follows by expanding the two affine pencils; the s terms cancel and the numerator coefficient is a b+t²d_X d_p=d.

**Theorem B.** At a point with d>0 and a regular combined chart, g_(t,s) is strongly rank-one convex at that point iff the four real numbers P_s(mu_i) have the same nonzero sign. Equivalently each cross-type product is strictly positive. There is no weak-boundary exception with zero cross-type difference for a regular chart and positive initial LH margin, by (5). On the identity component of regular charts all four signs are positive. This is a pointwise criterion, not an assertion of global single-valuedness.

In particular for fixed t and fixed X the identity-branch constraints are simply four STRICT LINEAR inequalities in s:
    P(mu_i)+s Q(mu_i)>0.
If Q(mu_i)=0 they reduce to P(mu_i)>0. Otherwise they bound s above or below, according to the sign of Q(mu_i). Over a compact input region take the intersection of these intervals. This is a one-dimensional feasibility problem for the auxiliary outer shear at each inner time t. There is no unknown evolved Hessian in it. If the energy has a semialgebraic formula with exact derivatives, the pointwise positivity over the entire compact input ball is a real-algebraic condition, using characteristic equations and the real spectrum. It can in principle be checked by exact quantifier elimination for fixed algebraic t,s; no such enormous decision problem has been solved here.

At an isolated first matrix fold for the pure inner shear with d>0, if d_X>0 the first vanishing denominator must be at the lowest, negative-type eigenvalue. At P(mu)=0, Q(mu)=-d/(t d_X), so along the approaching positive denominator m_s with s=0 tends to -infinity (assuming t>0). Since that eigenvector is C-negative, the corresponding Hessian quadratic form tends positively to infinity in the smoothly transported C-normalized basis. For d_X<0 the largest positive-type eigenvalue is first and gives the corresponding positive divergence. This is a convex curvature blow-up at such a regular physical point, not a guarantee that it can be crossed while preserving a globally RC function. The statement presumes a simple first fold and a nonzero d_X; the exact criterion (5) handles simultaneous signs without any informal blow-up classification.

### 3.2 A spatially regular quadratic chart control

Take f(X)=|X|²/2 at the two states I and diag(1,-1). Then p=X, H=I_4, T=0, B=I for all t, and the two cofactor types have mu=±1. At I the two distinct denominator values are
    1+s,  1-2t-s(1+2t);
at diag(1,-1) they are
    1-s,  1-2t+s(1+2t).
For t>=1/2 the last inequality from each state cannot both be strictly positive, whatever s is. Even adding an arbitrary positive common scaling of the outer first block does not change the feasibility after dividing by that scale. Thus identity-branch matrix folding cannot in general be eliminated merely by controlling the physical determinant or allowing one outer parameter. This is an exact pointwise control for a convex quadratic energy. It is NOT a maximum-defect law, does not have the required constitutive-stress compatibility, and does not disprove a rigidity/continuation theorem special to those laws. In particular we do not infer that a qualifying maximum-defect chart fails.

## 4. Nonperturbative sufficient continuation certificate

Take a shifted maximum-defect law from [the prior construction](IWANIEC_MORREY_INNER_STRESS_SHEAR.md), with nu supported on B_L, D>0, and exact compatible six-row lift
    W=[X;Cp;TJ],   mean W=[0;0;-D J],
    int f=-D, int det p=0, int det T=D².
Suppose the original f is smooth and uniformly strongly RC on an open neighborhood of the closed matrix ball B_R containing supp nu, f(0)=Df(0)=0, and Lip Df<=M on B_R. For ANY fixed parameters 0<t<1/D and s, make the following verifiable chart assumptions:
1. d=det(I+t CT)>0 everywhere on B_R.
2. P_s(mu_i)>0 for every eigenvalue of CH at every X in B_R.
3. |s|M<1.
4. r*=min_{|X|=R}|Psi_(t,s)(X)| is strictly larger than max_{supp nu}|Psi_(t,s)(X)|, where Psi_(t,s)=Y_s of (3).

These conditions may hold beyond the crude small-time bounds of the earlier note. No assumption that the INNER chart alone is injective, and no continuous path of intermediate times, is required.

**Proof of a single-valued RC chart.** Conditions 1–2 and (2) imply invertible derivative with positive determinant: Acal has determinant (det L)^-2(det B)^-2>0 and the product of the four pencil eigenvalues is positive. The inequality |X+s Cp(X)|>=(1-|s|M)|X| shows that the only zero of Psi_(t,s) is the recentered base. In particular r*>0. For every |Y|<r*, Brouwer degree of Psi_(t,s) on the input ball is constant and equals one (calculate at zero). Every preimage has local degree +1, and there are finitely many since none meet the boundary and the derivative is invertible. Therefore the preimage is unique. The inverse function theorem gives a smooth inverse throughout this output ball. Conditions 1–2 and Theorem B imply positive LH curvature throughout it. Choose an output sub-ball containing zero and the transformed witness range strictly in its interior, with closure inside radius r*. Compactness gives a common positive LH margin there. A smooth convex-maximum quadratic tail gluing as in the earlier notes gives a globally smooth strongly RC energy agreeing with (3), up to a common additive constant, on the entire witness range and base. The gluing does not give an unchanged global Hessian bound.

**Proof of actual compatible transport without small spatial deformation.** The joint law
    (G,V)=(I+t C T,\ [X+s Cp;\ Cp;\ TJ])
is a constant affine row map of the original genuine six-row gradient Young measure, since C T=J^T(TJ). Its upper block has mean (1-tD)I, and det G is strictly positive on the compact support by condition 1. Apply Theorem A; discard the inverse-domain rows. The transformed six-row law is exactly the determinant-weighted pushforward of V B^{-1}. By (3) and its stress identity, this is the full constitutive graph of the new RC energy. Its mean is [0;0;-D J/(1-tD)]. For the action formula before adding the irrelevant constant from the global extension we have g_(t,s)(0)=0 and
$$
\boxed{
\int g_{t,s}\,d\nu_{t,s}
 =\frac{\int (f+t\det T+s\det p)\,d\nu}{(1-tD)^2}
 =-\frac{D}{1-tD}.
}
\tag{6}
$$
All weights are positive and normalize by the determinant null Lagrangian. The shift used to extend the action cancels from the Jensen gap; if describing the full stress graph of the globally extended energy, recenter by subtracting that shift first. Thus the exhibited gap and the shifted full constitutive law are transported exactly. Since the output law is generated by actual bounded gradients, this yields a strict actual witness whenever D>0. QED.

Theorem A, rather than a hypothetical pointwise inverse of each generating deformation, is essential here. For a full graph lift it also transports all simultaneously compatible extra rows. The preceding algebra and degree proof separate the remaining matrix-space condition from the physical one.

## 5. Exact obstruction at the physical pole, and next gate

There is a simple consequence of the physical regularity condition itself. If d_t(X)>0 on the compact law support for EVERY 0<=t<1/D, then at the pole d_(1/D)>=0 on the support. Its integral is zero, because mean T=-D I and mean det T=D². Hence d_(1/D)=0 on the support. Each T has at least one eigenvalue -D; its other eigenvalue must be real and >=-D to avoid an earlier positive root. Its mean trace is -2D, so the other eigenvalue also equals -D everywhere on the support. Consequently
    tr(T+D I)=0, det(T+D I)=0, (T+D I)^2=0
on the law support. This gives a precise possible pole regime (nilpotent shifted stress), not a contradiction: nonzero nilpotent fields can themselves be compatible, and no argument here excludes that regime in the full constitutive law. If the pole regime fails, some support point must lose positive physical determinant earlier. Strict positivity is the hypothesis of Theorem A; we do not extend it past that event by dropping negative-sheet mass.

The two remaining questions are therefore exact and separate:
- Does a maximum-defect contact law admit parameters with d>0 and a feasible common chart interval, plus an output domain containing the witness, until tD is bounded away from zero uniformly?
- Can the resulting global curvature and amplitude normalization be controlled to obtain a uniform amplifier?

We have removed a real spatial obstruction and given an exact nonperturbative matrix chart criterion. We have not proved the needed inequalities at a hypothetical maximum-defect law, excluded the shifted law (including the nilpotent pole regime), or solved unrestricted Morrey. Positivity of d alone is demonstrably insufficient. Do not increase finite mesh sizes or assert an unlimited amplification iteration in place of the remaining rigidity proof.

## 6. Executed verification

Run python3 research/audit/combined_shear_exact.py (SymPy). Actual local execution passed 12 rational joint shear derivative, stress invariance, transformed Hessian and cofactor metric checks, the exact two-orientation quadratic control, and four rational near-singular folded-sheet controls. The latter use a degree-one product map with a negative sheet of slope -epsilon on a length-epsilon interval, compensated by a positive sheet of slope 2+epsilon on the adjacent interval. Its triple target fibers have length epsilon²; the signed inverse gradient there is 1+1/epsilon+1/(2+epsilon), yet its L1 mass on those fibers tends to zero and the exact mean derivative is one. This exercises the vanishing-fold budget; the full Young-measure theorem is the analytic proof in Section 1.

The exact executed script has SHA-256 43021001adfbfff7387a4a97105552b4439ae42bf23f79a3baba9690f9cad125. No higher-dimensional negative-witness campaign, large mesh or exact-zero computation was run. No new Lean validation or unrestricted resolution.
