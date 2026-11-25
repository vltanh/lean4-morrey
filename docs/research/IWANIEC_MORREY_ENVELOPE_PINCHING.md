# Planar minimum-set rigidity, envelope pinching, and chart-free stress contraction

24 November 2026. This is a new energy-based attack after the [combined shear continuation criterion](IWANIEC_MORREY_COMBINED_SHEAR_CONTINUATION.md). Instead of assuming a larger regular chart, use the special planar incompatibility theorems to prove a strict comparison between the quasiconvex and polyconvex envelopes. Then contract the quasiconvex/polyconvex gap and the stress oscillation by an exact envelope operation.

**New hand results.**
1. For a fixed C2 globally uniformly strongly RC F with bounded Hessian, and a fixed gradient-amplitude bound R, there is c(F,R)>0 such that for EVERY globally touching or nontouching polyaffine minorant l<=F and EVERY actual bounded periodic affine-base gradient X,
       int (F(X)-l(X)) >= c(F,R) int |X-mean X|².
   The constant is independent of the minorant and of the variance, even if the variance tends to zero. This uses planar minimum-set rigidity plus the Ball–James transition-layer estimate. No positive lower variance or prescribed number of wells is assumed.
2. For the complete counterexample class of smooth uniformly strongly RC energies with positive quadratic exterior, there is rho_F<1 such that at every base
       F-QF <= rho_F (F-PF).
   In particular QF=PF at a base implies F=QF there. If QF is polyconvex everywhere, F is QC. Any genuine defect has an additional nonzero QC-versus-PC envelope gap.
3. Write q=QF, p=PF and d=F-q. Subtracting a small multiple of q yields exact identities
       Q(F-theta q)=(1-theta)q, P(F-theta q)=(1-theta)p,
       (F-theta q)-Q(F-theta q)=d.
   This retains the strong RC margin m-theta M when theta<m/M. At a maximum-defect law of the earlier note, it keeps D fixed and multiplies the centered energy-momentum stress T+D I by 1-theta, with a genuine compatible affine transformation of the entire lift. This is a chart-free contraction of the obstructing stress oscillation and of the QC/PC gap.
4. An alternative rank-one-envelope amplifier, applied to q+c d for any c>1, preserves q and p exactly, retains a chosen positive LH margin kappa<m, and increases the maximum-defect gap by at least D min(c-1,(m-kappa)/(2M)). It is exact at the maximum for small c, with no matrix-chart singularities.

**Remaining limitation.** These are not a uniform gap separation or a proof of Morrey. The pinching constant is positive but nonconstructive and depends on F and the fixed amplitude bound; in particular the proof uses C2 compactness and cannot be assumed uniform through nonsmooth envelope subtraction or smoothing at vanishing scales. The chart-free subtraction loses curvature and cannot be iterated all the way to theta=1. The amplified RC envelope can have a larger Hessian bound. No control of this normalization sufficient to force a contradiction has been found. No strict negative planar pair, new Lean theorem or independent review. The external incompatibility results are published theorems, used explicitly; they are not new results of this repository or claimed formalized here. The exact algebra companion was run.

## 1. Published planar inputs and minimum-set rigidity

The following are the external inputs, separate from the earlier formalized scalar projection theorem.

* D. Faraco and L. Székelyhidi Jr., *Tartar's conjecture and localization of the quasiconvex hull in R2x2*, Acta Math. 200 (2008), 279–305, DOI [10.1007/s11511-008-0028-1](https://doi.org/10.1007/s11511-008-0028-1). Theorem 6 and Corollary 2 (pp. 300–301) establish the needed planar compactness: a compact planar set without rank-one connections and without T4 configurations cannot support a nontrivial homogeneous gradient Young measure. In the proof one may use directly that the rank-one convex hull of the support of such a measure is connected, together with the cited connected rank-one-free set rigidity.
* B. Kirchheim and L. Székelyhidi Jr., *On the gradient set of Lipschitz maps*, J. Reine Angew. Math. 625 (2008), 215–229, and its planar incompatibility consequence (see [MPI publication record](https://www.mis.mpg.de/publications/preprint-repository/article/2007/issue-16)). As summarized in the next reference, two disjoint compact planar sets are incompatible for gradient Young measures (also nonhomogeneous ones) if their rank-one convex hulls are disjoint and their union has rank-one convex hull equal to the union of the two hulls.
* J. M. Ball and R. D. James, *Incompatible sets of gradients and metastability*, Arch. Ration. Mech. Anal. 218 (2015), 1363–1416, DOI [10.1007/s00205-015-0883-9](https://doi.org/10.1007/s00205-015-0883-9), [arXiv:1407.5929v2](https://arxiv.org/abs/1407.5929v2). Remark 7 of the arXiv version gives the preceding planar equivalence. Theorem 14, p. 23 of that version, gives the transition-layer estimate. On a fixed cube, for incompatible disjoint compact sets K1,K2, there are epsilon0,gamma>0 such that for every 0<epsilon<epsilon0 and W1,2 map y,
       int_(transition) (1+|Dy|²) >= gamma min(|phase 1|,|phase 2|),
  where the two phases are the epsilon neighborhoods of K1 and K2 and the transition is their complement. This theorem is needed precisely to prevent an arbitrarily small minority phase from being discarded in a compactness argument. The constants need not be explicit here. The cube is an admissible C-connected domain.

Use standard compact rank-one hull representation by laminates and the homogeneous gradient Young-measure characterization/closedness on bounded supports. These are the usual background of Faraco–Székelyhidi's theorem, not an assertion that determinant-compatible laws are gradient Young measures.

**Lemma 1 (rigidity of global minima).** Suppose h is nonnegative and uniformly strongly RC on R2x2, meaning h-(m/2)|X|² is RC for m>0. Every compact subset K of its zero set has Krc=K, and supports only Dirac homogeneous gradient Young measures. Every pair of disjoint nonempty compact subsets partitioning K is incompatible in the Ball–James sense.

Proof. For any compact laminate mu supported on any compact K' subset K,
       0=int h dmu >= h(mean mu)+(m/2) int|X-mean mu|².
Both terms on the right are nonnegative, so mu is Dirac. By the laminate characterization of rank-one hulls, (K')rc=K'. Also distinct zero points cannot be rank-one connected, by strong RC on their segment. A T4 configuration would support a nontrivial laminate, so is excluded. Apply the planar compactness theorem. Equivalently, for a homogeneous gradient Young measure use connectedness of the rank-one hull of its support, which equals the support here, and the connected rank-one-free set rigidity as in Corollary 2 of that paper. For a disjoint compact partition, the individual hulls and the union hull are the sets themselves. The planar incompatibility theorem and Ball–James Remark 7 apply, proving full incompatibility. QED.

This input is genuinely two-dimensional: the corresponding inference from laminate incompatibility to gradient incompatibility is not valid in general higher dimensions. We will not apply it to the 6x2 stationary lift.

## 2. A uniform coercivity theorem, including vanishing variance

Let F be fixed, C2, uniformly strongly RC with margin m>0 and global Hessian bound ||D²F||<=M. It need not be QC. For a polyaffine minorant write
       l(X)=a+B:X+c det X <= F(X) for all X.
Fix R>0. Let X=A+Du be any periodic Lipschitz affine-base gradient, on the unit square, with |X|<=R a.e. Let E=int |X-A|². All norms are Frobenius unless an operator norm is specified.

**Theorem A.** There exists k=k(F,R)>0 such that simultaneously for every l and every such X,
$$
\boxed{\quad\int (F(X)-l(X))\ge k E.\quad}                 (1)
$$
This is an absolute energy above a global polyaffine minorant, not a claim that the Jensen gap F(X)-F(A) is positive. The constant can also be chosen uniformly over a class with a common strong RC margin, Hessian bound and locally precompact Hessians in C0, after affine recentering; the fixed F statement is sufficient here.

Proof by contradiction. Suppose there are l_j and X_j=A_j+Du_j with E_j>0 and
       h_j=F-l_j>=0, int h_j(X_j)=o(E_j).
Since E_j<=R², the total energies tend to zero. The scalar determinant coefficients c_j satisfy |c_j|<=M. Indeed test the global minorant inequality at t times any unit conformal or anticonformal matrix; divide by t² and use the quadratic upper bound on F from its Hessian. The determinant of those unit matrices is respectively +1/2 or -1/2, so both bounds follow. Thus Lip Dh_j<=2M, and all h_j retain the margin m (subtracting l_j does not change LH curvature).

The constant and linear coefficients of l_j are bounded as well. Choose a point in B_R where h_j is bounded by 1 (the vanishing average ensures this eventually). For any nonnegative globally C11 h with derivative Lipschitz bound 2M the ordinary descent estimate gives |Dh(Y)|²<=4M h(Y). Taylor's upper estimate from the chosen point bounds h_j(0) and Dh_j(0) uniformly. After a subsequence the coefficients converge, hence h_j->h in C2 on compact sets, with h nonnegative and of strong RC margin m.

Pass also to a subsequence of the bounded spatial gradient laws of X_j. Their limit is a compact homogeneous gradient Young measure nu: spatial affine-periodic laws are homogeneous gradient Young measures by fine replication/cutoff, and the class is weak-* closed for laws on a fixed compact range (alternatively use the usual QC Jensen characterization). Uniform convergence of h_j on B_R and the vanishing energies show nu is supported on
       K={h=0} intersect closed B_R.
Lemma 1 gives nu=delta_(A_*). Therefore A_j->A_*, X_j->A_* in L2, E_j->0, and h(A_*)=0, Dh(A_*)=0. Merely stopping here would NOT prove (1): the original variance may vanish. We now handle exactly that case.

### 2.1 A single determinant sign for all nearby wells

The planar Finsler lemma for the Hessian at A_* (proved by PSD separation in the cofactor-duality note) supplies a real lambda with
       D²h(A_*)+lambda C >= (m/2) I,
where C is the cofactor involution, the Hessian of det. We may choose lambda nonzero: first take a coefficient giving lower bound m via the strict Finsler lemma, and if it is zero, perturb it by at most m/2. By C2 convergence there is a fixed rho>0 and kappa>0 such that for all sufficiently large j,
       D²h_j(Y)+lambda C >=2 kappa I
on B_(3rho)(A_*), and the same holds for h. Thus on |U_j|=|X_j-A_j|<=rho, with A_j eventually within rho of A_*,
$$
h_j(X_j)+\lambda\det U_j
 \ge h_j(A_j)+Dh_j(A_j):U_j+\kappa |U_j|^2.               (2)
$$
This is Taylor integration on the local ball with a constant determinant gauge, not an assertion of globally convexity modulo det.

In particular for any zero Y of h sufficiently near A_*,
       lambda det(Y-A_*) >= kappa |Y-A_*|².
For any other Y in K, det(Y-A_*) is nonzero unless Y=A_*, by the no-rank-one-connection property of Lemma 1. Partition K into the two sets
       K_+={A_*} union {Y in K: lambda det(Y-A_*)>0},
       K_-={Y in K: lambda det(Y-A_*)<0}.
They are compact and disjoint: the local inequality excludes any negative-sign zero near A_*, and away from A_* the determinant cannot vanish on K. K_+ is nonempty. If K_- is nonempty, Lemma 1 implies these sets are incompatible, including for nonhomogeneous gradient fields. This is a global partition of the fixed zero set into orientations relative to A_*, not a claim that all wells belong to a single orientation.

### 2.2 Eliminate the minority and transition phases at RELATIVE scale

Choose a sufficiently small fixed epsilon>0 so the two neighborhoods are disjoint, and, when both sets are nonempty, so the Ball–James estimate applies. On the compact part of B_R outside both neighborhoods h has a strictly positive minimum if that part is nonempty. Since h_j->h uniformly there,
       |transition_j|=o(E_j).
The majority phase near K_+ has measure tending to one, since X_j->A_*. The transition-layer estimate at exponent 2 and the bounded range yield
       gamma |phase_minus_j| <= (1+R²)|transition_j|=o(E_j).
Thus the whole set outside the K_+ neighborhood has measure o(E_j). If K_- is empty the same conclusion follows directly from the transition estimate's first, compactness part (positive minimum off K_+); no two-set theorem is necessary.

We may make epsilon even smaller at the outset to ensure the following property. For all sufficiently large j, a point X_j in the K_+ neighborhood with |U_j|>rho satisfies
       lambda det U_j >= kappa_1 |U_j|²
for some kappa_1>0. To see this, the compact subset of K_+ with |Y-A_*|>=rho/2 has a strictly positive minimum of lambda det(Y-A_*), if it is nonempty. Uniform continuity of the determinant and A_j->A_* preserve half this positive minimum on the stated neighborhood. Divide by (2R)². If that compact subset is empty, the remote K_+ phase is empty for sufficiently small epsilon and large j; take any kappa_1>0. All constants can be chosen once after taking the limiting h,A_*.

Consequently on the remote good set |U_j|>rho near K_+,
       h_j(X_j)+lambda det U_j >= kappa_1 |U_j|².
On the remaining remote bad set, the same left side is bounded below by a fixed negative constant, since h_j>=0 and |U_j|<=2R. Its integrated cost is o(E_j), by the relative minority/transition estimate above.

### 2.3 Integrate the local and remote coercivity

The affine-base determinant null Lagrangian gives int det U_j=0. The mean of U_j is zero. In (2), h_j(A_j) is nonnegative, and the integral of its linear term over the local set is o(E_j), since
       |int_(local) U_j|=|int_(remote) U_j| <= E_j/rho,
       Dh_j(A_j)->Dh(A_*)=0.
The bad-set variance is o(E_j) because U_j is uniformly bounded. Integrating all three regions now gives
       int h_j(X_j) >= min(kappa,kappa_1) E_j-o(E_j),
contradicting the hypothesis. This proves (1). QED.

All uses of compactness and transition layers above are for actual compatible gradients or their bounded generating laws; a determinant-only moment relaxation would not justify the relative minority estimate. The conclusion is uniform over the polyaffine gauges because their coefficients were shown precompact when the ratio in (1) tends to zero. For a family of F's with a common m,M and locally equicontinuous Hessians, first subtract each affine tangent at zero (absorbing it into l_j); then the same argument obtains a C2-local subsequential limit of the h_j. Without that regularity, the fixed-radius Hessian argument is not justified.

## 3. All-base pinching of the envelopes for a complete energy class

Now assume in addition that F is smooth and has a positive quadratic exterior, as in [quadratic-tail critical states](IWANIEC_MORREY_QUADRATIC_TAIL_CRITICAL.md). This class is complete for strict counterexamples, after adding a sufficiently small quadratic to obtain m>0, smoothing, and gluing to a quadratic tail. Set q=QF and p=PF, the ordinary quasiconvex and polyconvex envelopes.

The lifted convexification defining p is finite on every (A,d) in R4 x R: for prescribed (A,d), average A+R1 and A-R1 with det R1=d-det A. This gives a finite cost, and the lower bound on F gives a finite lower bound on the convexification. Thus a supporting hyperplane at (A,det A) exists. It yields a global polyaffine minorant l_A<=F with l_A(A)=p(A). This is the usual convexification of the minors, not an assumption that q has a touching polyaffine support.

The quadratic-tail bound shows q=F for all bases outside a fixed ball. For bases in that ball the scalar row-clipping theorem of the pinned Iwaniec dependency (see the quadratic-tail note) bounds ALL needed cell minimizing sequences by a common R, independent of the base: take the clipping radius larger than the base radius and the nonlinear core, paying the bounded core cost with the quadratic exterior. Fix such an R and use k(F,R) from Theorem A. On a bounded minimizing sequence X_j=A+Du_j at any one such base, the null mean of l_A gives
       int (F(X_j)-l_A(X_j))=int F(X_j)-p(A)>= k E_j.
Also Taylor's lower bound on F gives F(A)-int F(X_j)<=M E_j/2. Pass to the cell infimum, without assuming attainment, to get
$$
\boxed{
q(A)-p(A)\ge \frac{2k}{M}\,[F(A)-q(A)].
}                                                        (3)
$$
Outside the fixed base ball the right side vanishes, so (3) is global. Equivalently
$$
\boxed{
F-QF\ \le\ \rho_F(F-PF),\qquad
\rho_F=\frac{M}{M+2k}<1 .
}                                                        (4)
$$
This proves the pinching theorem. At a base where q=p it gives F=q. Thus if the QC envelope of a smooth uniformly strongly RC quadratic-tail energy happens to be polyconvex, F was already QC. The proof in Section 2 handles dilution, so (4) is not merely a separation statement away from defect zero or on a fixed positive-defect subset.

At an individual maximum-defect law of the earlier construction, the same conclusion is immediate from Lemma 1 when q=p: the law would be supported on the zeros of F-l_A, a nonnegative uniformly strongly RC energy. The full estimate (4) is stronger and uses transition layers to be uniform down to vanishing gaps. It does not provide a computable or class-uniform rho_F for arbitrary RC energies, nor show q is polyconvex at a defect point. The general problem is NOT settled by (4).

## 4. Exact envelope subtraction: contract the secondary gap and stress without a chart

Let q=QF, p=PF, d=F-q. Recall from the earlier [cofactor duality](IWANIEC_MORREY_COFACTOR_DUALITY.md), or directly the cell infimum and rank-one convexity: q is globally C11 with Lip Dq<=M if F is globally C11 with that bound and the envelope is finite. Indeed the cell infimum is M-semiconcave; its mollifications are rank-one convex with upper Hessian bound M I, and their lower bound -M I follows by decomposing a matrix direction into two orthogonal rank-one summands and reflecting the second summand. Pass to the locally uniform limit of their derivatives. Here q=F outside a fixed ball by the quadratic-tail comparison.

For 0<=theta<1 define F_theta=F-theta q=(1-theta)q+d. The following envelope identities hold even before assuming F_theta is RC:
$$
\boxed{
QF_\theta=(1-\theta)q,\qquad
PF_\theta=(1-\theta)p.
}                                                        (5)
$$
For Q, the lower bound follows from F_theta>=(1-theta)q. For the upper bound take any F cell-minimizing sequence at the chosen base. QC of q and q<=F give int q->q(A) and int d->0. Thus the F_theta cell infimum is at most (1-theta)q(A). This gives equality using the cell formula (or Jensen for any QC minorant). For P, take the finite probability laws with prescribed matrix and determinant means that approach p(A) in F cost. Since p<=q<=F, their averages of q tend to p(A), and of d to zero. The same argument proves equality for the PC envelope. No attainment or uniform compact support of the PC minimizing sequence is needed. In particular
       F_theta-QF_theta=d,
       QF_theta-PF_theta=(1-theta)(q-p).
Moreover F_theta is globally C11 with Hessian bound (1+theta)M, and has strong LH margin at least m-theta M for theta<m/M. The inequality follows from the upper Hessian bound on q and the lower LH bound on F, first a.e. and then by smoothing/integrating along lines. It has the same type of positive quadratic exterior for theta<1.

Now recenter at a maximum-defect base as in the [maximum-defect law](IWANIEC_MORREY_INNER_STRESS_SHEAR.md): f(0)=Df(0)=0, q(0)=-D, Dq(0)=0. In the notation of that law, p_stress=Df(X), T=f I-X^T p_stress, and
       int f=-D, int p_stress=0, int T=-D I.
On the contact support f=q, their derivatives agree, since both C11 and f-q>=0. The new energy g=f-theta q-theta D has base value and gradient zero and the SAME maximum defect D. At each support point,
       g=(1-theta)f-theta D,
       Dg=(1-theta)p_stress,
       T_g=(1-theta)T-theta D I,
so
$$
\boxed{T_g+D I=(1-\theta)(T+D I).}                         (6)
$$
The full lift of g on the old support is a constant affine row map of the full lift of f. Thus it remains an actual compact homogeneous gradient Young measure with the shifted base [0;0;-DJ]. No PDE, inverse chart, or approximating stress field is needed for (6). The old first-block law is still a minimizing contact law, by (5). This is an exact operation on C11 energies; it need not yield C2 energies, and no application of the C2 pinching constant to a sequence of such nonsmooth outputs is asserted.

Let S=T+D I, L_S=sup_support ||S||op. The inner-shear physical block for g is
       I+t C T_g=(1-tD)I+t(1-theta) C S.
It has positive determinant on the support if
       tD < D/[D+(1-theta)L_S],    0<=tD<1.
Indeed cofactor preserves the operator norm in 2x2, and under the displayed strict bound the perturbation of the scalar positive matrix is smaller in operator norm than that scalar. Thus (6) improves the exact sufficient physical interval, independently of the matrix-space curvature chart. The other conditions of the combined shear theorem still need to be checked.

**The limit theta=1 is not justified.** Even for smooth input q is generally only C11. The strong margin estimate deteriorates; repeated subtractions from the current q are just a larger total subtraction from the original q. If f-q were globally RC in this quadratic-tail class, its compact support would force it to vanish on every rank-one line (convex and zero outside a bounded interval), so a positive defect cannot survive unlimited subtraction as RC. This explains why (5) alone cannot be iterated to make the secondary gap zero. A new curvature-preserving repair/contraction is required. The exact operation is not merely a heuristic adjustment of T independent of the constitutive energy.

## 5. Chart-free absolute gap amplification by a rank-one envelope

There is a second way to use q and d. It handles arbitrary obstacle amplification parameters by an actual rank-one convex envelope, rather than assume the amplified obstacle is RC.

Fix 0<kappa<m and c>1. Define the obstacle
       U_c=q+c d=F+(c-1)d
and its kappa-strong RC envelope
       G_c(X)=kappa |X|²/2+R[U_c-kappa |X|²/2](X),
where R is the usual global rank-one convex envelope. The lower minorant F-kappa |X|²/2 is RC, so this envelope is finite and
       F<=G_c<=U_c.
The function G_c is globally kappa-strongly RC. It is C11 with Lip DG_c<=(2c-1)M: the obstacle has this semiconcavity bound; the infimum over finite laminate splitting trees preserves the semiconcavity bound after subtracting the fixed quadratic and adding it back. Rank-one convexity gives the corresponding opposite Hessian bound as above. Also G_c=F=q on the entire old contact set and on the original quadratic exterior.

The QC and PC envelopes of U_c equal q,p, by precisely the minimizing-law argument of (5) (the additional term (c-1) int d tends to zero). Sandwiching G_c proves
       QG_c=q, PG_c=p.
Thus this amplifier preserves the entire QC/PC gap function, not merely its value at one base.

At any maximum-defect base A with d(A)=D>0, Dd(A)=0 and Lip Dd<=2M give
       d(X)>=max(0,D-M|X-A|²).
Use the infimum formula for the rank-one convex envelope over finite laminates with mean A. For each such law nu, its variance E obeys
       int U_c-kappa E/2
          >= F(A)+(m-kappa)E/2+(c-1) int d.
Pointwise, for v=|X-A|²>=0,
       (m-kappa)v/2+(c-1)max(0,D-Mv)
          >= D min(c-1,(m-kappa)/(2M)).
Consequently
$$
\boxed{
G_c(A)-q(A)\ge D[1+\min(c-1,(m-\kappa)/(2M))].
}                                                        (7)
$$
This is a strictly larger exhibited absolute defect at every old maximum, for every c>1. No nondegenerate projective chart is required. If c-1<=(m-kappa)/(2M), the lower bound is cD and the obstacle upper bound is exactly cD. Equality holds at A and its derivative there is the derivative of U_c (equal to DF(A) at the old maximum). In that range the global maximum is exactly cD; the same minimizing law and old contact values/derivatives give a shifted full lift with new defect cD and unchanged centered oscillation S, after recentering the base. This improves the ratio of stress oscillation to defect. At larger c we assert only the stated lower bound and preservation of q,p/contact data, not an equality formula for the new maximizing base or an unchanged curvature bound.

For small c the obstacle is already RC by the elementary Hessian bound (so the envelope repair is unnecessary); (7) is useful because the RC envelope construction is valid for arbitrary c. It is NOT an unbounded growth estimate as c increases: the explicit lower bound saturates, and the Hessian budget increases with c. Choosing kappa=m would also eliminate the variance slack used in this proof. Thus there is no justified infinite iteration with fixed curvature bounds or positive normalized gain.

## 6. Remaining exact gate and verification

We now have two different exact chart-free operations: preserve D and shrink the QC/PC gap and the centered stress by subtracting q; or preserve both envelopes and increase the exhibited defect via the rank-one envelope. The new planar pinching theorem gives a contradiction if one can drive (QF-PF)/(F-QF) to zero **while retaining the uniform rigidity bounds**. However the subtraction may reach the boundary of RC, and the rank-one envelope amplifier has a growing Hessian budget and possibly a falling strict margin. The rigidity constant in (4) is not known uniformly under those operations, especially through loss of C2 regularity. No positive-accuracy computation can substitute for that missing uniform control.

In particular:
- direct polyconvex-contact rigidity is proved for the whole complete smooth strongly RC quadratic-tail class, not a fixed number of wells;
- the estimates are valid down to arbitrarily diluted bounded gradients;
- a maximum-defect law must have strictly positive secondary QC/PC gap, which cannot simply be ignored in attempting to continue the inner shear;
- one concrete next target is a normalization-preserving operation that reduces the secondary gap or centered stress by a fixed factor, without sacrificing all rank-one curvature or C2 compactness. Another is to show q has a touching polyaffine support at a suitably chosen defect base after an admissible transformation. Neither target is proved.

The companion [envelope_contact_exact.py](../../research/audit/envelope_contact_exact.py) was actually executed. Its SHA-256 is 6c4646182ed8e5ff6b055c0ac58d219d09b4b9cf6e776d7a711320f200be0419. The exact stress contraction, base-defect and envelope-level identities and 360 rational atom-penalty budget checks passed. These check algebra only. The key new coercivity is a hand proof using the cited published planar incompatibility and transition-layer results; no formalization or independent proof review has been performed. The unrestricted Morrey problem remains open. There is no defensible percentage or assertion of near-completion from the remaining gates.
