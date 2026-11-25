# Stop-rule continuation: a tangent maximum principle and a curvature-independent barrier to fixed-contact flattening

24 November 2026. Follow-up to [the exact local-collapse falsification](IWANIEC_MORREY_NO_LOCAL_COLLAPSE.md). The task was to prove a compatibility-preserving improvement of an actual minimizing contact law, using its additional energy optimality rather than merely its support. That task remains OPEN. Do not count the result below as closure of that task.

The useful exact consequence is that the previous fixed-contact contraction obstruction does not require a positive lower curvature bound at all. Thus trying to overcome R24 by letting the ellipticity margin vanish cannot finish that route. We also obtain a uniform positive-energy tail condition for bounded, support-separated laws with fixed positive lower/upper rank-one curvature, without C2 compactness. These are hand arguments, not a new Lean theorem. No solver search, numerical regression claim, independent review or priority claim is made.

## 1. A tangent maximum principle for all compact planar gradient laws

Let nu be a compact homogeneous gradient Young measure on R2x2 with barycenter A and support K. Let F be finite rank-one convex, differentiable at A, and let m>=0 be a strong RC margin (m=0 is allowed). Define

    f(X)=F(A+X)-F(A)-DF(A):X,
    K0=K-A,
    Q(X)=|X|²/2.

Then f(0)=Df(0)=0, f-m Q is RC, and the translated gradient law has mean zero and determinant mean zero.

**Theorem.** There is a compact laminate mu supported on K0 whose barycenter B satisfies det B=0. This laminate depends only on K0, not on F. In particular, for EVERY such F and EVERY real determinant gauge c,

    int f dmu >= (m/2) int |X|² dmu,
    max_(X in K0) [f(X)-c det X-m|X|²/2] >= 0.            (1)

Proof. If K0 contains a singular matrix, its Dirac measure suffices. Otherwise the zero determinant moment forces K0 to contain both a positive and a negative determinant matrix. Faraco and Székelyhidi, *Tartar's conjecture and localization of the quasiconvex hull in R2x2*, Acta Math. 200 (2008), 279--305, Theorem 6, p. 300, [DOI](https://doi.org/10.1007/s11511-008-0028-1), prove that the rank-one convex hull of the support of a compact homogeneous gradient Young measure is connected. Its connected image under the continuous determinant contains zero. Consequently some singular B belongs to (K0)^rc. By the usual compact laminate representation of that hull (also stated in their Section 2), a compact laminate mu on K0 has barycenter B.

Apply its Jensen inequality to f-m Q. Since det B=0, B is a rank-one matrix or zero, and the supporting tangent inequality on the rank-one line through zero gives (f-m Q)(B)>=0. This proves the first inequality of (1). Since int det X dmu=det B=0, the second follows by bounding the integral of f-m Q-c det by its maximum. QED.

In particular

    inf_c max_K0(f-c det) >= (m/2) min_K0 |X|².           (2)

For a support separated from zero and m>0 this is a strictly positive lower bound. For m=0 it still prohibits every strict negative constant upper cap on f throughout the support. The determinant gauge is arbitrary. The assertion is about a supremum or an alternative laminate with a singular barycenter, NOT about int f dnu. The laminate need not have barycenter zero, nor be compatibly removable from nu. In particular no contradiction to a negative average for nu follows from (1).

There is an elementary finite evaluation of the left side of (2) for finite K0. More generally, it equals the maximum average of f over probability laws supported on K0 with determinant mean zero (no matrix-mean constraint). To see this, take the compact convex hull of the pairs (det X,f(X)). If determinant has both signs, the upper boundary at abscissa zero has a finite supporting line and its intersection with that line gives the stated equality; a point on the exposed line is a convex combination of at most two original pairs. If determinant does not have both signs, the original law's zero determinant moment implies det X=0 throughout K0, and both expressions are simply max f. Thus the maximum is attained by a one- or two-point determinant-neutral law. Such a law is NOT necessarily rank-one connected, a laminate or an actual gradient law. The singular-barycenter laminate above, rather than that two-point law, establishes the spatial inequality. This is a support test, not a fixed-atom reduction of Morrey.

## 2. A sharp limitation on the entire fixed-contact flattening idea

Use the recentered maximum-defect setup of R21 and R24. Its fixed nontrivial compact gradient law nu has mean zero, support K away from zero, int f=-D<0 and f(0)=Df(0)=0. The previous fixed-contact repair proposes values

    g(0)=0, Dg(0)=0,
    g(X)=a(f(X)+D)-d on K,

where a is the stress contraction factor and d the intended positive Jensen defect.

Regardless of HOW g is constructed, suppose only that g is finite, differentiable at zero and RC globally. Apply (1) to g with margin zero. Put

    B_K = inf_c max_K [f(X)-c det X] >= 0.

For a>0, varying the gauge of g by a times c gives

    d <= a(D+B_K).                                      (3)

If a=0, (1) gives d<=0 directly. If g has lower margin kappa>=0, with r=min_K |X|>0, the stronger inequality is

    d + kappa r²/2 <= a(D+B_K).                           (4)

These bounds use neither the upper quadratic-support construction, its QC lower barrier, the upper Hessian bound, nor any strictly positive lower margin for g. They also hold if g has an arbitrary nonsmooth Hessian, as long as its stated tangent exists. They are in addition to, and independent of, the R24 bound based on a chosen nontrivial laminate supported on K.

For approximate contact values, if sup_K |g(X)-[a(f(X)+D)-d]|<=eta, the right side of (3) increases by at most eta. Thus there is no limit with a->0, eta->0 and d bounded below by a positive number on the same support. Allowing the lower LH margin to tend to zero does not help. If f and K are fixed, B_K is finite; with a normalized full Hessian bound M and radius R, B_K<=MR²/2 by taking c=0. This is a genuine limitation even of a hypothetical unrestricted jet-repair scheme, not just a failure of the repair algorithm previously used.

## 3. Uniform positive-energy tail, without a common C2 modulus

This is a quantitative strengthening of the support statement in the normalization relevant to the bounded maximum-defect route. Fix 0<m<=M, 0<r<=R. Let F vary over the rank-one curvature sandwich (m,M) of [R24](IWANIEC_MORREY_LH_COMPACTNESS_JET_REPAIR.md), normalized F(0)=DF(0)=0. Let nu vary over compact homogeneous planar gradient Young laws with mean zero and support in r<=|X|<=R. Then there is a constant eta(m,M,r,R)>0 such that, for every real c,

    int (F(X)-c det X)_+ dnu >= eta(m,M,r,R).             (5)

Neither a common full-Hessian bound nor continuity of second derivatives is required. The constant is nonconstructive here.

Proof. Suppose the integrals tend to zero along F_j,c_j,nu_j. By the explicit multiaffine interpolation and local C1 compactness modulo affine+determinant gauges proved in R24, choose determinant coefficients b_j so that h_j=F_j-b_j det are locally C1-precompact. Indeed after subtracting the affine+determinant gauge in that proof, subtract its remainder's value and derivative at zero; because F_j has zero tangent, only a determinant subtraction remains. In particular on B_R the functions h_j have a common absolute bound L0 and Frobenius Lipschitz bound L1 (enlarge L1 to be positive). They retain the strong rank-one margin m and zero tangent.

For any X in the annulus choose the closest singular matrix S by singular-value decomposition, deleting its smaller singular value. Then |S|²>=|X|²/2>=r²/2, |X-S|<=sqrt(|det X|), and S belongs to B_R. Since h_j-m Q is RC with zero tangent at zero, h_j(S)>=m|S|²/2. Thus

    h_j(X)>=m r²/4-L1 sqrt(|det X|).

Write v_j=h_j+(b_j-c_j)det. Its average equals that of h_j by the determinant null Lagrangian, and is bounded above by int (v_j)_+->0. Averaging the previous inequality and using Cauchy--Schwarz shows, eventually,

    int |det X| dnu_j >= (m r²/(8L1))² > 0.

The determinant signs have equal weighted masses because its average is zero. Also pointwise (v_j)_+ >= ((b_j-c_j)det)_+ - |h_j|. Hence

    int (v_j)_+ >= (|b_j-c_j|/2) int |det X| - L0,

which forces b_j-c_j to stay bounded. After a subsequence v_j converges locally in C1 to a normalized energy v in the same sandwich. The bounded laws have a weak limit nu, again a homogeneous gradient law by the closedness of the bounded-support class. The support stays in the closed annulus and mean zero is preserved. Passing to the limit gives int (v)_+=0; continuity implies v<=0 on the entire support of nu.

This contradicts (2), since max_(supp nu) v>=m r²/2>0. QED.

The annulus separation is used essentially in this argument. The theorem does not assert a relative estimate for arbitrary concentrating or diluted sequences, or any relation of eta large enough to compensate for the entire negative part of the energy. In particular (5) is NOT a proof of the integral Jensen inequality. In the maximum-defect setup with a fixed positive defect D and common full-Hessian bound M, R21 gives r>=sqrt(D/M), so the statement directly applies. The previous R24 effective certificate machinery is not invoked here.

## 4. Stop rule and remaining problem

The published planar connectedness theorem was checked directly (Theorem 6 and Corollaries 1--2, pp. 300--301). Its use here is distinct from an unsupported claim that K^rc contains the original barycenter. We only obtain a point of its hull on the determinant-zero cone through the base. Neither ordinary support connectedness, (1), nor the necessary positive-energy tail (5) establishes a legal energy-decreasing change of the original minimizing law. The six-atom falsifier in N18 already prevents the universal support-only extraction.

The specialized lemma needed to advance the unrestricted proof remains unproved. We did not find a valid way to exploit the extra minimizing-law optimality to extract a compatible improvement. The present result also eliminates the apparent escape of continuing fixed-contact stress flattening with vanishing ellipticity. Do not resume that ladder or present these necessary conditions as evidence of proximity to a solution. No new computation over hypothetical minimizing supports was performed. Morrey remains open in the unrestricted planar case.
