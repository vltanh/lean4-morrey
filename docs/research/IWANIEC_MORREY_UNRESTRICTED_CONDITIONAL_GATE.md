# Unrestricted Morrey: eliminate every algebraic terminal trap and isolate a uniform conditional-compatibility gate

24 November 2026. **Research reset:** stop classifying integrand subclasses, exponents, and fixed numbers of waves. Work with the unrestricted gradient law, using the bounded terminal-geometry classification in [ADAPTIVE_MARTINGALE](IWANIEC_MORREY_ADAPTIVE_MARTINGALE.md) and the scalar determinant defect in [MARTINGALE_DEFECT](IWANIEC_MORREY_MARTINGALE_DEFECT.md).

Two useful deductions:

1. Every nontrivial blocked law in the previous complete two-/three-dimensional classification violates Jensen for an affine transform of the SAME already formally established truncated-determinant integrand. Thus neither terminal geometry can itself be a compactly supported homogeneous gradient Young measure. This works also for nonsmooth gradients and limits; connected support is unnecessary. There is a quantitative gap.
2. A uniform partial-resolution theorem, allowing approximate conditional compatibility, would suffice to prove unrestricted Morrey by a contraction argument. The needed operation is explicit; it does not require a classification of all integrands or all gradient distributions. No such universal operation is proved here.

The first deduction does NOT imply that the conditional laws in the old optimal decomposition are gradient Young measures. The missing conditional-compatibility step is the focus of the new roadmap. No new Lean proof, solver-based proof, independent review, or publication-priority claim. Unrestricted Morrey remains open.

## 1. The exact bounded terminal geometry already established

Use the previous adaptive decomposition theorem for a compact law nu of mean A with the correct determinant moment. Maximize resolved variance over decompositions into minor-compatible laws whose barycenter distribution is a laminate. Every nondirac conditional law at an optimum is blocked under minor-preserving binary rank-one observations. The previous classification says that, after centering at its mean b, the support of such a law eta lies in a subspace L of dimension d=2 or 3 with

    det(Y-C)=det C,     Y=X-b in L, C in L,

where, up to an overall sign on the determinant form, L has signature (d-1,1), C is timelike (negative for that convention), and the law charges both sheets. In particular det C != 0.

This is a classification of **all** residual geometries for that optimization, not a bound on atom count or lamination depth. We use it as given in the preceding hand proof. We do not infer any gradient compatibility for the conditional laws merely from their minor identities.

## 2. Normalize both blocked types to the same symmetric determinant-one geometry

Define Z=(X-b-C)(-C)^(-1). Then E Z=I, det Z=1 on the support, and Z lies in the linear subspace L'=L(-C)^(-1), which contains I. The determinant quadratic form restricted to L' has signature (1,d-1): right multiplication rescales the determinant by 1/det C, so the line through I is the timelike line with positive sign.

The determinant-orthogonal complement W of I inside L' is negative definite, of dimension d-1<=2. It consists of traceless matrices, since the determinant polarization with I is half the trace.

**Claim:** one simultaneous real similarity makes the whole subspace L' symmetric. To prove it, on the three-dimensional traceless space write a traceless matrix as [[a,b],[c,-a]], whose determinant is -a²-bc. The determinant has signature (1,2) there. Extend W to a negative definite two-dimensional subspace of this traceless space, if necessary. Its determinant-orthogonal complement is a positive line. Choose an element J0 of that line normalized by det J0=1. By the traceless Cayley-Hamilton identity J0²=-I. With a basis (v,J0 v), for any nonzero v, a real similarity S makes S J0 S^(-1)=J=[[0,-1],[1,0]]. For traceless T, the determinant polarization with J is -tr(JT)/2, which vanishes exactly when the off-diagonal entries of T are equal. Thus every member of S W S^(-1) is symmetric. I is unchanged, proving the claim.

Consequently the affine map

    N(X)=S (X-b-C)(-C)^(-1) S^(-1)

sends the blocked law to symmetric matrices of determinant 1, with barycenter I. Both signs of definiteness are charged: if all matrices were positive definite, tr Z>=2, with equality only at I, and mean trace 2 would force a Dirac law; if all were negative definite their traces would contradict the mean trace. Let p_->0 be the mass of the negative definite matrices in this normalized law.

This uses the planar signature (2,2) and the fact that the residual dimension is at most three. No further classification of individual supports is needed.

## 3. One known quasiconvex kernel excludes the complete trap classification

For r>0 use the known QC kernel

    K_r(X)=(s(X)-r)_+ (r-delta(X)),
    s(X)=||X||op, delta(X)=det X/s(X) (zero at zero).

Indeed K_r(X)=r² L(X/r)-det X, where L is the [formally established truncated determinant](https://github.com/vltanh/lean4-iwaniec/blob/972c01272b2a573ae58fb43fac47c97196db2cbb/Agazzi/Quasiconvex.lean). This is the same kernel as K_r^- in [NONHOMOG_SHELL_AFFINE](IWANIEC_MORREY_NONHOMOG_SHELL_AFFINE.md). Translation, positive rescaling, and invertible left/right matrix multiplication preserve QC, using the affine-boundary domain formulation for right multiplication.

Choose r>max(1,sup_support ||N(X)||op). Define the globally finite QC test

    T_eta(X)=K_r(N(X)-r I).

At the original mean b, N(b)=I and T_eta(b)=0.

For any normalized positive definite matrix Z, both eigenvalues are in (0,r). Z-rI is negative definite with largest singular value r-lambda_min(Z)<r. Therefore K_r(Z-rI)=0.

For any normalized negative definite matrix Z, the two eigenvalues lambda_min<=lambda_max<0 give
    s(Z-rI)=r-lambda_min,
    delta(Z-rI)=r-lambda_max
because det(Z-rI)>0. Hence
    K_r(Z-rI)=(-lambda_min) lambda_max=-det Z=-1.

We obtain the exact negative gap

    integral T_eta(X) d eta(X) - T_eta(b) = -p_- < 0.

**Theorem A.** Every nontrivial blocked law in the complete classification of [ADAPTIVE_MARTINGALE](IWANIEC_MORREY_ADAPTIVE_MARTINGALE.md) violates the Jensen inequality for a translate and invertible left/right transform of the already verified L, up to a determinant null Lagrangian. In particular no such law is a compactly supported homogeneous gradient Young measure. This applies to arbitrary compact support, not merely to a smooth gradient's connected support.

This is a direct certificate, not a claim that the arbitrary blocked laws are planar Morrey counterexamples. It excludes them as actual gradient laws.

### 3.1 Quantitative normalized detection

Suppose the normalized support has op norm <=R with R>=1. On symmetric determinant-one matrices, put t=tr Z. Then
    |Z-I|_F²=t(t-2),     E t=2,     |t|<=2R.
On the positive sheet t>=2; on the negative sheet t<=-2. Hence
    E|t-2|=2 E[(2-t) 1_negative] <=4(1+R)p_-.
It follows that
    Var(Z)=E|Z-I|_F² <= 2R E|t-2| <=8R(1+R)p_-.

Thus the certificate gap magnitude is at least Var(Z)/(8R(1+R)). This controls all normalized blocked configurations of bounded radius. The affine normalization need not be uniformly conditioned across arbitrary traps; no global quantitative cutoff follows from this estimate alone.

### 3.2 A single homogeneous limit detector (optional)

On arbitrary matrices let E(X)=(X+X^T)/2 and let lambda_min,max be its eigenvalues. As r->infinity,

    K_r(X-rI) -> G(X)=(-lambda_min(E(X)))_+ lambda_max(E(X))

locally uniformly. Indeed (X-rI)^T(X-rI)=r²I-2r E(X)+X^T X. Eigenvalue perturbation by X^T X is bounded by ||X||op², and expanding the square roots gives the two singular values r-lambda_min+O_R(1/r), r-lambda_max+O_R(1/r), uniformly on bounded balls. For r>||X||op, det(X-rI)>0 by the path rI-tX, 0<=t<=1. This proves the formula. Local uniform limits of finite QC functions are QC on bounded gradient tests. G is thus a finite positively 2-homogeneous QC detector, requiring no material or frame symmetry. On normalized symmetric determinant-one matrices it is zero on the positive sheet and -1 on the negative sheet. The finite-r proof above suffices and does not depend on this limit calculation.

## 4. One uniform conditional-compatibility gate with a rigorous contraction

The trap result solves the geometric classification/detection part of the earlier adaptive route. It does not show that the optimal *conditional* laws obey the detector inequalities. To make the remaining task quantitative and avoid an endless classification of integrands, use the following independent sufficient criterion.

Let D(nu) be the nonnegative determinant defect defined in [MARTINGALE_DEFECT](IWANIEC_MORREY_MARTINGALE_DEFECT.md), for a compactly supported law nu of mean A:

    D(nu)=inf_experiments E[sum_j |det(M_j-M_(j-1))|+|X-M_n|²/2],

where M_j are conditional matrix means in finite binary experiments. That note proves
    0<=D(nu)<=Var(nu)/2,
    D(nu)=0 iff nu is a laminate,
and the transfer bound for same-mean coupled X,Y:
    D(law X)<=D(law Y)+sqrt(Var(Y)) W_2(law X,law Y)
                       +W_2(law X,law Y)²/2.
The transfer bound uses an optimal coupling (or a limiting sequence of couplings), and does not require the laws to be gradient laws.

**Composition lemma.** For a finite decomposition nu=sum_i p_i nu_i, with conditional means m_i, and coarse law B=sum_i p_i delta_(m_i),
    D(nu)<=D(B)+sum_i p_i D(nu_i).

Proof: choose a finite experiment for B, then reveal the finite child label i completely by binary refinements. The cost of these extra determinant increments is at most half the unrevealed variance of B, since |det H|<=|H|²/2 and martingale squared increments telescope. This replaces the residual term in the experiment for B. A label distinguishing two children with the same mean adds no variance or cost. Realize X by first sampling that label and then sampling from nu_i. The initial experiment's conditional means are the same as the conditional means for B. Append any chosen finite experiment for each nu_i, using auxiliary randomness as necessary. Take infima, which is legitimate for a finite list. QED.

Let C be all actual bounded periodic planar gradient laws with arbitrary base, including constant laws. Define

    Lambda = sup {D(nu)/Var(nu) : nu in C, Var(nu)>0} in [0,1/2].

No homogeneity, isotropy, wave count or integrand degree is present.

**Uniform partial-resolution gate.** Find one theta>0 such that for every nu in C of nonzero variance V and every epsilon>0 there exists a finite decomposition nu=sum_i p_i nu_i and actual bounded gradient laws eta_i with the same means m_i as nu_i, satisfying

    (i)  Var(B) >= theta V,
    (ii) D(B) <= epsilon V,
    (iii) sum_i p_i W_2(nu_i,eta_i)² <= epsilon² V.

One need not represent the whole law by a laminate in a single step. A uniformly positive fraction of the variance must be resolved with negligible determinant cost, and the unresolved pieces must be approximately spatially compatible. A particularly direct version would have B a finite rank-one laminate exactly and nu_i actual gradient laws exactly. No fixed number of children or explicit construction is claimed in this criterion; proving an operation with bounded local complexity would be especially useful.

**Theorem B.** This gate implies unrestricted planar Morrey.

Write e²=sum_i p_i W_2(nu_i,eta_i)² and Q=sum_i p_i Var(eta_i). Variance decomposition gives R=sum_i p_i Var(nu_i)=V-Var(B)<=(1-theta)V. Minkowski for the centered coupled variables, over the mixture and optimal couplings, gives sqrt(Q)<=sqrt(R)+e. Combining composition, the transfer bound and Cauchy-Schwarz gives

    D(nu) <= D(B)+Lambda Q+sqrt(Q)e+e²/2
          <= V [epsilon+Lambda(sqrt(1-theta)+epsilon)²
                         +(sqrt(1-theta)+epsilon)epsilon+epsilon²/2].

For each nu let epsilon->0. Then D(nu)/V<=(1-theta)Lambda. Take the supremum to obtain Lambda<=(1-theta)Lambda. Since Lambda is finite and theta>0, Lambda=0. Every bounded compatible gradient law is a laminate, proving Morrey in the periodic formulation, with the repo's existing domain bridges. QED.

The gate is not asserted to be an easier theorem automatically. It is in fact necessary in an existential sense if Morrey holds: D(nu)=0 supplies arbitrarily low-cost finite experiments whose unrevealed variance is arbitrarily small. Take their terminal conditional laws as nu_i and take eta_i to be Dirac laws at their means. Their coarse conditional-mean tree has determinant cost bounded by the experiment cost, so (ii) holds; the remaining variance gives (iii) and (i) for any fixed theta<1. The constructive challenge is to derive a partial-resolution operation directly from spatial compatibility, without first assuming D=0.

## 5. Research discipline: one gate, not another list of families

The old unrestricted adaptive optimization already reduces every minor-compatible residual to two geometries. Theorem A now gives an explicit verified-QC obstruction for both. It is NOT sufficient to rule out these traps for the original gradient law: conditioning by an arbitrary matrix-dependent likelihood does not preserve gradient compatibility, and positive gaps on other components may conceal the negative conditional gap. In particular we must not treat the old unconstrained maximizer as a decomposition into gradient Young measures.

Attack the single conditional-compatibility gate:

* Seek input-adaptive spatial cuts, projections, or graph changes that produce actual compatible child laws, or child laws with the vanishing error in (iii), while retaining a rank-one coarse mean tree resolving a fixed fraction of variance.
* Use the transformed K or G tests to monitor whether a proposed conditional construction approaches either of the now-excluded terminal geometries. If using a relaxation of true gradient compatibility by these tests, prove that the split preserves the relaxed constraints. Merely adding the constraints invalidates the old terminal classification unless a new feasible-splitting proof is given.
* Use computers only to discover a uniform rule or an actual counterexample to Morrey. A blocked conditional law with no realization, failure of a chosen split rule, or a finite grid gap is not a counterexample. Keep the existing complete strict-negative rational-certificate hierarchy as the parallel fallback; no degree/mesh cutoff is known.

The previous common-filtration no-go still applies: the operation must be input-adaptive. The uniformity required here is the resolved variance fraction and error budget, NOT a common filtration of the spatial variable.

Stop only on a proof of the universal gate, a certified actual planar counterexample, or a demonstrated failure of the proposed construction with a changed strategy. Further exponents, symmetry families, wave counts, or special radial integrands do not close this gate. No fixed finite exhaustive classification of the original Morrey problem is claimed.

## Verification status

The calculations above are analytic. The determinant-one normal form uses only the elementary traceless 2x2 Cayley-Hamilton identity and determinant signature. The exact detector values use the previously formally established L and the domain invariance of quasiconvexity. The variance and contraction inequalities follow from ordinary martingale variance and the previously recorded defect transfer theorem. No independent formal or numerical validation of this new note is claimed.
