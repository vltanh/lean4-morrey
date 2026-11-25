# An exact LP-discovered all-affine moment certificate for the beta attack

24 November 2026. Continue the computer-assisted exact-zero attack after [N22](IWANIEC_MORREY_BETA_ADAPTIVE_CERTIFICATE.md). Instead of another guessed covariance normalization, derive a parameter-uniform polynomial certificate for approximate blocked geometry. Its entire infinite affine-test family is expressible in finitely many preserved moments. This also gives a complete, very small finite-dimensional proof of positive residual separation for the bounded-amplitude **polyconvex** stabilization branch.

**Results.** Let H be globally C11 with lower rank-one curvature m>0 and Lip DH<=M, normalized H(0)=DH(0)=0. For any mean-zero compatible gradient Y, including arbitrary W1,2 amplitudes, write kappa=m/M and j=int H(Y), E=int|Y|². We prove

    E <= (4/m) j
       + (16/kappa²+4/kappa-2) int |det Y-tr Y|
       + (8/kappa²+4/kappa-2) int |skew Y|².                 (1)

No nonnegativity, PC or QC assumption on H is needed. The one special spatial input is the previously verified truncated determinant and its translated limit. A six-variable LP with fifteen coefficient inequalities discovers the certificate polynomials; seven exact square decompositions prove the continuum result, not a sampled inequality.

Applying (1) to arbitrary constant invertible left/right transforms gives a universal family of necessary inequalities depending only on the lifted weighted covariance Gamma=int (X,det X) tensor (X,det X)/(1+|X|²) and the ordinary matrix covariance. Thus an entire affine family of regression constraints can be imposed AFTER finite moment reduction. This resolves the specific infinite-test preservation problem for this detector, not for all QC tests. Adding Gamma to the N22 baseline gives at most 58 atoms. There is no bound on their coordinates.

For PC H and |X|<=R with E=1, the new detector and a robust PC reweighting inequality prove uniform positive separation j>=epsilon(m,M,R)>0 using a compact semialgebraic feasibility problem with just a symmetric 5x5 covariance matrix (15 scalar entries) and the scalar residual. No atom variables, higher-order mesh, smooth Hessian modulus or gradient-Young-measure characterization enter that proof. For rational bounds a terminating real-algebraic decision procedure yields a rational positive epsilon; the full quantified decision problem has NOT been run. This closes this particular bounded-amplitude PC branch, not the general stabilized QC branch. R23/R24 already provided related qualitative rigidity; the new contribution is the explicit detector and low-dimensional finite certificate.

**Limits.** For a hypothetical positive b=-beta_* the universal stabilization H=F+b|.|² is QC and strongly RC, but not known PC, and near-extremizers may concentrate at unbounded amplitudes. The PC reweighting inequality cannot be applied to arbitrary QC H on conditioned laws. No unrestricted infeasibility certificate, self-contraction, gap separation for beta_*, improved universal bound, negative actual gradient witness or Lean theorem is claimed. The LP and exact arithmetic checks below were actually executed. These are hand arguments pending independent review.

## 1. A spatial detector with no amplitude cutoff

Let C be the linear cofactor involution on planar matrices, and let the norm be Frobenius. The verified QC kernel, as used in R06, is

    K_r(A)=(s-r)_+(r-det A/s), s=||A||op,

with the value zero for s<=r. It is r² L(A/r)-det A, where L is the truncated determinant from the pinned lean4-iwaniec dependency. The translated limit of the same kernel is

    G(Z)=(-lambda_min(sym Z))_+ lambda_max(sym Z).

Indeed for Z in a bounded set and r sufficiently large, det(Z-rI)>0 and its two singular values are r-lambda_min(sym Z)+O(1/r) and r-lambda_max(sym Z)+O(1/r), in decreasing order. This follows by expanding (Z-rI)^T(Z-rI)=r²I-2r sym Z+Z^T Z and using the symmetric eigenvalue perturbation bound. The formula for K_r then gives locally uniform convergence K_r(Z-rI)->G(Z). Hence G is QC on bounded compatible gradient tests. It is continuous with |G(Z)|<=|Z|²/2, so strong W1,2 gradient approximation proves Jensen on that class too (quadratic growth and uniform integrability of the squares). In particular,

    int G(I-Y)>=G(I)=0                                     (2)

for any mean-zero compatible Y. This uses actual spatial compatibility and is not a determinant moment alone. The same G appeared in the earlier blocked-law note; the present quantitative certificate is new.

## 2. LP discovery and exact continuum proof

By strong RC along the two orthogonal rank-one singular summands R,S of Y and Lip DH<=M,

    H(R+S)>=H(R)+DH(R):S+(m/2)|S|²
           >=(m/2)|Y|²-M|det Y|.                           (3)

We seek a pointwise estimate which integrates using (2). Put Z=I-Y, let S0=sym Z, and define
    r=tr S0-2, d=det S0, e=|d-1|, k=|skew Y|².
In two dimensions,
    |Y|²=r²+2r+2(1-d)+k,
    det Z=d+k/2,
    det Y=d-1-r+k/2,
hence |det Y|<=e+|r|+k/2. On S0>=0 one has G(Z)=0; otherwise G(Z)=-d (including indefinite S0).

Normalize h=H/M and kappa=m/M, with 0<kappa<=1. Set A=4/kappa>=4. The proposed certificate is

    |Y|² <= A h + B e + C1 k + lambda r - mu G(Z).         (4)

Take lambda=A-2 and C1=A/2-1. Subtract the left side, use (3) and A*kappa=4, and expand. The residual is bounded below by

    R=r²+A(r-|r|)+2(1-d)+(B-A)e-mu G(Z).                   (5)

Search for mu,B of degree at most two in A-4, with nonnegative coefficients. The square-completion budgets are the polynomial inequalities

    mu-A²>=0,
    B-A+2-mu>=0,
    B-A-2>=0,
    B-A+2-4A>=0,
    mu-4>=0.

Require each coefficient in the basis (A-4)^i, i=0,1,2, to be nonnegative. This sufficient condition is a finite LP: six unknown scalar coefficients and fifteen linear inequalities. Minimize the sum of the six coefficients. SciPy HiGHS returned the coefficient vectors (16,8,1) and (18,9,1), objective 53. Reconstruct exactly and check all fifteen inequalities over the rationals, giving

    mu=A², B=A²+A-2.

The objective is merely a discovery choice; no claim of global optimality among all certificates. To prove (4), the following exact identities give all cases of (5):

| S0 | r | d | exact residual |
|---|---|---|---|
| PSD | >=0 | <=1 | r²+mu e |
| PSD | >=0 | >=1 | r²+(mu-4)e |
| PSD | <0 | <=1 | z²+2A(2e-z)+(mu-4A)e, z=-r |
| non-PSD | >=0 | <=1 | r²+mu |
| non-PSD | >=0 | >=1 | r²+mu+(2mu-4)e |
| non-PSD | <0 | <=1 | (z-A)², z=-r |
| non-PSD | <0 | >=1 | (z-A)²+(2mu-4)e |

The third row is valid because PSD and r<0 imply 0<=tr S0<2 and d<=1. If its eigenvalues are p,q>=0, then 2e-z=(p+q)-2pq = (p+q)(2-p-q)/2+(p-q)²/2>=0. The omitted PSD r<0,d>1 region is empty. All coefficients are nonnegative for A>=4; the script verifies each polynomial identity. Thus this is a finite exact square certificate over the full real parameter domain, not evidence obtained by checking a mesh of matrices.

Integrate (4). The trace term integrates to zero and (2) implies the last term contributes nonpositively. Substitute
    e=|det(sym(I-Y))-1|
       <=|det Y-tr Y|+k/2.
Since A/M=4/m, B=16/kappa²+4/kappa-2 and C1+B/2=8/kappa²+4/kappa-2, we obtain (1). This proof does not require H>=0, PC or QC. All integrals exist for W1,2 gradients by quadratic growth.

In particular exact symmetric determinant-one trap geometry after affine normalization forces j>=m E/4, rather than merely excluding the zero-energy limit. This lower bound is relative, independent of amplitude/dilution and valid also for approximately blocked laws with the stated explicit errors.

## 3. Preserve the ENTIRE affine detector family with finitely many moments

Return to an actual mean-zero gradient X with int|X|²=1 and a common H as above. Write z=(vec X, det X), C_X=int vec X tensor vec X, and

    Gamma=int z tensor z/(1+|X|²).

All Gamma entries are integrable even for W1,2 gradients; the bottom-right integrand is <=|X|²/4, cross entries have at most linear growth, and top entries are bounded. They are continuous functions of X. Let P,Q be ANY invertible real 2x2 matrices and Y=P X Q. The gradient law of Y is compatible by the usual affine-domain equivalence (or approximate on an affine lattice). Apply (1) to the pullback energy H_T(Y)=H(P^{-1}YQ^{-1}). Admissible curvature bounds are
    m_T=m/(||P||op²||Q||op²),
    M_T=M ||P^{-1}||op²||Q^{-1}||op².
Frobenius norm versions with these factors enlarged are also valid and convenient for rational semialgebraic formulas. The Jensen residual j does not change.

The key exact identity is
    det Y-tr Y = a(P,Q) dot z,
    a(P,Q)=(-vec((QP)^T), det(P) det(Q)).
Cauchy-Schwarz gives
    int |det Y-tr Y| <= sqrt(2 a^T Gamma a).                (6)
Also E_Y=int|Y|² and K_Y=int|skew Y|² are linear functions of C_X, with polynomial coefficients in P,Q. Thus (1) implies the necessary inequality for EVERY invertible P,Q

    E_Y <= (4/m_T) j
          + B(m_T/M_T) sqrt(2 a^T Gamma a)
          + D(m_T/M_T) K_Y,                               (7)

where B(kappa)=16/kappa²+4/kappa-2 and D(kappa)=8/kappa²+4/kappa-2. For bounded X with finite ordinary lifted covariance Sigma=int z tensor z, we can also use sqrt(a^T Sigma a) in place of sqrt(2 a^T Gamma a). Both are valid; the unweighted one will be convenient below.

This is important for finite certificate search: (7), universally quantified over P,Q, depends on just the two displayed matrices and j. It is therefore retained EXACTLY by preserving those moments before Caratheodory. The N22 baseline with 43 atoms already preserves ordinary lifted covariance including C_X; add 15 scalar weighted Gamma entries to obtain at most 58 atoms for that same baseline. Bounded smooth actual witnesses suffice for near-extremization, so ordinary fourth moments are finite before reduction. No fixed support/amplitude bound has been asserted. The preserved functions are continuous on the bounded range, and the usual finite moment Caratheodory proof applies.

There is no logical step asserting that these reduced laws are gradients. We have instead proved a genuinely universally quantified necessary constraint on finite moments, valid for arbitrary affine transforms of the ORIGINAL law. At fixed b>0, all parameters of H=F+b|.|² in (7) are explicit. The square root, matrix inverses and curvature constants can be encoded by semialgebraic equations (or use the Frobenius norm bounds). This answers the previous N22 infinite-test preservation objection for this specific quantitative affine family. It does not automatically extend to arbitrary QC tests.

Both previous exact trap families have a normalizer with a^T Gamma a=K_Y=0 and E_Y>0, hence fail (7) at j=0 for every scaling and anisotropy. For each fixed such normalizer, the same strict separation persists under sufficiently small perturbations at the same positive b. The script checks 18 transformed/diluted controls and 18 rational small rank-one perturbations, with amplitude scales 1,3,1000 and anisotropy factors 1/2,1/10,1/100. For the perturbed checks it uses the rigorous upper budget j<=5 eps/8 when the common stabilized H vanishes on the original support and Lip DH<=5/4; it does not claim to reconstruct H numerically. The sufficient contamination weights are intentionally conservative. This does NOT assert a uniform relative exclusion of all nearly blocked sequences whose normalizing condition numbers or scales diverge; (7) explicitly shows the dependence on those parameters.

## 4. A complete finite proof for the bounded-amplitude PC stabilization branch

Here is one closed finite subproblem with no fixed number of gradient atoms or waves. Fix R>=1, 0<m<=M. Assume H is additionally PC and X is an actual mean-zero gradient with E=1 and |X|<=R. Prove j>=epsilon(m,M,R)>0.

### 4.1 Robust PC reweighting, rather than existential nonblocked tests

If a finite H with Lip DH<=M is PC, choose a convex representative g(X,d) on the lifted space with g(X,det X)=H(X). For any matrix A and scalar d, take R1 with det R1=d-det A and |R1|²=2|d-det A|, using a scaled conformal or anticonformal matrix. The midpoint of the lifted matrices A+R1,A-R1 is (A,d). By convexity and the quadratic Taylor upper bound,
    g(A,d)<=H(A)+M|d-det A|.
The representative is finite on the entire lifted space by the same construction, and convex in d. The displayed global linear upper bound implies its slope in d lies in [-M,M]. Thus for any compact probability law with mean B and determinant mean D0, even with incorrect minors,
    int H >= g(B,D0) >= H(B)-M |D0-det B|.                (8)
This assertion relies essentially on PC, NOT merely QC.

Put Sigma=int z tensor z for z=(vec X,det X), and choose any c with |c|<=1/(R+R²). Since mean z=0 and |z|<=R+R², the two probability reweightings 1±c dot z are nonnegative. Their matrix means are ±B and determinant means ±D0, where (vec B,D0)=Sigma c. Apply (8) to both and (3) at ±B. The result is the closed necessary inequality
    j >= (m/2)|B|²-2M|det B|-M|D0|                         (9)
for EVERY such c. We used only PC for the reweighted laws; they are not asserted to be compatible. Unlike the earlier existential covariance condition, (9) is stable in the covariance variables.

### 4.2 The finite covariance problem

Use only a symmetric 5x5 matrix Sigma (15 scalar entries) and scalar j. Impose:

* Sigma PSD, C_X its upper 4x4 block, trace C_X=1 and tr(C C_X)=0 (the latter is twice the average determinant).
* 0<=j<=m/4, (m/(4M))²<=Sigma_55<=R²/4. The lower bound follows from (3), j<=m/4 and Cauchy-Schwarz; the upper follows from |det X|²<=R²|X|²/4.
* For every unit vector v representing a rank-one matrix,
      Sigma_55<=R²(1-v^T C_X v).
  Indeed the orthogonal projection of X to that line has zero determinant, and the derivative norm of determinant on B_R is <=R.
* All (9) for |c|<=1/(R+R²).
* All (7) with sqrt(a^T Sigma a) instead of the weighted root, for all invertible P,Q.

These are finite semialgebraic quantified constraints with **no atom coordinates and no function variables**. The feasible set is compact: diagonal bounds and PSD bound all entries, j is bounded, and every inequality for each fixed test parameter is closed in (Sigma,j). If an actual gradient has j>m/4 it is already separated; otherwise its covariance and j satisfy these constraints. The problem is an outer relaxation, not a characterization of covariances of gradient laws.

### 4.3 Exclude j=0 for the entire covariance relaxation

Suppose an admissible covariance has j=0. Let S=range Sigma, L its projection to R4, V={X in L:(X,0) belongs to S}. The range of C_X is L (by PSD). If V contains a nonzero rank-one R1, choose c with Sigma c=(vec R1,0), and scale c down to fit its allowed ball. Then (9) gives a strictly positive right side, contradiction.

The determinant quadratic form q restricted to L has zero trace against C_X, which is positive definite on L. Thus it is indefinite or identically zero. If identically zero then every nonzero vector of L is rank-one; since dim V>=dim L-1, absence of rank-one directions forces dim L=1 (L is nonzero by trace one). But on this rank-one line v^T C_X v=1, so the rank-one-line inequality forces Sigma_55=0, contrary to its positive lower bound. Therefore q|L is indefinite.

If S has a vertical kernel, S=L times R and V=L, which would contain a nonzero null vector of q. Thus S is the graph of a linear form ell:L->R. Ell is nonzero and V=ker ell is definite for q. The determinant form has signature (2,2); V has dimension one or two, L dimension two or three. Change the sign of q if necessary to make V positive definite. Its q-orthogonal complement in L is one-dimensional and negative definite by indefiniteness. Hence q|L is nondegenerate.

There is a unique C0 in L with ell(X)=(cof C0):X by determinant polarization. It lies in the negative line (up to the chosen sign) and det C0!=0. On S the affine determinant relation is exact, so for Y0=X C0^{-1}, the linear expression det Y0-tr Y0 in the lifted coordinates vanishes on S. Indeed it equals (d-ell(X))/det C0 at a lifted vector (X,d). The transformed linear subspace L'=L C0^{-1} contains I and has determinant signature (1,dim L-1), with I the positive direction. Its determinant-orthogonal complement to I is a negative definite subspace of the traceless matrices.

As in the earlier blocked classification, make all of L' symmetric by one real similarity U: extend that traceless negative subspace, if needed, to a negative plane in the traceless determinant form of signature (1,2). Choose a positive unit determinant J0 on the orthogonal line. Its trace is zero and J0²=-I, so conjugate it to the usual rotation J=[[0,-1],[1,0]] using a real basis (v,J0 v). Orthogonality to J for a traceless matrix means its two off-diagonal entries coincide. The transformed L' therefore consists of symmetric matrices. This is a linear-space argument, not a reconstruction of atoms or an assumption of an actual gradient law for the covariance.

Set P=U, Q=C0^{-1}U^{-1}. Since a(P,Q) annihilates S, a^T Sigma a=0, and since the image of L is symmetric, K_Y=0. Invertibility and trace C_X=1 give E_Y>0. Inequality (7) at j=0 would say E_Y<=0, contradiction. This eliminates the entire j=0 slice of the covariance problem.

### 4.4 Exact consequence and computability

By compactness the minimum j on any nonempty feasible set is strictly positive. Together with the j>m/4 alternative this proves j>=epsilon(m,M,R)>0 on all actual bounded-amplitude PC tests, uniformly over all energies with the given curvature bounds. No C2 modulus, mesh count or unknown integrand-specific constant enters. For rational m,M,R the finite semialgebraic statement can use the Frobenius norm versions of m_T,M_T to avoid spectral functions. Exact real quantifier elimination decides each test of feasibility with j<=2^-k. Enumerating k until the first infeasible stage is a terminating algorithm, with termination justified above. This proof of termination does not assume Morrey. The full quantified search was not executed, and no numerical value of epsilon is claimed. The low-dimensional covariance formulation replaces the much larger mesh and energy interpolation problem for this restricted branch.

The PC reweighting condition is essential in this reasoning. At a TRUE hypothetical b>0, H=F+b|.|² has lower LH margin 2b and is QC by the definition of beta_*, but there is no argument that H is PC. Its arbitrary reweighted laws in Section 4.1 are not necessarily compatible. The covariance compactness also uses a common amplitude bound R in this branch; (1) and (7) alone do not furnish such a bound. Thus the closed PC branch is not a finite reduction of the general conjecture. The next substantive target would be to justify a replacement for (9) on general QC critical laws, or a different finite inequality excluding them, while retaining control of concentrations. Do not simply impose (9) on QC H or count the PC result as exact zero of beta_*.

## 5. Executed computation and scope

Run research/audit/beta_hyperboloid_sos.py (Python 3, SciPy, NumPy, SymPy). Local execution used SciPy 1.17.0 and SymPy 1.14.0: HiGHS optimal objective 53, exact rational coefficient vector (16,8,1,18,9,1), all 15 coefficient inequalities, seven exact local square identities, PSD trace identity and skew coefficient, 18 exact transformed/diluted and 18 near-critical nonblocked controls, and generic affine coefficient and covariance trap identities passed. SHA-256 4324a7e6c4fa42f2ba5b825c0f5512811f2c7ddcc48e42b323d31215625c1e02; Git blob 7273010d1eb0b71e8d20295e0bd1e057cdc79e85. The script verifies the finite algebra; the global gradient and PC compactness arguments are the hand proofs above. No full quantified covariance solve, true negative witness, independent review, new Lean theorem or unrestricted proof was completed.
