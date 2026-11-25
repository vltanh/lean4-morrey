# Frame-indifferent isochoric and volume-affine energies: complete anisotropic shape theorem

24 November 2026. Hand proofs. The previous [one-sided degree-two theorem](IWANIEC_MORREY_ONE_SIDED_ROTATION.md) is extended directly to GL^+(2); no global finite extension or nonnegativity is required. Shield then eliminates **all material isotropy** in the classical isochoric implication. This also yields a complete nonhomogeneous coupled class and an exact reduction of the arbitrary material-anisotropic additive split to log-homogeneous energies.

The original unrestricted planar Morrey conjecture and arbitrary full-matrix homogeneous Gate 1 remain open. There is no new Lean verification, independent review, or publication-priority claim. The classical bi-isotropic isochoric result is Martin–Ghiba–Neff (2017), https://doi.org/10.1017/S0308210516000275. The proofs here require only one rotation group, not both. We did not find the one-sided representation in that literature search; this is not an exhaustive priority audit.

## 1. Conventions and one-sided degree-two theorem on the open orientation cone

Write d(X)=det X>0 and G=GL^+(2). Rank-one convexity means convexity along every rank-one segment in G. The domain is rank-one convex since the determinant is affine on such segments. A finite rank-one-convex function is locally Lipschitz, by separate convexity on coordinate boxes compactly contained in G. Polyconvexity permits a convex lift on R^(2x2) x (0,infinity), extended by +infinity outside this domain.

**Theorem 1.** For a finite F:G->R, the following are equivalent:
1. F is rank-one convex, positively 2-homogeneous, and left-SO(2)-invariant.
2. For some nonempty set T of pairs (v,k) in R^2 x R,
   F(X)=sup_{(v,k) in T} (|Xv|^2+k d(X)),
   with finite value at every X in G.

In particular every such F is polyconvex on G, without any sign restriction. The supremum lift is finite on every (X,z) with z>0. Right invariance alone has the transposed representation. There is no requirement that T be bounded on this open domain.

**Proof.** At an invertible differentiability base A in G normalize Y=X A^(-1), and put f(Y)=F(YA). The normalization preserves left invariance and rank-one convexity. Set H=f(I), P=Df(I). Left rotations imply P symmetric; homogeneity implies tr P=2H. Let lambda1>=lambda2 be its eigenvalues, e a unit lambda1-eigenvector, and e_perp an oriented perpendicular. For arbitrary Y in G let t=|Ye|>0. A proper rotation Q makes QYe=t e. In this basis QY=[[t,b],[0,d(Y)/t]], so QY and tI are rank-one connected, with the whole segment in G. The tangent of f at tI gives

    f(Y)>=t^2 H+t P:(QY-tI)
         = (H-lambda2)|Ye|^2+lambda2 d(Y).

Here H-lambda2=(lambda1-lambda2)/2>=0. Equality holds at I, independently of the sign of H. Undo the normalization:
    F(X)>=(lambda1-lambda2)/2 |X A^(-1)e|^2
            +lambda2/d(A) d(X),
with equality at A. Absorb the nonnegative square coefficient into v and collect these supports over differentiability bases.

For any X (even singular or orientation reversing) and z>0, there exists H0 with cof X:H0=0 and det H0=z-det X. Indeed the kernel of the linear functional cof X:· has dimension at least three, and the determinant quadratic form has signature (2,2), so this kernel meets both its positive and negative definite two-dimensional subspaces nontrivially. Scale an appropriate direction; use zero when z=det X. Then det(X+/-H0)=z and both matrices are in G. For each support the lifted convex function |Xv|^2+kz at (X,z) is at most the average of F(X+H0),F(X-H0). Hence the supremum lift is finite there (and bounded below by any one support). It is convex and continuous on that open convex domain. Its physical restriction equals F on the dense set of differentiability points, is everywhere <=F, and equals F everywhere by continuity. The converse follows by convexity of the lift and the homogeneity/invariance of each term. QED.

This argument uses no theorem about bi-isotropic energies and no global extension through det=0. In particular it is valid for signed singular-on-boundary energies.

## 2. Exact one-sided isochoric theorem (degree zero)

**Theorem 2.** Every finite left-SO(2)-invariant, positively 0-homogeneous rank-one-convex W on G is polyconvex, with the exact representation

    W(X)=sup_{(v,k) in T} (|Xv|^2/d(X)+k).

Conversely every finite-valued such supremum is rank-one convex, frame indifferent, and positively 0-homogeneous. No sign, differentiability or material symmetry is assumed.

**Proof.** Set E(Y)=d(Y) W(Y^(-1)). This is finite, right-SO(2)-invariant and positively 2-homogeneous. Shield preserves rank-one convexity without a sign assumption: for Y=(1-t)Y0+tY1 on a rank-one segment, d is affine and
    Y^(-1)=[(1-t)d0/d]Y0^(-1)+[t d1/d]Y1^(-1).
The inverse endpoints are rank-one connected. Apply rank-one convexity of W and multiply by d. This proves rank-one convexity of E. The right-invariant version of Theorem 1 gives E(Y)=sup(|Y^T v|^2+k d(Y)). Substituting Y=X^(-1) and multiplying by d(X) gives
    W(X)=sup (|adj(X)^T v|^2/d(X)+k).
With J the proper quarter turn, adj(X)^T=J X J^T, so replace v by J^T v to obtain the claimed representation. Each lift (X,z)->|Xv|^2/z+k on z>0 is convex by the quadratic perspective. Its supremum is convex and finite for every z>0 by the two-atom argument of Section 1. The converse follows immediately. QED.

In normalized right-Cauchy–Green variables S=X^T X/d(X), det S=1, this characterizes the entire one-sided isochoric RC cone as suprema of affine functions v^T S v+k with positive semidefinite rank-one slopes. Arbitrary signed shifts are allowed. For example any maximum of such terms with non-rotationally-invariant directional coefficients is material-anisotropic.

## 3. Genuinely coupled nonhomogeneous consequence: entire volume-affine class

**Theorem 3.** Let W:G->R be finite, left-SO(2)-invariant and rank-one convex. Suppose it is affine in the determinant at each fixed shape, in the precise sense
    W(X)=h0(X)+d(X) h1(X),
where h0,h1 are positively 0-homogeneous. Then W is polyconvex. There is no sign condition, and the two shape functions are arbitrary and may have unrelated material anisotropy.

For a>0, W(sqrt(a) X)=h0(X)+a d(X)h1(X) is rank-one convex. Taking a->0 yields rank-one convexity of h0; dividing by a and taking a->infinity gives rank-one convexity of d h1. Both inherit frame indifference and continuity (the latter follows also from solving the two linear identities at a=1,2). Apply Theorem 2 to h0 and Theorem 1 to d h1, then add the convex lifts. Conversely a sum of such two convex-lift components is polyconvex. In fact this proves the equivalence:
    W is RC iff h0 and d h1 are RC iff W is PC.

This is not restricted to additive distortion/volume separation. For instance W(X)=|Xe1|^2/d(X)+|Xe2|^2-2d(X) is in this class and has coupled scale and shape dependence. Arbitrary nonhomogeneous sums, positive maxima, and convex increasing scalar compositions of the represented energies also give PC energies, but no universal representation of all objective RC functions by this cone is claimed.

## 4. Arbitrary additive split: exact log reduction, no material or frame symmetry needed

Let W(X)=h(X)+g(d(X)) be finite continuous and RC on G, where h is positively 0-homogeneous and g continuous on (0,infinity). No rotation assumption is used in this section.

**Theorem 4.** There exists a finite real beta with
    h(X)-beta log d(X) rank-one convex,
    g(z)+beta log z convex on z>0.
Moreover beta is the largest real b for which g(z)+b log z is convex. For C^2 g, beta=inf_{z>0} z^2 g''(z).

First assume g smooth. On a rank-one line X(t) in G, d(t)>0 is affine. By dilation, q(t)+g(a d(t)) is convex for every a>0, where q(t)=h(X(t)). Thus q has a distributional second derivative which is a signed Radon measure locally (difference of a convex and a smooth function), with nonnegative singular part. For each positive rational a the absolutely continuous density m(t) satisfies
    m(t)+a^2 g''(a d(t)) d'(t)^2>=0
almost everywhere. On a common full-measure set use continuity in a to extend to all a>0. On X(t)=diag(t,1) with 1<t<2, choose a point of finite density and d'=1, which bounds inf_z z^2 g''(z) below. It is finite above by testing z=1. Taking the infimum on any rank-one line gives m(t)+beta d'^2/d(t)^2>=0; if d'=0 this follows directly. Including the singular part proves h-beta log d RC. The other assertion is precisely g''-beta/z^2>=0.

For continuous g, let g_j(z)=int rho_j(t)g(exp(t)z)dt with smooth compactly supported approximate identities in the log variable. Then g_j is smooth and converges locally uniformly; W_j is the average of W(exp(t/2)X), so is RC. The smooth conclusion gives beta_j. They are uniformly bounded above: apply scalar convexity of g_j+beta_j log to fixed distinct endpoints and their midpoint; strict concavity of log gives a finite upper bound in terms of the bounded three g_j values. They are uniformly bounded below: the same q(t)=h(diag(t,1)) has a signed measure second derivative (use W_1), and the simultaneous inequalities m(t)+beta_j/t^2>=0 hold at a common point with finite density. Take a convergent subsequence beta_j->beta. Both RC and convexity pass by locally uniform convergence. If g+b log is convex, then g_j+b log is convex by averaging dilates and dropping constant terms, so b<=beta_j for every j, hence b<=beta. This proves optimality and the theorem. QED.

Consequently the entire one-sided objective additive-split implication reduces to the scalar log-homogeneous gate
    W0(X)=h(X)+c log d(X), c=-beta,
with arbitrary objective degree-zero h. The theorem is the anisotropic version of the normalization in [VOLUMETRIC_SHIELD](IWANIEC_MORREY_VOLUMETRIC_SHIELD.md), not a claim to have solved that remaining one-sided log gate.

**Complete nonhomogeneous anisotropic split at beta=0.** If W is left objective and beta=0, Theorem 4 gives h RC and g convex, so Theorem 2 gives W PC. For smooth convex g the condition is inf z^2 g''(z)=0; it includes e.g. a positive multiple of (z-1)^2 and all positive powers z^q with q>=1. Every convex g having a finite limit at 0 also has beta=0: if beta>0 then g+beta log, convex and finite on (0,infinity), would tend to -infinity at 0, which contradicts any finite supporting affine lower bound at an interior point. The beta=0 class has no material isotropy hypothesis.

For beta!=0, the prior bi-isotropic transfer does not automatically extend to one-sided rotation invariance. In particular the degree-two argument cannot simply be used at degree 2-2 eps c. That would require the higher-exponent one-sided theorem.

## 5. The positive logarithmic branch at every stationary-shape base

Suppose W0(X)=h(X)+c log d(X) is RC and left objective on G with c>=0. Let A in G be a differentiability point of h with Dh(A)=0. Then W0 is quasiconvex at A in the orientation-preserving affine-boundary sense of Astala–Faraco–Guerra–Koski–Kristensen, arXiv:2309.03495.

Normalize G(Y)=W0(YA). Its derivative at I is c I. For Y in GL^+(2), take a proper polar decomposition Y=Q R diag(s,t)R^T, s>=t>0. The matrix R diag(s/t,1)R^T is rank-one connected to I. By frame indifference, the log scaling, and the tangent at I,
    G(Y)>=G(I)+c(s/t-1)+2c log t
         =G(I)+c(W_magic^+(Y)-W_magic^+(I)).
Here W_magic^+(Y)=||Y||op^2/d(Y)+log d(Y)-log(||Y||op^2/d(Y)).
Use the published QC of magic-plus at I and the right-coordinate change X->X A^(-1) (domain becomes A times the original domain). This proves the claimed Jensen inequality. The convex determinant remainder from Theorem 4 can be added, so the result applies also to arbitrary additive splits with beta<=0 at such stationary-shape bases. For c=0 the stronger all-base PC statement was already proved. For c<0, at a global minimum of h the elementary support h(A)+c log d is convex in the determinant and gives QC; stationary points alone are not asserted sufficient there.

The step from stationary shapes to all shapes is not established. At a general differentiability base the normalized derivative is a non-scalar symmetric matrix, and the directional rank-one tangents carry a material-anisotropic linear term. Replacing it by its rotational average would lose the touching inequality. The proof here deliberately does not make that inference.

## 6. Verification and remaining gates

The algebra used in Theorems 1--2 consists of a rank-one column alignment, Euler's identity, the linear planar adjugate, and the quadratic perspective. Sections 3--4 are exact dilation and distributional curvature arguments. No numerical optimization is needed. The new note is a hand proof; no Lean build is claimed.

* Closed here: all signed one-sided degree 2 on GL^+(2); all signed objective isochoric energies on GL^+(2); all objective volume-affine shape couplings; the arbitrary objective additive split at beta=0.
* Reduced exactly: the unrestricted objective additive split to log-homogeneous energies with arbitrary real coefficient.
* Open: that log gate at arbitrary bases and nonzero coefficient, the genuinely nonlinear coupled scale/shape gate, fully anisotropic all-base homogeneous Gate 1 and unrestricted planar Morrey.

The natural next step is to prove all-base touching QC supports for the log gate without imposing material symmetry or trying to force every such energy to be polyconvex. The results are entire functional classes, not a finite list of shape profiles or gradient configurations.
