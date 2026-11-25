# A global rigidity theorem for rank-one-convex homogeneous polynomials on 2×2 matrices

**Status:** Full hand proof; independent exact symbolic checks accompany the note. **Does not settle Morrey's unrestricted 2×2 problem.** This is a classification of an infinite-degree subclass rather than a finite-grid test. It is not claimed as a new theorem without a broader literature/priority audit.

## Main theorem (all homogeneous polynomial degrees)

Let \(P:\mathbb R^{2\times2}\to\mathbb R\) be a homogeneous polynomial, globally rank-one convex, and assume \(P(A)=0\) whenever \(\det A=0\). Then **exactly one of the following holds**:

1. \(P\equiv0\);
2. \(P(A)=c\det A\), homogeneous degree 2, where \(c\in\mathbb R\);
3. \(P(A)=c(\det A)^{2k}\), homogeneous degree \(4k\), where \(k\in\mathbb N_{\ge1}\) and \(c>0\).

Conversely, each displayed polynomial is rank-one convex, since on any rank-one line \(A+tH\) the determinant is affine in \(t\), and an even power is convex. Every such polynomial is polyconvex, hence quasiconvex on arbitrary domains and for all base matrices.

**No grid size, polynomial-degree bound, symmetry hypothesis, or finite enumeration is assumed.**

### Proof

Write \(q(A)=\det A\). The real rank-one locus \(q=0\) is Zariski dense in the irreducible quadric hypersurface \(\{q=0\}\). Thus a polynomial vanishing at every rank-one matrix is divisible by \(q\). (An elementary proof: substitute \(d=bc/a\) when \(a\ne0\), and use polynomial division in \(d\), after localizing at \(a\).) If \(P\ne0\), write

\[
P=q^kR,\qquad k\ge1,
\]

with maximal \(k\), and with homogeneous \(R\) of degree \(m=d-2k\ge0\) that does not vanish identically on the rank-one cone. Choose \(B=u\otimes v\ne0\) rank one such that \(r=R(B)\ne0\), and choose \(u',v'\) independent of \(u,v\), respectively. Put

\[
H_{\varepsilon,\pm}=(u+\varepsilon u')\otimes(v\pm\varepsilon v').
\]

These are rank-one matrices approaching \(B\). Exactly,

\[
q(B+tH_{\varepsilon,\pm})=\pm\kappa\varepsilon^2t,
\qquad \kappa=(u\wedge u')(v\wedge v')\ne0.
\]

For each nonzero \(\varepsilon\), the scalar polynomial \(t\mapsto P(B+tH_{\varepsilon,\pm})\) is convex by rank-one convexity. Divide by the positive number \((|\kappa|\varepsilon^2)^k\), then let \(\varepsilon\to0\). A pointwise limit of convex functions is convex, so both functions

\[
t\longmapsto (\pm1)^k(\operatorname{sgn}\kappa)^k\,r\,t^k(1+t)^m
\]

must be convex on the real line.

If \(k\) is odd, the two limits are negatives of one another. A function and its negative can both be convex only if the function is affine. Since \(r\ne0\), the polynomial \(t^k(1+t)^m\) is affine only for \(k=1,m=0\). Hence \(P=cq\) and \(d=2\).

If \(k\) is even, convexity of \(r t^k(1+t)^m\) near \(t=0\) forces \(r>0\), since \(k\ge2\). If \(m>0\), this function equals zero at \(t=-1\) and \(t=0\), but is strictly positive at \(t=-1/2\). That violates convexity, which would bound the midpoint value above by zero. Hence \(m=0\) and \(P=cq^k\), \(c>0\), with \(k\) even. This completes the classification. ∎

## Consequence 1: an exposed extreme ray of the entire quartic cone

Let \(\mathcal R_4\) be the cone of **all** globally rank-one-convex homogeneous quartics on \(\mathbb R^{2\times2}\). Let \(\sigma\) be normalized arclength measure on the unit circle and define the exact linear functional

\[
\Lambda(P)=\int_{S^1}\int_{S^1}P(a\otimes n)\,d\sigma(a)\,d\sigma(n).
\]

For every \(P\in\mathcal R_4\), \(P(a\otimes n)\ge0\): rank-one convexity of \(t\mapsto P(t\,a\otimes n)=t^4P(a\otimes n)\) forces this. Thus \(\Lambda(P)\ge0\). Equality implies \(P=0\) on all rank-one matrices, since the restriction is continuous and pointwise nonnegative. The main theorem then gives

\[
\boxed{\mathcal R_4\cap\ker\Lambda=\{c(\det A)^2:c\ge0\}.}
\]

So \((\det A)^2\) spans an **exposed extreme ray** of the full 35-dimensional rank-one-convex quartic cone. It is already polyconvex, so this face cannot contain a counterexample to Morrey.

\(\Lambda\) has rational coefficients in the 35 standard quartic monomial coordinates: for the unit circle, \(\mathbb E[x^4]=3/8\), \(\mathbb E[x^2y^2]=1/8\). The independent exact checker evaluates it, verifies \(\Lambda(q^2)=0\) and \(\Lambda(|A|^4)=1\), and computes determinantal restriction kernels in degrees 2, 3, 4, 6 and 8.

## Consequence 2: a degree obstruction for *inhomogeneous* polynomial witnesses

Let \(P\) be any globally rank-one-convex real polynomial that vanishes on all rank-one matrices. Its top nonzero homogeneous component \(P_d\) is rank-one convex: take the leading term in \(D^2P(rA)[H,H]\ge0\) as \(r\to+\infty\). Every homogeneous component vanishes on rank-one matrices, because \(P(tA)=0\) for every \(t\) and rank-one \(A\).

Therefore \(d=2\) or \(d\) is a positive multiple of 4, and \(P_d\) is a multiple of \(\det\) or a nonnegative multiple of an even power of \(\det\), respectively. This is only a leading-degree restriction: it does **not** assert that the entire inhomogeneous polynomial depends only on the determinant.

## Why the global Morrey conjecture remains open

The relevant difficult quartics need not vanish on rank-one matrices: for example the globally quasiconvex Dacorogna–Marcellini energies \(f_\gamma(A)=|A|^4-2\gamma|A|^2\det A\) all restrict to \(|A|^4\) on rank-one matrices. The new rigidity theorem classifies an exposed boundary face of the rank-one-convex cone, not the full cone.

To resolve Morrey, one must control nontrivial restriction data on the rank-one variety, e.g. prove the **positive-cone inclusion** for all 35 homogeneous quartic coefficients or give a dimension-uniform argument applying to arbitrary rank-one-convex integrands. Neither is supplied here.

Related literature: Guerra–Kristensen, *Extremal rank-one convex integrands and a conjecture of Šverák* (2019), analyzes rank-one convex homogeneous integrands vanishing on determinant-defined cones, and Bruno–Pasqualotto (2026) proves quasiconvexity for the Dacorogna–Marcellini family. A detailed novelty audit is required before claiming priority for this elementary algebraic classification.

## Checks

```bash
python morrey_rankone_null_rigidity.py
```

The script uses SymPy and exact integer/rational arithmetic, verifies the determinant identity for the two sign choices and the determinantal ideal restriction ranks in degrees 2, 3, 4, 6, 8, and checks the exact exposing linear functional. The **all-degree** classification follows from the hand proof, not from finite-degree testing.
