# A universal all-\(p\) isotropic level-set theorem, and why it does not prove Morrey

Research date: 22 November 2026. **Hand deduction from a published 2003 theorem; no claim of independent novelty or Lean verification.** The new content here is the explicit all-level, noncoercive formulation and its place in the \(p>2\) roadmap. It is a **global in \(p\), matrices, integrands, and perturbation amplitudes** statement, but it proves **supremal** quasiconvexity, not the ordinary average-energy Jensen inequality.

## 1. Primary theorem used (published, not new)

Conti–De Lellis–Müller–Romeo, *Polyconvexity equals rank-one convexity for connected isotropic sets in \(\mathbb M^{2\times2}\)*, C. R. Math. Acad. Sci. Paris 337 (2003), 233–238,
[DOI](https://doi.org/10.1016/S1631-073X(03)00333-9).

Their theorem (building on Cardaliaguet–Tahraoui): **a compact connected, SO(2)×SO(2)-invariant rank-one-convex/lamination-convex subset of \(\mathbb R^{2\times2}\) is polyconvex as a set**. Polyconvexity of a set \(K\) means that whenever finitely many \(A_i\in K\) and probability weights \(w_i\) obey
\[
  \sum_i w_i A_i=A,\qquad
  \sum_i w_i\det A_i=\det A,
\]
then \(A\in K\). Equivalently, \(K\) equals its polyconvex hull, the intersection of the convex hull of its lifted minors \((A,\det A)\) with the minors graph.

## 2. The all-integrand corollary (elementary but global)

**Theorem.** Let \(p>0\). Let \(F:\mathbb R^{2\times2}\to[0,\infty)\) be finite-valued, globally rank-one convex, SO(2)×SO(2)-isotropic and positively \(p\)-homogeneous. Then for **every** \(c\ge0\), its sublevel set
\[
              K_c=\{A:F(A)\le c\}
\]
is polyconvex as a set, whether or not \(F\) is coercive. This holds for all admissible positive exponents simultaneously; no degree, mesh, or fixed cardinality restriction is used.

**Proof.** By finite-valued rank-one convexity, \(F\) is continuous on the whole matrix space. Homogeneity implies \(F(0)=0\); nonnegativity and \(p>0\) imply \(F(sA)=s^pF(A)\le F(A)\) for \(0\le s\le1\). Thus each \(K_c\) is closed, isotropic and star-shaped around zero.

For every \(R>0\), set \(K_{c,R}=K_c\cap\overline B_R(0)\), with the Frobenius-norm ball. It is compact, connected (star-shaped), isotropic and rank-one convex **as a set**: if A,B belong to it with rank(A−B)≤1, convexity of F on the rank-one segment and convexity of the ball keep the entire segment in the set. The 2003 theorem therefore makes \(K_{c,R}\) polyconvex.

Now take **any finite** minors-preserving probability law supported in \(K_c\). Its atoms all lie in some \(K_{c,R}\), so polyconvexity of that compact truncation forces the barycenter A to belong to \(K_{c,R}\subset K_c\). Hence \(K_c\) is polyconvex, with no coercivity assumption. QED.

## 3. Universal \(L^\infty\) Jensen inequality (not ordinary QC)

**Corollary.** For every base \(A\in\mathbb R^{2\times2}\) and every periodic Lipschitz displacement \(\varphi:Q=\mathbb R^2/\mathbb Z^2\to\mathbb R^2\),
\[
\boxed{
     F(A)\le\operatorname{ess\,sup}_{x\in Q} F(A+D\varphi(x)).
}\tag{1}
\]
Consequently the **supremal quasiconvex envelope** of F coincides with F at every matrix.

**Proof.** Write \(M(x)=A+D\varphi(x)\), which is essentially bounded. Let \(c=\operatorname{ess\,sup} F(M(x))\), finite by continuity and boundedness; then \(M(x)\in K_c\cap\overline B_R\) a.e. for some finite R. The determinant is a null Lagrangian:
\[
 \fint_QM(x)\,dx=A,\qquad
 \fint_Q\det M(x)\,dx=\det A.
\]
Thus the lifted barycenter \((A,\det A)\) belongs to the **closed convex hull** of the compact minor graph
\(\{(B,\det B):B\in K_{c,R}\}\). Compactness makes that hull closed (Carathéodory); polyconvexity of \(K_{c,R}\) forces \(A\in K_c\). Hence \(F(A)\le c\). The zero perturbation gives equality in the infimum defining the supremal envelope. QED.

The same argument works for Lipschitz zero-boundary test maps on a bounded domain, using the usual determinant null-Lagrangian boundary identity.

## 4. Why the p>2 open problem is still genuinely different

The desired Morrey/class-wide quasiconvexity inequality is
\[
                  F(A)\le\fint_QF(A+D\varphi).
\tag{2}
\]
The globally proved inequality (1) has **essential supremum instead of average**. Even for ordinary scalar level-convex functions this implication is false: \(f(x)=\min\{|x|,1\}\) has convex sublevel sets; at x=1, a two-point law with equal mass at 0 and 2 yields f(1)=1 but energy average 1/2. This one-dimensional illustration is **not** a rank-one-convex matrix counterexample.

The scalar profile and one-multiplier pointwise support criterion from
[the ongoing p>2 program](IWANIEC_MORREY_GENERAL_SUPPORT_CRITERION.md)
therefore remain open. Polyconvexity of **each sublevel set** does not automatically produce a single convex minor representative for the values of F across different levels. A proof of compatibility of the set-level supports **across energy levels** would be a qualitatively global advance; repeatedly proving level-set inclusions will not suffice.

**Exact remaining gate:** Construct a cross-level polyconvex calibration or prove the global one-multiplier feasibility for *every* nonnegative isotropic rank-one-convex \(p>2\) integrand. Alternatively, find a profile with a certified failure of the stronger polyconvexity theorem; that still would not by itself settle ordinary quasiconvexity.

**Evidence status:** Deduction from published 2003 set theorem and standard determinant-null-Lagrangian identity. No numerical search, Lean build, or CI run is claimed for this note.
