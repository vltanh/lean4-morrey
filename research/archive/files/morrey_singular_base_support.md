# Global supporting-null-Lagrangian theorem for a rank-one-null class

**Status:** Hand proof, all C² integrands and all singular base matrices, with no polynomial-degree, grid, or mold restriction. **Does not settle Morrey for general integrands or full-rank base matrices.** Priority relative to earlier rank-one-convexity literature remains to be established.

## Theorem

Let \(f\in C^2(\mathbb R^{2\times 2};\mathbb R)\) be globally rank-one convex and suppose
\[
 f(A)=0\qquad\text{for every }A\text{ with }\det A=0.
\]
Then there exists a **single real constant** \(c\) such that
\[
\boxed{f(A)\ge c\det A\quad\text{for every }A\in\mathbb R^{2\times2}.}
\]
Moreover for every nonzero rank-one \(B\),
\[
Df(B)=c\,D(\det)(B).
\]
Consequently, **f is quasiconvex at every singular matrix F**: for any bounded Lipschitz domain Ω and any \(u\in C_c^\infty(\Omega;\mathbb R^2)\),
\[
\int_\Omega f(F+Du)\,dx \ge |\Omega|f(F)=0\qquad (\det F=0).
\]

### Proof

Write \(q(A)=\det A\). The manifold \(\Sigma=\{A:\det A=0,\ A\ne0\}\) is smooth and connected. At every \(B\in\Sigma\), \(Dq(B)\ne0\). Since \(f\) vanishes on \(\Sigma\), the local Hadamard division lemma gives a \(C^1\) function \(g_B\) in a neighborhood of B such that \(f=qg_B\). Its restriction to \(\Sigma\) is independent of the chosen local division, and equals the normal derivative ratio of \(f\) to \(q\).

Fix \(B=u\otimes v\ne0\), and let \(H=b\otimes v\) with \(u,b\) linearly independent. Choose \(v'\) independent of \(v\), and put \(H_{\varepsilon}=b\otimes(v+\varepsilon v')\). Then \(H_\varepsilon\) is rank one, \(Dq(B)[H_\varepsilon]=\varepsilon(u\wedge b)(v\wedge v')\), and \(D^2q(B)[H_\varepsilon,H_\varepsilon]=2\det H_\varepsilon=0\). Because \(q(B)=0\),
\[
D^2f(B)[H_\varepsilon,H_\varepsilon]
=2Dq(B)[H_\varepsilon]Dg_B(B)[H_\varepsilon].
\]
Global rank-one convexity makes the left side nonnegative for both positive and negative ε. Sending ε→0 from both sides yields \(Dg_B(B)[b\otimes v]=0\). By linearity this holds for all \(b\in\mathbb R^2\). Similarly, perturbing the left factor of a rank-one \(u\otimes n\) proves \(Dg_B(B)[u\otimes n]=0\) for every n. These directions span \(T_B\Sigma\). Thus the restriction \(g|_\Sigma\) has zero tangential derivative everywhere. Since \(\Sigma\) is connected, it is a constant, say c.

It follows that \(Df(B)=g(B)Dq(B)=cDq(B)\) for every rank-one B. Now take any invertible \(A\). Write \(A=B+H\), where B consists of the first column of A and a zero second column, and H consists of a zero first column and the second column of A. Both are rank-one. The one-variable convex function \(t\mapsto f(B+tH)\) lies above its tangent line at zero, so
\[
f(A)\ge f(B)+Df(B)[H]=cDq(B)[H]=c\det A,
\]
using rank-one affinity of the determinant and \(q(B)=q(H)=0\). For singular A, the same inequality is equality. Thus the global support inequality is proved.

Finally, for singular F, integrate and use the determinant null-Lagrangian identity
\(
\int_\Omega\det(F+Du)\,dx=|\Omega|\det F=0
\), together with \(f(F)=0\), to obtain quasiconvexity at F. ∎

## Why it matters and why it is not Morrey

The result uses **all** rank-one convex lines and has no fixed polynomial degree, frequency, grid, or mold. It proves the desired inequality for an infinite-dimensional class of integrands at every singular base matrix. The hypothesis \(f|_{\det=0}=0\), however, is very restrictive: Dacorogna–Marcellini quartics restrict to \(|A|^4\) on singular matrices, not zero. Furthermore, the supporting determinant inequality does not compare \(f(F)\) to its average when \(\det F\ne0\). Therefore this cannot establish the unrestricted conjecture.

The accompanying all-degree polynomial theorem (in `morrey_rankone_null_rigidity.md`) strengthens the conclusion for homogeneous polynomial f: f is in fact a convex function of the determinant, and is thus quasiconvex at **every** base matrix.

## Exact algebraic sanity test

The companion script `morrey_singular_base_support_check.py` checks the determinant derivative formula, the rank-one perturbation signs, a positive example \(f=q^2+q\) with supporting coefficient \(c=1\), and an explicit rank-one-line convexity violation for \(f=q^2|A|^2\), which is **not** rank-one convex. These are algebraic tests, not the justification for the C² theorem.
