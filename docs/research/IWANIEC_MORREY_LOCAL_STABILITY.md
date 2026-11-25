# Uniform local-gradient stability of the exact p=4 separator

Date: 22 November 2026. Status: an **unconditional** standard
strong-ellipticity/local-quasiconvexity hand argument for the
exact rank-one-convex integrand introduced in
[the global hybrid-envelope no-go](IWANIEC_MORREY_HYBRID_NOGO.md).
Its pointwise acoustic arithmetic is certified by exact rational
identities in [the checker](../../research/audit/iwaniec_local_stability_exact.py).
The Fourier/Taylor implication is a hand proof,
not Lean-checked or independently refereed.
This is **not** unrestricted Morrey and
does **not** assert global quasiconvexity of the candidate.

## 1. Exact Hessian lower bound at the original rank-one base

Recall
\[
F(0)=0,\quad F(A)=\|A\|_{\mathrm{op}}^4
 h\left(\frac{\det A}{\|A\|_{\mathrm{op}}^2}\right), \quad
 h(r)=2^{-24}\sum_{j=0}^{12}a_jT_j(r),
\]
with the integer coefficient vector in the linked note.
At \(A_0=\operatorname{diag}(1,0)\),
\(F\) is \(C^2\) on an open neighborhood
because its largest singular value is simple.

The exact coefficients at \(r=0\) are
\[
 h(0)=\frac{2139095}{2097152},\quad
 h'(0)=\frac{50331651}{16777216},\quad
 h''(0)=\frac{2264943}{4194304}.
\]
The acoustic tensor from
[the scalar criterion](IWANIEC_MORREY_ACOUSTIC.md)
has constants
\[
 B=\frac{2139095}{524288},\quad
 U=\frac{6417285}{524288},\quad
 V=\frac{2264943}{4194304},\quad
 T=\frac{50331651}{8388608}.
\]
Thus, for rank-one H=u⊗v,
\[
D^2F(A_0)[H,H]
=u^\top\begin{pmatrix}
 U v_1^2+Bv_2^2&T v_1v_2\\
 T v_1v_2&B v_1^2+Vv_2^2
\end{pmatrix}u.
\]

**Proposition 1 (uniform rank-one Hessian margin).**
\[
\boxed{\quad
 D^2F(A_0)[u\otimes v,u\otimes v]
 \ge\frac16\,\|u\|^2\|v\|^2
 \quad\text{for every }u,v\in\mathbb R^2.
 \quad} \tag{1}
\]

**Exact certificate.**
Set \(\mu=1/6\),
\(U'=U-\mu\), \(B'=B-\mu\), \(V'=V-\mu\).
All three numbers are strictly positive.
The remaining 2×2 acoustic tensor after
subtracting \(\mu\|v\|^2 I\) is positive
semidefinite if \(T\le B'+\sqrt{U'V'}\).
Here \(T>B'\) and the rational squared slack is
\[
\boxed{
(U-\mu)(V-\mu)-(T-B+\mu)^2
=\frac{32352523009765}{211106232532992}>0.
}\tag{2}
\]
This proves (1), with all inequalities exact.
The checker verifies the coefficient extraction,
positive differences and (2) by Fraction arithmetic.

## 2. Local quasiconvexity for EVERY wavelength/mesh

**Theorem 2.** There exists \(\eta>0\) such
that for **every smooth periodic** two-component
\(\varphi\) on the unit torus, provided
\(\|D\varphi\|_{L^\infty}\le\eta\), one has
\[
\boxed{\quad
\fint_Q F(A_0+D\varphi)\,dx-F(A_0)
\ge\frac1{24}\fint_Q\|D\varphi\|_F^2\,dx.
\quad}\tag{3}
\]
The same holds for periodic Lipschitz
\(\varphi\) with essentially bounded gradients.

**Proof.** The quadratic form
\(Q(H)=D^2F(A_0)[H,H]\) is constant-coefficient
and satisfies \(Q(u\otimes v)\ge\mu|u|^2|v|^2\).
The Fourier decomposition of any periodic
vector field \(\varphi\) yields
\[
\fint_Q Q(D\varphi)\,dx
 \ge\mu\fint_Q\|D\varphi\|_F^2\,dx,
\]
since the gradient of each Fourier mode
has rank one, even when the Fourier
coefficient is complex (apply the real
inequality to its real and imaginary parts).

Because F is C² near A₀, pick η>0 so that
\(\|D^2F(A_0+H)-D^2F(A_0)\|_{\mathrm{op}}
 \le\mu/2\)
whenever \(|H|\le\eta\).
Taylor's integral remainder then satisfies
\[
 |F(A_0+H)-F(A_0)-DF(A_0):H
  -\tfrac12 Q(H)|\le \tfrac{\mu}{4}|H|^2.
\]
Integrating, the linear term vanishes
because the periodic gradient has mean zero.
Thus the Jensen gap is at least
\((\mu/2-\mu/4)\fint|D\varphi|^2
=\mu/4\,\fint|D\varphi|^2\), which
equals 1/24. QED.

This result excludes **all sufficiently
small-amplitude gradient counterexamples at A₀**,
regardless of oscillation wavelength, mesh size,
or number of Fourier modes. The exact scalar
separator from the hybrid-cone no-go does
not imply a negative gradient law even locally.

## 3. Uniform local stability at a continuum of other bases

The exact rational Bernstein certificate for
global rank-one convexity of F is **strict**:
the acoustic conditions hold with a positive
margin for all signed ratios r∈(-1,1).
Thus
\[
D^2F(A)[u\otimes v,u\otimes v]>0
\quad\text{for all }A\ne0
\text{ with distinct singular values, }
 u,v\ne0.
\]
This positivity is continuous in A,u,v.
For any **compact** set K of nonzero matrices
with distinct singular values there exist
\(\mu_K,\eta_K>0\) such that for every A∈K
and periodic test map with
\(\|D\varphi\|_{L^\infty}\le\eta_K\),
\[
 \fint_Q F(A+D\varphi)-F(A)
 \ge\frac{\mu_K}{4}\fint_Q\|D\varphi\|_F^2.
\]
Proof: take the positive minimum of the
rank-one Hessian over compact
K×S¹×S¹, then apply the same uniform
Fourier/Taylor argument (the compact set
stays a positive distance from singular
value collisions and the origin).

**Scope and decision:** These are *local
in gradient amplitude*, not local in
wavelength, finite mesh, or number of
gradients. A genuine negative Jensen
witness for this F must involve
gradients with sufficiently large amplitude
to escape these neighborhoods or bases
at the conformal singular-value locus.
This does not show F globally QC, and
the unrestricted anisotropic/nonhomogeneous
Morrey conjecture is unchanged.

The theorem is a targeted stopping
rule for small-amplitude optimization
around the explicit p=4 candidate:
future searches need globally
nonlinear field configurations rather
than further low-amplitude local
perturbation tests.
