# Exact all-N Jensen under a strict rank-one margin and sufficiently high resonance order

Research date: 23 November 2026. **Status:** self-contained hand-level quantitative theorem, an extension of the [unrestricted all-wave Fourier-resonance sieve](IWANIEC_MORREY_RESONANCE_SIEVE.md). No isotropy, homogeneity, nonnegativity, degree, fixed wave number or small-amplitude hypothesis. This is **NOT** unrestricted Morrey: it assumes strict rank-one ellipticity and a computable high-resonance-order condition. No publication novelty or Lean verification claimed.

## 1. Full global analytic statement (arbitrarily many waves)

Let \(F\in C^2(\mathbb R^{2\times2};\mathbb R)\), fix any \(A\), any **finite N** and compatible periodic plane-wave gradient
\[
D\varphi(x)=\sum_{j=1}^N H_j\cos(2\pi k_j\cdot x+\theta_j),
\quad H_j=a_j\otimes k_j,\ k_j\in\mathbb Z^2\setminus0.
\]
There is no bound on N, the amplitudes, or the frequencies. Let R>0 be such that the entire **independent-phase** cube
\[
\mathcal K=\{A+\sum_{j=1}^N H_j t_j:-1\le t_j\le1\}
\]
lies in the open matrix-coordinate cube \((-R,R)^4\). Let \(K_R=[-R,R]^4\), and assume constants \(\mu>0\), \(M_R<\infty\) with
\[
D^2F(X)[H,H]\ge\mu\|H\|_F^2
\quad\text{for every }X\in K_R,\ \operatorname{rank}H\le1,
\qquad
\|D^2F(X)\|_{\rm op}\le M_R\quad (X\in K_R).
\]
The first property is uniform strict **rank-one convexity** on K_R; no convexity on rank-two directions is assumed.

Let \(\ell\) be the minimum nonzero integer resonance length
\[
\ell=\min\{\sum_j|n_j|:0\ne n\in\mathbb Z^N,\ \sum_jn_jk_j=0\},
\]
possibly infinity. Set \(S=\sum_{j=1}^N\|H_j\|_F^2>0\).

**Theorem (all-wave high-order-resonance positivity).** If there is an integer n≥1 with
\[
\boxed{\quad4n<\ell,\qquad \frac{4M_RR^2}{n}\le\frac{\mu S}{4},\quad}\tag{1}
\]
then **the exact compatible-gradient quasiconvex Jensen inequality holds**:
\[
\boxed{\quad \int_{\mathbb T^2}F(A+D\varphi(x))\,dx\ge F(A).\quad}\tag{2}
\]
More quantitatively,
\[
\boxed{\quad\int_{\mathbb T^2}F(A+D\varphi)-F(A)
 \ge \frac{\mu S}{4}-\frac{4M_RR^2}{n}.\quad}\tag{3}
\]
This holds for **every** phase choice, even when the waves have genuine integer resonances at much higher order. It is an exact global all-N positivity theorem, not a bound merely saying the deficit is small.

## 2. Self-contained proof

**Strong independent-phase Jensen.** For any B,H with rank H≤1 and the segment \(B+[-1,1]H\subset K_R\), Taylor's integral formula and the Hessian margin yield
\[
F(B+H\cos\theta)\ge F(B)+DF(B):H\cos\theta+\tfrac\mu2\|H\|_F^2\cos^2\theta.
\]
Average over uniform θ: linear term vanishes, \(E\cos^2\theta=1/2\), hence
\[
\int_0^{2\pi}F(B+H\cos\theta)\,\frac{d\theta}{2\pi}
 \ge F(B)+\frac{\mu}{4}\|H\|_F^2.
\]
Successively average all **independent** wave phases (taking the remaining fixed components as B). This proves
\[
\boxed{\quad
\mathbb E_{\Theta_1,\dots,\Theta_N}
 F\bigl(A+\sum H_j\cos\Theta_j\bigr)
 \ge F(A)+\frac{\mu}{4}S.\quad}\tag{4}
\]

**Control the true spatial phase correlations.** On the matrix-coordinate cube \([-R,R]^4\), let \(B_nF\) denote the four-fold tensor Bernstein polynomial of order n per coordinate (total degree at most 4n). Independent binomial sampling Y with mean X has
\(\mathbb E\|Y-X\|_F^2\le4R^2/n\), so Taylor's formula and \(\|D^2F\|_{\rm op}\le M_R\) imply
\[
           \|B_nF-F\|_{\infty,K_R}\le2M_RR^2/n.
\]
Because its total degree is ≤4n and 4n<ℓ, spatial Fourier orthogonality gives **exact equality**
\[
 \int_{\mathbb T^2}B_nF\bigl(A+\sum H_j\cos(2\pi k_j\cdot x+\theta_j)\bigr)\,dx
 =\mathbb E_{\Theta}B_nF\bigl(A+\sum H_j\cos\Theta_j\bigr).
\]
The original and Bernstein energies differ by at most \(2M_RR^2/n\) on either side, so
\[
\int_{\mathbb T^2}F(A+D\varphi)
 \ge \mathbb E_{\Theta}F(A+\sum H_j\cos\Theta_j)-4M_RR^2/n.
\]
Combine with (4) to get (3), hence (1) implies (2). QED.

The proof is independent of the **invalid** attempted stochastic square-wave three-ridge extension; see [the explicit logic retraction](IWANIEC_MORREY_THREE_RIDGE_GLOBAL_QC.md). The two directions of Jensen are used correctly here.

## 3. Exact signed, anisotropic, nonhomogeneous control

A reproducible nonconvex test is
\[
 F(X)=\|X\|_F^2+5\det X+X_{11}.
\]
It is **signed, anisotropic and nonhomogeneous**, and **nonconvex** in the full matrix space. Its full Hessian has eigenvalues 7 and −3, so \(M_R=7\) globally. On every rank-one H, \(\det H=0\), and \(D^2F(X)[H,H]=2\|H\|_F^2\), hence \(\mu=2\). (F is also polyconvex because det is a null Lagrangian, but the theorem does not use this.)

Take A=0 and three waves with
\[
k_1=(1,0),\ a_1=(1,0);\quad
k_2=(0,1),\ a_2=(0,1);\quad
k_3=(1024,1),\ a_3=(1/1024,0).
\]
The entries of every independent-phase matrix lie in \((-3,3)\). Their squared Frobenius-amplitude sum is
\(S=3+1/1024^2\). The shortest nonzero integer relation is
\((-1024,-1,1)\), of length \(\ell=1026\).
With R=3 and n=169, exact rational arithmetic gives
\[
 4n=676<1026,\qquad
 \frac{4M_RR^2}{n}=\frac{252}{169}
 <\frac{\mu S}{4}=\frac{3145729}{2097152}.
\]
Thus the theorem certifies exact Jensen for all phases. The accompanying [exact checker](../../research/audit/iwaniec_strict_resonance_exact.py) reproduces the rational inequalities and relation order.

The numerical control is **not** the proof of the arbitrary-N theorem and is **not** a counterexample.

## 4. Research scope and stopping rule

This closes a **global high-resonance-order region for every smooth, uniformly strictly rank-one-convex F**, no matter how anisotropic, signed, nonhomogeneous or how many waves. It is a quantitative complement to the plain Bernstein deficit sieve.

The condition need not hold for general rank-one-convex F with vanishing rank-one curvature, for strongly resonant frequencies, or for gradients without a finite cosine-wave representation. In particular, no **universal** minimum resonance order independent of the integrand or amplitudes is derived.

**Unrestricted planar Morrey remains OPEN**. Any universal proof must handle the low-order resonant phase corrections with no strict Hessian margin; a counterexample must supply a genuinely negative compatible-gradient Jensen value. No assertion of publication priority or Lean formalization is made.
