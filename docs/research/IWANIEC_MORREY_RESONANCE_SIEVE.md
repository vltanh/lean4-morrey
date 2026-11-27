# An all-integrand Fourier-resonance sieve toward unrestricted planar Morrey

Date: 23 November 2026. **Status:** self-contained hand theorem, exact integer/rational regression controls, and explicit quantitative approximation. **It does not solve unrestricted Morrey.** The statement works for arbitrary finite-valued rank-one-convex integrands, including anisotropic, signed and nonhomogeneous ones. The numerical constants are elementary; no originality or outside refereeing is asserted.

## 0. Priority: two- and three-wave results are known

**Do not claim to have discovered the basic two-wave theorem.** Guerra and Teixeira da Costa, *Numerical evidence towards a positive answer to Morrey's problem* (2021), Theorem 3.3, explicitly cite rank-one convexity ⇒ two-wave quasiconvexity. Their Theorem 3.3(d) also records the **stronger preexisting three-sawtooth-wave result** in dimension 2×2, due to Sebestyén–Székelyhidi, *Laminates Supported on Cubes*, J. Convex Anal. 24 (2017), 1217–1237. Sources: https://doi.org/10.4171/RMI/1286 and https://doi.org/10.68381/jca24070 .

The theorem here is a **frequency-order sieve** for *arbitrary* numbers of smooth sinusoidal modes, arbitrary polynomial degree, and an explicit Bernstein-approximation remainder for **every** finite-valued rank-one-convex F. It is based on basic Fourier orthogonality and product Jensen. No publication novelty of this elementary frequency sieve has been established.

## 1. Setup: any number of rank-one plane waves

Let \(F:\mathbb R^{2\times2}\to\mathbb R\) be finite-valued and globally rank-one convex. No symmetry, sign, growth or homogeneity hypotheses are imposed.

Let \(A\in\mathbb R^{2\times2}\), choose any finite \(N\ge1\), nonzero integer wavevectors \(k_j\in\mathbb Z^2\), target vectors \(a_j\in\mathbb R^2\), and phases \(\theta_j\in\mathbb R\). Put
\[
 H_j=a_j\otimes k_j,\qquad
 \varphi(x)=\frac1{2\pi}\sum_{j=1}^N a_j
     \sin(2\pi k_j\cdot x+\theta_j).
\]
Then \(D\varphi(x)=\sum_j H_j\cos(2\pi k_j\cdot x+\theta_j)\) is **an actual compatible, periodic planar gradient**. Here \(\mathbb T^2=\mathbb R^2/\mathbb Z^2\) has normalized Haar measure.

Define the **shortest nonzero integer frequency relation**
\[
 \ell(k_1,\ldots,k_N):=
 \min\left\{\sum_j|n_j|:\ 
  n\in\mathbb Z^N\setminus\{0\},
  \ \sum_j n_j k_j=0\right\}
 \ \in\mathbb N\cup\{+\infty\}.
\]
The minimum is infinity when the set is empty.

Define also
\[
 \Phi(t_1,\ldots,t_N)
   :=F\left(A+\sum_{j=1}^NH_j\cos t_j\right)
\]
on the independent-phase torus \(\mathbb T_{2\pi}^N\).

### Lemma 1: product-phase Jensen, globally in all N

\[
\boxed{\quad \fint_{\mathbb T_{2\pi}^N}\Phi(t)\,dt\ge F(A).\quad}\tag{1}
\]
Indeed, for any fixed values of the other phases, the matrix depends affinely on the scalar \(\cos t_j\), with **rank-one** coefficient \(H_j\). Rank-one convexity and zero mean of \(\cos t_j\) give Jensen in variable \(t_j\). Iterate \(j=1,\ldots,N\), ending at \(F(A)\). This argument holds for every N, regardless of frequency relations.

## 2. Polynomial theorem: no resonances up to the total degree

**Theorem 2.** If F is a polynomial in the four matrix entries of total degree at most \(d\), and
\[
                      \ell(k_1,\ldots,k_N)>d ,
\]
then for **every** A, all amplitudes and all phases,
\[
\boxed{\quad\fint_{\mathbb T^2}F(A+D\varphi(x))\,dx
   =\fint_{\mathbb T_{2\pi}^N}\Phi(t)\,dt
   \ge F(A).\quad}\tag{2}
\]
No restriction to isotropic, homogeneous, nonnegative, quadratic, or quartic polynomials is used; d is arbitrary.

**Proof.** Since F has total degree ≤d in A, \(\Phi(t)\) is a trigonometric polynomial with characters \(e^{i n\cdot t}\) supported only on \(\sum_j|n_j|\le d\). Write
\(\Phi(t)=\sum_{\|n\|_1\le d}c_ne^{i n\cdot t}\).
Integrating along \(t_j=2\pi k_j\cdot x+\theta_j\) over \(\mathbb T^2\) removes every term for which \(\sum_jn_jk_j\ne0\). By \(\ell>d\), only the zero character survives. Its coefficient \(c_0\) is precisely the independent-phase mean. Apply (1). QED.

**Exact regression controls.** For \(k_1=(1,0), k_2=(0,1),k_3=(5,1)\), the shortest relation is
\((-5,-1,1)\) of length 7. The accompanying exact checker verifies spatial/independent-phase equality for **all 35 distinct three-variable cosine monomials of degree ≤4**, with rational coefficients.

The no-resonance hypothesis is substantive as a Fourier equality statement: for \(k_3=(1,1)\), the cubic triad is resonant and
\[
 \fint_{\mathbb T^2}\cos(2\pi x_1)
  \cos(2\pi x_2)\cos(2\pi(x_1+x_2))\,dx=\frac14,
\]
whereas the corresponding **independent-phase** mean is zero. This is **not a negative quasiconvexity example**; it only demonstrates genuine phase correlation.

## 3. Arbitrary finite-valued rank-one-convex F: explicit defect bound

**Theorem 3 (all-integrand quantitative version).**
Let
\[
R\ge \max_{1\le \alpha,\beta\le2}\left(
 |A_{\alpha\beta}|+\sum_j |(H_j)_{\alpha\beta}|
\right),\quad R>0.
\]
Both the spatial and the independent-phase matrix fields take values in the cube \(K_R=[-R,R]^4\).
Since every finite-valued rank-one-convex F is locally Lipschitz, there is a finite Frobenius-norm Lipschitz constant
\[
  L_R:=\sup_{X\ne Y\in K_R}
       \frac{|F(X)-F(Y)|}{\|X-Y\|_F}<\infty .
\]

For **every integer n≥1 such that 4n<\ell**, one has the fully explicit global estimate
\[
\boxed{\quad
  F(A)-\fint_{\mathbb T^2}F(A+D\varphi)
       \ \le\ \frac{4L_RR}{\sqrt n}.
\quad}\tag{3}
\]
In particular, if \(\ell=+\infty\), take \(n\to\infty\): rank-one convexity gives **exact Jensen**.

**Proof.** Approximate F on \(K_R\) by its four-variable tensor Bernstein polynomial \(B_nF\) (order n per matrix coordinate, total polynomial degree ≤4n). At each \(X\in K_R\), the Bernstein polynomial is the expectation \(E F(Y)\), where
\[
Y_{\alpha\beta}=-R+\frac{2R}{n}\operatorname{Bin}
\left(n,\frac{X_{\alpha\beta}+R}{2R}\right)
\]
independently over the four entries. Then \(EY=X\) and, using \(\operatorname{Var}(\operatorname{Bin}(n,t))\le n/4\),
\[
 E\|Y-X\|_F^2\le\frac{4R^2}{n}.
\]
Consequently
\[
 \|B_nF-F\|_{L^\infty(K_R)}
 \le L_R E\|Y-X\|_F\le\frac{2L_RR}{\sqrt n}.
\]
By Theorem 2's **Fourier equality mechanism**, spatial and independent-phase means of \(B_nF\) coincide because its degree is ≤4n<\ell; rank-one convexity of **B_nF is not needed**. Thus
\[
 \fint_x F(A+D\varphi)
 \ge \fint_x B_nF(A+D\varphi)-\varepsilon
 =\fint_t B_nF(A+\textstyle\sum H_j\cos t_j)-\varepsilon
 \ge \fint_t F(A+\textstyle\sum H_j\cos t_j)-2\varepsilon
 \ge F(A)-2\varepsilon ,
\]
where \(\varepsilon=2L_RR/\sqrt n\). QED.

### Better C² rate

If F is \(C^2\) on a neighborhood of \(K_R\), set
\[
 M_R=\sup_{X\in K_R}\|D^2F(X)\|_{\mathrm{op}}<\infty .
\]
Use Taylor's formula, \(E(Y-X)=0\), and the same variance estimate to get
\[
 \|B_nF-F\|_\infty\le\frac12 M_R E\|Y-X\|_F^2
 \le\frac{2M_RR^2}{n}.
\]
Therefore
\[
\boxed{\quad F(A)-\fint F(A+D\varphi)
             \le \frac{4M_RR^2}{n}
             \quad\text{whenever }4n<\ell.\quad}\tag{4}
\]
The Hessian bound is a bound on **all** directions needed for approximation, not a rank-one ellipticity hypothesis.

## 4. A bounded short-resonance obstruction to every fixed-size deficit

Suppose this **actual compatible** periodic gradient violates quasiconvex Jensen by a strict gap
\[
 \delta:=F(A)-\fint F(A+D\varphi)>0 .
\]
Choose
\[
 n_\delta=\left\lfloor(4L_RR/\delta)^2\right\rfloor+1.
\]
If \(\ell>4n_\delta\), inequality (3) would give a gap **strictly less than δ**, contradiction. Hence every such violation has a nontrivial relation
\[
\boxed{\quad \sum_j n_jk_j=0,\qquad
  0<\sum_j|n_j|\le4n_\delta .\quad}\tag{5}
\]
For C² F one may replace \(n_\delta\) by
\(\lfloor4M_RR^2/\delta\rfloor+1\), using (4).

Thus a fixed positive deficit forces an **explicit bounded-order phase resonance**. This is uniform over **every finite number of waves**, all phases, full anisotropy, nonhomogeneity, all matrix bases, and all integrands with the displayed compact-bound data. It does NOT bound the number of waves, wavevector magnitudes, polynomial degree of an unknown F, or give a universal all-integrand finite case list.

## 5. Exact two-frequency-line limit, no polynomial assumption

If the Fourier support of a periodic gradient perturbation lies on at most two distinct lines through the origin in \(\mathbb Z^2\), regroup the waves into two vector-valued ridge functions, \(\varphi(x)=g_1(k_1\cdot x)+g_2(k_2\cdot x)\).
If the directions are independent, the map \(x\mapsto(k_1\cdot x,k_2\cdot x)\) pushes Haar measure to product Haar measure (possibly as a finite covering), so two successive rank-one Jensen inequalities give
\[
\fint_{\mathbb T^2}F(A+D\varphi)\ge F(A)
\]
for every finite-valued rank-one-convex F and arbitrary ridge profiles, amplitudes and frequencies. If directions coincide, F is convex on the fixed-right-factor affine plane and a single Jensen step applies. This is a standard two-wave result, **not new**.

The polynomial resonance theorem and quantitative Bernstein bound are useful beyond that two-line result, notably for ≥4 waves where nontrivial short relations can occur.

## 6. Where this leaves unrestricted Morrey

The general Morrey implication is **not settled**. The moment/phase difference between the true spatial law and the independent-phase laminate law is supported on resonant Fourier characters. A global proof would have to bound those **resonant contributions** using the full rank-one-convexity inequalities, for every F, every phase configuration and arbitrary wave count; or construct one globally rank-one-convex F and a real compatible gradient producing a negative gap.

The prior 2017 three-sawtooth-wave theorem closes that particular configuration class. No claim is made here that all arbitrary three-wave profiles or all 4-wave configurations are solved. The all-N resonance inequality is a **structural bound**, not a uniform all-N Jensen theorem.

**Reproduction:** [pure-standard-library exact regression](../../research/audit/iwaniec_morrey_resonance_exact.py) verifies the 35 polynomial moments, minimal resonance 7, cubic triad 1/4, and Bernstein variance constants. It checks illustrative finite identities; the arbitrary-N and approximation theorems are proved by the displayed hand calculations, **not** by enumerating test cases. No Lean build or external human review is claimed.
