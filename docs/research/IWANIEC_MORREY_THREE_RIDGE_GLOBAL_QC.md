# Global three-ridge Jensen theorem and spectral-tail control for unrestricted planar Morrey

Date: 23 November 2026. **Status:** a hand deduction from the published planar three-sawtooth-wave theorem of Sebestyén–Székelyhidi (2017), with a fully explicit random-square-wave reduction. NO claim of priority, independent human review, Lean proof, or solution of unrestricted Morrey. The result does not assume isotropy, homogeneity, nonnegativity, polynomiality or small amplitudes.

## 1. Published input and new deduction

**Published input (three-sawtooth theorem).** Let \(F:\mathbb R^{2\times2}\to\mathbb R\) be any finite-valued globally rank-one-convex integrand. For any matrix \(A\), any three integer directions \(k_j\ne0\), any three vector amplitudes \(v_j\in\mathbb R^2\), and any three phases \(\theta_j\), one has
\[
 F(A)\le \int_{\mathbb T^2}
 F\Bigl(A+\sum_{j=1}^3 (v_j\otimes k_j)\,
       {\rm sgn}\cos(2\pi k_j\cdot x-\theta_j)\Bigr)\,dx . \tag{S}
\]
The sign square wave is a.e. the derivative of a periodic half-duty sawtooth. This is the planar 3-wave result in Sebestyén–Székelyhidi, *Laminates Supported on Cubes*, J. Convex Anal. **24** (2017), 1217–1237, and is explicitly restated in Guerra–Teixeira da Costa, *Numerical evidence towards a positive answer to Morrey's problem*, Rev. Mat. Iberoam. **38** (2022), Theorem 3.3(d). The 2017 paper's cube theorem and its discussion of frequency-dependent weights justify (S) for arbitrary waves and phases, not merely a single cubic frequency triad. Translation by A is harmless. For one or two directions, standard repeated rank-one Jensen also gives (S).

**Deduction: arbitrary three-ridge waveforms.** For arbitrary periodic Lipschitz vector-valued ridge profiles \(g_j:\mathbb T\to\mathbb R^2\), \(j=1,2,3\), arbitrary integer directions \(k_j\in\mathbb Z^2\setminus0\), and every \(A\), the *actual compatible gradient*
\[
\varphi(x)=\sum_{j=1}^3 g_j(k_j\cdot x),\quad
D\varphi(x)=\sum_{j=1}^3 g'_j(k_j\cdot x)\otimes k_j
\]
obeys the universal Jensen inequality
\[
\boxed{\quad \int_{\mathbb T^2}F(A+D\varphi(x))\,dx\ge F(A).\quad}\tag{1}
\]
This is a global, amplitude-unrestricted, non-isotropic and nonhomogeneous theorem for an **infinite-dimensional family of compatible gradients**, not just three prescribed sawtooth profiles. It is conditional only on the published (S), which is established mathematics. It does NOT cover arbitrary fields with four or more Fourier directions. No novelty beyond (S) is asserted.

## 2. Exact random-square-wave representation

Write \(h(\xi)={\rm sgn}(\cos\xi)\), a \(2\pi\)-periodic, mean-zero function. Elementary integration gives
\[
\frac{1}{2\pi}\int_0^{2\pi}
h(s-\theta)\cos\theta\,d\theta=\frac2\pi\cos s,\qquad
\frac{1}{2\pi}\int_0^{2\pi}
h(s-\theta)\sin\theta\,d\theta=\frac2\pi\sin s. \tag{2}
\]
Indeed at s=0, the cosine integral is (2−(−2))/(2π)=2/π and the sine integral vanishes by symmetry; a change of variables gives the general s.

Let \(G:\mathbb T\to\mathbb R^2\) be an arbitrary **mean-zero vector trigonometric polynomial**,
\[
G(\xi)=\sum_{m=1}^M[u_m\cos(2\pi m\xi)+v_m\sin(2\pi m\xi)].
\]
Let \(J\) be uniform on \(\{1,\ldots,M\}\), \(\Theta\) uniform on \([0,2\pi)\), independent, and set
\[
 Z_G(\xi;J,\Theta)
 =\frac{\pi M}{2}\bigl(u_J\cos\Theta+v_J\sin\Theta\bigr)
  h(2\pi J\xi-\Theta).                                      \tag{3}
\]
By (2), **pointwise for every \(\xi\)**,
\[
             \mathbb E_{J,\Theta}Z_G(\xi;J,\Theta)=G(\xi). \tag{4}
\]
Each realization of Z_G is a **single** vector amplitude multiplying a shifted ±1 square wave, with integral zero. Its contribution to a 2D gradient is one rank-one matrix
\[
 Z_G(k\cdot x;J,\Theta)\otimes k
 =\bigl(v(J,\Theta)/J\bigr)\otimes(Jk)\,
   h(2\pi(Jk)\cdot x-\Theta).
\]
Thus it belongs to the published three-sawtooth class.

For three such trig profiles \(G_j=g'_j\) choose independent \(J_j,\Theta_j\). At **each fixed x**, integrate over the random variable for the first ridge while holding the others fixed: \(F\) is ordinary convex in \(v\in\mathbb R^2\) along the affine rank-one plane \(B+v\otimes k_1\), since every difference has rank≤1. Hence Jensen. Repeat independently for ridges 2 and 3:
\[
 F\Bigl(A+\sum_{j=1}^3 G_j(k_j\cdot x)\otimes k_j\Bigr)
 \le \mathbb E_{\omega}
 F\Bigl(A+\sum_{j=1}^3 Z_{G_j}(k_j\cdot x;\omega_j)\otimes k_j\Bigr). \tag{5}
\]
Integrate over x, use Fubini (all relevant inputs bounded for fixed finite Fourier expansions), and apply the published theorem (S) to **each fixed choice of \(\omega\)**. This yields (1) for all trigonometric ridge gradients.

For arbitrary \(g_j\in W^{1,\infty}(\mathbb T;\mathbb R^2)\), their derivatives have zero mean. Fejér approximants \(G_{j,M}\) are zero-mean vector trigonometric polynomials with
\(\|G_{j,M}\|_\infty\le\|g'_j\|_\infty\) and \(G_{j,M}\to g'_j\) in L¹. They are derivatives of periodic Lipschitz \(g_{j,M}\). The true gradient fields are uniformly bounded and converge in L¹ to \(D\varphi\), so continuity of finite rank-one-convex F and dominated convergence (or uniform continuity on a compact matrix ball) pass (1) to the limit. QED.

## 3. Global quantitative spectral-tail theorem for EVERY periodic gradient

Now let \(\varphi\in W^{1,\infty}(\mathbb T^2;\mathbb R^2)\) be **arbitrary**, with \(B=\|D\varphi\|_{L^\infty,F}\). Choose any set \(\mathcal L\) of **at most three** distinct one-dimensional rational lattice lines through the origin. Each line has a primitive integer direction \(k_j\) (defined up to sign).

Let \(P_{\mathcal L}\varphi\) retain exactly the nonzero Fourier frequencies of \(\varphi\) lying on these lines, and discard all others. Equivalently,
\[
  \psi=P_{\mathcal L}\varphi
   =\sum_{j=1}^{|\mathcal L|}
      \bigl(\mathbb E[\varphi\mid k_j\cdot x]
                          -\overline\varphi\bigr).
\]
Each summand is a periodic vector-valued one-variable ridge, and differentiation commutes with the conditional expectation. Thus
\[
 \|D\psi\|_{L^\infty,F}\le|\mathcal L|B\le3B.
\]
By (1) the projected gradient satisfies \(\int F(A+D\psi)\ge F(A)\).

Since finite-valued rank-one-convex F is locally Lipschitz on the matrix space, fix any
\[
 R>\|A\|_F+3B,\qquad
 L_R=\sup_{X\ne Y\in\overline B_R}
       \frac{|F(X)-F(Y)|}{\|X-Y\|_F}<\infty.
\]
The **full unrestricted** periodic gradient then obeys
\[
\begin{aligned}
F(A)-\int_{\mathbb T^2}F(A+D\varphi)
 &\le \int_{\mathbb T^2}
    \bigl[F(A+D\psi)-F(A+D\varphi)\bigr]\\
 &\le L_R\|D\varphi-D\psi\|_{L^1}
 \le L_R\|D\varphi-D\psi\|_{L^2}.
\end{aligned}
\]
By Parseval, with \(\widehat\varphi(k)\) using \(e^{2\pi ik\cdot x}\),
\[
\boxed{
 F(A)-\int_{\mathbb T^2}F(A+D\varphi)
 \ \le\
  2\pi L_R\left(
  \sum_{k\in\mathbb Z^2\setminus(\{0\}\cup\bigcup_{\ell\in\mathcal L}\ell)}
      |k|^2\,|\widehat\varphi(k)|^2
   \right)^{1/2}.
 }\tag{6}
\]
This estimate applies to **every** anisotropic, signed, nonhomogeneous F that is globally rank-one convex and **every** periodic Lipschitz gradient, with no bound on its frequency count, amplitude or oscillation scale. One may minimize the RHS over all choices of up to three directions.

**Necessary quantitative condition for a Morrey counterexample.** If a genuine periodic gradient produces strict deficit \(\delta>0\), then for **every** choice of three frequency lines,
\[
\boxed{
 \|D\varphi-DP_{\mathcal L}\varphi\|_{L^2}
 \ge\delta/L_R,\qquad
 \sum_{k\notin\cup\ell}|k|^2|\widehat\varphi(k)|^2
 \ge \delta^2/(4\pi^2L_R^2).
 }\tag{7}
\]
No such counterexample can be exactly supported on three Fourier lines or even *too close* to one. This is not a bound on the number of directions needed for a hypothetical counterexample beyond "at least four," and \(\delta/L_R\) depends on the integrand and its amplitude range.

## 4. Exact checks and limits

The [standard-library exact checker](../../research/audit/iwaniec_three_ridge_kernel_exact.py) verifies the square-wave fundamental Fourier coefficient numerator 4, the vanishing sine moment, and an exact rational five-line Fourier projection example with total gradient spectral energy 542, retained 80, and discarded tail 462. The signed integral identities were also independently checked symbolically by exact integration.

**What is known versus deduced:** (S), the three-sawtooth case, is **published** (2017). Equations (2)–(7) are elementary hand deductions with no priority claim. This is not a finite exhaustive classification of general gradients and is NOT unrestricted Morrey: for generic fields the right side of (6) is strictly positive. To settle the general problem one must control the genuinely four-and-more-direction phase correlations for arbitrary RC energies, or construct an actual globally RC/non-QC gradient pair.

## References

- G. Sebestyén and L. Székelyhidi Jr., *Laminates Supported on Cubes*, J. Convex Anal. 24 (2017), 1217–1237, https://doi.org/10.68381/jca24070.
- A. Guerra and R. Teixeira da Costa, *Numerical evidence towards a positive answer to Morrey's problem*, Rev. Mat. Iberoam. 38 (2022), 601–614, Theorem 3.3(d), https://doi.org/10.4171/RMI/1286.
