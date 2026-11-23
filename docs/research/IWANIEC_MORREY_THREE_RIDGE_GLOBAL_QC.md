# INVALID three-ridge theorem attempt: Jensen inequality runs in the wrong direction

**Critical audit correction, 23 November 2026. STATUS: THE PROPOSED THREE-RIDGE PROOF IS INVALID AND ITS GLOBAL FOURIER-TAIL CLAIM IS UNPROVED.**

This file supersedes the same-day preliminary argument published in commit
[a18f1e5](https://github.com/vltanh/lean4-morrey/commit/a18f1e53a30405a067ad65dc6679caeb145891a3).
It is retained explicitly as a failed research approach to avoid reusing a false implication.
**Do not cite the earlier commit as proving arbitrary-three-ridge Jensen, a spectral-tail estimate, or any extension of Morrey.**

## 1. Correct published input

Sebestyén–Székelyhidi, *Laminates Supported on Cubes* (2017), and Guerra–Teixeira da Costa (2022), Theorem 3.3(d), prove that every real 2×2 rank-one-convex integrand F satisfies Jensen for any **three half-duty square-wave/sawtooth gradient components**. The compatible square-wave gradients are
\[
 D\psi(x)=\sum_{j=1}^3 (v_j\otimes k_j)
    {\rm sgn}\cos(2\pi k_j\cdot x-\theta_j).
\]
This external theorem is correct and does not impose isotropy, homogeneity or nonnegativity.

**It does NOT say** that every sum of three arbitrary vector-valued ridge gradients satisfies Jensen. The latter conclusion was purportedly inferred by square-wave randomization, but the inference fails as explained below.

## 2. Exact randomization is correct, but yields only an UPPER bound

For \(h(s)=\operatorname{sgn}(\cos s)\), exact integration gives
\[
 \mathbb E_\Theta[\cos\Theta\,h(s-\Theta)]
    =\tfrac2\pi\cos s,\quad
 \mathbb E_\Theta[\sin\Theta\,h(s-\Theta)]
    =\tfrac2\pi\sin s.
\]
Consequently any zero-mean trigonometric vector polynomial
\[
G(s)=\sum_{m=1}^M[u_m\cos(ms)+v_m\sin(ms)]
\]
is the pointwise expectation of one randomly chosen and shifted square-wave vector amplitude:
\[
 Z(s;J,\Theta)=\tfrac{\pi M}2
  (u_J\cos\Theta+v_J\sin\Theta)\,
  h(Js-\Theta),\qquad \mathbb E Z(s)=G(s).
\]
Here J is uniform in \(\{1,\ldots,M\}\) and Theta is uniform on the circle.

For independent randomizations of three ridge components, **rank-one convexity** yields at each spatial point x
\[
\boxed{
F\bigl(A+\sum_j G_j(k_j\cdot x)\otimes k_j\bigr)
\ \le\
\mathbb E_\omega F\bigl(A+\sum_jZ_j(k_j\cdot x;\omega_j)\otimes k_j\bigr).
}\tag{1}
\]
The rank-one differences for fixed right factor make Jensen valid, but its **direction is ≤, not ≥**.

The published three-sawtooth theorem says
\[
\boxed{\quad
\mathbb E_\omega\int F\bigl(A+\sum_jZ_j\otimes k_j\bigr)
  \ \ge\ F(A).\quad}\tag{2}
\]

The inequalities (1)–(2) have **no implication** about the sign of
\[
\int F\bigl(A+\sum_jG_j\otimes k_j\bigr)-F(A).
\]
In elementary logic, \(X\le Y\) and \(Y\ge Z\) do NOT imply \(X\ge Z\).
This is the precise fatal gap in the previous attempt.

Even for the convex quadratic F(B)=||B||², the randomization generally has a **strict positive Jensen surplus**: for one scalar \(G(s)=\cos s\), the randomization \(Z=(\pi/2)\cos\Theta\,h(s-\Theta)\) has
\[
\mathbb E_\Theta Z^2=\pi^2/8>1/2
=\int_{\mathbb T}G(s)^2\,ds.
\]
Thus one cannot reverse the energy comparison by appealing to Fourier identities.

## 3. Status of the proposed global Fourier-tail inequality

The earlier note also proposed the spectral-tail bound
\[
F(A)-\int F(A+D\varphi)
 \overset{?}{\le}
 L_R\|D\varphi-DP_{\mathcal L}\varphi\|_{L^2},
\]
where \(P_{\mathcal L}\) is Fourier projection onto three frequency lines.

**This claim is unproved.** Its derivation required
\(\int F(A+DP_{\mathcal L}\varphi)\ge F(A)\)
for **arbitrary three-ridge vector waveforms**, precisely the missing theorem.
The identity for the Fourier projection and the Lipschitz comparison between
\(\int F(A+D\varphi)\) and
\(\int F(A+DP_{\mathcal L}\varphi)\) are correct, but provide no lower
bound without proving this three-ridge Jensen step.

The [exact kernel/projection test](../../research/audit/iwaniec_three_ridge_kernel_exact.py)
checks **only** Fourier identities; it must not be interpreted as a three-ridge Jensen certificate.

## 4. What remains VALID and global

The separately proved [all-wave frequency resonance sieve](IWANIEC_MORREY_RESONANCE_SIEVE.md)
remains sound: for any finite-valued rank-one-convex F and any number N of compatible
**sinusoidal** plane waves, independent-phase Jensen and absence of short integer
frequency relations give exact Jensen for polynomial F; tensor Bernstein
approximation gives an explicit approximate Jensen bound for arbitrary locally
Lipschitz F. It does **not** rely on the invalid randomized-square-wave argument.

**Research gate:** To upgrade to arbitrary three-ridge Jensen, one must supply a
genuine **lower-energy preserving** approximation by published laminates,
or prove the three-ridge inequality independently. Applying ordinary
Jensen to a barycentric randomization has the wrong sign.
For unrestricted Morrey, even a valid three-ridge theorem would
still leave four-and-more-direction compatible gradients.

**Evidence level:** Exact logical audit and elementary countercontrol to the
proposed inference. No general three-ridge theorem, no counterexample to
three-ridge Jensen, and no unrestricted Morrey solution are claimed.
