# An exact three-wave heat-flow obstruction inside the globally polyconvex p>2 class

Date: 23 November 2026. **Fully exact Fourier arithmetic, with an independently replayable
standard-library checker**. This is a negative result for a universal proof METHOD:
componentwise heat flow may *increase* energy even for globally polyconvex,
nonnegative, isotropic, positively homogeneous integrands on real 2×2 matrices.
It does not provide a counterexample to Morrey, Guerra–Kristensen, or quasiconvexity.

The existing [research ledger H24](LEDGER.md) already noted a heat-flow
obstruction for \(F_\eta=(\det A)^2+\eta\|A\|^2\), including the case η=0.
The main new value of this note is a **short, completely explicit three-wave
periodic Fourier certificate and a smooth open-exponent extension**,
not a claim of novelty of the failure phenomenon.

## 1. The integrand and the actual periodic trajectory

Let \(Q=(\mathbb R/2\pi\mathbb Z)^2\) and write
\(\fint_Q\) for normalized average.
Choose the integer base matrix
\[
 A=\begin{pmatrix}8&-2\\-18&-17\end{pmatrix},
 \quad \det A=-172.
\]
Let
\[
 k_0=(1,-1),\quad k_1=(2,2),\quad k_2=(1,3)
\]
with squared frequencies
\(\lambda_0=2,\lambda_1=8,\lambda_2=10\).
Define the entire smooth affine-periodic trajectory
\[
 u(t,x)=Ax+
 \begin{pmatrix}
 -2e^{-2t}\sin(k_0\cdot x)
 +3e^{-8t}\sin(k_1\cdot x)
 +2e^{-10t}\sin(k_2\cdot x)\\
 -e^{-8t}\sin(k_1\cdot x)
 -3e^{-10t}\sin(k_2\cdot x)
 \end{pmatrix}.
\]
The affine part is harmonic, and each Fourier mode
solves \(\partial_t u=\Delta u\).
The gradients \(Du(t,\cdot)\) are **actual compatible
2×2 planar gradients**; no unphysical measure
or inconsistent determinant moments appear.

Take
\[
               F_4(B)=(\det B)^2.
\]
This is globally polyconvex, isotropic,
nonnegative and positively 4-homogeneous.

## 2. Exact Fourier determinant and derivative

Write \(c_{m,n}(x)=\cos(mx_1+nx_2)\).
Directly expanding \(\det Du(0,x)\) with the
product-to-sum identity yields
\[
\begin{aligned}
J(x)=\det Du(0,x)
 ={}&-172+56c_{1,-1}-2c_{2,2}+4c_{3,1}\\
 &\quad+12c_{0,4}-14c_{3,5}.
\end{aligned}                                                \tag{1}
\]
Differentiating the determinant along the heat
trajectory gives
\[
\begin{aligned}
\dot J(x)
={}&112c_{1,-1}-32c_{2,2}-40c_{3,1}\\
 &\quad-144c_{0,4}+252c_{3,5}.
\end{aligned}                                                \tag{2}
\]
All frequencies in these lists are distinct up to
sign. Their normalized cosine products have mean
0 for unequal frequencies and mean 1/2 for equal
nonzero frequencies. Thus the exact initial energy is
\[
\fint_QJ^2
 =(-172)^2+\frac12(56^2+(-2)^2+4^2+12^2+(-14)^2)
 =31332.
\]
More importantly,
\[
\boxed{\begin{aligned}
\frac{d}{dt}\bigg|_{t=0}
   \fint_Q(\det Du(t,x))^2\,dx
 &=2\fint_QJ\dot J\\
 &=56(112)+(-2)(-32)+4(-40)\\
 &\qquad+12(-144)+(-14)(252)\\
 &=\mathbf{920}>0 .
\end{aligned}}                                             \tag{3}
\]
There is **no numerical quadrature** in this identity.
The actual gradient and determinant moment check
\(\fint_Q\det Du(0,x)=\det A=-172\)
follows directly from the constant Fourier coefficient.
The [exact verifier](../../research/audit/iwaniec_p4_heatflow_three_wave_exact.py)
constructs the full cosine Fourier algebra from
integer wavevectors/coefficients, verifies (1),(2),
the energy 31332, the correct determinant moment
and derivative +920.

Thus **heat-flow energy decrease is false already
for a globally polyconvex degree-4 integrand**,
and for a concrete three-wave compatible map.

## 3. Robust continuum of positive exponents near p=4

For every real p≥2 the determinant-power integrand
\[
                  F_p(B)=|\det B|^{p/2}
\]
is nonnegative, isotropic, positively
p-homogeneous, and polyconvex globally,
because \(d\mapsto|d|^{p/2}\) is convex.

For the **same** heat trajectory let
\[
 E_p(t)=\fint_Q|J(t,x)|^{p/2}\,dx .
\]
For p>2, the time derivative at zero is
\[
 E'_p(0)=\frac p2\fint_Q
 |J|^{p/2-2}J\,\dot J\,dx.
\]
The integrand is continuous in p near 4,
uniformly dominated because J and \(\dot J\)
are bounded smooth periodic functions.
Thus \(p\mapsto E'_p(0)\) is continuous
at p=4. Equation (3) yields \(E'_4(0)=920>0\).
Therefore there exists \(\varepsilon>0\) such
that
\[
  E'_p(0)>0 \qquad
  \text{for every }p\in(4-\varepsilon,4+\varepsilon).
\]
No explicit numerical ε is asserted;
the open-exponent conclusion follows from
rigorous continuity and the exact strict sign.

This is an **infinite interval of p>2
globally polyconvex counterexamples to
universal heat-flow monotonicity**.
They are not counterexamples to RC⇒QC.

## 4. Research stop rule

The 2026 Bruno–Pasqualotto proof of the special
Dacorogna–Marcellini quartic uses a
**specialized** componentwise heat-flow sign.
The example above shows that no
argument asserting a universally
nonincreasing \(\int F(Du_t)\) for all
nonnegative isotropic p>2 rank-one-convex
F can be correct. This fails on an open
p interval even among polyconvex energies.

A global proof of Guerra–Kristensen
Question 1.7 or Morrey must exploit
further structure, find an adaptive
flow with a genuinely new sign identity,
or avoid universal heat-flow
monotonicity entirely. This stop rule
does **not** rule out all evolution methods.

Evidence: exact Fourier coefficient equality
and elementary continuity for the open-p
extension; no Lean/CI or external referee
validation has been performed.
