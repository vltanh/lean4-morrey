# A global open anisotropic/nonhomogeneous class of quasiconvex but nonpolyconvex energies

Date: 23 November 2026. **Theorem conditional only on the external 2026 Bruno–Pasqualotto quasiconvexity preprint** for the Dacorogna–Marcellini quartic, [arXiv:2608.06367](https://arxiv.org/abs/2608.06367). The remaining algebra, nonpolyconvexity witness, and perturbation estimate are elementary and exact. This note is an infinite-dimensional stability extension of existing PR examples, **not** unrestricted Morrey or a publication-priority claim. No Lean build or external refereeing is claimed.

## Statement: arbitrary anisotropy AND nonhomogeneity in one open family

Put \(s(A)=\|A\|_F^2,\ d(A)=\det A\), and
\[
 q(A)=s(A)^2-\tfrac94s(A)d(A).
\]
For **every** \(G\in C_b^2(\mathbb R^{2\times2};\mathbb R)\) satisfying
\[
\boxed{
 \|G\|_{L^\infty}<\frac1{10000},\qquad
 \sup_A\|D^2G(A)\|_{\rm op}<\frac1{1000},
}\tag{1}
\]
define
\[
\boxed{
 W_G(A)=1+\exp(q(A))+\frac1{1000}\|A\|_F^2+G(A).
}\tag{2}
\]

**Theorem.** Every \(W_G\) is simultaneously:

1. globally **positive**, \(C^2\) (smooth if G smooth), quadratically **coercive**;
2. globally **quasiconvex** (conditional on the cited Bruno–Pasqualotto 2026 theorem);
3. uniformly **strongly rank-one convex**, with
\[
 D^2W_G(A)[H,H]\ge \frac1{1000}\|H\|_F^2
 \quad\text{for every rank-one H};
\]
4. globally **nonpolyconvex**, with a fixed exact four-atom minors Jensen deficit independent of G;
5. generally **anisotropic and nonhomogeneous**: e.g. a nonzero sufficiently small \(G(A)=\eta\sin(a_{11})\) meets (1) and breaks SO(2)×SO(2)-isotropy.

In fact the class is a genuine open ball in the full infinite-dimensional bounded-\(C^2\) topology. It is not restricted to polynomials or to a fixed number of anisotropic parameters. The statement of global quasiconvexity holds for **every** Lipschitz periodic planar gradient of arbitrary amplitude and frequency, *given the published q result*.

## Proof

**Quasiconvexity.** The published Bruno–Pasqualotto result states that
\(f_\gamma(A)=s^2-2\gamma sd\) is QC for
\(|\gamma|\le2/\sqrt3\). Here \(\gamma=9/8\), and
\(9/8<2/\sqrt3\) since \(243<256\) after
squaring the positive fractions.
Thus q is QC (external 2026 input).
Because the exponential is convex increasing,
\[
 e^{q(A)}
 \le e^{\fint q(A+D\varphi)}
 \le \fint e^{q(A+D\varphi)}
\]
for any periodic Lipschitz gradient, by QC
and scalar Jensen. So \(e^q\) is QC.

The perturbation
\(V_G(A)=\|A\|_F^2/1000+G(A)\)
is **globally convex**, not merely rank-one
convex: for every A,H,
\[
D^2V_G(A)[H,H]\ge
(2/1000-1/1000)\|H\|^2
= \|H\|^2/1000.
\]
The sum \(1+e^q+V_G\) is QC and has the stated
global strong rank-one margin. No small-gradient
or finite-mesh assumption is used.

**Positive/coercive.** By \(|G|<1/10000\),
\[
 W_G(A)>1-\frac1{10000}
             +\frac1{1000}\|A\|_F^2>0 .
\]
Hence it is globally positive and coercive.

**Fixed minors law and nonpolyconvexity.**
Take \(J=\operatorname{diag}(1,-1)\), \(K=J/5\)
and the symmetric probability law
\[
 \nu=\tfrac1{52}(\delta_I+\delta_{-I})
   +\tfrac{25}{52}(\delta_K+\delta_{-K}).
\]
It satisfies exactly
\(\int A\,d\nu=0\) and
\(\int\det A\,d\nu=0=\det0\).
At its atoms,
\[
 q(\pm I)=-1/2,\quad q(\pm K)=17/1250,
 \qquad
 \int\|A\|^2\,d\nu=2/13.
\]
Using the *rational exponential upper bounds*
from [the independently checked no-homogeneity example](IWANIEC_MORREY_NONHOMOG_PC_NOGO.md),
\[
 \int e^{q(A)}\,d\nu
 <\frac{19705}{19728}.
\]
Thus, with \(W_0=1+e^q+\|A\|^2/1000\),
\[
\boxed{
 \int W_0\,d\nu-W_0(0)
 <-\frac{32443}{32058000}.
}
\]
For any G satisfying (1), the weighted average of its values
has absolute value less than \(1/10000\),
as does \(G(0)\). Therefore
\[
\boxed{
 \int W_G\,d\nu-W_G(0)
 <-\frac{32443}{32058000}+\frac1{5000}
 =-\frac{130157}{160290000}<0.
}\tag{3}
\]
This strict lifted minors Jensen violation
contradicts polyconvexity. The witness
is **not claimed to be an actual compatible
planar gradient Young measure**; it
does not contradict quasiconvexity.

**Infinite dimensional and symmetry breaking.**
For example choose \(G(A)=10^{-5}\sin(a_{11})\).
Its sup norm and all Hessian spectral norms
are at most \(10^{-5}\), so (1) holds. It is
not bi-SO(2)-invariant, and W_G cannot be
positively homogeneous because of the
constant and exponential terms. Arbitrary
bounded C² perturbations within (1) are
allowed, including nonsymmetric, nonpolynomial
functions of all four matrix entries.
That proves the theorem. QED.

## Exact independent control and limits for unrestricted Morrey

The accompanying [exact rational checker](../../research/audit/iwaniec_anisotropic_open_qc_nonpc_exact.py)
verifies:
\(9/8<2/\sqrt3\) by integer comparison,
the four lifted minor moments,
the energy of the quartic at the atoms,
and the strict rational upper gap
after *every* C² perturbation obeying (1).
The proof of QC of the quartic itself
is **not derived by this checker**; the
Bruno–Pasqualotto 2026 result is explicitly
an external assumption.

This class crosses **both** anisotropy and
nonhomogeneity at once, giving an
all-amplitude QC non-PC neighborhood in
which the unrestricted Morrey implication
holds. However the reason it holds is
the chosen **known QC core plus a
globally convex perturbation**.
It says nothing about an *arbitrary*
anisotropic nonhomogeneous globally RC
integrand, and it does not provide
a general rank-one-convex decomposition
into this QC core and convex perturbations.
The general 2×2 Morrey problem therefore
remains **OPEN**.
