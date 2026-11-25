# Open-family strengthening of the exact hybrid-cone obstruction

22 November 2026. **Mathematical hand consequence of the
[exact p=4 no-go](IWANIEC_MORREY_HYBRID_NOGO.md);
not a Morrey counterexample or Lean theorem.**

Let h₀ be the rational Chebyshev profile from the linked note.
There is **δ>0** such that for every
\(p>2\) and \(h\in C^2([-1,1])\) with
\[
 |p-4|+\|h-h_0\|_{C^2}<\delta,
\]
the isotropic p-homogeneous integrand
\(F_{p,h}(A)=\|A\|_{\mathrm{op}}^p
h(\det A/\|A\|_{\mathrm{op}}^2)\), with F(0)=0,
is nonnegative and **globally rank-one convex**,
but the Burkholder–polyconvex hybrid minorant
envelope lies strictly below it at
\(A_0=\operatorname{diag}(1,0)\).

## Proof

Write \(\kappa(p)=1-2/p\) and, for a general p,h,
\[
\begin{aligned}
 C&=ph-2rh',\quad U=(p-1)C+r^2h'',\\
 E&=(p-2)h'-rh'',\\
 P_+&=C+(1-r)E,\quad P_-=C-(1+r)E,\\
 Q_+&=(1-r)^2Uh''-P_+^2,\quad
 Q_-=(1+r)^2Uh''-P_-^2.
\end{aligned}
\]
The exact Bernstein checker in the parent note proves that
on the entire compact interval \([-1,1]\),
\(h_0,C,h_0''\) are **strictly positive**, and both
\(\max(P_+,Q_+)\) and \(\max(P_-,Q_-)\) are
strictly positive. Their joint minimum is therefore
positive. These expressions depend continuously
on p,h,h',h'',r, so the signs persist in a product
neighborhood of \((4,h_0)\). The general scalar
acoustic criterion and its positive endpoint
conditions prove global rank-one convexity there.

To keep the two-point separator valid when p varies,
take \(r_\pm=\pm1/3\) and
\[
 \lambda_-=\frac54,\qquad
 \lambda_+(p)=
 \frac{5/12-\kappa(p)/4}{\kappa(p)+1/3}.
\]
Both weights are positive near p=4. For the
Burkholder linear generators \(\kappa\pm r\),
\(\lambda_-(\kappa-1/3)+\lambda_+(\kappa+1/3)
=\kappa\) identically, while the opposite
orientation has strict slack at p=4.

For the power generators \((c+mr)_+^{p/2}\)
with c>0, divide by c^{p/2}, set z=m/c,
and consider
\[
 \Psi_p(z)=\lambda_-(1-z/3)_+^{p/2}
           +\lambda_+(p)(1+z/3)_+^{p/2}.
\]
The minimum is attained (uniform coercivity in z)
and varies continuously with p. At p=4,
\(\min_z\Psi_4(z)=35/32>1\), so this
inequality is strict for p near4.
The c=0 case is automatic. Thus for every
hybrid generator g, its positive-cone sums
and pointwise suprema,
\(\lambda_-g(-1/3)+\lambda_+g(1/3)\ge g(0)\).

Finally, at the center the profile gap is
exactly
\[
 h_0(0)-\frac54h_0(-1/3)-\frac7{20}h_0(1/3)
 =\frac{356912972869}{17832200896512}>0.
\]
Continuity in p,h preserves a strictly positive
gap, completing the proof. No explicit numerical δ
is asserted; its existence follows from compactness
and the strict exact certificate.

**Scope:** This refutes the hybrid **representation**
for an infinite-dimensional open set of profiles
and an interval of p, not the quasiconvexity of
any of the integrands. It closes the old positive
gate G_p *negatively*, rather than solving Morrey.
