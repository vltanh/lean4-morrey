# Global failure of the p>2 hybrid Burkholder–polyconvex certificate hierarchy

**22 November 2026. Exact counterexample to the specific certificate-completeness conjecture, NOT to Morrey.**
The code in [iwaniec_hybrid_no_go_exact.py](../../research/audit/iwaniec_hybrid_no_go_exact.py)
uses **only standard-library rational arithmetic**. It proves a finite recursive
Bernstein certificate and an exact separator inequality. The mathematical
bridge from the scalar acoustic criterion to global rank-one convexity is written
below and is not yet formalized in Lean or independently peer-reviewed.
No assertion that a Morrey counterexample has been found is made.

## 1. The precise conjecture disproved

The [hybrid support hierarchy](IWANIEC_MORREY_GENERAL.md) conjectured, for every
p>2 and every nonnegative isotropic positively p-homogeneous globally
rank-one-convex integrand F, that its signed singular-value profile
h(r), r∈[-1,1], can be recovered pointwise as the supremum
of all profiles below h that have the form

\[
 g(r)=\alpha(\kappa+r)+\beta(\kappa-r)
       +\sum_{j=1}^N\gamma_j(c_j+m_jr)_+^{p/2},\qquad
 \kappa=1-2/p,
\]
with N arbitrary finite, \(\alpha,\beta,\gamma_j,c_j\ge0\),
\(m_j\in\mathbb R\).
These are globally quasiconvex matrix energies if the 2026
Iwaniec Burkholder claim holds. We show that even for p=4,
their **pointwise-supremum envelope need not equal h**.

This obstruction is **independent of accepting Iwaniec's paper**:
it is an exact algebraic impossibility of the proposed representation.
It does **not** imply h is non-quasiconvex; a different support
class or a proof bypassing lower supports might still work.

## 2. A single globally rank-one-convex p=4 profile

Let \(T_j(r)=\cos(j\arccos r)\) be the Chebyshev polynomials
(\(T_0=1,T_1=r,T_{j+1}=2rT_j-T_{j-1}\)). Define

\[
 \boxed{h(r)=2^{-24}\sum_{j=0}^{12}a_jT_j(r)}
\]

with the **exact integer vector**

\[
\begin{split}
(a_0,\ldots,a_{12})={}&
(37676885,55559819,22507846,3634764,1122809,\\
&1068027,57237,275379,623336,96945,\\
&-261804,-126467,-6991).
\end{split}
\]

Define \(F(0)=0\), and for every \(A\ne0\) let

\[
 a=\|A\|_{\mathrm{op}}>0,\quad
 r_A=\frac{\det A}{a^2}\in[-1,1],\quad
 \boxed{F(A)=a^4h(r_A)}.                 \tag{1}
\]

This is nonnegative, SO(2)×SO(2)-invariant, positively
4-homogeneous, finite and continuous.

**Proposition 2.1.** F is rank-one convex globally on \(\mathbb R^{2\times2}\).

**Hand proof with exact computation reduced to integer signs.**
Use the smooth isotropic [acoustic criterion](IWANIEC_MORREY_ACOUSTIC.md).
At a distinct-singular-value matrix, for p=4 let

\[
\begin{aligned}
C&=4h-2rh', & B&=\frac C{1-r^2},\\
U&=3C+r^2h'', & V&=h'',\\
T&=rB+2h'-rh''.
\end{aligned}
\]

For each r∈(-1,1), nonnegativity of the rank-one Hessian
is **equivalent** to

\[
 C\ge0,\quad V\ge0,\quad |T|\le B+\sqrt{UV}.             \tag{2}
\]

The exceptional conformal matrices require
\(C(\pm1)=4h(\pm1)\mp2h'(\pm1)\ge0\).
On rank-one lines through 0, the restriction is
\(|t|^4F(H)\), convex because \(h(0)\ge0\).

To verify (2) with **no floating-point samples**, put
\(H=2^{24}h\), \(N=H''\), \(C_0=4H-2rH'\),
\(U_0=3C_0+r^2N\), and \(E=2H'-rN\).
Define the four **integer polynomials**

\[
\begin{aligned}
P_+&=C_0+(1-r)E,&
P_-&=C_0-(1+r)E,\\
Q_+&=(1-r)^2U_0N-P_+^2,&
Q_-&=(1+r)^2U_0N-P_-^2 .
\end{aligned}                                          \tag{3}
\]

A direct rearrangement, using
\(B\pm T=P_\pm/[2^{24}(1\mp r)]\), shows that
(2) follows from these **univariate exact sign tests**:

\[
\boxed{H>0,\ C_0>0,\ N>0,\quad
(P_+>0\ \lor\ Q_+>0),\quad
(P_->0\ \lor\ Q_->0)}                    \tag{4}
\]

for all r∈[-1,1]. The script converts all seven
integer polynomials to rational Bernstein coefficients
on [-1,1], recursively bisects at dyadic midpoints,
and requires **all Bernstein coefficients strictly
positive** for each of H,C₀,N and one of each P/Q
pair on every covered interval. Bernstein positivity
is an exact sufficient proof of polynomial positivity.
The checker finishes with **12 covered intervals,
maximum bisection depth 6**. Endpoints are included.
Thus (4), and hence global rank-one convexity, follow
without trusting any numerical optimizer. QED.

## 3. Universal two-point separator for the whole hybrid cone

At p=4, \(\kappa=1/2\). Define the positive linear
evaluation functional

\[
 \Lambda(g)=\frac54g(-1/3)+\frac7{20}g(1/3).
\]

**Lemma 3.1 (exact, infinite generator family).**
For **every** hybrid generator \(g\) with p=4,
including arbitrary nonnegative finite sums,

\[
                  \boxed{\Lambda(g)\ge g(0).}          \tag{5}
\]

**Proof for the two Burkholder generators.**
For \(b_\pm(r)=1/2\pm r\),

\[
 \Lambda(b_+)=1/2=b_+(0),\qquad
 \Lambda(b_-)=11/10>1/2=b_-(0).
\]

**Proof for every polyconvex generator.**
Let \(q(r)=(c+mr)_+^2\) with *any*
\(c\ge0\), \(m\in\mathbb R\).
When c=0, (5) follows from nonnegativity.
For c>0 divide by c² and set z=m/c.
The convex function

\[
 \frac54(1-z/3)_+^2+\frac7{20}(1+z/3)_+^2
\]

has global minimum **35/32**, attained at \(z=27/16\)
where both positive parts are active.
Its derivative vanishes there, and convexity
establishes the global minimum, including
z outside [-3,3]. Since 35/32>1=q(0)/c²,
(5) holds strictly for c>0.

Linear addition with nonnegative coefficients
preserves (5). Pointwise maxima, pointwise
suprema (when finite), and locally uniform limits
also preserve the inequality by monotonicity
of the positive functional \(\Lambda\). QED.

**Proposition 3.2 (strict exact separation).**
The actual h above satisfies

\[
\begin{aligned}
h(0)-\Lambda(h)
&=\frac{356912972869}{17832200896512}\\
&>0.                                                 \tag{6}
\end{aligned}
\]

This equality is verified using only rational
Chebyshev evaluation in the standard-library
checker. Thus for *every* admissible hybrid
minorant \(g\le h\),

\[
 g(0)\le\Lambda(g)\le\Lambda(h)
       =h(0)-\frac{356912972869}{17832200896512}
       <h(0).                                         \tag{7}
\]

The same strict gap holds after taking
**arbitrary pointwise suprema of admissible
hybrid minorants** and therefore disproves
\(\mathcal E_4h=h\) at r=0.

The corresponding matrix is \(A_0=\operatorname{diag}(1,0)\).
This is an **entirely explicit nonnegative, globally
rank-one-convex and isotropic 4-homogeneous**
matrix integrand with a strict gap in the
proposed quasiconvex-support hierarchy.

## 4. What this does and does not establish

**Closed, exact:** The all-p>2 *hybrid envelope
completeness conjecture is false*, already at
p=4. The same finite pair of testing ratios
obstructs every number of generators,
their positive sums, maxima and arbitrary
pointwise supremum/limit closure. This is
an infinite-class no-go, not a finite-grid
negative search result.

**NOT established:** Failure of quasiconvexity
of this F; the separating evaluations are
*not* shown to be a compatible planar
gradient distribution. In fact the
separator mass \(5/4+7/20=8/5>1\);
it is **not a probability Jensen witness**.
No rank-one-convex/non-quasiconvex integrand
has been produced.

**Consequent stopping rule:** Do not attempt to
prove the old Gₚ envelope identity using
stronger scalar inequalities: (6) refutes
it as stated. Either enlarge the
quasiconvex generator class beyond the
two Burkholder orientations and the
\((c\|A\|_{\mathrm{op}}^2+m\det A)_+^{p/2}\)
family, or change to a direct all-gradient
approach. The unrestricted anisotropic,
nonhomogeneous 2×2 Morrey problem remains open.

**Next candidate:** The exact F provides
a globally rank-one-convex,
nonnegative isotropic stress-test for a
direct quasiconvexity search at A₀.
A strict negative Jensen gap would require
an **actual** compatible periodic/compactly
supported gradient law; a negative result
for this certificate cone is insufficient.
No such gap is currently certified.

**Validation:** The script is exact
and was executed against the saved coefficients.
A Lean theorem and independent mathematical
review of the acoustic-to-global bridge
are still required.
