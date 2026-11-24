# Complete N=0,...,4 case ledger and a two-corner reduction of N=4

23 November 2026. Hand proofs plus exact rational controls executed
in Python. No Lean verification, independent refereeing, priority
clearance, full four-wave theorem or unrestricted Morrey proof claimed.

**Main new result:** To prove four-sawtooth-wave quasiconvexity
for every planar rank-one convex F, it suffices to prove the
following TWO fixed-weight cube inequalities for arbitrary
rank-one matrices H_1,...,H_4. There is no remaining enumeration
over integer frequencies or phases in this sufficient target.

For e in {-1,1}^4 write e_S=prod_{i in S} e_i and X_e=sum_i e_i H_i.
The targets, each with zero barycenter, are

(D)  sum_e [1 + e_{123}/2 + e_{124}/2] F(A+X_e)/16 >= F(A).

(TQ) sum_e [1 + e_{123}/2 + e_{1234}/2] F(A+X_e)/16 >= F(A).

Both laws have four zero weights, eight weights 1/16, and four
weights 1/8. These are fixed 16-vertex tests with continuous
amplitude-matrix parameters, NOT two proven laminates.

This is a **sufficient** reduction. Arbitrary H_i in a model
corner need not have the spatial directions of a compatible
gradient realizing that corner. Failure of a corner for some H_i
would not automatically refute four-wave quasiconvexity.

## 1. The correct quantifiers and the cases N=0,...,3

The wave model is
$$
\varphi(x)=\sum_{i=1}^N a_i s(k_i\cdot x+c_i),\quad
D\varphi(x)=\sum_i H_i r(k_i\cdot x+c_i),\quad H_i=a_i\otimes k_i,
$$
with integer nonzero k_i, arbitrary phases and amplitudes, periodic
sawtooth s, and r=s' equal to +1 on [0,1/2) mod 1 and -1 on
the other half.

[Guerra–Teixeira da Costa (2022), Proposition 3.2 and Theorem 3.3](https://doi.org/10.4171/RMI/1286)
give the all-N characterization and the known one-, two-, and
three-wave results. The deep input throughout this note is
[Sebestyén–Székelyhidi (2017), Theorem 1](https://doi.org/10.68381/jca24070),
which proves Jensen on any three-rank-one cube for the pure
triple-parity law 2^{-3}(1+rho e_1 e_2 e_3), |rho|<=1/2.
See also [the arXiv version](https://arxiv.org/abs/1504.06516).
The theorem plus independent rank-one splits proves the
pure-parity law for any support size >=3, as in
[the preceding four-wave note](IWANIEC_MORREY_FOUR_WAVE_PARITY_THEOREM.md).

| Wave count | Complete status |
| --- | --- |
| 0 | Equality. |
| 1 | Single rank-one midpoint split. |
| 2 | Nonparallel character phases are independent Haar; parallel waves lie in one rank-one subspace. |
| 3 | Published planar three-wave theorem. |
| 4 | Reduced here to D and TQ; neither is claimed closed. |
| Arbitrary N | Open. |

The [minimal resonance theorem](IWANIEC_MORREY_MINIMAL_RESONANCE.md)
bounds the size of an inclusion-minimal odd resonance by four.
It does NOT bound the number of waves in a negative Jensen
witness. Arbitrarily large overlapping circuit clusters exist.
In particular, closure of both targets above would settle N=4
but not by itself settle unrestricted Morrey.

## 2. Four distinct spatial directions: exhaustive mod-2 types

For the sign law let C_S=E e_S. Every singleton moment is zero.
When all four spatial directions are pairwise nonparallel, every
pair of characters sends Haar measure on T^2 onto Haar measure
on T^2, so all pair moments are zero. Walsh inversion then gives
$$
p(e)=\frac1{16}\left(1+\sum_{|S|=3}C_Se_S+C_{1234}e_{1234}\right).
\tag{1}
$$
The triple coefficients have magnitude <=1/2, by the published
three-wave frequency bound (or the direct primitive-relation
Fourier computation in the dyadic note).

Normalize the generated lattice L=sum Z k_i by a choice of
integral basis of L. Thus the coordinate vectors q_i generate
Z^2, even if the basis is not unimodular in the original ambient
lattice. This preserves the phase law: the map of tori with
the original basis rows is Haar-surjective. Write z for the
number of zero classes q_i mod 2. At least two distinct nonzero
classes occur, because the q_i generate Z^2. A moment C_S
can be nonzero only if the sum of q_i over S vanishes mod 2:
an odd integer relation is necessary, by Fourier support
(or average over half-period translations). The possibilities
are completely exhausted by this table, up to the action
permuting the three nonzero classes.

| z | Nonzero class multiplicities | Potential triple moments | Potential quadruple moment | Result |
| --- | --- | --- | --- | --- |
| 0 | 3+1 | 0 | No | Uniform, closed |
| 0 | 2+2 | 0 | Yes | Pure 4-parity, closed below |
| 0 | 2+1+1 | 2 | No | D square |
| 1 | 2+1 | 1 | No | Pure 3-parity, closed |
| 1 | 1+1+1 | 1 | Yes | TQ square |
| 2 | 1+1 | 0 | No | Uniform, closed |

These are possible supports, not assertions that every listed
moment is nonzero for every frequency tuple or phase. The exact
checker counts the 22 normalized rank-two multisets of four
mod-2 classes; the six rows above merge equivalent multisets.

The crucial missing quantitative fact for the TQ row is
the uniform quadruple bound, proved next.

## 3. Universal four-parity bound for pairwise nonparallel directions

**Theorem.** For any four pairwise nonparallel nonzero integer
frequencies and any phases,
$$
|C_{1234}|\le 1/2. \tag{2}
$$
This includes mixed triple/quadruple resonance, not only a
minimal four-circuit. No matrix amplitudes enter the assertion.

### 3.1. A lattice-projection Fourier bound

Use normalized q_i as above and let
K=ker(Z^4 -> Z^2), where the map has columns q_i.
If there is no all-odd integer relation, the quadruple
moment is identically zero. Otherwise choose one odd relation
n^0. The set of all odd relations is exactly R=n^0+2K:
the difference of two such relations is even and halving
it still gives an integer relation.

For any two-index set I, its coordinate projection P_I K
is a full-rank subgroup of Z^2 of index
$$
d_I=|\det(q_j,q_l)|,\qquad I^c=\{j,l\}.
$$
Indeed the image of the homomorphism Z^I -> Z^2/L_{I^c}
given by the corresponding q_i is onto, since all four q_i
generate Z^2. Its kernel is precisely P_I K. Moreover
P_I is injective on K, because the complementary two
vectors are independent. It is also injective on R.
Thus summing over R a function of just the two projected
coordinates does not overcount their multiplicity.

Put W=sum_{n odd} n^{-2}=pi^2/4 (both positive and negative).
We will use two exact estimates:
$$
\sum_{n\in R}\prod_{i\in I}n_i^{-2}
\le \begin{cases}
W^2/2 & \text{if } d_I\text{ is even},\\
4W^2/9 & \text{if } d_I\text{ has an odd prime divisor},\\
W^2 & \text{always}.
\end{cases} \tag{3}
$$
For the even-index estimate, the image P_I K modulo 2 is
a proper subspace, with at most two elements. Therefore
P_I R modulo 4 occupies at most two of the four pairs
of odd residue classes. Each odd class modulo 4 has
reciprocal-square sum W/2 by sign reversal, so the
total is at most W^2/2.

For an odd prime p dividing d_I, the image of P_I K
modulo p is proper. There is a nonzero linear form
over F_p that vanishes on this image, so P_I R lies
in an affine congruence a n_i+b n_j=c mod p with
at least one coefficient nonzero. At fixed value of
the other coordinate, this restricts one coordinate
to a single residue class modulo p. Among odd integers
any such class has reciprocal-square sum at most 4W/9:
write its odd representative modulo 2p with absolute
value h in [1,p]; its sum is
$$
\sum_{t\ge0}\big((2pt+h)^{-2}+(2p(t+1)-h)^{-2}\big).
$$
Each parenthesis is nonincreasing for 1<=h<=p
(by differentiation), hence maximized at h=1.
It is then nonincreasing in p>=3 term by term.
For p=3,h=1 the class has sum (1-1/9)W/2=4W/9
(by sign symmetry of the two classes not divisible
by 3). This proves (3).

The Fourier coefficient of the quadruple moment in
the four phases is zero outside R, and on R its
absolute value is 16/(pi^4 |n_1 n_2 n_3 n_4|).
For any complementary pair partition I,J,
Cauchy–Schwarz and (3) give
$$
\frac{16}{\pi^4}\sum_{n\in R}\frac1{|n_1 n_2 n_3 n_4|}
\le \sqrt{\gamma_I\gamma_J},
\tag{4}
$$
where gamma_I,gamma_J are the respective factors
1/2,4/9,1 supplied by (3). In particular the
phase Fourier series is absolutely summable; L^1
continuity of sign translations and Fourier uniqueness
identify it everywhere with the actual continuous moment.

### 3.2. The pure 2+2 case

By Section 2, the only z=0 pattern admitting a quadruple
moment is 2+2. Partition the indices into pairs occupying
the same nonzero mod-2 class. Both complementary
determinants are nonzero even integers. Formula (4)
with factors 1/2 and 1/2 proves (2). This also supplies
a short alternative to the previous full minimal
four-circuit argument.

### 3.3. The triple plus quadruple case with a nonunit determinant

Now z=1 and the other three classes are distinct and
nonzero. Label the zero-class vector q_4. Every pair
among q_1,q_2,q_3 has odd determinant. If one such
determinant has absolute value greater than one, select
that pair and its complement as the partition in (4).
The odd determinant has an odd prime divisor, and the
other determinant is even, since its pair includes q_4.
Consequently
$$
|C_{1234}|\le\sqrt{(4/9)(1/2)}=\sqrt{2}/3<1/2.
$$

### 3.4. The unit-triad case: a direct square integral

The only remaining case has all three pair determinants
among q_1,q_2,q_3 of magnitude one. Up to changing signs,
coordinates and phases, we may take q_1=(1,0), q_2=(0,1),
q_3=(1,1), q_4=(2a,2b), with a,b nonzero distinct
integers. The first two phases may be removed by translation.
The product of the four signs is invariant under both
half-coordinate translations. Restrict to [0,1/2)^2 and
scale both coordinates by two. The quadruple correlation
is now
$$
\int_{[0,1]^2} h(x+y)r(ax+by+c_4)\,dxdy,
\qquad h(t)=r(t/2+c_3),
$$
where h(t+1)=-h(t). On [0,1] h has at most one jump.

For integers alpha,beta nonzero and distinct, write
I(alpha,beta)=integral h(x+y)exp(2pi i(alpha x+beta y)) dxdy
over the unit square. Integrate first on the lines x+y=t.
For 0<=t<=1 the inner integral is
(exp(2pi i alpha t)-exp(2pi i beta t))/(2pi i(alpha-beta)).
For 1<=t<=2 the two terms reverse sign, since alpha,beta
are integers. Antiperiodicity of h then gives
$$
I(\alpha,\beta)
=\frac{2}{2\pi i(\alpha-\beta)}
 \int_0^1 h(t)(e^{2\pi i\alpha t}-e^{2\pi i\beta t})\,dt.
$$
For any nonzero integer l the single jump gives
|integral_0^1 h(t) exp(2pi i l t) dt| <= 2/(pi |l|):
integrate separately on the two constant pieces and
use |exp(i theta)-1|<=2. Hence
$$
|I(na,nb)|\le
\frac{2}{\pi^2 n^2}
\frac{|a|^{-1}+|b|^{-1}}{|a-b|}.
$$
Fourier expansion in c_4 now gives, by absolute
convergence (or initial L^2 approximation followed
by the summable bound),
$$
|C_{1234}|\le
\frac4{\pi^3}\sum_{n\text{ odd}}|n|^{-3}
\frac{|a|^{-1}+|b|^{-1}}{|a-b|}
\le \frac{3}{2\pi}<\frac12.
$$
In the last step sum |n|^{-3}<=W and the ratio is at
most 3/2: for equal signs the two positive magnitudes
are distinct integers, at least 1 and 2, with difference
at least 1; for opposite signs the ratio equals
1/(|a b|)<=1. This handles all integer a,b, phases,
and amplitudes without a finite cutoff.

Sections 3.1–3.4 prove (2). QED.

## 4. The two fixed corners suffice for four distinct directions

By the table in Section 2 and Theorem (2), the rows with
at most one possible Walsh coefficient are known laminates
by the pure-parity result. For the two-triple row the
two triples share two indices. Relabeling gives
p(e)=2^{-4}(1+t e_{123}+u e_{124}) with
(t,u) in [-1/2,1/2]^2. This entire square is the convex
hull of its four corners, all equivalent to D by
independent sign flips of H_i. Each law has mean zero,
so convex mixtures preserve the universal Jensen property.

For the triple+quadruple row the law is
p(e)=2^{-4}(1+t e_{123}+u e_{1234}) with both
coefficients in [-1/2,1/2]. The four corners are
equivalent to TQ (one can flip e_4 to change only
the quadruple sign, and another coordinate to
change the triple sign). Thus TQ suffices for this row.

These reductions use outer squares. They do not require
every point of the square to be attainable by actual
frequencies, nor claim this.

## 5. Parallel directions: no third corner required

At most two distinct spatial directions, with any number
of parallel waves in either, is closed: group the waves
by direction, use independence of the two primitive
character phases, and convex Jensen in each group's
rank-one linear subspace.

Suppose there are exactly three directions among four
waves. Relabel the parallel pair as 1,2; H_1,H_2 lie in
a common linear subspace E of rank-at-most-one matrices.
The other two directions are pairwise nonparallel and
transverse to the pair. The singleton moments vanish
and the only potentially nonzero pair moment is
c=E e_1e_2. Triple moments involving both parallel
waves and one other vanish by independence of the
parallel-group phase from that other character.
The entire law is therefore
$$
p(e)=\frac1{16}
(1+c e_{12}+a e_{134}+b e_{234}+d e_{1234}),\quad
|a|,|b|\le 1/2. \tag{5}
$$
Here the triple bounds come from the published
three-wave frequency bound.

### 5.1. Exact support restrictions and |d|<=1/2

Choose a primitive spatial vector p for the parallel
direction, k_j=m_j p, j=1,2, with m_j nonzero integers.
Complete p to an integer basis with determinant +/-1
and write the independent Haar phase coordinates as t,z.
The remaining phase characters are a_3 t+b_3 z+c_3,
a_4 t+b_4 z+c_4, with nonzero integers b_3,b_4 and
a_3 b_4-a_4 b_3 !=0. Let b'_i=b_i/gcd(b_3,b_4)
for i=3,4, with gcd positive. Given t, both remaining
signs are fair, and their conditional pair correlation
is the function
$$
G(t)=\int_0^1 r(a_3t+b_3z+c_3)
                 r(a_4t+b_4z+c_4)\,dz.
$$
Using the Fourier expansion of each sign, only indices
(n_3,n_4)=j(b'_4,-b'_3) contribute. If either b'_i
is even the correlation is identically zero. Otherwise
the Fourier coefficient products for odd j are
4/(pi^2 j^2 b'_3 b'_4), and the function is
$$
G(t)=\frac{1}{b'_3 b'_4}
  C(\lambda t+\theta),\quad
C(s)=1-4\min(\{s\},1-\{s\}),
$$
where lambda=a_3 b'_4-a_4 b'_3 !=0 and
theta=b'_4 c_3-b'_3 c_4. This follows also from the
usual square-wave autocorrelation C, whose Fourier
coefficients are 4/(pi^2 j^2) for odd j.
The sign choices of the b'_i are included in the
formula. All series here are absolutely summable.

Thus E|G|<=1/2, since C is a triangular wave taking
values uniformly distributed on [-1,1]. In particular
|d|=|E(e_1e_2 G(t))|<=1/2.
Moreover G has Fourier support in the odd multiples
of lambda, and is sign-reversed by the translation
t -> t+1/2^{v_2(lambda)+1}, where v_2 is the valuation
of the absolute value of a nonzero integer.
The sign r(m_j t+c_j) has odd-multiple support, so
E(e_j G) can be nonzero only if v_2(m_j)=v_2(lambda).
The same odd-support argument gives c=0 if the
valuations of m_1,m_2 differ.

It follows that:
* If neither of the triple moments is permitted by
  these valuation tests (or G=0), then a=b=0.
* If exactly one is permitted, c=0 and at most one
  of a,b can be nonzero.
* If both are permitted, the translation displayed
  above flips e_1,e_2 and G simultaneously. Thus
  E(e_1e_2 G)=0, i.e. d=0.

These cover all phase choices, including accidental
vanishing of permitted moments.

### 5.2. The three support cases

If a=b=0, condition on e_3,e_4. The conditional
law of e_1,e_2 has density proportional to
1+(c+d e_3e_4)e_1e_2, so its first moments are zero.
The parallel group is supported in E and has
conditional mean zero. Convex Jensen on E removes
it. The remaining two signs are independent,
and the usual two-wave Jensen argument finishes.

If exactly one triple is permitted, c=0 and
(5) is a triple+quadruple law, with |a| or |b|
<=1/2 and |d|<=1/2. The TQ square argument of
Section 4 applies verbatim, with parallel H_i
allowed in that universal corner target.

It remains to handle d=0 when both triples are
permitted. Put u=a+b, v=a-b. Positivity and the
two triple bounds imply
$$
|u|+|v|\le1,\qquad |u|-1\le c\le 1-|v|.
$$
Indeed the sign choice e_1=e_2 gives |a+b|<=1+c,
whereas e_1=-e_2 gives |a-b|<=1-c.
Independent sign relabelings and swapping 1,2
permit u,v>=0 without changing c. In those
coordinates the outer polytope is
$$
u,v\ge0,\quad u+v\le1,\quad u-1\le c\le1-v.
$$
It is the convex hull of the upper and lower
graph endpoints over the three triangle vertices
(u,v)=(0,0),(1,0),(0,1). To verify this directly,
at fixed u,v first interpolate c between the
two affine graphs, and then use barycentric
coordinates in the triangle on each graph.
There are only six generating points.

At (0,0), c=+/-1, the parallel group is independent
of the other signs and has mean zero, hence Jensen.
At (1,0), c=1, we have e_1=e_2 almost surely.
Combine the pair into the rank-one matrix
H_1+H_2 and observe that the merged three-sign law
is 2^{-3}(1+e_1e_3e_4/2), a known laminate.
At (0,1), c=-1, the identical reasoning merges
H_1-H_2 and gives the pure triple law.
The two remaining endpoints have c=0 and
(a,b)=(1/2,1/2) or (1/2,-1/2).
They are D corners after relabeling/flipping signs.

All these laws have zero barycenter, so the stated
mixtures preserve Jensen. This closes the reduction
of the parallel case to D and TQ as well. No assumption
that the amplitudes are nonzero is needed.

Combining Sections 1–5 proves the two-corner sufficient
reduction of the ENTIRE four-wave problem. QED.

## 6. Exact actual-gradient controls and a bounded worklist

[The checker](../../research/audit/iwaniec_four_wave_cases_exact.py)
was executed with Python 3. It enumerated all 22 rank-two
mod-2 multisets, verified all six generating points of
the parallel polytope, and integrated two actual gradients
by clipping rational torus polygons. Output:

    normalized rank-two mod-2 multisets: 22 [((0, False), 9), ((0, True), 3), ((1, False), 6), ((1, True), 1), ((2, False), 3)]
    six parallel-pair generating points: exact masses and merged parity passed
    unit double triad: {(1, 2, 3): Fraction(-1, 2), (1, 2, 4): Fraction(1, 2)}
    triple + quadruple: {(1, 2, 3): Fraction(-1, 2), (1, 2, 3, 4): Fraction(1, 4)}
    two exact actual-gradient controls passed; both exceed old total-parity budget

The controls use:
* k=(e_1,e_2,e_1+e_2,e_1-e_2) with phases
  (0,0,1/4,1/4), attaining a D corner exactly.
* k=(e_1,e_2,e_1+e_2,2(e_1-e_2)) with the same
  phases, attaining |C_123|=1/2, |C_1234|=1/4.
  In particular neither the old l1<=1/2 rule
  nor conditioning naively on e_4 then using
  the pure-triple theorem is sufficient.

**Next bounded tasks (not infinite frequency cases):**

- [ ] D: universal Jensen at the double-triple corner.
- [ ] TQ: universal Jensen at the triple/quadruple corner.
- [ ] Audit and formalize the resulting N=4 implication.
- [ ] Find an actual induction or global decomposition for all N.

For the first two tasks a computer-assisted approach can
work directly with H_i rank-one and fixed 16-atom weights.
For generic linearly independent H_i, set the quadratic
form Q(v)=det(sum_i v_i H_i) on R^4. It has zero diagonal
coefficients and split signature (2,2), and its null
directions are exactly the rank-one directions in matrix
coordinates. Thus D and TQ become two fixed cube-measure
Jensen tests for Q-null convex functions, with Q ranging
over this finite-dimensional semialgebraic family.
Singular amplitude tuples can be reached by continuity
of rank-one convex F from generic tuples: parameterize each
H_i=a_i⊗b_i and note linear independence is the complement
of a nonzero determinant polynomial in the 16 factor
coordinates. No uniform finite bound on lamination tree
depth or number of auxiliary support points follows
from this observation; a bounded certificate search is
not an exhaustive decision procedure without that bound.

If an outer corner is disproved, first verify the right
directions and actual frequency/phase realization before
claiming a four-wave counterexample. The TQ square
is deliberately an outer bound, and even D with arbitrary
rank-one H_i is stronger than the particular actual
unit-triad realization checked above.

This is a finite **sufficient gate list for N=4**, not
a reduction of unrestricted Morrey to N<=4. Do not
substitute closure of two model inequalities for
an all-N theorem.
