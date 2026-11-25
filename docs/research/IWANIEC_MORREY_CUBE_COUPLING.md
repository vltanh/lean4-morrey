# An all-N composition theorem: random rank-one cubes and overlapping resonances

23 November 2026. Hand proofs and executed exact arithmetic controls.
No isotropy, homogeneity, nonnegativity, smoothness or growth hypothesis
on F. No independent human review, Lean certification, novelty clearance
or unrestricted Morrey proof is claimed.

Deep input: the planar three-wave theorem of Sebestyén and Székelyhidi,
[Laminates Supported on Cubes (2017)](https://doi.org/10.68381/jca24070),
in the arbitrary rank-one pure-parity form proved in
[the earlier note, Theorem B](IWANIEC_MORREY_FOUR_WAVE_PARITY_THEOREM.md):
on any rank-one cube, the uniform law perturbed by a single parity of
order at least three with coefficient of magnitude at most 1/2 is
a laminate. Independent rank-one splits on its complementary coordinates
are allowed. The all-N sawtooth characterization of Morrey is discussed
in [Guerra–Teixeira da Costa (2022)](https://doi.org/10.4171/RMI/1286).

## 1. General rank-one product perturbation theorem

Let (T_i,mu_i), i=1,...,N, be standard probability spaces, and
B_i:T_i -> E_i bounded measurable maps, where E_i is a linear subspace
of R^{2x2} all of whose elements have rank at most one. Each E_i can be
a whole column or row rank-one subspace; the B_i need not be scalar
multiples of one matrix. Write mu=product_i mu_i. Suppose nu has a
density p relative to mu, with EVERY one- and two-coordinate marginal
equal to its corresponding product marginal. Write
$$
g_S(t_S)=\int (p(t)-1)\,d\mu_{S^c}(t_{S^c}),\qquad g_\varnothing=0 .
$$
In particular g_S=0 if |S|≤2. For N≥3 put
$$
C_N=\sum_{s=3}^N {N\choose s}2^s = 3^N-2N^2-1.
$$

**Theorem A.** If
$$
\|p-1\|_{L^\infty(\mu)} \le {1\over 2 C_N},
\tag{1}
$$
then for EVERY finite-valued planar rank-one convex F and every base A,
$$
\int F\left(A+\sum_i B_i(t_i)\right)\,d\nu(t)
\ \ge\
F\left(A+\sum_i\int B_i\,d\mu_i\right).
\tag{2}
$$
More generally, it suffices that the random-cube budget (3) below
hold almost surely, with no bound required on the full density.

**Proof.** Independently in all coordinates draw two samples
t_i^+, t_i^- from mu_i, independent also within each pair. For a
fixed collection of these pairs and a subset S with |S|≥3 define
$$
\rho_S = \sum_{e\in\{-1,1\}^S}
 \left(\prod_{i\in S} e_i\right)
 g_S((t_i^{e_i})_{i\in S}).
$$
Since |g_S|≤||p-1||_infty, hypothesis (1) implies, almost surely,
$$
\sum_{|S|\ge3}|\rho_S|\le 1/2. \tag{3}
$$
Consider the following probability law on the full local sign cube:
$$
w(e)=2^{-N}\left(1+\sum_{|S|\ge3}\rho_S\prod_{i\in S}e_i\right).
\tag{4}
$$
It is the convex mixture of the uniform cube law with weight
1-2 sum_S |rho_S|, and one pure-S parity law at coefficient
sgn(rho_S)/2 with weight 2|rho_S| for every nonzero coefficient.
The matrix at e is
$$
A+\sum_i B_i(t_i^{e_i}) =
A+\sum_i M_i+\sum_i e_i H_i,\qquad
M_i=(B_i(t_i^+)+B_i(t_i^-))/2,\quad
H_i=(B_i(t_i^+)-B_i(t_i^-))/2.
$$
Every H_i has rank at most one. Each component of (4) is a
laminate by the pure-parity theorem and independent complementary
splits. All have the SAME barycenter A+sum_i M_i. Thus the
local law satisfies rank-one Jensen at that barycenter.

We must prove **exact reconstruction of the original joint law**,
rather than merely bounding a test function on another law.
Take a uniform independent cube sign e and condition on its
selected tuple t=(t_i^{e_i})_i. Before reweighting by 2^N w(e),
this tuple has the product law mu. For every S, the unselected
samples are independent with their respective mu_i laws.
A term in rho_S indexed by a sign vector that agrees with e
on U⊆S and disagrees on S\U has conditional expectation
g_U(t_U), by integrating out the other coordinates.
Its sign after multiplication by product_{i in S} e_i is
(-1)^{|S|-|U|}. Consequently
$$
\mathbb E\left[\rho_S\prod_{i\in S}e_i\,\middle|\,t,e\right]
 = h_S(t_S)
 :=\sum_{U\subseteq S}(-1)^{|S|-|U|}g_U(t_U).
$$
By finite subset Möbius inversion, sum_{S⊆[N]} h_S=g_[N]=p-1;
all the |S|≤2 terms vanish. The conditional mean of the
reweighting factor is therefore exactly p(t).
This proves that the mixture over sampled pairs of (4) has
the selected-coordinate law nu, and not just its low moments.

Integrating local Jensen gives the right side
E F(A+sum_i M_i). The M_i are independent, each lies in E_i,
and E M_i=integral B_i dmu_i. Successive ordinary convex Jensen
inequalities along the E_i give (2). This last step is
essential because the local cube barycenters vary. All
integrals are finite by local boundedness/continuity of
finite-valued rank-one convex functions and boundedness of B_i.
QED.

The result is stable under arbitrary translations of the B_i.
No geometric relation among their E_i is required, and any
number of overlapping interactions h_S are permitted.
The sharper sufficient hypothesis is (3), or
sum_{|S|≥3} 2^{|S|}||g_S||_infty≤1/2. This can be much
better than the uniform full-density condition. If the
reference variables are already fair signs, fixed opposite
pairs instead of iid pairs recover the earlier Walsh budget.
The method does not show that all pairwise-independent
densities satisfy (3).

**Conditional composition.** Let an arbitrary bounded tail
matrix T be retained. If conditional on T=t the block has
a density p_t relative to a fixed product reference mu with
the same one/two-coordinate marginals and satisfies (1)
or (3) almost surely in t, then (2) holds conditionally
at A+t. In particular a zero-mean block can be removed
without changing the tail distribution, even when the
block's high-order correlations depend on the entire tail.
This is an exact removal inequality; no comparison of
unconditional low-order marginal distributions is used.

## 2. Application: arbitrary-length overlapping nonparallel circuits
##    at comparable frequency magnitudes

**Theorem B.** For every integer m≥1 there is an explicit family of
m+2 pairwise nonparallel integer frequencies with:

* all frequency lengths between D and 5D for an odd integer D;
* every frequency belonging to a minimal odd-resonant rank-two
  circuit, and m triple circuits sharing the same two core waves;
* no possible elimination by the previous parallel-block rule,
  and no dyadic frequency peeling (all frequencies nonzero mod 2
  in the generated lattice);
* Jensen for all finite-valued planar rank-one convex F, all
  amplitudes and phases, even with **arbitrary bounded vector-valued
  ridge derivatives in the two core directions**.

This is an actual periodic-gradient theorem, not just a theorem
on abstract sign arrays.

**Construction.** Put N=m+2, delta=1/(2C_N) and
eta=delta/2^m. Choose positive odd integers L_i recursively:
L_1=1, and for i≥2,
$$
J_{i-1}:=1+2\sum_{j<i}L_j,\qquad L_i>4J_{i-1}/\eta .
$$
Choose an odd D>2J_m/eta, and define the core frequencies
q_1=(D,0), q_2=(0,D), and the m additional frequencies
$$
k_i=(2D+L_i,\ 2D+1).
\tag{5}
$$
The original core phases t_1=q_1·x, t_2=q_2·x mod 1
are independent uniform circle variables. Write
epsilon_i=r(k_i·x+c_i), where r is the half-positive,
half-negative periodic sign function, with half-open intervals.
All pairs of the N phase characters are independent Haar
variables because the corresponding two integer rows
have nonzero determinant and define an onto map of T².
The two core phases and all sign variables are therefore
pairwise independent with the required marginal laws.

**Uniform conditional independence approximation.**
For any real phases theta_i, consider the m signs
r(L_i t+theta_i) for t uniform on T. A pattern for the
first i-1 signs is a union of at most J_{i-1} half-open
intervals in [0,1). For any interval I, any shift and
either sign value, the difference between the measure
of the corresponding portion of I for the ith sign and
|I|/2 is at most 1/L_i: integrate the centered periodic
indicator, whose primitive oscillation is at most 1/L_i.
Thus if E_i is the largest absolute deviation of an i-sign
pattern probability from 2^{-i}, uniformly over phases,
$$
E_1=0,\qquad E_i\le E_{i-1}/2+J_{i-1}/L_i.
$$
Our recursive choices give E_m≤eta/2. This holds uniformly
even for phases at discontinuities.

Replacing continuous t by uniform j/D, 0≤j<D, changes a
pattern probability by at most J_m/D: on any half-open
interval the discrepancy between its length and normalized
grid count is at most 1/D. Hence on every such D-grid,
for arbitrary phases, every m-sign pattern probability
differs from 2^{-m} by at most eta.

Condition now on (t_1,t_2)=(u,v). The conditional law of x
is uniform on the D² points ((u+j)/D,(v+l)/D).
For each fixed l, the conditional k_i phase, modulo 1,
is L_i j/D plus a phase depending on u,v,l,c_i; the added
2D frequency coordinates in (5) contribute only integers
to the j,l parts. The just-proved uniform grid estimate
therefore applies for every l, and averaging l preserves it.
Consequently the joint law of the N variables relative
to the product of two uniform circle laws and m fair-sign
laws has density
$$
p(u,v,e)=2^m\Pr((\epsilon_i)_i=e\mid t_1=u,t_2=v),
\qquad |p-1|\le 2^m\eta=\delta .
$$
Theorem A proves the desired Jensen inequality for
$$
B_1(t_1)+B_2(t_2)+\sum_i H_i\epsilon_i,
$$
with B_j(t)=b_j(t)⊗q_j, arbitrary bounded b_j of zero mean,
and H_i=a_i⊗k_i. These are actual periodic gradients:
integrate b_j in its circle variable to obtain the
periodic Lipschitz ridge primitives and similarly for r.
Constant means, if desired, belong in the base A.

**Overlap and scale verification.** Each L_i<D. The
frequency lengths in (5) are between D and 5D; the core
lengths equal D. All pair determinants are nonzero.
For every i,
$$
(2D+L_i)q_1+(2D+1)q_2-D k_i=0
$$
is a primitive all-odd relation (gcd(D,2D+1)=1).
Every pair in this triple is nonparallel, so it is
a minimal odd-resonant circuit. For m≥2 the m circuits
overlap in both core frequencies. With sawtooths also
in the core, every triple moment is a nonzero function
of phases, by the phase Fourier coefficient criterion
in the preceding parity note. The two core phases can
be fixed, e.g. to zero, and each extra phase chosen
separately to make its triple moment nonzero (with
primitive relation, the moment is a nonzero multiple
of the standard triad correlation as a function of
the relation phase). Hence all m actual triple correlations
can be nonzero simultaneously. The result is not simply
independence of isolated resonant components.

The earlier [minimal-resonance theorem](IWANIEC_MORREY_MINIMAL_RESONANCE.md),
Theorem C, proves that no member of any such rank-two
circuit is removable by parallel-block peeling. Moreover,
the core pair has odd determinant D², so the generated
lattice has odd index in ambient Z². All frequencies in
(5) and the core have nonzero reductions mod 2 in that
lattice. In particular none can belong to an even multiple
of the generated lattice, as required for a dyadically
divisible tail. This construction is not a separated
dyadic block theorem.

The proof establishes the family for every m, not by
a bounded-N computation. The necessary D from this
construction is enormous and correlations are weak,
even though the actual frequency lengths are comparable.
No claim is made that all comparable-magnitude
frequency tuples have this near-product property.

## 3. Stronger three-ridge waveform bridge for nonunit winding

There is also an exact nonperturbative consequence for
actual three-direction fields, addressing part of the
previously retracted arbitrary-three-ridge attempt.

Let q_1,q_2,q_3 be pairwise nonparallel integer vectors and
let a q_1+b q_2+m q_3=0 be their primitive integer relation,
with m>0 and a,b nonzero. Define t_j=q_j·x modulo 1.
The image of T² in T³ under the phase map is exactly the
kernel of (a,b,m): it is a connected compact subgroup of
dimension two in that connected two-dimensional kernel
(the coefficients are primitive). Hence conditional on
t_1=u,t_2=v, the t_3 law is uniform on the m roots of
m t_3=-au-bv mod 1. For any fixed phase c, the conditional
expectation of the sign r(t_3+c) is zero for m even, and
for m odd is
$$
m^{-1}r(-au-bv+mc).
\tag{6}
$$
Indeed the evenly spaced m points in a half-open half-circle
number exactly m/2 for m even and (m±1)/2 for m odd, with
the latter sign determined by the indicated residual phase.

**Theorem C.** If m≥2, Jensen holds for
$$
B_1(t_1)+B_2(t_2)+H_3r(t_3+c)
$$
with arbitrary bounded rank-one-valued ridge derivatives
B_j(t)=b_j(t)⊗q_j, arbitrary amplitude H_3=a_3⊗q_3,
and every F and base. For even m the sign is independent
of the two phases, and ordinary successive rank-one Jensen
applies. For odd m≥3 use the following explicit
antithetic rather than iid pairs.

Draw u,v independently uniformly, use their paired
alternatives u+1/(2a), v+1/(2b) modulo 1, and choose the
four pair selections independently with equal weights.
Each shift reverses the sign on the right side of (6).
At each pair cube, the actual conditional sign distribution
for the third wave is therefore precisely the local
three-parity law with coefficient
rho=m^{-1}r(-au-bv+mc), with |rho|≤1/3.
Its rank-one directions are the half-differences of
the two arbitrary profile values and H_3. The local
law is a laminate by the published three-wave input.
Averaging these cubes reconstructs the original law
exactly, since the selected phases are independent
uniform and the conditional law of the sign is (6).
The two varying midpoint matrices are independent
and in their rank-one subspaces; Jensen on those
subspaces completes the argument. This handles
unbounded numbers of harmonics or sawtooths in
the first two directions, not just three literal waves.

**Further waveform corollary.** Let the third derivative
instead be an arbitrary bounded step profile, constant
on a finite partition of its phase circle into half-open
intervals of lengths at least ell>0. The two other profiles
are arbitrary bounded ones as above. If m ell≥16, then
Jensen holds for this whole field. In fact, condition on
the first two phases; the count of the m equally spaced
roots in each interval differs from m times its length
by at most one. The joint density of (t_1,t_2,third interval
label) relative to the product of its marginals therefore
differs from one by at most 1/(m ell). All pairs of variables
are independent since all pairs of phase characters are
independent. Apply Theorem A for N=3, for which C_3=8.
The interval profile need not be a sawtooth.

This does NOT establish the unrestricted arbitrary
three-ridge waveform theorem. The unit-winding case
m=1 in Theorem C is not covered, nor are unrestricted
third profiles for fixed m in the step-profile corollary.
Fine partition lengths tend to zero, violating the
fixed-m bound. No limiting argument removing this
condition is asserted.

## 4. Verification and stop rule

The checker
[research/audit/iwaniec_cube_coupling_exact.py](../../research/audit/iwaniec_cube_coupling_exact.py)
was actually run with Python 3. Its output:

    nonbinary nonuniform four-coordinate density: exact reconstruction, local parity budget, all pair marginals passed
    three exact phase controls: interval/grid discrepancy and comparable-frequency residue lift passed
    parameter inequalities verified through 102 variables (exact integer arithmetic)

The first check uses unequal nonbinary coordinate marginal
laws and four simultaneous overlapping higher-order interaction
terms. It independently reconstructs every probability by
summing all randomly sampled pair cubes and all selections.
The second uses rational interval endpoints and exact grid
counts, including the frequency residue lift. The third
checks only the arithmetic parameter inequalities, not all
sign probabilities on the huge grids; the uniform discrepancy
proof supplies the latter.

**Remaining unrestricted gate:** Theorem A is a genuine
composition principle and Theorem B proves an all-N actual
overlapping-circuit family at comparable frequency lengths.
Nevertheless the small-dependence threshold can be very
restrictive and decays exponentially in N. Arbitrary
strongly correlated sign fields need not lie in this
near-product neighborhood. To close Morrey one needs
a global, gap-preserving reduction to admissible conditional
cube decompositions, or a new argument that handles strong
dependencies directly. Do not claim pairwise independence
or separate laminate marginals imply (2); the parity bound
is a real hypothesis. No bounded exhaustive classification,
general four-wave closure or solution of unrestricted P2
is claimed.
