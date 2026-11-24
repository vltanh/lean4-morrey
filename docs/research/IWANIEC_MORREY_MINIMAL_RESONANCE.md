# Minimal odd-resonance circuits: bounded classification and exact global peeling

23 November 2026. **Hand proofs**, with a locally executed exact arithmetic
regression. These are statements for arbitrary finite wave counts, all
phases and amplitudes, and every finite-valued planar rank-one convex
integrand. No independent human review, Lean certification, novelty
clearance or proof of unrestricted Morrey is claimed.

The only deep laminate input is the published planar three-wave theorem,
Sebestyén–Székelyhidi, [Laminates Supported on Cubes (2017)](https://doi.org/10.68381/jca24070),
in the pure-parity form established in
[the four-wave note, Theorem B](IWANIEC_MORREY_FOUR_WAVE_PARITY_THEOREM.md).
The arithmetic peeling rule used below is Theorem A of
[the conditional dyadic note](IWANIEC_MORREY_DYADIC_LAMINATION.md).
The all-wave target is the one in
[Guerra–Teixeira da Costa (2022)](https://doi.org/10.4171/RMI/1286).

## 1. Exact bounded classification of minimal resonance supports

Let k_1,...,k_N be arbitrary nonzero vectors in Z² (repetitions allowed).
For a nonempty index set S write L_S=sum_{i in S} Z k_i. Call S
odd-resonant when there exist odd signed integers n_i with
sum_{i in S} n_i k_i=0. This is precisely the Fourier support condition
for its Walsh moment to be not identically zero as a function of all
phases (four-wave note, Theorem A). Equivalently,
$$
S\text{ odd-resonant}\quad\Longleftrightarrow\quad
\sum_{i\in S} k_i\in 2L_S. \tag{1}
$$
Indeed writing each n_i=1+2m_i proves both implications.

A *circuit* in this note is an inclusion-minimal nonempty odd-resonant
set. This terminology is only shorthand; no matroid circuit axiom
is assumed.

**Theorem A. Every odd-resonant set contains a circuit of size 2, 3
or 4. The bound 4 is sharp.** More precisely:

- A size-two circuit consists of parallel frequencies with odd
  coefficients relative to the primitive generator of their joint lattice.
- A size-three circuit has rank two; its three vectors occupy the three
  distinct nonzero classes of L_S/2L_S.
- A size-four circuit has rank two; its four vectors occupy two distinct
  nonzero classes of L_S/2L_S, twice in each, and the four directions
  are pairwise nonparallel.

**Proof.** Normalize L_S by choosing an integral basis of this lattice,
not necessarily a basis of the ambient Z². In these coordinates the
vectors generate Z^r with r=1 or 2. Their classes modulo 2 generate
(F_2)^r. Equation (1) says their sum is zero modulo 2.

We use repeatedly the following fact: if a subcollection U generates
the full mod-2 space of L_S, then its subgroup L_U has odd index in
L_S. In rank one this is the gcd of its coefficients; in rank two
some pair determinant is odd, so the index (gcd of the pair
determinants) is odd. Consequently, if sum_{i in U} k_i is in 2 L_S,
it is in 2 L_U: multiplication by 2 on the finite odd-order quotient
L_S/L_U is invertible. By (1), U is odd-resonant.

For rank one, the number of nonzero mod-2 classes is positive and even,
so select two odd vectors. They generate the mod-2 space and their
sum is zero there. They give the asserted pair.

For rank two denote the numbers of occurrences of the three
nonzero classes e_1,e_2,e_1+e_2 by n_1,n_2,n_3. At least two
classes occur, and
n_1 = n_2 = n_3 mod 2.
If they are odd, take one vector from each class; this triple
generates the mod-2 space and its sum is zero. Otherwise they
are all even; take two vectors from each of any two classes that
occur. This quadruple again generates the mod-2 space and has
sum zero. This proves the bounded assertion; any circuit must itself
be one of the selected patterns.

For the size-three case all pair determinants are odd in the
normalized coordinates, hence no parallel pair is possible.
For size four, cross-class pairs are nonparallel (their mod-2
determinants are nonzero). If a within-class pair were parallel,
write them as m p, n p for a primitive vector p in the normalized
lattice. Their nonzero mod-2 class implies m,n odd, hence the pair
itself has an odd relation. This contradicts minimality. Conversely,
four pairwise nonparallel vectors with the displayed 2+2 class
pattern have zero sum modulo 2, and none of their proper subsets
has an odd relation: singleton/pair by nonparallelity, triple by
nonzero mod-2 sum. The triple and pair converse statements are
equally immediate. QED.

The earlier (1,0),(0,1),(1,2),(2,1) example is a size-four
circuit, so a size-three bound would be false.

**Algorithmic consequence.** Detecting whether ANY nonconstant
Walsh moment can be nonzero at some phases needs no enumeration
of 2^N supports: testing all 2-, 3-, and 4-subsets by (1) suffices.
For a prescribed larger support, (1) is still the exact criterion.
The rank-two membership check for w in L_S is
gcd of pair determinants divides det(k_i,w) for every i, and in
rank one it is the elementary scalar gcd test. All arithmetic
can be exact, with no bound on the frequency integers.

## 2. Every minimal resonant block is a laminate (full four-circuit theorem)

**Theorem B.** For EVERY circuit S of any actual planar integer
frequency list, the sign-gradient law of that block alone is a
laminate for all phases and amplitudes.

The two-wave case has parallel right directions, so convex Jensen
on the common rank-one subspace applies. The three-wave case follows
from the published planar three-wave theorem. It remains to prove
the assertion for ALL four-circuits, including non-unimodular
frequency choices not covered by the previous odd-diagonal/even-mixed
integer-coefficient family.

In normalized coordinates order a four-circuit so that
q_1,q_3 occupy the same nonzero mod-2 class, and q_2,q_4
the other. Put D=det(q_1,q_2), an odd nonzero integer. Write
$$
Dq_3=a q_1+b q_2,\qquad Dq_4=c q_1+d q_2,
$$
where a,d are odd, b,c are even, and b,c are nonzero by
nonparallelity. This normalization changes the frequencies for
the correlation calculation only: odd integer relations are
preserved by the injective lattice-coordinate map. The amplitude
matrices H_i=a_i⊗k_i remain arbitrary rank-one matrices in the
pure-parity lemma.

All proper nonempty Walsh moments are zero for all phases by
circuit minimality. Thus the sign law is 2^{-4}(1+rho e_1e_2e_3e_4).
It suffices to show |rho|≤1/2 uniformly in phases.

The Fourier coefficients of rho as a function of the four phases
are zero except at odd tuples (n_1,n_2,m,n) with
sum n_i q_i=0, where their magnitudes are
16/(pi^4 |n_1 n_2 m n|). These relations obey
$$
D n_1=-a m-c n,\qquad D n_2=-b m-d n.
$$
Let R denote the allowed odd tuples. For each fixed odd m,
the map n ↦ n_1 is injective since c≠0, and n_1 belongs
to a fixed odd class modulo 4: D is invertible mod 4 and
c n=c mod 4 for odd n. Hence
$$
\sum_R \frac1{m^2n_1^2}
\le \frac{\pi^2}{8}\sum_{m\text{ odd}}\frac1{m^2}
=\frac{\pi^4}{32}.
$$
The same argument for fixed odd n and nonzero even b gives
sum_R 1/(n² n_2²) ≤ pi⁴/32.
Cauchy–Schwarz therefore gives an absolutely summable Fourier
series with
$$
\frac{16}{\pi^4}\sum_R\frac1{|m n n_1 n_2|}
\le\frac12.
$$
As in the earlier four-wave proof, the moment is continuous in
the phases by L¹ continuity of translations of the sign
function. Fourier uniqueness identifies it everywhere with this
absolutely convergent series. Therefore |rho|≤1/2 for all phases.
The pure-parity N=4 lemma of the preceding four-wave note
(deduced from the published planar N=3 theorem) proves the
laminate Jensen inequality. QED.

This closes ALL phase-uniform pure four-parity configurations,
rather than just those containing a unimodular coordinate pair
for the lattice. It does NOT say that a circuit stays a
laminate after conditioning on the signs of other waves.
That stronger inference is unjustified and is the key remaining
issue.

## 3. Exact all-N characterization of parallel-block lattice peeling

The preceding dyadic note proves the following exact removal
rule. Given a remaining frequency tuple, let B be a block of
parallel frequencies and T its complement. If every k_i in B
has even finite or infinite order modulo L_T, then
$$
\int F(A+V_B+V_T)\ge \int F(A+V_T), \tag{2}
$$
where V_I is the sum of the sign waves in I. This is Jensen
over the compact annihilator of L_T, since the conditional
mean of each removed sign is zero and the removed matrices
lie in a single rank-one subspace. The whole rule is independent
of the integrand and of phases and amplitudes.

**Theorem C.** The following properties of an arbitrary finite
integer frequency tuple are equivalent:

1. There is NO circuit of rank two (equivalently no minimal
   nonparallel odd-resonant triple or quadruple).
2. The tuple can be completely eliminated by the parallel-block
   rule (2).
3. The following deterministic algorithm reaches rank at most one,
   no matter which permitted parallel class is chosen:
   recompute the lattice L generated by the remaining tuple at
   each iteration; if rank L=2, classify the remaining vectors
   in L/2L. If exactly two nonzero classes occur and one of them
   consists entirely of parallel frequencies, remove ALL waves
   of that class and continue. Otherwise stop.

Rank zero is empty, and rank one is removed by convex Jensen
on the common right-direction rank-one subspace (or by (2)
with empty tail). In particular, **every tuple satisfying (1)
generates a laminate for every base A, every finite-valued
planar rank-one convex F, all phases and arbitrary amplitudes,
with absolutely no bound on the number of waves**. This
covers some tuples with arbitrarily many actual resonant
subsets, even though every minimal resonance is parallel.

**Proof of sufficiency and the algorithm.** At a rank-two stage,
the nonzero mod-2 classes generate the full two-dimensional
space, so there are two or three of them. If three occur,
take a representative of each. By the proof of Theorem A,
this triple admits an odd relation and is a rank-two circuit
(no parallel pairs). Hence under (1) only two classes occur.

If neither class consists entirely of parallel directions,
take a nonparallel pair from each. The chosen four vectors
generate the full mod-2 space and their sum is zero, so
they admit an odd relation by the odd-index argument.
Cross-class pairs are nonparallel, and no triple has zero
sum in L/2L. Thus this is a rank-two circuit, again
contradicting (1). There is therefore a parallel class B
which the algorithm may choose.

For each k_i in B, its nonzero mod-2 class lies outside
the span of the remaining tail classes. If d k_i belonged
to L_T for an odd positive integer d, reducing modulo
2L would contradict this. Its order modulo L_T is thus
even or infinite, exactly as required by (2). Deletion
preserves (1), which is inherited by subsets (circuit
minimality is defined in each subset's own lattice).
Induction finishes the proof. The same reasoning works
for every permitted class choice.

**Proof of necessity (an exact obstruction, not a Morrey
counterexample).** Suppose a rank-two circuit S is present.
Consider the first step in any putative parallel-block peeling
sequence that removes a member of S. At this step all members
of S are still present. Write J=S∩B, a nonempty set, and
choose an integer primitive direction p for B; write k_i=m_i p
for i in B, with m_i nonzero signed integers. Let
L_T∩Zp=d Zp with d≥0. If d=0, each removed wave has infinite
order. If d>0, the order of m_i p modulo L_T is d/gcd(d,m_i),
so the removal hypothesis says v_2(m_i)<v_2(d).

The odd relation of the circuit implies
$$
\left(\sum_{i\in J} n_i m_i\right)p \in L_T,
\qquad n_i\text{ odd}.
$$
If there were a unique minimum of the valuations v_2(m_i)
over J, the sum would have exactly that finite valuation.
For d=0 this contradicts its being zero, and for d>0 it
contradicts divisibility by d. Thus at least two indices
of J share the same minimal valuation. For these two
parallel frequencies the integer coefficients after dividing
by their common gcd are both odd, giving an odd-resonant
pair. This is a proper subset of the rank-two circuit S,
contradicting its minimality. So no permitted step can
remove any member of S. Complete elimination is impossible.
QED.

**Precise interpretation:** Theorem C gives a necessary and
sufficient frequency-only condition for THIS parallel-block
peeling strategy, not a necessary condition for a laminate.
For example, the four-circuit in Theorem B is irreducible
under this strategy but is nevertheless a laminate.

## 4. Some overlapping circuits, without frequency restrictions

An additional direct all-N sufficient criterion follows from
the pure-parity lemma. Suppose all pairwise Walsh moments
vanish (e.g. distinct nonparallel right directions), and let
C_S be the actual Walsh coefficients for |S|≥3. If
$$
\sum_{|S|\ge3}|C_S|\le 1/2, \tag{3}
$$
then the matrix law is a laminate for arbitrary rank-one H_i.
Indeed Walsh inversion expresses the whole law as a convex
mixture of the uniform sign law with weight
1-2 sum_S |C_S|, and one pure-S parity law
2^{-N}(1+sgn(C_S) prod_{i in S}e_i/2)
with weight 2|C_S| for each nonzero coefficient. Each latter
law is a laminate by the pure-parity lemma on S and independent
rank-one splits for its complement, all with the same zero
barycenter. Thus arbitrary overlapping resonance supports
are allowed under (3); this is a sufficient inequality, not
a claim that actual fields always satisfy it.

For example, consider four pairwise nonparallel frequencies
whose normalized mod-2 pattern has multiplicities 2,1,1
among the three nonzero classes. There are at most two
nonzero Walsh moments, both triples sharing the singleton
classes; no fourth-order resonance is possible because the
total mod-2 sum is nonzero. For a pairwise nonparallel
triple with primitive signed relation coefficients alpha_i,
the continuum calculation in the dyadic note, Section 4,
gives |C_S|≤1/(2|alpha_1 alpha_2 alpha_3|) for all-odd
coefficients and zero otherwise. If both triple relations
are nonunit, the sum of their bounds is ≤1/3. Hence this
entire doubly resonant family is a laminate, with neither
a prescribed integer frequency geometry nor a prescribed
phase. The same argument covers every phase of any such
configuration satisfying the actual bound (3), including
some unit-triad cases. It does not cover the extreme case
of two unit triads with both correlations of size 1/2.

## 5. Verification and the remaining global obstruction

The exact regression checker
[research/audit/iwaniec_minimal_resonance_exact.py](../../research/audit/iwaniec_minimal_resonance_exact.py)
was actually executed with Python 3 in the working container.
Output:
    Sharp 4-circuit, parallel peeling, 150 small exact classifications, 63-wave irreducible family: passed

The 150 deterministic small controls check the complete list
of inclusion-minimal odd-resonant subsets via integer gcd
lattice membership and compare the presence of a rank-two
circuit with the greedy algorithm. They are regression
checks, not an exhaustive proof for arbitrary N. The hand
arguments above supply those quantifiers.

**No finite bound on the size of an irreducible cluster
has been proved; indeed such a bound is false for the
parallel-block strategy.** For arbitrary J≥1 take
$$
(1,0),\ (0,1),\ (1,1),\ (1,2),\ (1,4),\ldots,(1,2J).
$$
These are all distinct directions. Each of the (1,2j)
waves, together with (0,1),(1,1), forms a rank-two
triple circuit (distinct nonzero mod-2 classes, odd-index
argument). All original waves also lie in such circuits.
By Theorem C's necessity proof none can be removed.
The cluster size J+3 is unbounded. This is only an
obstruction to this pruning rule, not a negative
gradient Jensen witness.

Theorem B shows that **all minimal odd-resonant blocks**
are individually planar laminates. Theorem C completely
handles the all-N class without nonparallel minimal blocks.
Section 4 handles certain overlaps. The unbounded problem
has therefore been localized to interactions between
the bounded circuits, not to larger isolated minimal
resonances. Beware that a higher-order resonance need NOT
be a disjoint union of circuits: for example the triple
(1,0),(0,1),(1,1) plus the even wave (4,0) has a
four-way odd relation despite the last wave not belonging
to any minimal circuit in this tuple.

**Next unrestricted gate:** prove a conditional
laminate decomposition for overlapping circuit clusters
or find a genuinely negative compatible-gradient witness.
Do NOT infer that independent Jensen for each circuit
implies Jensen for their union, or that checking all
N≤4 waves suffices for Morrey. A new coupling theorem
is required, and the unrestricted P2 gate remains open.
