# Counterexample-first pivot: degree-four angular-polynomial LP probe

24 November 2026. The positive stress construction has not closed G1.
We reverse direction and search for a genuine planar counterexample,
not another signed-stress obstruction. No validated counterexample
was obtained in this turn.

## Search class and actual witnesses

For p=2, 3/2, 3, use F(X)=|X|^p P(X/|X|), F(0)=0,
where P is a polynomial of total degree at most four on S^3.
The 55 monomials with fourth exponent at most one form the basis
used (eliminate x4^2 using the unit sphere relation). Odd degrees
are included: the energies need not be even or isotropic.
Coefficient bounds [-1,1] fix an arbitrary search scale.
For a monomial x^alpha and q=p-|alpha|, its homogeneous extension
is |X|^q X^alpha. At a unit u its rank-one directional Hessian is

    D²P(u)[h,h] + 2q(u:h) DP(u):h
       + [q |h|²+q(q-2)(u:h)²] P(u).

Use the formula term by term. The numerical implementation was
checked against central finite differences at 100 random pairs
for each exponent (maximum absolute discrepancy below 1.3e-7
with difference step 1e-4). This is a regression check, not a
global curvature certificate.

The nine fixed compatible laws came from periodic nodal values
on a 6x6 square grid, split along a common diagonal into 72
triangles. Three types of nodal field (random, six sine modes,
one dominant mode with five small additional modes) were paired
with three unit-Frobenius diagonal bases. The last type had
gradient RMS 1/4; the others RMS 1. Seed 20261124.
The means and determinant moment identities were checked
numerically to 1e-12. The energy integral for these piecewise
affine maps is the arithmetic mean over the triangles, with
floating-point energy evaluation.

For each fixed field optimize P by LP with 3600 random
(unit matrix, unit rank-one direction) Hessian constraints,
then use 24000 held-out probes to add up to 100 most violated
constraints per round, at most five rounds. Finite sampling
only relaxes the RC constraint and cannot certify RC.

## Actual completed output

The broad run completed 23 of the intended 27 field/exponent
pairs before the execution timeout. It did not write the
end-of-run JSON. The displayed numerical output was:

| p | fields 0..8, final LP objectives |
| --- | --- |
| 2 | ~0, ~0, -0.0146983641, ~0, ~0, -0.0038368604, ~0, ~0, -0.0185659902 |
| 3/2 | 0, 0, -0.0088246060, 0, 0, -0.0026041552, 0, 0, -0.0120511373 |
| 3 | 0, 0, -0.0192166519, 0, 0, not completed, not completed, not completed, not completed |

All negative 3/2 candidates, and the degree-two field 5
candidate, failed the held-out rank-one tests. The degree-three
field 2 candidate passed that finite sample to numerical
tolerance but was not further certified or retained in this
turn. It is not a counterexample claim.

The two degree-two candidates for fields 2 and 8 looked
particularly deceptive: their held-out minimum Hessian was
about -4.23e-14 and -3.02e-14, respectively, despite their
negative objectives. Re-solving those two LPs with the same
seed reproduced the objectives. Testing unit directions
concentrated at A and the actual triangle gradient directions
found Hessian values -1.2663 and -1.0468. The candidates were
then refuted by EXACT rational unit matrix and rank-one
direction witnesses. The binary floating-point coefficients
are treated as exact rationals. The checked curvatures are
about -1.26702549843 and -1.04720081478. The standalone
checker below stores those exact coefficients and directions.
Thus both integrands are definitely NOT rank-one convex.
A further re-optimization with field-local samples was
attempted but timed out without a completed new result.

## Decision

The search remains worth considering, but do not count
sampled negative gaps as evidence for a negative resolution.
In particular a 24000-probe validation set can miss large
violations in the small angular region actually traversed
by a low-amplitude test field. Start with witness-local
curvature constraints, and certify the global homogeneous
Hessian by semialgebraic positivity (or a rigorous SOS
certificate), rather than indefinitely increasing random
probe counts. A true counterexample must use the same
globally RC F and a genuine compatible gradient with a
strict, certified negative energy gap. The p=2 origin gate
is already settled; nonzero bases and anisotropy are essential
for that exponent. No evidence here resolves planar Morrey
in either direction. No new Lean proof.
