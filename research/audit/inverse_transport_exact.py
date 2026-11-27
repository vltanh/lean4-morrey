#!/usr/bin/env python3
"""Exact inverse-coordinate algebra; no planar counterexample search."""

from fractions import Fraction
import sympy as s


I = s.eye(2)
J = s.Matrix([[0, -1], [1, 0]])


def cof(A):
    return s.Matrix([[A[1, 1], -A[1, 0]], [-A[0, 1], A[0, 0]]])


def ip(A, B):
    return s.trace(A.T * B)


def eq(A, B):
    difference = A - B
    if isinstance(difference, s.MatrixBase):
        difference = difference.applyfunc(s.cancel)
        assert difference == s.zeros(*difference.shape), difference
    else:
        assert s.cancel(difference) == 0, difference


x = s.symbols("x0:4")
X = s.Matrix(2, 2, x)
B = s.Matrix(2, 2, s.symbols("b0:4"))
p = s.Matrix(2, 2, s.symbols("p0:4"))
V = s.Matrix(2, 2, s.symbols("v0:4"))
t, f = s.symbols("t f")
Q = I + t * B * X
L = I + t * X * B
delta = Q.det()
N = X + t * X.det() * B.adjugate()

# Polynomial forms avoid spurious assumptions about symbolic denominators.
eq(cof(X), J.T * X * J)
eq(cof(X).T, X.adjugate())
eq(X * Q.adjugate(), N)
eq(L.det(), delta)
eq(delta * I - t * B * N, Q.adjugate())
eq(N * (delta * I - t * B * N).adjugate(), delta * X)
print("Symbolic cofactor, projective numerator, and inverse identities passed.")

# Differentiate the action in an arbitrary initial matrix direction.
T = f * I - X.T * p
p_num = L.T * (p * Q.T - t * f * B.T)
d_delta = t * ip(cof(Q), B * V)
eq(ip(p_num, L.adjugate() * V * Q.adjugate()),
   delta * (delta * ip(p, V) - f * d_delta))
eq(delta * f * I - Q.adjugate().T * X.T * p_num,
   delta * T * Q.T)
eq(cof(p_num) * Q, delta * (cof(p) - t * B.adjugate() * cof(T)))
eq(cof(T * Q.T) * Q, delta * cof(T))
print("Symbolic action chain rule and full-stress transport identities passed.")

# A non-RC polynomial is deliberately used: the identities do not presume
# the desired curvature sign. Check its actual rational coordinate pullback.
jet = (x[0] ** 2 + 2*x[1] ** 2 + 3*x[2] ** 2 + 4*x[3] ** 2)/2
jet += x[0]*x[3]/3 + x[0]*x[1]*x[2]/5
grad = s.Matrix(2, 2, [s.diff(jet, z) for z in x])
hess = s.hessian(jet, x)
h = s.symbols("h")
controls = [
    (s.Matrix([[1, 0], [0, 0]]), s.Matrix([[1, 2], [-1, 1]]),
     s.Matrix([1, 2])*s.Matrix([[2, -1]])),
    (s.Matrix([[0, -1], [1, 0]]), s.Matrix([[0, 1], [2, -1]]),
     s.Matrix([1, -1])*s.Matrix([[1, 3]])),
    (s.Matrix([[1, 1], [-1, 2]]), s.Matrix([[1, -1], [0, 1]]),
     s.Matrix([2, 1])*s.Matrix([[-1, 1]])),
]
tt = s.Rational(1, 20)
for B0, W0, R0 in controls:
    W = W0 + h * R0
    inv_q = I - tt * B0 * W
    old = W * inv_q.inv()
    transformed = inv_q.det() * jet.subs(dict(zip(x, list(old))),
                                        simultaneous=True)
    X0 = old.subs(h, 0)
    Q0 = I + tt * B0 * X0
    L0 = I + tt * X0 * B0
    direction = L0 * R0 * Q0
    vector = s.Matrix(list(direction))
    H0 = hess.subs(dict(zip(x, list(X0))))
    expected = (vector.T * H0 * vector)[0] / Q0.det()
    eq(s.diff(transformed, h, 2).subs(h, 0), expected)
    # Independently differentiate at fixed W with variable chart time.
    inv_q_t = I - t * B0 * W0
    old_t = W0 * inv_q_t.inv()
    action_t = inv_q_t.det() * jet.subs(dict(zip(x, list(old_t))),
                                       simultaneous=True)
    g0 = grad.subs(dict(zip(x, list(W0))))
    f0 = jet.subs(dict(zip(x, list(W0))))
    eq(s.diff(action_t, t).subs(t, 0),
       ip(g0, W0 * B0 * W0) - f0 * s.trace(B0 * W0))
print("3 exact polynomial-jet curvature and fixed-coordinate generator checks passed.")

# This is the algebra in the stationary identity, not proof of stationarity
# or attainment of a universal extremizer.
beta = s.symbols("beta")
eprime = ip(X, X) * s.trace(B * X) - 2 * ip(X, X * B * X)
k_f = ip(p, X * B * X) - f * s.trace(B * X)
k_H = ip(p + 2 * beta * X, X * B * X)
k_H -= (f + beta * ip(X, X)) * s.trace(B * X)
eq(k_H - k_f, -beta * eprime)
E0, M0, Ep, Mp, gap, a = s.symbols("E0 M0 Ep Mp gap a", nonzero=True)
quotient = gap / ((M0 + a * Mp) * (E0 + a * Ep))
eq(s.diff(quotient, a).subs(a, 0),
   -gap / (M0 * E0) * (Mp / M0 + Ep / E0))
print("Stationarity algebra and conditional normalized-quotient derivative passed.")

# An exact finite martingale control with e(X) != 0 and E e = 0:
# X is the four-atom diagonal gradient laminate; Y=(1 +/- 1/2)X.
# The target is a mixture of two scaled product laminates. This coupling
# is not optimal (the source itself has optimal cost zero).
matrices = [
    s.Matrix([[1, 2], [0, 0]]),
    s.Matrix([[1, 1], [-1, 2]]),
    J,
]
quarter = Fraction(1, 4)
half = s.Rational(1, 2)
for B0 in matrices:
    total_weight = Fraction(0)
    total_e = Fraction(0)
    total_first = s.zeros(2)
    for aa in (-1, 1):
        for bb in (-1, 1):
            X0 = s.diag(aa, bb)
            targets = [(1-half)*X0, (1+half)*X0]
            e = X0.det()/4
            total_e += quarter * Fraction(e)
            dx = (I + tt * B0 * X0).det()
            weights = [(I + tt * B0 * Y).det() for Y in targets]
            assert dx > 0 and all(w > 0 for w in weights)
            images = [Y * (I + tt * B0 * Y).inv() for Y in targets]
            w = sum(weights)/2
            mean = (weights[0]*images[0] + weights[1]*images[1])/(2*w)
            expected_w = dx + tt**2 * B0.det() * e
            expected_mean = (X0 + tt*(X0.det()+e)*B0.adjugate())/expected_w
            actual_image = X0 * (I + tt * B0 * X0).inv()
            eq(w, expected_w)
            eq(mean, expected_mean)
            eq(mean - actual_image,
               tt*e*B0.adjugate()*(I+tt*B0*X0).inv()/w)
            conditional_det = sum(
                weights[i] * (images[i] - mean).det() for i in range(2)
            )/(2*w)
            eq(conditional_det, e/w**2)
            if B0.det() == 0:
                eq(w, dx)
                eq(mean-actual_image, tt*e*B0.adjugate()/dx)
                assert mean != actual_image
            total_weight += quarter * Fraction(w)
            total_first += s.Rational(1, 4) * w * mean
    assert total_weight == 1 and total_e == 0
    eq(total_first, s.zeros(2))
print("12 rational conditional-weight, mean-mismatch, and determinant-defect checks passed.")

# A nonoptimal martingale coupling whose corrected barycenter law violates
# the determinant null Lagrangian, despite a genuine gradient source and
# a product-laminate target. All arithmetic here is Fraction arithmetic.
tq = Fraction(1, 4)
target_marginal = {(ss, rr): Fraction(0) for ss in (-1, 1) for rr in (-1, 1)}
source_mass = Fraction(0)
source_mean = [Fraction(0), Fraction(0)]
corrected_det_mean = Fraction(0)
conditional_e_mean = Fraction(0)
for aa in (-1, 1):
    for bb in (-1, 1):
        mass = Fraction(0)
        mean = [Fraction(0), Fraction(0)]
        defect = Fraction(0)
        tilt_mass = Fraction(0)
        tilt_first = [Fraction(0), Fraction(0)]
        for ss in (-1, 1):
            for rr in (-1, 1):
                probability = Fraction(4+2*aa*ss+2*bb*rr+(aa*bb+aa)*ss*rr, 16)
                assert probability >= 0
                mass += probability
                mean[0] += probability * 2*ss
                mean[1] += probability * 2*rr
                defect += probability * (2*ss-aa)*(2*rr-bb)
                target_marginal[ss, rr] += probability/4
                dy = 1 + tq*2*ss
                assert dy > 0
                tilt_mass += probability*dy
                tilt_first[0] += probability*2*ss
                tilt_first[1] += probability*dy*2*rr
        assert mass == 1 and mean == [aa, bb] and defect == aa
        dx = 1+tq*aa
        assert tilt_mass == dx
        corrected = [tilt_first[0]/dx, tilt_first[1]/dx]
        assert corrected == [Fraction(aa)/dx, bb+tq*aa/dx]
        source_mass += dx/4
        source_mean[0] += dx*corrected[0]/4
        source_mean[1] += dx*corrected[1]/4
        corrected_det_mean += dx*corrected[0]*corrected[1]/4
        conditional_e_mean += defect/4
assert all(value == Fraction(1, 4) for value in target_marginal.values())
assert source_mass == 1 and source_mean == [0, 0] and conditional_e_mean == 0
assert corrected_det_mean == tq/(1-tq*tq) == Fraction(4, 15)
print("Nonoptimal 16-atom control: true gradient source, laminate target, corrected determinant 4/15.")

# Actual independent triangular gradients: an exact all-B energy identity.
energy = 0
for aa in (-1, 1):
    for bb in (-1, 1):
        X0 = s.diag(aa, bb)
        dd = X0.det()
        den = (I + t * B * X0).det()
        num_matrix = X0 + t * dd * B.adjugate()
        num = ip(num_matrix, num_matrix)
        eq(num, 2 + 2*t*s.trace(B*X0) + t*t*ip(B, B))
        eq(num - 2*den, t*t*(ip(B, B)-2*dd*B.det()))
        energy += num/den/4
eq(energy.subs(t, 0), 2)
eq(s.diff(energy, t).subs(t, 0), 0)
eq(s.diff(energy, t, 2).subs(t, 0)/2, ip(B, B))

# Both signs have nonnegative numerators as explicit sums of squares.
b00, b01, b10, b11 = list(B)
eq(ip(B, B)-2*B.det(), (b00-b11)**2+(b01+b10)**2)
eq(ip(B, B)+2*B.det(), (b00+b11)**2+(b01-b10)**2)
c, r = s.symbols("c r")
for O in (s.Matrix([[c, -r], [r, c]]),
          s.Matrix([[c, r], [r, -c]])):
    conformal = s.factor(energy.subs(dict(zip(list(B), list(O)))))
    eq(s.factor(conformal.subs(r*r, 1-c*c)), 2/(1-t*t))
for B0 in matrices:
    for t0 in (s.Rational(1, 20), s.Rational(-1, 20)):
        value = s.cancel(energy.subs(dict(zip(list(B), list(B0)))).subs(t, t0))
        assert Fraction(value) > 2
print("All-B triangular-gradient identity, strict sign, and conformal specializations passed.")
print("No universal Hessian-extension estimate, QC closure, or optimal repair was certified.")
