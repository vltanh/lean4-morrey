#!/usr/bin/env python3
"""Exact algebra controls for the discrete quadratic scaling reduction.

Run from the repository root:
    python3 research/audit/discrete_scaling_exact.py

These are symbolic identities and finite rational controls. They do not
prove the analytic localization, smoothing, preservation of an unspecified
strict witness, or quasiconvexity of a discretely homogeneous energy.
The compact-annulus control below is not asserted to be rank-one convex.
The Taylor check verifies rescaling algebra, not a differentiability limit.
"""

from fractions import Fraction as Q

import sympy as s


def equal(actual, expected):
    difference = s.simplify(s.expand(actual - expected))
    assert difference == 0, difference


# A logarithmic cutoff along X(t)=A+tV. Here r=|X|, q=X:V,
# v2=|V|^2, and ell=log(r/R)/L. The symbols z1,z2 represent the
# first two derivatives of the scalar cutoff with respect to ell.
r, width = s.symbols("r width", positive=True)
q, v2, z0, z1, z2 = s.symbols("q v2 z0 z1 z2", real=True)
f, fp, fpp = s.symbols("f fp fpp", real=True)


def line_derivative(expression):
    return (
        s.diff(expression, r) * q / r
        + s.diff(expression, q) * v2
        + s.diff(expression, z0) * z1 * q / (width * r**2)
        + s.diff(expression, z1) * z2 * q / (width * r**2)
        + s.diff(expression, f) * fp
        + s.diff(expression, fp) * fpp
    )


cutoff_first = line_derivative(z0)
cutoff_second = line_derivative(cutoff_first)
equal(cutoff_first, z1 * q / (width * r**2))
equal(
    cutoff_second,
    z2 * q**2 / (width**2 * r**4)
    + z1 / width * (v2 / r**2 - 2 * q**2 / r**4),
)
equal(
    line_derivative(line_derivative(z0 * f)) - z0 * fpp,
    2 * cutoff_first * fp + cutoff_second * f,
)
print("Logarithmic cutoff and exact product-rule remainder: passed")

# D^2(log r)=r^-2(I-2nn^T). The reflection identity certifies its
# operator norm at a unit n; no rank-one assumption is used here.
n = s.Matrix(s.symbols("n0:4", real=True))
reflection = s.eye(4) - 2 * n * n.T
reflection_error = reflection * reflection - s.eye(4)
expected_error = 4 * ((n.T * n)[0] - 1) * n * n.T
assert all(s.expand(x) == 0 for x in reflection_error - expected_error)

K, C1, C2, margin = s.symbols("K C1 C2 margin", positive=True)
# |f|<=Kr^2/2 and |Df|<=Kr. The two cross terms and cutoff Hessian
# produce precisely the bound used in the hand proof.
product_budget = (
    2 * C1 / (width * r) * K * r
    + K * r**2 / 2 * (C1 / width + C2 / width**2) / r**2
)
equal(product_budget, K * (s.Rational(5, 2) * C1 / width + C2 / (2 * width**2)))
print("Full-Hessian logarithmic cutoff budget: passed")

# A concrete C^2 cutoff. Its endpoint joins are C^2; an analytic
# smooth-cutoff argument can instead use any finite derivative bounds.
t, u = s.symbols("t u", real=True)
cutoff = 1 - 10 * t**3 + 15 * t**4 - 6 * t**5
equal(s.diff(cutoff, t), -30 * t**2 * (1 - t)**2)
equal(s.diff(cutoff, t, 2), -60 * t * (1 - t) * (1 - 2 * t))
for endpoint, value in [(0, 1), (1, 0)]:
    equal(cutoff.subs(t, endpoint), value)
    equal(s.diff(cutoff, t).subs(t, endpoint), 0)
    equal(s.diff(cutoff, t, 2).subs(t, endpoint), 0)
equal(s.Rational(1, 4) - t * (1 - t), (t - s.Rational(1, 2)) ** 2)
equal(
    s.Rational(4, 27) - u * (1 - u) ** 2,
    (u - s.Rational(1, 3)) ** 2 * (s.Rational(4, 3) - u),
)
# The displayed nonnegative-polynomial identities give |cutoff'|<=15/8<2
# and |cutoff''|^2<=100/3<64 on [0,1], so C1=2,C2=8 suffice.
assert Q(15, 8) < 2 and Q(100, 3) < 64

# With x=K/m, L=1+20x makes the error strictly smaller than m/2.
x = s.symbols("x", positive=True)
normalized_budget = 5 * x / (1 + 20 * x) + 4 * x / (1 + 20 * x) ** 2
equal(
    s.Rational(1, 2) - normalized_budget,
    (1 + 22 * x + 200 * x**2) / (2 * (1 + 20 * x) ** 2),
)
budget_cases = [Q(1, 1000), Q(1, 10), Q(1), Q(13, 2), Q(10**6)]
for ratio in budget_cases:
    L = 1 + 20 * ratio
    assert 5 * ratio / L + 4 * ratio / L**2 < Q(1, 2)
print("Cutoff endpoint certificates and universal positive budget polynomial: passed")

# General quadratic backgrounds, not merely a multiple of the norm.
coordinates = s.symbols("x0:4", real=True)
scale = s.symbols("scale", positive=True)
coefficients = s.symbols("b0:10", real=True)
quadratic = sum(
    coefficient * coordinates[i] * coordinates[j]
    for coefficient, (i, j) in zip(
        coefficients, ((i, j) for i in range(4) for j in range(i, 4))
    )
)
equal(
    quadratic.subs({v: scale * v for v in coordinates}, simultaneous=True),
    scale**2 * quadratic,
)
assert all(entry == 0 for entry in s.hessian(quadratic, coordinates).diff(coordinates[0]))
print("Arbitrary quadratic background scaling: passed")

# Finite-sum reindexing leaves exactly two boundary terms. The infinite
# locally finite identity follows in the proof from vanishing of these
# endpoint terms, not from taking a numerical series limit here.
T = s.symbols("T", positive=True)
for N in [1, 2, 4]:
    symbols = {k: s.Symbol(f"phi_{k}") for k in range(-N - 1, N + 1)}
    scaled_sum = sum(T ** (2 * k) * symbols[k - 1] for k in range(-N, N + 1))
    original_scaled = T**2 * sum(T ** (2 * k) * symbols[k] for k in range(-N, N + 1))
    boundary = T ** (-2 * N) * symbols[-N - 1] - T ** (2 * N + 2) * symbols[N]
    equal(scaled_sum - original_scaled, boundary)

a, b = s.symbols("a b", positive=True)
k = s.symbols("k", integer=True)
equal(a * T ** (k + 1) - b * T**k, T**k * (a * T - b))
# Thus the analytic condition aT>b separates every pair of consecutive
# support annuli, for all integer k. Check a few exact positive margins.
for inner, outer, ratio in [(Q(1), Q(3), Q(4)), (Q(1, 100), Q(7), Q(1000)), (Q(2), Q(5), Q(3))]:
    assert inner * ratio > outer
print("Finite period reindexing and all-index annulus separation identity: passed")


# Rational compact-annulus control: phi(r)=r^2(r-1)^3(3-r)^3 on [1,3].
# Its radial coefficient lies in [0,1]; this control is NOT asserted RC.
def annular_bump(radius):
    if not Q(1) <= radius <= Q(3):
        return Q(0)
    return radius**2 * (radius - 1) ** 3 * (3 - radius) ** 3


def periodized_control(radius):
    assert radius > 0
    normalized = radius
    exponent = 0
    while normalized < 1:
        normalized *= 4
        exponent -= 1
    while normalized >= 4:
        normalized /= 4
        exponent += 1
    return 2 * radius**2 + Q(4) ** (2 * exponent) * annular_bump(normalized)


radii = [Q(1, 16), Q(1, 8), Q(1, 4), Q(3, 8), Q(1, 2), Q(3, 4), Q(1), Q(5, 4), Q(3, 2), Q(2), Q(5, 2), Q(3), Q(7, 2), Q(4), Q(6), Q(12), Q(16)]
period_checks = 0
for radius in radii:
    active = [j for j in range(-8, 9) if annular_bump(radius / Q(4)**j) != 0]
    assert len(active) <= 1
    finite_sum = 2 * radius**2 + sum(Q(4)**(2 * j) * annular_bump(radius / Q(4)**j) for j in range(-8, 9))
    assert finite_sum == periodized_control(radius)
    assert 0 <= periodized_control(radius) - 2 * radius**2 <= radius**2
    for j in range(-5, 6):
        assert periodized_control(Q(4)**j * radius) == Q(4)**(2 * j) * periodized_control(radius)
        period_checks += 1
print(f"Compact-annulus rational control: {period_checks} exact scaling comparisons passed")

# A single active rescaled bump inherits the same B*r^2 bound. The
# Jensen perturbation estimate includes both the average and the base.
B, delta2, gap = s.symbols("B delta2 gap", positive=True)
equal(T ** (2 * k) * B * (r / T**k) ** 2, B * r**2)
equal((2 * B * delta2).subs(delta2, gap / (8 * B)), gap / 4)
equal(-gap + gap / 4, -3 * gap / 4)
print("Rescaled bump bound and strict-gap perturbation budget: passed")

# The unrestricted reduction permits translating a compact perturbation
# of a positive scalar quadratic far from zero. This fixes T=2 without
# imposing a period bound on the original, unmodified witness range.
# Translation does not preserve isotropy, so these controls are separate
# from the centered isotropic construction above.
center = s.symbols("c0:4", real=True)
translated_quadratic = quadratic.subs(
    {v: v + c for v, c in zip(coordinates, center)}, simultaneous=True
)
center_quadratic = quadratic.subs(
    dict(zip(coordinates, center)), simultaneous=True
)
translation_difference = s.expand(translated_quadratic - quadratic)
assert all(entry == 0 for entry in s.hessian(translation_difference, coordinates))
equal(
    translation_difference,
    center_quadratic
    + sum(s.diff(quadratic, v).subs(dict(zip(coordinates, center)), simultaneous=True) * v for v in coordinates),
)
print("Exact affine change of a translated arbitrary quadratic: passed")


def vector_add(left, right):
    return tuple(x + y for x, y in zip(left, right))


def vector_scale(factor, vector):
    return tuple(factor * value for value in vector)


def squared_norm(vector):
    return sum(value * value for value in vector)


def ball_bump(vector):
    norm2 = squared_norm(vector)
    return -(1 - norm2) ** 3 if norm2 <= 1 else Q(0)


def translated_control(vector, center_vector, scalar_background=Q(3)):
    # Finite range only for the exact control points below. The analytic
    # proof uses a locally finite sum over all integer indices.
    return scalar_background * squared_norm(vector) + sum(
        Q(2) ** (2 * j)
        * ball_bump(vector_add(vector_scale(Q(2) ** (-j), vector), vector_scale(-1, center_vector)))
        for j in range(-8, 9)
    )


center_control = (Q(8), Q(0), Q(0), Q(0))
base_control = (Q(1, 3), Q(0), Q(0), Q(-2, 5))
# These four matrices arise from independent scalar periodic sawteeth
# in the two coordinate directions; only their mean identity is needed
# for the translation check. This is not a negative witness search.
test_matrices = [
    vector_add(base_control, (sx * Q(1, 4), Q(0), Q(0), sy * Q(1, 5)))
    for sx in [-1, 1] for sy in [-1, 1]
]
assert all(squared_norm(vector) < 1 for vector in test_matrices + [base_control])
assert tuple(sum(vector[i] for vector in test_matrices) / 4 for i in range(4)) == base_control


def original_control(vector):
    return 3 * squared_norm(vector) + ball_bump(vector)


original_gap = sum(original_control(vector) for vector in test_matrices) / 4 - original_control(base_control)
shifted_base = vector_add(center_control, base_control)
translated_gap = (
    sum(translated_control(vector_add(center_control, vector), center_control) for vector in test_matrices) / 4
    - translated_control(shifted_base, center_control)
)
assert translated_gap == original_gap
for vector in test_matrices + [base_control]:
    shifted = vector_add(center_control, vector)
    active = [j for j in range(-8, 9) if ball_bump(vector_add(vector_scale(Q(2) ** (-j), shifted), vector_scale(-1, center_control))) != 0]
    assert active == [0]
    for j in range(-3, 4):
        assert translated_control(vector_scale(Q(2)**j, shifted), center_control) == Q(2)**(2*j) * translated_control(shifted, center_control)
assert Q(2) * (8 - 1) > 8 + 1
print("Fixed dyadic period, disjoint translated supports, and exact compatible-test gap preservation: passed")

# The exhaustive planar target can use the one base I and the one range
# B_(1/10)(I). First center the original compatible test at zero, choose
# the distant patch center 8I, then scale the base and map together by1/8.
# This is a constant scaling of an actual gradient, not pointwise scaling.
identity = (Q(1), Q(0), Q(0), Q(1))
conformal_center = vector_scale(Q(8), identity)
centered_test = [
    (sx * Q(1, 4), Q(0), Q(0), sy * Q(1, 5))
    for sx in [-1, 1] for sy in [-1, 1]
]
zero_matrix = (Q(0),) * 4
centered_gap = sum(original_control(v) for v in centered_test) / 4 - original_control(zero_matrix)


def even_translated_control(vector):
    return translated_control(vector, conformal_center) + sum(
        Q(2) ** (2 * j)
        * ball_bump(vector_add(vector_scale(-Q(2) ** (-j), vector), vector_scale(-1, conformal_center)))
        for j in range(-8, 9)
    )


fixed_base_gap = (
    sum(even_translated_control(vector_add(identity, vector_scale(Q(1, 8), v))) for v in centered_test) / 4
    - even_translated_control(identity)
)
assert fixed_base_gap == centered_gap / 64
for v in centered_test + [zero_matrix]:
    scaled_gradient = vector_scale(Q(1, 8), v)
    assert squared_norm(scaled_gradient) < Q(1, 100)
    value = vector_add(identity, scaled_gradient)
    assert Q(1) < squared_norm(value) < Q(4)
    assert value[0] * value[3] - value[1] * value[2] > 0
    assert even_translated_control(value) == even_translated_control(vector_scale(-1, value))
print("One fixed base I, fixed ball B_(1/10)(I), evenness, and exact rescaled gap: passed")

# On the kth active support, |X|>=2^k(M-R), while the bump and
# its derivative have sizes at most 2^(2k)B0 and 2^k B1. Thus
# translation makes both relative C0 and C1 errors small, without
# making the Hessian perturbation small.
B0, B1, rho, tolerance = s.symbols("B0 B1 rho tolerance", positive=True)
radial_gap = s.symbols("radial_gap", positive=True)
equal(T ** (2 * k) * B0 / (T**k * radial_gap) ** 2, B0 / radial_gap**2)
equal(T**k * B1 / (T**k * radial_gap), B1 / radial_gap)

# Explicit sufficient distance: M=R+D, D=1+2R+B0/tol+B1/tol.
# D>2R gives 2(M-R)>M+R. D>B1/tol gives the C1 bound;
# D>1+B0/tol and (1+x)^2>=x give the C0 bound.
distance = 1 + 2 * rho + B0 / tolerance + B1 / tolerance
equal(2 * distance - (distance + 2 * rho), 1 + B0 / tolerance + B1 / tolerance)
equal(distance - B1 / tolerance, 1 + 2 * rho + B0 / tolerance)
equal(distance - (1 + B0 / tolerance), 2 * rho + B1 / tolerance)
equal((1 + x) ** 2 - x, 1 + x + x**2)

relative_cases = [
    (Q(1), Q(1), Q(6), Q(1, 10)),
    (Q(7), Q(50), Q(17), Q(1, 1000)),
    (Q(1, 100), Q(1, 10000), Q(1, 50), Q(1, 100)),
]
for support_radius, value_bound, derivative_bound, tol in relative_cases:
    D = 1 + 2 * support_radius + value_bound / tol + derivative_bound / tol
    assert D > 2 * support_radius
    assert value_bound / D**2 < tol and derivative_bound / D < tol
# If the relative C0 tolerance is <=q0/2, the background q0|X|^2
# remains coercive with lower bound q0|X|^2/2.
q0 = s.symbols("q0", positive=True)
equal(q0 - q0 / 2, q0 / 2)
print("Fixed-period relative C0/C1 and coercivity budget identities: passed")

# A universal full-Hessian bound for the fixed-period normal form.
# Normalize the original centered test to B1, subtract its affine jet,
# and let a bound the smooth Hessian on B4. The tail h=2a*r^2-8a
# is separated from F by at least 11a/2 on the two gluing collars.
hessian_scale = s.symbols("hessian_scale", positive=True)
tail = 2 * hessian_scale * r**2 - 8 * hessian_scale
inner_separation = -hessian_scale * r**2 / 2 - tail
outer_separation = tail - hessian_scale * r**2 / 2
equal(inner_separation.subs(r, 1), s.Rational(11, 2) * hessian_scale)
equal(outer_separation.subs(r, 3), s.Rational(11, 2) * hessian_scale)
# Smoothmax at width a has weights summing to1 and an extra Hessian
# term bounded by |DF-Dh|^2/a. On B4, |DF|<=4a and |Dh|<=16a.
full_hessian_budget = 4 * hessian_scale + (4 * hessian_scale + 16 * hessian_scale) ** 2 / hessian_scale
equal(full_hessian_budget, 404 * hessian_scale)
equal(full_hessian_budget / (2 * hessian_scale), 202)
print("Universal full-Hessian bound 202 after normalization: passed")

# Twice-differentiable-at-zero rigidity: the proof scales a Taylor
# remainder bounded by eta*|Y|^2 at Y=T^-k X. After multiplication
# by T^(2k), the same bound is eta*|X|^2. Letting eta decrease to0
# is an analytic step, not certified by finite tests.
eta = s.symbols("eta", positive=True)
equal(T ** (2 * k) * eta * (r / T**k) ** 2, eta * r**2)
equal(T ** (2 * k) * quadratic.subs({v: v / T**k for v in coordinates}, simultaneous=True), quadratic)
print("Taylor remainder and quadratic rescaling identities: passed (limit is analytic)")

# Phase averaging controls only the constant Fourier mode. The following
# scalar function is not claimed to arise from an RC energy/gradient pair.
theta = s.symbols("theta", real=True)
scalar_phase = 1 - 2 * s.cos(theta)
equal(s.integrate(scalar_phase, (theta, 0, 2 * s.pi)) / (2 * s.pi), 1)
equal(scalar_phase.subs(theta, 0), -1)

# A genuinely convex radial energy with nonconstant discrete scaling
# phase: r^2[1+eta*sin(omega*log r)]. Radial/tangential Hessian
# coefficients are as follows; their amplitudes give explicit bounds.
omega = s.symbols("omega", positive=True)
radial_energy = r**2 * (1 + eta * s.sin(omega * s.log(r)))
phase = omega * s.log(r)
equal(s.diff(radial_energy, r) / r, 2 + eta * (2 * s.sin(phase) + omega * s.cos(phase)))
equal(s.diff(radial_energy, r, 2), 2 + eta * ((2 - omega**2) * s.sin(phase) + 3 * omega * s.cos(phase)))
# At omega=1, eta=1/10, bounds by sums of absolute coefficients
# give tangential eigenvalue>=17/10, radial eigenvalue>=8/5.
equal(2 - s.Rational(1, 10) * (2 + 1), s.Rational(17, 10))
equal(2 - s.Rational(1, 10) * (1 + 3), s.Rational(8, 5))
print("Phase-average limitation and nonconstant convex-phase control identities: passed")

print("All exact algebra and finite rational controls passed.")
print("No new quasiconvexity theorem or negative compatible-gradient witness was certified by this script.")
