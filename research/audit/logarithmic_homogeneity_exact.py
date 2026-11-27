#!/usr/bin/env python3
"""Exact algebra controls for the logarithmic homogeneity hand theorem.

Run from the repository root:
    python3 research/audit/logarithmic_homogeneity_exact.py

SymPy checks identities, not the analytic theorem. In particular, positivity
of the distributional second derivative of a convex line restriction, the
locally uniform limit, and the verified homogeneous QC input are used in the
accompanying proof, not established by finite numerical sampling here.
"""

import sympy as s


def equal(actual, expected):
    difference = s.simplify(s.expand(actual - expected))
    assert difference == 0, difference


# Abstract calculus along a rank-one line X(t): r=|X|, q=X:V,
# v2=|V|^2, d=det X, dp=(det X)'. Along this line d''=0 and q'=v2.
r = s.symbols("r", positive=True)
eps = s.symbols("eps", positive=True)
q, v2, d, dp, drift = s.symbols("q v2 d dp drift", real=True)
f, fp, fpp = s.symbols("f fp fpp", real=True)


def line_derivative(expression):
    return (
        s.diff(expression, r) * q / r
        + s.diff(expression, q) * v2
        + s.diff(expression, d) * dp
        + s.diff(expression, f) * fp
        + s.diff(expression, fp) * fpp
    )


power = r**eps
log_factor = power * (1 - eps * s.log(r))
equal(line_derivative(power), eps * r ** (eps - 2) * q)
equal(
    line_derivative(line_derivative(power)),
    eps * r ** (eps - 2) * v2
    + eps * (eps - 2) * r ** (eps - 4) * q**2,
)
equal(line_derivative(log_factor), -eps**2 * r ** (eps - 2) * q * s.log(r))
equal(
    line_derivative(line_derivative(log_factor)),
    -eps**2
    * (
        r ** (eps - 2) * v2 * s.log(r)
        + (eps - 2) * r ** (eps - 4) * q**2 * s.log(r)
        + r ** (eps - 4) * q**2
    ),
)
print("Scalar factors on an arbitrary rank-one line: passed")

# Keep fpp symbolic: this is the coefficient of the positive curvature
# measure in the nonsmooth proof, and must not disappear in the algebra.
g = eps * power * f + drift * log_factor * d
gpp = line_derivative(line_derivative(g))
equal(s.diff(gpp, fpp), eps * power)
f0, f1, alpha, d0 = s.symbols("f0 f1 alpha d0", real=True)
normalized_remainder = (gpp - eps * power * fpp).subs(
    {
        f: r**2 * f0 + drift * d * s.log(r),
        fp: r * f1 + drift * dp * s.log(r),
    },
    simultaneous=True,
).subs({q: r * alpha, d: r**2 * d0}, simultaneous=True)
expected_remainder = eps**2 * power * (
    2 * alpha * f1 + (v2 + (eps - 2) * alpha**2) * f0
    - drift * alpha**2 * d0
)
equal(normalized_remainder, expected_remainder)
print("Exact normalized curvature remainder, including the measure coefficient: passed")

equal(
    line_derivative(line_derivative(r ** (2 + eps))),
    (2 + eps) * r**eps * v2
    + eps * (2 + eps) * r ** (eps - 2) * q**2,
)
# Write alpha^2=theta*v2, 0<=theta<=1. The remainder coefficient
# divided by v2 belongs to [-1,1] for 0<eps<=1, by these certificates.
theta = s.symbols("theta", real=True)
b = 1 + (eps - 2) * theta
equal(1 - b, (2 - eps) * theta)
equal(1 + b, 2 * (1 - theta) + eps * theta)
print("Radial repair and scalar interval certificates: passed")

# Scaling covariance of the exact approximants, with log(t)=ell.
t = s.symbols("t", positive=True)
ell, correction = s.symbols("ell correction", real=True)
g_with_correction = g + correction * eps**2 * r ** (2 + eps)
scaled_g = (
    eps * t**eps * r**eps * t**2 * (f + drift * ell * d)
    + drift * t**eps * r**eps * (1 - eps * (ell + s.log(r))) * t**2 * d
    + correction * eps**2 * t ** (2 + eps) * r ** (2 + eps)
)
equal(scaled_g, t ** (2 + eps) * g_with_correction)
equal(s.diff(g_with_correction, eps).subs(eps, 0), f)
equal(g_with_correction.subs(eps, 0), drift * d)
print("Homogeneous covariance and first-order recovery of the original energy: passed")

# The first-order dilation cocycle and its nonresonant determinant gauge.
u, tp, up, gauge = s.symbols("u tp up gauge", real=True)
bt = gauge * (tp - t**2)
bu = gauge * (up - u**2)
equal(gauge * (tp * up - t**2 * u**2), up * bt + t**2 * bu)
equal(bt + gauge * t**2 - tp * gauge, 0)
log_t, log_u = s.symbols("log_t log_u", real=True)
equal(
    drift * t**2 * u**2 * (log_t + log_u),
    u**2 * (drift * t**2 * log_t) + t**2 * (drift * u**2 * log_u),
)
print("Both determinant-drift cocycles and the nonresonant gauge: passed")

# Global determinant bound used in the proof: 4 det(X)^2 <= |X|_F^4.
x11, x12, x21, x22 = s.symbols("x11 x12 x21 x22", real=True)
norm2 = x11**2 + x12**2 + x21**2 + x22**2
determinant = x11 * x22 - x12 * x21
equal(
    norm2**2 - 4 * determinant**2,
    (x11**2 + x12**2 - x21**2 - x22**2)**2
    + 4 * (x11 * x21 + x12 * x22)**2,
)
print("Frobenius/determinant inequality as an exact sum of squares: passed")

# Example: 2r^2 + d log r + d^2/r^2. These are general-radius identities.
equal(
    line_derivative(line_derivative(d * s.log(r))),
    2 * dp * q / r**2 + d * (v2 / r**2 - 2 * q**2 / r**4),
)
equal(
    line_derivative(line_derivative(d**2 / r**2)),
    2 / r**2 * (dp - 2 * d * q / r**2)**2 - 2 * d**2 * v2 / r**4,
)
equal(4 - s.Rational(5, 2) - s.Rational(1, 2), 1)
print("Example rank-one Hessian identities and curvature margin: passed")

large, small = s.symbols("large small", real=True)
profile = (
    2 * (large**2 + small**2)
    + large * small * s.log(large**2 + small**2) / 2
    + large**2 * small**2 / (large**2 + small**2)
)
angular_curvature = s.diff(profile, small, 2)
at_first = angular_curvature.subs({large: 2, small: 1})
at_second = angular_curvature.subs({large: 3, small: 1})
equal(at_first, s.Rational(662, 125))
equal(at_second, s.Rational(1453, 250))
equal(at_first - at_second, -s.Rational(129, 250))
print("Exact exclusion of affine-shell and separated-angular profile forms: passed")

print("All exact algebra controls passed; the full analytic proof is in the research note.")
