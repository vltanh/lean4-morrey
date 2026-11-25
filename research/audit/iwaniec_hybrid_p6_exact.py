#!/usr/bin/env python3
"""Exact p=6 hybrid-cone regression control (no floating-point computations).

Checks the identity
  h(r) = 1+r+(1+r)^3
       = (5/4)(2/3+r) + (1/4)(2/3-r) + (1+r)^3,
and the strict failure of *both individual* touching tests at r0=0.
It does NOT check the 2026 Burkholder theorem or constitute a Lean proof.

Run: python research/audit/iwaniec_hybrid_p6_exact.py
"""
from fractions import Fraction as Q


def add(a, b):
    return tuple((a[i] if i < len(a) else Q(0)) +
                 (b[i] if i < len(b) else Q(0))
                 for i in range(max(len(a), len(b))))


def scale(c, a):
    return tuple(c * x for x in a)


K = Q(2, 3)  # 1 - 2/p for p=6
ONE_PLUS_R_CUBED = (Q(1), Q(3), Q(3), Q(1))
H = (Q(2), Q(4), Q(3), Q(1))
B_PLUS = (K, Q(1))
B_MINUS = (K, Q(-1))

CERTIFICATE = add(
    add(scale(Q(5, 4), B_PLUS), scale(Q(1, 4), B_MINUS)),
    ONE_PLUS_R_CUBED,
)
assert CERTIFICATE == H, (CERTIFICATE, H)

# The (unique) ordinary supporting line of h at r0 = 0
# has intercept c=h(0) and slope m=h'(0).
c, m = H[0], H[1]
assert c == 2 and m == 4
assert c < K * abs(m)  # 2 < 8/3: Burkholder-line test fails

# For v=h^(1/3), v'(0)/v(0)=h'(0)/(3h(0))=2/3.
# The unique tangent at r0=0 therefore has
# l(-1)/v(0) = 1-v'(0)/v(0) = 1/3 > 0.
# But v(-1)=h(-1)^(1/3)=0, so it is NOT a global minorant.
assert sum(H[i] * (-1) ** i for i in range(len(H))) == 0
relative_root_slope = m / (3 * c)
assert relative_root_slope == Q(2, 3)
assert 1 - relative_root_slope == Q(1, 3) > 0

print("PASS: exact hybrid identity and two strict single-test obstructions")
