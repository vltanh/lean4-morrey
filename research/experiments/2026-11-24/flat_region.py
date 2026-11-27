"""Numerical checks for docs/research/IWANIEC_MORREY_FLAT_REGION.md.

Usage (from the repository root):

    python3 research/experiments/2026-11-24/flat_region.py checks
    python3 research/experiments/2026-11-24/flat_region.py search [N]

`checks` samples the pointwise statements of the note in floating point.
`search` runs local descent for periodic piecewise-affine test maps.
Neither is a proof; see the README in this folder.
"""

import sys

import numpy as np
from scipy.optimize import minimize


# ---------------------------------------------------------------- coordinates

def zw(a, b, c, d):
    """Conformal and anticonformal parts of [[a, b], [c, d]]."""
    z = 0.5 * ((a + d) + 1j * (c - b))
    w = 0.5 * ((a - d) + 1j * (c + b))
    return z, w


def E_xy(x, y):
    """The integrand E as a function of x = |z|, y = |w|."""
    d = x - y
    s = x + y
    return np.where(d >= 1, 0.0,
                    np.where(d <= -1, 2 * (y * y - x * x),
                             2 * y * y - 0.5 * (1 - s) ** 2))


def E_mat(A):
    z, w = zw(A[..., 0, 0], A[..., 0, 1], A[..., 1, 0], A[..., 1, 1])
    return E_xy(np.abs(z), np.abs(w))


def E2_mat(H):
    z, w = zw(H[..., 0, 0], H[..., 0, 1], H[..., 1, 0], H[..., 1, 1])
    a = z.real
    r = np.abs(w)
    return np.where(a >= r, 0.0, -0.5 * a * a - a * r + 1.5 * r * r)


def det(A):
    return A[..., 0, 0] * A[..., 1, 1] - A[..., 0, 1] * A[..., 1, 0]


# --------------------------------------------------------------------- checks

def rank_one_second_differences(f, rng, n=200000):
    worst = 0.0
    for _ in range(n):
        A = rng.normal(size=(2, 2)) * rng.choice([0.3, 1.0, 3.0])
        R = np.outer(rng.normal(size=2), rng.normal(size=2))
        R /= np.linalg.norm(R)
        h = rng.choice([1e-2, 1e-1, 0.5])
        worst = min(worst, (f(A + h * R) + f(A - h * R) - 2 * f(A)) / h ** 2)
    return worst


def checks():
    rng = np.random.default_rng(0)
    print("min second difference / h^2 of E  along rank-one lines:",
          rank_one_second_differences(E_mat, rng))
    print("min second difference / h^2 of E2 along rank-one lines:",
          rank_one_second_differences(E2_mat, rng))

    X = rng.normal(size=(400000, 2, 2)) * rng.choice([0.2, 1.0, 3.0], size=(400000, 1, 1))
    z, w = zw(X[:, 0, 0], X[:, 0, 1], X[:, 1, 0], X[:, 1, 1])
    x, y = np.abs(z), np.abs(w)
    e = E_xy(x, y)
    q = 2 * x - 1 - det(X)
    I = np.eye(2)
    print("Proposition 2, min of E - (2|z| - 1 - det X):", (e - q).min())
    d = x - y
    s = x + y
    strip = np.abs(d) < 1
    U = d >= 1
    print("Proposition 2, formula on S, max error:",
          np.abs((e - q)[strip] - 0.5 * (1 - d[strip]) ** 2).max())
    print("Proposition 2, formula on U, max error:",
          np.abs((e - q)[U] - (d[U] - 1) * (s[U] - 1)).max())
    print("E(X) >= -det(X - I), min difference:", (e + det(X - I)).min())
    neg = e < 0
    print("E < 0 exactly on |z| + 3|w| < 1, mismatches:",
          int(np.sum(neg != (x + 3 * y < 1))))

    e2 = E2_mat(X)
    a = z.real
    M = -det(X) + z.imag ** 2 + 0.5 * np.minimum(a - y, 0.0) ** 2
    print("E2 >= M (polyconvex minorant at 0), min difference:", (e2 - M).min())

    S = X + np.transpose(X, (0, 2, 1))
    print("E2(S) >= -det S on symmetric S, min difference:", (E2_mat(S) + det(S)).min())

    H = rng.normal(size=(2000, 2, 2))
    for t in [1e-2, 1e-3]:
        err = np.abs(E_mat(I + t * H) / t ** 2 - E2_mat(H)).max()
        print(f"blow-up at I, t = {t}: max |E(I + tH)/t^2 - E2(H)| =", err)

    # shadow of U: from |X| < 1 no rank-one line reaches U
    worst = -np.inf
    for _ in range(20000):
        Y = rng.normal(size=(2, 2))
        Y *= rng.uniform(0, 1) / np.linalg.norm(Y, 2)
        R = np.outer(rng.normal(size=2), rng.normal(size=2))
        ts = np.linspace(-20, 20, 401)
        P = Y[None] + ts[:, None, None] * R[None]
        zz, ww = zw(P[:, 0, 0], P[:, 0, 1], P[:, 1, 0], P[:, 1, 1])
        worst = max(worst, (np.abs(zz) - np.abs(ww)).max())
    print("Lemma 3 (a): max of |z| - |w| on rank-one lines through |X| < 1:", worst)


# --------------------------------------------------------------------- search

def energy(phi, N, A0, f):
    """Exact mean of f(A0 + D phi) for the periodic P1 map phi, and its gradient.

    f(a, b, c, d) returns the value and the four partial derivatives.
    """
    h = 1.0 / N
    p = phi.reshape(2, N, N)
    px = np.roll(p, -1, axis=1) - p
    py = np.roll(p, -1, axis=2) - p
    pxy = np.roll(px, -1, axis=2)
    pyx = np.roll(py, -1, axis=1)
    tot = 0.0
    g = np.zeros_like(p)
    wgt = h / 2
    for G1, G2, kind in [(px / h, py / h, 1), (pxy / h, pyx / h, 2)]:
        a = A0[0, 0] + G1[0]
        b = A0[0, 1] + G2[0]
        c = A0[1, 0] + G1[1]
        d = A0[1, 1] + G2[1]
        val, ga, gb, gc, gd = f(a, b, c, d)
        tot += val.sum() * h * h / 2
        for comp, (gG1, gG2) in enumerate([(ga, gb), (gc, gd)]):
            if kind == 1:
                g[comp] += wgt * (np.roll(gG1, 1, axis=0) - gG1 + np.roll(gG2, 1, axis=1) - gG2)
            else:
                gg = gG1 + gG2
                g[comp] += wgt * (np.roll(np.roll(gg, 1, axis=0), 1, axis=1)
                                  - np.roll(gG1, 1, axis=1) - np.roll(gG2, 1, axis=0))
    return tot, g.ravel()


def _chain(dz_re, dz_im, dw_re, dw_im):
    """Partial derivatives in (a, b, c, d) from those in (Re z, Im z, Re w, Im w)."""
    ga = 0.5 * (dz_re + dw_re)
    gd = 0.5 * (dz_re - dw_re)
    gb = 0.5 * (-dz_im + dw_im)
    gc = 0.5 * (dz_im + dw_im)
    return ga, gb, gc, gd


def f_E(a, b, c, d):
    z, w = zw(a, b, c, d)
    x, y = np.abs(z), np.abs(w)
    dl, s = x - y, x + y
    V = dl <= -1
    S = (dl > -1) & (dl < 1)
    val = E_xy(x, y)
    ex = np.where(V, -4 * x, np.where(S, 1 - s, 0.0))
    ey = np.where(V, 4 * y, np.where(S, 4 * y + 1 - s, 0.0))
    xs = np.where(x > 0, x, 1.0)
    ys = np.where(y > 0, y, 1.0)
    ux = np.where(x > 0, z / xs, 0.0)
    uy = np.where(y > 0, w / ys, 0.0)
    return (val,) + _chain(ex * ux.real, ex * ux.imag, ey * uy.real, ey * uy.imag)


def f_E2(a, b, c, d):
    z, w = zw(a, b, c, d)
    A = z.real
    r = np.abs(w)
    neg = A < r
    val = np.where(neg, -0.5 * A * A - A * r + 1.5 * r * r, 0.0)
    dA = np.where(neg, -A - r, 0.0)
    dr = np.where(neg, -A + 3 * r, 0.0)
    rs = np.where(r > 0, r, 1.0)
    u = np.where(r > 0, w / rs, 0.0)
    return (val,) + _chain(dA, 0 * dA, dr * u.real, dr * u.imag)


def smooth_random(N, amp, kmax, rng):
    p = np.zeros((2, N, N))
    X, Y = np.meshgrid(np.arange(N) / N, np.arange(N) / N, indexing="ij")
    for comp in range(2):
        for _ in range(12):
            k1, k2 = rng.integers(-kmax, kmax + 1, size=2)
            if k1 == 0 and k2 == 0:
                continue
            ph = rng.uniform(0, 2 * np.pi)
            p[comp] += (amp * rng.normal() / np.hypot(k1, k2)
                        * np.cos(2 * np.pi * (k1 * X + k2 * Y) + ph) / (2 * np.pi))
    return p.ravel()


def radial_compression(N, s, r1):
    X, Y = np.meshgrid(np.arange(N) / N - 0.5, np.arange(N) / N - 0.5, indexing="ij")
    bump = np.clip(1 - (np.hypot(X, Y) / r1) ** 2, 0, None) ** 2
    return np.stack([-s * X * bump, -s * Y * bump]).ravel()


def gradient_check(f, rng, N=8):
    A0 = np.array([[1.2, 0.1], [-0.3, 0.9]])
    phi = rng.normal(size=2 * N * N) * 0.4
    _, g = energy(phi, N, A0, f)
    eps = 1e-6
    worst = 0.0
    for k in rng.integers(0, 2 * N * N, size=10):
        e = np.zeros_like(phi)
        e[k] = eps
        num = (energy(phi + e, N, A0, f)[0] - energy(phi - e, N, A0, f)[0]) / (2 * eps)
        worst = max(worst, abs(num - g[k]))
    return worst


def run(f, A0, N, starts, rng, amps):
    best = np.inf
    for trial in range(starts):
        if trial % 4 == 0:
            phi0 = radial_compression(N, A0[0, 0] + 1.0, rng.uniform(0.15, 0.4)) \
                + smooth_random(N, 0.1, 3, rng)
        else:
            phi0 = smooth_random(N, rng.choice(amps), rng.integers(1, 6), rng)
        res = minimize(energy, phi0, args=(N, A0, f), jac=True, method="L-BFGS-B",
                       options={"maxiter": 4000, "maxfun": 8000})
        best = min(best, res.fun)
        print(f"  start {trial:2d}: final mean energy {res.fun:.3e} after {res.nit} iterations",
              flush=True)
    return best


def search(N):
    rng = np.random.default_rng(1)
    print("gradient check E :", gradient_check(f_E, rng))
    print("gradient check E2:", gradient_check(f_E2, rng))
    for s in [1.0, 1.05, 1.2, 1.6]:
        print(f"E at s I, s = {s}:")
        best = run(f_E, s * np.eye(2), N, 8, rng, [0.5, 1, 2, 4])
        print(f"  smallest final mean energy: {best:.3e} (E(s I) = 0)")
    print("E2 at I:")
    best = run(f_E2, np.eye(2), N, 16, rng, [1, 2, 4, 8])
    print(f"  smallest final mean energy: {best:.3e} (E2(I) = 0)")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "checks"
    if cmd == "checks":
        checks()
    elif cmd == "search":
        search(int(sys.argv[2]) if len(sys.argv) > 2 else 32)
    else:
        raise SystemExit(__doc__)
