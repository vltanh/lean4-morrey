"""Exact finite-grid controls for conditional lamination; not a Morrey proof."""
from fractions import Fraction as Q
from itertools import product


def sign(z, m):
    return 1 if (z % m) < m // 2 else -1


def moments(m, k, shifts):
    n = len(k)
    counts = [0] * (1 << n)
    for x, y in product(range(m), repeat=2):
        mask = sum((sign(a*x+b*y+s, m) < 0) << i
                   for i, ((a,b),s) in enumerate(zip(k,shifts)))
        counts[mask] += 1
    return [Q(sum(w * (-1)**((j & h).bit_count())
                  for j,w in enumerate(counts)), m*m)
            for h in range(1 << n)]


def check_triad(m,k,shifts):
    w=moments(m,k,shifts)
    assert w[0] == 1 and w[1:7] == [0]*6, (m,k,shifts,w)
    assert abs(w[7]) <= Q(1,2), (m,k,shifts,w)
    return w[7]


def r(t):
    return 1 if t % 1 < Q(1,2) else -1


def triangular(t):
    z=t % 1
    return 1-4*min(z,1-z)


def main():
    for a,b in product((1,3),repeat=2):
        for shifts in product(range(4),repeat=3):
            assert abs(check_triad(4,((1,0),(0,1),(a,b)),shifts)) == Q(1,2)
    print('256 quarter-grid triads: all lower moments zero, |rho|=1/2')
    assert abs(moments(2,((1,0),(0,1),(1,1)),(0,0,0))[7]) == 1
    for shifts in product((0,1,3),repeat=3):
        check_triad(8,((2,0),(0,1),(2,-1)),shifts)
    print('27 index-two unit triads on Z8^2: passed')
    for k in (((1,0),(0,1),(3,1)), ((1,0),(0,1),(2,1)), ((2,0),(0,1),(1,1))):
        for shifts in ((0,0,0),(1,17,41),(3,63,201)):
            check_triad(256,k,shifts)
    print('9 nonunit/even-relation grid controls: passed')
    w=moments(16,((2,0),(3,0),(1,2)),(0,4,1))
    assert w[1]==w[2]==w[4]==w[5]==w[6]==w[7]==0
    print('parallel/transverse control: passed')
    c=sum((r(x)*r(4*x)*triangular(x)*Q(1,8)
           for j in range(8) for x in [Q(2*j+1,16)]),Q(0))
    assert c == Q(1,4)
    print('mixed four-wave Walsh moment:',c)


if __name__ == '__main__':
    main()
