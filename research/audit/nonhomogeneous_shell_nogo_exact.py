"""Exact arithmetic for the four-atom affine-shell separation.
The analytic bound for the rotational integral is in the hand proof.
No sampled-radii inference is made: minimize each quadratic on its full interval.
"""
from fractions import Fraction as Q
from itertools import product

LAW = [(Q(1,2),Q(1,2),Q(4,7)),
       (Q(5,4),-Q(5,4),Q(16,49)),
       (Q(3),Q(3),Q(1,14)),
       (Q(3),-Q(3),Q(3,98))]


def check():
    assert sum(w for s,d,w in LAW)==1
    assert sum(w*s for s,d,w in LAW)==1
    assert sum(w*d for s,d,w in LAW)==0
    assert sum(w*s*d for s,d,w in LAW)==0
    print('Exact mass, two matrix means, and determinant moment: passed')
    knots=[Q(0),Q(1,2),Q(1),Q(5,4),Q(3)]
    for e,(lo,hi) in product((-1,1),zip(knots,knots[1:])):
        mid=(lo+hi)/2
        active=[(s,d,w) for s,d,w in LAW if s>mid]
        # Difference of expected K_r^e and the base value r(1-r)_+.
        a=-sum(w for s,d,w in active)
        b=sum(w*(s-e*d) for s,d,w in active)
        c=sum(w*e*s*d for s,d,w in active)
        if mid<1:
            a+=1; b-=1
        f=lambda r:a*r*r+b*r+c
        candidates=[lo,hi]
        if a>0 and lo<=-b/(2*a)<=hi:
            candidates.append(-b/(2*a))
        minimum=min(f(r) for r in candidates)
        assert minimum>=0,(e,lo,hi,a,b,c)
        print('e=',e,'interval',lo,hi,'coefficients',a,b,c,'minimum',minimum)
    # Both kernels vanish at every radius >= 3.
    # F(base)=sqrt(3)/(4*pi)-1/12 > 1/20 from sqrt(3)>17/10, pi<22/7.
    assert Q(17,10)**2<3
    assert Q(17,10)*Q(7,88)-Q(1,12)>Q(1,20)
    # E F(X) = (16/49) E[(-13-20cos(theta))/16]_+.
    # The integrand is at most 7/16 and its nonzero region has fraction <= 1/3.
    assert Q(5,14)-Q(3,98)-Q(16,49)==0
    assert Q(16,49)*Q(7,48)==Q(1,21)
    assert Q(1,20)-Q(1,21)==Q(1,420)
    print('All-radius Jensen tests and strict separation > 1/420: passed')

if __name__=='__main__': check()
