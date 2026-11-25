"""Exact rational controls for the quantitative trap separation note.
These tests check matrix normalization, finite moments, and a smooth-product
plateau construction's weights. The analytic inequalities are proved by hand.
"""
from fractions import Fraction as Q
from itertools import product

I=(Q(1),Q(0),Q(0),Q(1))
Z=(Q(0),)*4

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(s,a): return tuple(s*x for x in a)
def det(a): return a[0]*a[3]-a[1]*a[2]
def trace(a): return a[0]+a[3]
def norm2(a): return sum(x*x for x in a)
def tr(a): return (a[0],a[2],a[1],a[3])
def mul(a,b): return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2)) for i,j in product(range(2),repeat=2))
def inv(a): return scale(1/det(a),(a[3],-a[1],-a[2],a[0]))
def mean(xs,ws): return tuple(sum(w*x[i] for x,w in zip(xs,ws)) for i in range(4))

def control(points,weights):
    # Original trap centered at 0, det(X-I)=1; normalize by I-X.
    points=[tuple(map(Q,x)) for x in points]
    assert mean(points,weights)==Z
    assert all(det(x)==trace(x) for x in points)
    S=[sub(I,x) for x in points]
    assert all(x==tr(x) and det(x)==1 for x in S)
    assert mean(S,weights)==I
    w=sum(p for x,p in zip(S,weights) if trace(x)<0)
    M2=sum(p*norm2(x) for x,p in zip(S,weights))
    var=sum(p*norm2(sub(x,I)) for x,p in zip(S,weights))
    T=max(abs(trace(x)) for x in S)
    assert var==M2-2
    assert var<=2*T*(T+2)*w
    assert sum(p*det(x) for x,p in zip(S,weights) if trace(x)>0)==1-w
    assert w==Q(1,9)
    # Congruence is not required for the original orientation of a trap.
    # Check nonsymmetric left/right images and recovery of the normalization.
    for P,R in [((Q(2),Q(1),Q(0),Q(1)),(Q(1),Q(0),Q(1),Q(-1))),
                ((Q(1),Q(2),Q(3),Q(1)),(Q(2),Q(0),Q(1),Q(1)))]:
        B=(Q(3),Q(-2),Q(1),Q(5))
        images=[add(B,mul(mul(P,x),R)) for x in S]
        b=mean(images,weights)
        assert b==add(B,mul(P,R))
        assert all(det(sub(x,B))==det(P)*det(R) for x in images)
        assert all(mul(mul(inv(P),sub(x,B)),inv(R))==y for x,y in zip(images,S))
        assert sum(p*det(x) for x,p in zip(images,weights))==det(b)
    return var,M2,T,w


def main():
    v,m,t,w=control([(-1,0,0,Q(1,2)),(Q(1,2),0,0,-1),(2,0,0,2)],[Q(4,9),Q(4,9),Q(1,9)])
    assert (v,m,t,w)==(2,4,Q(5,2),Q(1,9))
    assert w/(3*2+2)==Q(1,72)
    print('2D trap: variance=2, E|X|^2=4, opposite mass=1/9, W2 lower bound=1/72')
    v,m,t,w=control([(-1,0,0,Q(1,2)),(Q(1,2),0,0,-1),(Q(-1,25),Q(-18,25),Q(-18,25),Q(-23,50)),(Q(-23,50),Q(18,25),Q(18,25),Q(-1,25)),(2,0,0,2)],[Q(2,9)]*4+[Q(1,9)])
    print('3D trap and four nonsymmetric affine normalization controls: passed')
    # Positive plateaus after convolution with a mollifier of radius 1/36.
    p=[Q(1,3)]*3; q=[Q(4,9),Q(4,9),Q(1,9)]; vals=[Q(-1),Q(1,2),Q(2)]
    radius=Q(1,36); alpha=Q(1,9)
    assert sum(a*x for a,x in zip(p,vals))==Q(1,2)
    assert sum(a*x for a,x in zip(q,vals))==0
    for i,j,w in [(0,1,Q(4,9)),(1,0,Q(4,9)),(2,2,Q(1,9))]:
        assert (p[i]-2*radius)*(q[j]-2*radius)>=alpha*w
    b=(Q(1,2),Q(0),Q(0),Q(0)); tail=scale(1/(1-alpha),b)
    assert tail==(Q(9,16),0,0,0)
    assert det(tail)==det(b)==0 and add(scale(alpha,Z),scale(1-alpha,tail))==b
    print('smooth-product plateau mass, exact trapped-branch weights, and rank-one child means: passed')

if __name__=='__main__': main()
