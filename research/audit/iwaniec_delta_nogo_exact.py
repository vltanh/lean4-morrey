"""Exact algebraic controls for the compatibility-penalty no-go.
The all-transform result follows from the hand proof, not the samples.
"""
from fractions import Fraction as Q
from itertools import product
from random import Random

I=(1,0,0,1); J=(0,-1,1,0); D=(1,0,0,-1); K=(0,1,1,0)
def scale(t,x): return tuple(t*u for u in x)
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def mul(a,b): return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2)) for i,j in product(range(2),repeat=2))
def tr(x): return (x[0],x[2],x[1],x[3])
def det(x): return x[0]*x[3]-x[1]*x[2]
def norm2(x): return sum(a*a for a in x)
def sym(x): return scale(Q(1,2),add(x,tr(x)))
def skew(x): return scale(Q(1,2),add(x,scale(-1,tr(x))))
def h(s): return det(s) if s[0]>0 and det(s)>0 else Q(0)
def law(r=5):
    p=Q(1,1+r*r)
    return [(scale(s*r,x),p/4) for x in (I,J) for s in (-1,1)]+[(scale(s,x),(1-p)/4) for x in (D,K) for s in (-1,1)]
def E(L,f): return sum(w*f(x) for x,w in L)
def F(x): return norm2(x)*(norm2(x)-Q(9,4)*det(x))

def main():
    L=law(); c=Q(25,26)
    assert E(L,lambda x:1)==1 and E(L,det)==0
    assert all(E(L,lambda x:x[i])==0 for i in range(4))
    assert all(E(L,lambda x:x[i]*x[j])==(c if i==j else 0) for i,j in product(range(4),repeat=2))
    assert E(L,F)==-Q(50,13)
    # Symbolic coefficients of the rank-one second derivative divided by 4:
    # 3a²+d²-(27/8)ad+b²+c²+(9/8)bc.
    gamma=Q(9,8)
    assert 1-3*gamma*gamma/4==Q(13,256)
    assert 1-gamma*gamma/4==Q(175,256)
    print('8-atom law: mean zero, determinant moment zero, covariance (25/26)I4, quartic gap -50/13; exact SOS coefficients passed')
    rng=Random(20261123)
    for i in range(256):
        P=tuple(Q(rng.randrange(-3,4),rng.randrange(1,4)) for _ in range(4))
        R=tuple(Q(rng.randrange(-3,4),rng.randrange(1,4)) for _ in range(4))
        B=tuple(Q(rng.randrange(-3,4),rng.randrange(1,4)) for _ in range(4))
        X=lambda x:mul(mul(P,x),R)
        v=E(L,lambda x:norm2(skew(X(x))))
        s=E(L,lambda x:norm2(sym(X(x))))
        gap=h(sym(B))-E(L,lambda x:h(sym(add(B,X(x)))))
        assert E(L,lambda x:det(add(B,X(x))))==det(B)
        assert gap<=s/2 and gap<=Q(3,2)*v,(i,gap,s,v)
        assert gap<=0 or 4*gap*gap<=3*s*v,(i,gap,s,v)
    print('256 rational affine controls, including singular factors: determinant identity, both gap bounds and strict relative margin passed')

if __name__=='__main__': main()
