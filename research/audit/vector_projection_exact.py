"""Exact algebra checks for vector operator-ball projection calibration.
Analytic local selection uses Kirszbraun, not this finite check.
"""
from fractions import Fraction as Q
from itertools import product

for k in [Q(1,i) for i in range(1,81)]:
    tau=k/320
    eps=k*tau/4
    assert 0<tau<Q(1,4)
    assert 5*eps/4<k*tau
    assert Q(3,4)-Q(5,4)/4>=Q(1,4)
    assert (1-tau)**2>Q(1,2)
    assert 1-(1-tau)**2<=2*tau
    assert k*tau/32-5*tau*tau==k*k/20480>0
print('Exact local comparison constants: passed')

def profile(s,d,r,lam,eta,gamma):
    x,y=(s+d)/2,(s-d)/2
    a,b=abs(lam+eta),abs(lam-eta)
    q=a*x-b*y+gamma*r
    t=max(-r,min(r,q/(2*lam)))
    C=r*(a*x+b*y)-lam*r*r+q*t-lam*t*t
    H=max((gamma+2*eta)*s*d,C) if s<=r else C
    return H,C,t

n=0
for r,lam,eta,gamma in product((Q(1),Q(3,2)),(Q(1,2),Q(1),Q(2)),(Q(-2),Q(-1,3),Q(0),Q(2)),(Q(-1),Q(0),Q(3,2))):
    for d in [r*Q(i,5) for i in range(-5,6)]:
        s=r
        H,C,t=profile(s,d,r,lam,eta,gamma)
        assert C>=(gamma+2*eta)*s*d
        assert H==C
        x,y=(s+d)/2,(s-d)/2
        a,b=abs(lam+eta),abs(lam-eta)
        for tt in [r*Q(i,8) for i in range(-8,9)]:
            for ez,ew in product((-1,1),repeat=2):
                value=(lam+eta)*(r+tt)*x*ez+(lam-eta)*(r-tt)*y*ew+gamma*r*tt-lam*(r*r+tt*tt)
                assert C>=value
        ez=1 if lam+eta>=0 else -1;ew=1 if lam-eta>=0 else -1
        assert C==(lam+eta)*(r+t)*x*ez+(lam-eta)*(r-t)*y*ew+gamma*r*t-lam*(r*r+t*t)
        n+=1
print(f'Exact boundary maximum and interface contact: {n} rational controls passed')
