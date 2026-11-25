from fractions import Fraction as Q
from itertools import product

# Mixed atomic and diffuse radial curvatures:
# Mu+ = 2 delta_1 + dr on [1,3], Mu- = 3 delta_2 + 2 dr on [1,3].
def moments(s,e):
    r0,w=(Q(1),Q(2)) if e==1 else (Q(2),Q(3))
    density=Q(1) if e==1 else Q(2)
    b=min(s,Q(3)); a=Q(1)
    T=[w*r0**j if s>r0 else Q(0) for j in range(3)]
    if b>a:
        T=[v+density*(b**(j+1)-a**(j+1))/(j+1) for j,v in enumerate(T)]
    return T

def K(s,d,r,e): return max(s-r,0)*(r+e*d)

def integ(s,d,e):
    T=moments(s,e)
    return s*T[1]-T[2]+e*d*(s*T[0]-T[1])

def I(s):
    b=max(Q(1),min(s,Q(3)))
    return (Q(7)+2*s+2*max(s-1,0)+6*max(s-2,0)
            +3*(s*(b*b-1)/2-(b**3-1)/3))

def M(s):
    b=max(Q(1),min(s,Q(3)))
    return (Q(1)-s/2+2*max(s-1,0)-3*max(s-2,0)
            -(s*(b-1)-(b*b-1)/2))

def deriv(s):
    plus,minus=moments(s,1),moments(s,-1)
    return Q(2)+plus[1]+minus[1],-Q(1,2)+plus[0]-minus[0]

for s in [Q(i,4) for i in range(1,25) if i not in (4,8,12)]:
    i,m=deriv(s)
    assert i>=abs(M(s)-s*m)
    for t in (Q(-1),Q(-2,3),Q(0),Q(1,3),Q(1)):
        d=s*t
        assert I(s)+M(s)*d==7+2*s+d-s*d/2+integ(s,d,1)+integ(s,d,-1)
        for eps in (Q(1,4),Q(5,4),Q(9,4)):
            if eps>s: continue
            ip,mp=deriv(eps)
            q=I(eps)+ip*(s-eps)+(M(eps)-eps*mp)*d+mp*s*d
            v=q
            for e in (-1,1):
                t0,t1,t2=[a-b for a,b in zip(moments(s,e),moments(eps,e))]
                v+=s*t1-t2+e*d*(s*t0-t1)
            assert v==I(s)+M(s)*d
print('exact mixed atomic/diffuse curvature representation and truncation: passed')

# Compression preserves affine-shell observables and lowers convex-in-delta tests.
law=[(Q(2),Q(-1),Q(1,6)),(Q(2),Q(1),Q(1,3)),
     (Q(3),Q(-2),Q(1,4)),(Q(3),Q(2),Q(1,4))]
compressed=[]
for s in sorted(set(x[0] for x in law)):
    mass=sum(w for r,d,w in law if r==s)
    mean=sum(w*d for r,d,w in law if r==s)/mass
    compressed.append((s,mean,mass))
def E(nu,f): return sum(w*f(s,d) for s,d,w in nu)
for f in [lambda s,d:s,lambda s,d:d,lambda s,d:s*d,lambda s,d:I(s)+M(s)*d]+[lambda s,d,r=r,e=e:K(s,d,r,e) for r,e in product((Q(1,2),Q(1),Q(2),Q(5,2),Q(3),Q(4)),(-1,1))]:
    assert E(law,f)==E(compressed,f)
assert E(compressed,lambda s,d:d*d)<=E(law,lambda s,d:d*d)
print('exact spectral compression and kernel-moment invariance: passed')
