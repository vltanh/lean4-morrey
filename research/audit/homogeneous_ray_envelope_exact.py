"""Exact arithmetic for ray-envelope geometry; not a proof of QC or viscosity theory."""
from fractions import Fraction as Q
from itertools import product
# Each sequential coordinate split has rank-one increment in a matrix entry.
# The 16-vertex product distribution has the correct mean and determinant.
count=0
for x in product([Q(-1),Q(-2,3),Q(0),Q(1,3),Q(1)],repeat=4):
    weights=[]
    for sign in product((-1,1),repeat=4):
        w=Q(1)
        for i in range(4): w*= (1+sign[i]*x[i])/2
        weights.append((sign,w))
    assert all(w>=0 for s,w in weights)
    assert sum(w for s,w in weights)==1
    assert all(sum(s[i]*w for s,w in weights)==x[i] for i in range(4))
    assert sum((s[0]*s[3]-s[1]*s[2])*w for s,w in weights)==x[0]*x[3]-x[1]*x[2]
    count+=1
print(f'{count} exact rank-one coordinate splitting controls passed.')
# Separate-convex lower-bound geometry: for y in [-1,1] and z in [-1/2,1/2],
# z = theta*y+(1-theta)*endpoint, with endpoint in {-2,2}, theta >= 1/2.
count=0
for y in [Q(i,8) for i in range(-8,9)]:
    for z in [Q(i,8) for i in range(-4,5)]:
        endpoint=Q(2) if z>=y else Q(-2)
        theta=(endpoint-z)/(endpoint-y)
        assert Q(1,2)<=theta<=1
        assert theta*y+(1-theta)*endpoint==z
        count+=1
assert Q(1,2)**4==Q(1,16)
# Rounding to integer vectors at radius n: each coordinate error <=1/2,
# so norm error <=1 and radial normalization changes distance by <=2/n.
assert 4*Q(1,2)**2==1
print(f'{count} exact signed separate-convex interpolation controls passed.')
