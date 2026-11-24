"""Rational controls for the finite-ray transfer gadget (not an analytic proof)."""
from fractions import Fraction as Q
from itertools import product

def det(x):
    return x[0]*x[3]-x[1]*x[2]

def norm2(x):
    return sum(z*z for z in x)

# A product of four coordinate splits is a rank-one laminate in 2x2.
# Its favored vertex y receives mass >= 1-sum_i |x_i-y_i|/t.
# Test nonunit, signed coordinates and boundary cases as well.
y = (Q(2,3), Q(-1,3), Q(2,3), Q(0))  # norm 1
assert norm2(y)==1
n=0
for t in (Q(1,2), Q(1), Q(3)):
    Y=tuple(t*z for z in y)
    for delta in product((Q(-1,4), Q(0), Q(1,4)),repeat=4):
        X=tuple(a+t*d for a,d in zip(Y,delta))
        far=tuple(a+t*(1 if d>=0 else -1) for a,d in zip(Y,delta))
        w=tuple(abs(d) for d in delta)
        atoms=[]
        for b in product((0,1),repeat=4):
            v=tuple(far[i] if b[i] else Y[i] for i in range(4))
            prob=Q(1)
            for i in range(4): prob*=w[i] if b[i] else 1-w[i]
            assert prob>=0 and norm2(v)<=9*t*t
            atoms.append((v,prob))
        assert sum(z for v,z in atoms)==1
        assert tuple(sum(v[i]*z for v,z in atoms) for i in range(4))==X
        assert sum(det(v)*z for v,z in atoms)==det(X)
        assert atoms[0][1]>=1-sum(w)
        # Replacing the remaining vertices by a coordinate-cube laminate
        # uses leaves of norm <= 6t.
        for v,z in atoms[1:]:
            R=max(abs(k) for k in v)
            assert 4*R*R<=36*t*t
        n+=1
print(f'{n} exact product-split, mass, determinant and radius controls passed.')

# Every root can include an arbitrary X with distinguished mass 1/16.
A=(Q(1),Q(0),Q(0),Q(-1))
X=(Q(3,2),Q(7),Q(-2,3),Q(4))
Z=tuple(2*a-x for a,x in zip(A,X))
vertices=[tuple(X[i] if b[i]==0 else Z[i] for i in range(4)) for b in product((0,1),repeat=4)]
assert vertices[0]==X
assert tuple(sum(v[i] for v in vertices)/16 for i in range(4))==A
assert sum(det(v) for v in vertices)/16==det(A)
print('Exact root embedding identity passed.')
