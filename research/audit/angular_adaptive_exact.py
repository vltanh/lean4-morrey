"""Exact examples and identities for the degree-two angular splitting argument."""
from fractions import Fraction as Q
import sympy as sp

# The following calculations use non-unit ray generators (v_i). For degree
# two, changing a generator v_i -> v_i/|v_i| changes the angular coefficient
# a_i -> |v_i|^2 a_i and the first-moment coefficient s_i -> |v_i| s_i.
# Thus sum s_i^2/a_i is invariant. Work on diagonal matrices, coordinates a,d.
V = sp.Matrix([[0, sp.Rational(3,2), 3], [sp.Rational(5,2), 1, 4]])
b = sp.Matrix([1,2])
a = sp.Matrix([sp.Rational(4,9), sp.Rational(4,9), sp.Rational(1,9)])
d = sp.Matrix([V[0,i]*V[1,i] for i in range(3)])
assert V*a == b and d.dot(a)==2
# Original law is blocked in its affine plane: det(Y)=tr(Y).
for i in range(3):
    y=V[:,i]-b
    assert y[0]*y[1]==sum(y)
# Radius change with fixed angular second moments and fixed barycenter.
k=V.nullspace()[0]
if sum(k)>0:k=-k
assert sum(k)<0
s=a+sp.Rational(1,100)*k
assert V*s==b and all(x>0 for x in s)
slack=sp.factor(1-sum(s[i]**2/a[i] for i in range(3)))
assert slack>0
# Nonzero rank-one shift of the root, with corresponding angular weight shift.
H=sp.Matrix([1,0]); ds=sp.Matrix([-sp.Rational(4,15), sp.Rational(2,3),0]); h=sp.Matrix([0,sp.Rational(4,3),0])
assert V*ds==H and d.dot(h)==2
eta=sp.Rational(1,10000)
for sign in (-1,1):
    ss=s+sign*eta*ds; aa=a+sign*eta*h; bb=b+sign*eta*H
    assert all(t>0 for t in ss) and all(t>0 for t in aa)
    assert V*ss==bb and d.dot(aa)==bb[0]*bb[1]
    assert sum(ss[i]**2/aa[i] for i in range(3))<1
print('Blocked ordinary law has exact angular split; moment slack =',slack)

# A genuinely blocked generalized tight state: two finite matrices and
# concentration at a single opposite-determinant ray. F(a,b,c,d)=a_+d_+ +
# (b^2+c^2)/2 is RC (analytic proof in note).
e=sp.Rational(1,4)
X1=sp.diag(1+e,1-e); X2=sp.diag(1-e,1+e); Z=-sp.eye(2)
weights=[sp.Rational(1,2),sp.Rational(1,2),e**2]
assert (X1+X2)/2==sp.eye(2)
assert sum(w*x.det() for w,x in zip(weights,[X1,X2,Z]))==1
ell=lambda X:sp.trace(X)/2
assert ell(X1)==ell(X2)==1 and ell(Z)==-1
assert sum(w*max(ell(x),0)**2 for w,x in zip(weights,[X1,X2,Z]))==1
assert (X1-X2).det()<0
F=lambda X:max(X[0,0],0)*max(X[1,1],0)+(X[0,1]**2+X[1,0]**2)/2
gap=sum(w*F(x) for w,x in zip(weights,[X1,X2,Z]))-F(sp.eye(2))
assert gap==-e**2
print('Tight concentration state has exact homogeneous RC gap =',gap)

# Determinant moment under symmetric rank-one shifts and scaling.
A=sp.Matrix(2,2,sp.symbols('a0:4')); u=sp.Matrix(sp.symbols('u0:2')); v=sp.Matrix(sp.symbols('v0:2')); t=sp.symbols('t'); R=u*v.T
assert sp.expand((A+t*R).det()-A.det()-t*sp.diff((A+t*R).det(),t).subs(t,0))==0
x,y,k=sp.symbols('x y k',positive=True)
assert sp.simplify((x/sp.sqrt(k))**2/(y/k)-x**2/y)==0
print('Rank-one determinant shift and normalization identities passed.')
