"""Algebra checks supporting the analytic proof; no finite test implies the theorem."""
from fractions import Fraction as Q
from itertools import product
import sympy as S
l1,l2,t,b,d=S.symbols('l1 l2 t b d', real=True, nonzero=True)
H=(l1+l2)/2
P=S.diag(l1,l2)
Y=S.Matrix([[t,b],[0,d/t]])
assert S.det(Y-t*S.eye(2))==0
assert S.simplify(t*t*H+t*S.trace(P.T*(Y-t*S.eye(2)))-((l1-l2)*t*t/2+l2*d))==0
print('Exact rank-one tangent identity passed.')
# Right normalization and the lifted support. Use a rational nonorthogonal base.
a,b,c,d,h,k=S.symbols('a b c d h k', real=True)
A=S.Matrix([[2,1],[1,1]])
X=S.Matrix([[a,b],[c,d]])
Y=X*A.inv()
assert S.expand(Y.det()-X.det()/A.det())==0
# A polynomial graph lift is full: average det(X+H),det(X-H)=det X+det H.
D=S.Matrix([[1,0],[0,k]])
assert S.expand(((X+D).det()+(X-D).det())/2-X.det()-k)==0
print('Exact normalized minors and lifted convex-extension identities passed.')
# Real-spectrum conditions for trace-free coordinates, and symmetrizer at polar maximum.
u,v,w,k=S.symbols('u v w k', real=True)
M=S.Matrix([[u+v,w-k],[w+k,u-v]])
assert S.expand(S.trace(M)**2-4*M.det()-4*(v*v+w*w-k*k))==0
p,q=S.symbols('p q', real=True)
N=S.Matrix([[a,b],[c,d]])
assert S.expand((N*S.diag(p,q))[0,1]-(N*S.diag(p,q))[1,0]-(b*q-c*p))==0
# A concrete anisotropic, frame-indifferent but not right-rotation invariant PC example.
# max(|X e1|^2-2 det X, 3 |X e2|^2+det X).
def f(X):
    return max((X[:,0].dot(X[:,0])-2*X.det()), (3*X[:,1].dot(X[:,1])+X.det()))
J=S.Matrix([[0,-1],[1,0]])
D=S.diag(2,1)
assert f(J*D)==f(D) and f(D*J)!=f(D)
# Every elementary support is convex+det: exact rank-one second derivative.
r,s,v1,v2,t=S.symbols('r s v1 v2 t', real=True)
R=S.Matrix([r,s])*S.Matrix([[v1,v2]])
for vv in (S.Matrix([1,0]),S.Matrix([0,1]),S.Matrix([1,2])):
    L=X+t*R
    E=(L*vv).dot(L*vv)-2*L.det()
    assert S.expand(S.diff(E,t,2)-2*(R*vv).dot(R*vv))==0
print('Exact real-spectrum, frame-indifference, and generator Hessian identities passed.')
