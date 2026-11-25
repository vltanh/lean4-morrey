"""Exact algebra checks for homogeneous angular curvature duality.
The measure duality and compactness arguments are analytic.
"""
import sympy as s
from fractions import Fraction as Q
from itertools import product

u=s.Matrix(s.symbols('u0:4', real=True))
h=s.Matrix(s.symbols('h0:4', real=True))
p=s.symbols('p', real=True)
a=u.dot(h)
w=h-a*u
C=s.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
# Scalar radial extension on a unit sphere slice.
t=s.symbols('t',real=True)
alpha,b=s.symbols('alpha b',real=True)
r=s.sqrt(1+2*alpha*t+(alpha**2+b**2)*t**2)
U=(1+alpha*t)/r; V=b*t/r
# Quadratic polynomial suffices to verify its arbitrary value/first/second jet.
P0,Pu,Pv,Puu,Puv,Pvv=s.symbols('P0 Pu Pv Puu Puv Pvv',real=True)
P=P0+Pu*(U-1)+Pv*V+Puu*(U-1)**2/2+Puv*(U-1)*V+Pvv*V**2/2
actual=s.diff(r**p*P,t,2).subs(t,0)
expected=Pvv*b*b+(p*P0-Pu)*b*b+2*alpha*(p-1)*Pv*b+p*(p-1)*P0*alpha**2
assert s.simplify(actual-expected)==0
# For homogeneous quadratic determinant, its radial extension at p=2 is itself.
D=(u.T*C*u)[0]/2
DP=C*u
L=(w.T*C*w)[0]+(2*D-DP.dot(u))*w.dot(w)+2*a*DP.dot(w)+2*D*a*a
assert s.expand(L-(h.T*C*h)[0])==0
# Tensor contractions and the constant-function angular Hessian.
M=s.Matrix(4,4,lambda i,j:s.Symbol(f'm{min(i,j)}{max(i,j)}',real=True))
basis=s.eye(4)
T=basis-u*u.T
A=(u.T*M*u)[0]; B=T*M*u; K=T*M*T
assert s.expand(A*u*u.T+u*B.T+B*u.T+K-M)==s.zeros(4)
assert s.expand(s.trace(C*M)-(A*(u.T*C*u)[0]+2*(C*u).dot(B)+s.trace(C*K)))==0
print('Exact radial Hessian, determinant, and tensor-decomposition identities passed.')
# Balanced covariance rotation identities.
x=s.Matrix(s.symbols('x0:4',real=True)); y=s.Matrix(s.symbols('y0:4',real=True))
z=s.symbols('z',real=True)
P=(x+z*y)/s.sqrt(1+z*z); R=(-z*x+y)/s.sqrt(1+z*z)
assert s.simplify(P*P.T+R*R.T-x*x.T-y*y.T)==s.zeros(4)
assert s.simplify((P.T*C*P)[0]+(R.T*C*R)[0]-(x.T*C*x)[0]-(y.T*C*y)[0])==0
print('Exact balanced covariance rotation identities passed.')
# Uniform finite-degree distance error arithmetic.
d,dn,e,A0,W=s.symbols('d dn e A0 W', nonnegative=True)
assert s.cancel((1+e)*(dn-(d-e*(A0+W))/(1+e))-((1+e)*dn-d+e*(A0+W)))==0
# The order-unit mass bound: L_p 1 = p[1+(p-2) alpha^2].
count=0
for pp,aa in product([Q(5,4),Q(3,2),Q(2),Q(5,2),Q(4)],[Q(i,8) for i in range(-8,9)]):
    ell=pp*(1+(pp-2)*aa*aa)
    assert pp*min(Q(1),pp-1)<=ell<=pp*max(Q(1),pp-1)
    count+=1
print(f'Exact finite-degree distance inequality and {count} order-unit bounds passed.')
