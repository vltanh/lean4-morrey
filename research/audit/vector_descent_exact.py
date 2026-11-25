"""Exact algebra supporting the projection normal-stress obstruction and heat certificate."""
from fractions import Fraction as Q
import sympy as S

# Explicit local map v=(r-1,k theta) near (1,0), R=1.
r,k=S.symbols('r k',positive=True)
t=k/r
flux=4*(1-t*t)/r
assert S.simplify(S.diff(flux,r)-4*(-1+3*t*t)/r**2)==0
rho=Q(1,100); k0=Q(4,5)
assert 1-rho>k0 and 3*k0*k0>(1+rho)**2
# Lower bound for positive derivative on the entire ball:
positive=4*(3*k0*k0-(1+rho)**2)/(1+rho)**4
assert positive>0
print('Exact local quartic normal-stress obstruction:',positive)
# Analytic implicit equation for a matrix with top singular value R.
R,T,p,q,j,w=S.symbols('R T p q j w',real=True)
A=S.Matrix([[p,q],[j,w]])
H=S.expand((R**2*S.eye(2)-A.T*A).det())
subs={p:R,q:0,j:0,w:T}
assert S.expand(H.subs(subs))==0
assert S.factor(S.diff(H,p).subs(subs))==-2*R*(R**2-T**2) or S.simplify(S.diff(H,p).subs(subs)+2*R*(R**2-T**2))==0
assert all(S.simplify(S.diff(H,k).subs(subs))==0 for k in (q,j,w))
# Off-diagonal shear Hessian formula.
x,y,fx,fy=S.symbols('x y fx fy', positive=True)
s0=x+y; d0=x-y
fs=(fx+fy)/2; fd=(fx-fy)/2
assert S.simplify((fy/y-fx/x)/4-(d0*fs-s0*fd)/(s0**2-d0**2))==0
print('Exact implicit constraint jet and shear Hessian identities passed')
# Two-block heat-flow algebra and cancellation of a constant determinant coefficient.
u,v,p,q,a,b=S.symbols('u v p q a b',real=True)
c=a+v+q; d=u-p-b
Jz=u*b-v*a; Jw=p*d-q*c
energy=u*u+v*v+a*a+b*b-p*p-q*q-c*c-d*d
assert S.expand(energy-2*(Jz+Jw))==0
print('Exact heat-flow determinant cancellation passed')
