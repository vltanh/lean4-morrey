#!/usr/bin/env python3
"""Exact full-stationary-lift controls; not a planar counterexample search."""
import sympy as s
from itertools import product

J=s.Matrix([[0,-1],[1,0]])
C=s.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
I=s.eye(2)

def mat(x): return s.Matrix(2,2,list(x))
def col(x): return s.Matrix(list(x))
def cof(X): return mat(C*col(X))
def dot(X,Y): return (col(X).T*col(Y))[0]

# Full-lift null rank-one tangent and exact second derivative.
X=s.Matrix(2,2,s.symbols('x0:4')); p=s.Matrix(2,2,s.symbols('p0:4'))
a=s.Matrix(s.symbols('a0:2')); n=s.Matrix(s.symbols('n0:2')); c=s.symbols('c')
R=a*n.T; HR=c*cof(R)
assert (R.T*cof(R)).applyfunc(s.expand)==s.zeros(2)
D=((dot(p,R))*I-R.T*p-X.T*HR)*J
# Check rows have common right direction n, even for arbitrary X,p.
assert (D*J*n).applyfunc(s.expand)==s.zeros(2,1)
assert (cof(HR)-c*R).applyfunc(s.expand)==s.zeros(2)
# For a null rank-one direction, v=D^3F[R,R,.]=0; the second
# derivative of every lifted block then vanishes.
assert dot(R,HR).expand()==0
assert ((dot(R,HR)*I-2*R.T*HR)*J).applyfunc(s.expand)==s.zeros(2)
# Full chain rule for an arbitrary cubic jet at one point.
x=s.Matrix(2,2,s.symbols('y0:4')); h=s.Matrix(2,2,s.symbols('h0:4'))
y=col(x); H0=s.Matrix([[2,1,-2,1],[1,3,0,-1],[-2,0,4,2],[1,-1,2,5]])
f=(y.T*H0*y)[0]/2 + y[0]*y[1]*y[3]+2*y[2]**3
p0=mat(s.Matrix([s.diff(f,v) for v in y])); T=f*I-x.T*p0
jet=s.symbols('t'); sub=dict(zip(y,col(x+jet*h)))
q=mat(s.hessian(f,list(y))*col(h))
v=mat(s.Matrix([s.diff(dot(q,h),z) for z in y]))
first=((dot(p0,h)*I-h.T*p0-x.T*q)*J)
second=((dot(q,h)*I-2*h.T*q-x.T*v)*J)
assert ((T*J).subs(sub,simultaneous=True).diff(jet).subs(jet,0)-first).applyfunc(s.expand)==s.zeros(2)
assert ((T*J).subs(sub,simultaneous=True).diff(jet,2).subs(jet,0)-second).applyfunc(s.expand)==s.zeros(2)
print('Full-lift symbolic null-direction and general first/second jet identities passed.')

# Three-wave exactness: the wedge coefficients are independent.
# At (pi/2,pi/2),(pi/2,0),(0,pi/2), they isolate all three pairs.
x0,y0=s.symbols('x y',real=True)
r=[s.cos(x0),s.cos(y0),s.cos(x0+y0)]
coeff=[s.diff(r[i],x0)*s.diff(r[j],y0)-s.diff(r[i],y0)*s.diff(r[j],x0) for i,j in [(0,1),(0,2),(1,2)]]
E=s.Matrix([[q.subs({x0:x,y0:y}) for q in coeff] for x,y in [(s.pi/2,s.pi/2),(s.pi/2,0),(0,s.pi/2)]])
assert abs(E.det())==1
print('Sverak three-wave exterior-derivative independence control passed.')

# Cassese/Dragicevic canonical power-field direct stress compatibility.
a0=s.symbols('alpha',real=True)
A=-a0*(2-a0); B=a0*(1+a0); D=A; C0=(2-a0)*(1-a0)
# Stress p has complex coefficients C0 and -D exp(i theta).
ac=A*C0; bd=-B*D
assert s.expand(ac+3*bd-2*a0*(2-a0)*(a0*a0+3*a0-1))==0
# If direct integrability holds, C0=3 B, so K has positive density.
Y=2*(3*B)**2; X2=3*B**2
assert s.expand(30*X2**2+20*X2*Y-2*Y**2-702*B**4)==0
av=s.Rational(1,4)
xx=(3*B**2).subs(a0,av); yy=(2*C0**2).subs(a0,av)
k=s.factor(30*xx**2+20*xx*yy-2*yy**2)
assert k==-s.Rational(32049,32768)
assert (ac+3*bd).subs(a0,av)!=0
print('Cassese direct power-field control: negative quartic density at alpha=1/4, failed exactness.')

# The row-remixed power field can be closed as a one-form even at alpha=1/4.
# M(s,theta)=s*M(theta), no rho factor in second block (absorb it in row mixing).
t=s.symbols('t',real=True)
M=s.Matrix([[A*s.cos(t)+B*s.cos(2*t),-A*s.sin(t)+B*s.sin(2*t)],
            [A*s.sin(t)+B*s.sin(2*t), A*s.cos(t)-B*s.cos(2*t)],
            [C0+D*s.cos(t),D*s.sin(t)],
            [D*s.sin(t),C0-D*s.cos(t)]]).subs(a0,av)
S=s.diag(-49,-49,1,1)
expr=(M[:,0].T*S*M.diff(t)[:,1]-M.diff(t)[:,0].T*S*M[:,1])[0]
assert s.trigsimp(s.expand_trig(expr))==0
# Explicit remix: U=Z0+7 X0, V=J (Z0-7 X0), p=cof V.
U=M[2:,:]+7*M[:2,:]; V=J*(M[2:,:]-7*M[:2,:]); P=cof(V)
assert s.trigsimp(s.expand_trig(U.det()-s.Rational(49,8)*(1-s.cos(t))))==0
energy=dot(P,U)/2
print("remix energy", s.trigsimp(s.expand_trig(energy)))
assert s.trigsimp(s.expand_trig(energy-s.Rational(49,8)*s.sin(t)))==0 or s.trigsimp(s.expand_trig(energy+s.Rational(49,8)*s.sin(t)))==0
# The integral one-form is closed, but determinant support fails at theta=0.
assert s.trigsimp(s.expand_trig(dot(P,U.diff(t))-s.diff(energy,t)))==0
print('Split-signature row remix passes exactness; this remix violates degree-two determinant support near theta=0.')
print('All controls passed; no unrestricted positivity or negative planar witness.')
