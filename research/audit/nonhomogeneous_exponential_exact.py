"""Symbolic identities used in the exponential reparametrization proof.
No finite test is used to infer quasiconvexity or a uniform exponent."""
import sympy as S
x,y,x0,y0,c,k,dx=S.symbols('x y x0 y0 c k dx',real=True)
b,g=S.symbols('beta gamma',nonnegative=True)
D=x*x-y*y
P=k+b*x+g*y+c*D
shift=dx*((x-x0)**2-(y-y0)**2)
Q=P+shift
assert S.simplify((Q-P).subs({x:x0,y:y0}))==0
for v in (x,y): assert S.simplify(S.diff(Q-P,v).subs({x:x0,y:y0}))==0
assert S.expand(Q-(k+dx*(x0*x0-y0*y0)+(b-2*dx*x0)*x+(g+2*dx*y0)*y+(c+dx)*D))==0
psi=(x*x-x0*x0)**2+(y*y-y0*y0)**2
assert S.hessian(psi,(x,y)).subs({x:x0,y:y0})==S.diag(8*x0*x0,8*y0*y0)
psi_conf=(x*x-x0*x0)**2+y*y
assert S.hessian(psi_conf,(x,y)).subs({x:x0,y:0})==S.diag(8*x0*x0,2)
Pcrit=2*k*x0*x-k*(x*x-y*y)-k*x0*x0
assert S.expand(Pcrit-k*(y*y-(x-x0)**2))==0
r,a,theta=S.symbols('r a theta', real=True)
assert S.expand_trig((r*S.cos(theta)-a)**2+(r*S.sin(theta))**2-(r-a)**2-2*a*r*(1-S.cos(theta))).simplify()==0
print('Exact spectral-penalty Hessians, determinant-shift first jets, critical support, and phase identity passed.')
