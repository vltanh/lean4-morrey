"""Exact rational symbolic certificate that componentwise heat flow need not
lower energy even for a smooth, uniformly rank-one-convex polyconvex integrand.

On the 2π-periodic torus set
  u(x,y) = -2 cos x - 2 cos y
  v(x,y) = 5 cos(x+y) + 5 cos(x-y) + 2 cos(2x) + 2 cos(2y).
Then for u_t,v_t evolved by heat and f(A)=det(A)^2 + eta |A|_F^2,
normalized energy derivative is 20 - 336 eta at t=0.
For every eta>0, rescale (u,v) by s with s^2>84 eta/5 to make
energy derivative >0, despite f being uniformly strictly rank-one convex.
"""
import sympy as s
x,y,t,eta,amp=s.symbols('x y t eta amp',real=True)
U=-2*s.exp(-t)*(s.cos(x)+s.cos(y))
V=5*s.exp(-2*t)*(s.cos(x+y)+s.cos(x-y))+2*s.exp(-4*t)*(s.cos(2*x)+s.cos(2*y))
J=s.trigsimp(s.diff(U,x)*s.diff(V,y)-s.diff(U,y)*s.diff(V,x),method='fu')
Jwant=(20*s.exp(-3*t)-16*s.exp(-5*t))*s.sin(x)*s.sin(y)*(s.cos(y)-s.cos(x))
assert s.trigsimp(J-Jwant,method='fu')==0
# Averaging the square of the sin/cos factor over the 2D torus.
Q=s.sin(x)**2*s.sin(y)**2*(s.cos(y)-s.cos(x))**2
avg=s.integrate(s.integrate(s.expand_trig(s.expand(Q)),(x,0,2*s.pi)),(y,0,2*s.pi))/(4*s.pi**2)
assert s.simplify(avg-s.Rational(1,8))==0
E_det=s.Rational(1,8)*(20*s.exp(-3*t)-16*s.exp(-5*t))**2
E_grad=4*s.exp(-2*t)+50*s.exp(-4*t)+16*s.exp(-8*t)
assert E_det.subs(t,0)==2
assert s.diff(E_det,t).subs(t,0)==20
assert E_grad.subs(t,0)==70
assert s.diff(E_grad,t).subs(t,0)==-336
E=amp**4*E_det+eta*amp**2*E_grad
assert s.simplify(s.diff(E,t).subs(t,0) - (20*amp**4-336*eta*amp**2))==0
print('exact Jacobian identity: PASS')
print('trigonometric average: 1/8')
print('E_det(0)=2; E_det_prime(0)=20')
print('E_dirichlet(0)=70; E_dirichlet_prime(0)=-336')
print('E_eta_prime(0) = 20 s^4 - 336 eta s^2')
print('For eta>0 and s^2>84 eta/5, E_eta_prime(0)>0')
