"""Algebra and exact controls for determinant stabilization.
The analytic proof is not replaced by these controls.
"""
from fractions import Fraction as Q
import sympy as S
from itertools import product
u,v,d,y,c,m=S.symbols('u v d y c m',real=True)
f=-u*u/2+8*u*v+S.Rational(17,2)*v*v+2*(u+v)
gp=S.expand(f.subs({u:d+y*y,v:y*y},simultaneous=True))
gm=S.expand(f.subs({u:y*y,v:d+y*y},simultaneous=True))
assert gp==-d*d/2+7*d*y*y+16*y**4+2*d+4*y*y
assert gm==S.Rational(17,2)*d*d+25*d*y*y+16*y**4+2*d+4*y*y
assert S.expand(S.diff(gp,y,2)-(14*d+192*y*y+8))==0
assert S.expand(S.diff(gm,y,2)-(50*d+192*y*y+8))==0
assert S.diff(gp,d,y)==14*y and S.diff(gm,d,y)==50*y
assert S.diff(gp,d,2)==-1 and S.diff(gm,d,2)==17
D,D0,C=S.symbols('D D0 C',real=True)
assert S.expand(C*(D-D0)**2-C*D**2+C*D0**2+2*C*D0*(D-D0))==0
r,a,b=S.symbols('r a b',positive=True)
rho=b*(r*r-a*a)**2
assert S.expand(S.diff(rho,r)/r-4*b*(r*r-a*a))==0
assert S.expand(S.diff(rho,r,2)-(4*b*(r*r-a*a)+8*b*r*r))==0
assert S.expand(4*b*(r*r-a*a)-3*b*r*r-b*(r*r-4*a*a))==0
print('Symbolic two-orientation profiles, lift shift, and radial repair Hessians passed.')
B=Q(17); L=Q(100); m0=Q(2); K=B/2+L*L/(4*m0)
assert K==Q(2517,2)
def F(x,y):return -x**4/2+8*x*x*y*y+Q(17,2)*y**4+2*(x*x+y*y)
def G(d,y,sgn):
    return (-d*d/2+7*d*y*y if sgn==1 else Q(17,2)*d*d+25*d*y*y)+16*y**4+2*d+4*y*y
def gy(d,y,sgn):return (14 if sgn==1 else 50)*d*y+64*y**3+8*y
def gd(d,y,sgn):return (-d+7*y*y if sgn==1 else 17*d+25*y*y)+2
pts=[(Q(i,4),Q(j,4)) for i in range(9) for j in range(9-i)]
count=0
for x0,y0 in pts:
 d0=x0*x0-y0*y0
 sig=1 if d0>=0 else -1
 v0=y0 if sig==1 else x0
 for x,y in pts:
  dd=sig*(x*x-y*y-d0); v=y if sig==1 else x
  for phase in (-1,1):
   diff=phase*v-v0
   lhs=F(x,y)-F(x0,y0)+K*dd*dd
   rhs=gy(abs(d0),v0,sig)*diff+gd(abs(d0),v0,sig)*dd+m0*diff*diff
   assert lhs>=rhs,(x0,y0,x,y,phase,lhs,rhs)
   count+=1
print(f'{count} exact rational compact-ball support controls passed for C={K}.')
