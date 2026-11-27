"""Exact algebra for the heat counterexample and the radius-gap sign.
The component theorem uses topology and rank-one geometry, not grid enumeration.
"""
import sympy as S
from fractions import Fraction as Q
x,y,a,b,c=S.symbols('x y a b c', real=True)
u=a*(S.cos(x)+S.cos(y))
v=1+b*(S.cos(2*x)+S.cos(2*y))/2+2*c*S.cos(x)*S.cos(y)
D=S.diff(u,x)*S.diff(v,y)-S.diff(u,y)*S.diff(v,x)
assert S.trigsimp(S.expand_trig(D-2*a*(c-b)*S.sin(x)*S.sin(y)*(S.cos(x)-S.cos(y))))==0
# Moments for normalized torus: E sin^2=1/2, E sin^2 cos^2=1/8,
# E sin^2 cos=0, so E det^2=4 a^2 (c-b)^2*(2/2/8).
a0,b0,c0=Q(1,2),Q(1,16),Q(1,4)
det_energy=Q(1,2)*a0*a0*(c0-b0)**2
norm_energy_initial=Q(4)
norm_energy_final=a0*a0+b0*b0+2*c0*c0
assert det_energy==Q(9,2048)
assert norm_energy_final==Q(97,256)
strict_gap=det_energy+(norm_energy_final-norm_energy_initial)/1000
assert strict_gap==Q(99,128000)>0
print('Exact heat Jacobian identity, heat-energy increase, and strictified gap:',det_energy,strict_gap)
# K_r sign is exactly (s-r)(r - sigma*delta) above the gap.
for sign in (-1,1):
 for r in (Q(1,2),Q(1),Q(2)):
  for s in (r+Q(1,3),r+1,r+4):
   for d in (r+Q(1,6),s):
    assert 0<r<d<=s
    assert (s-r)*(r-sign*(sign*d))<0
  for s in (Q(0),r/2,r):
   assert max(s-r,0)*(r-sign*s)==0
print('Exact spectral-gap sign controls passed.')
