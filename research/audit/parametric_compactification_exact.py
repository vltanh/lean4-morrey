#!/usr/bin/env python3
"""Exact algebra controls; not a universal Morrey solver."""
import sympy as S

x,y,z,w=S.symbols('x y z w', real=True)
a=1;b=x*w-y*z
xi=S.Matrix([a,y,w,-x,-z,b])
p=S.Matrix([xi[0]+xi[5],xi[1]-xi[4],xi[2]+xi[3]])
q=S.Matrix([xi[0]-xi[5],xi[1]+xi[4],xi[2]-xi[3]])
assert S.expand(p.dot(p)-q.dot(q))==0
assert S.expand((p.dot(p)+q.dot(q))/2-(1+x*x+y*y+z*z+w*w+b*b))==0

P1,P2,P3,Q1,Q2,Q3,U1,U2,U3,V1,V2,V3=S.symbols(
    'p1 p2 p3 q1 q2 q3 u1 u2 u3 v1 v2 v3')
coords=(P1,P2,P3,Q1,Q2,Q3)
tangent=(U1,U2,U3,V1,V2,V3)
t=S.symbols('t')
polys=[1,P1,Q2,P1*Q2,P1**2*P2*Q3**2,P1**3*Q1**2+Q2*P2+2]
for f in map(S.sympify,polys):
    jet=f.subs(dict(zip(coords,[a+t*h-t*t*a/2 for a,h in zip(coords,tangent)])),
               simultaneous=True)
    second=2*S.expand((1+t*t/2)*jet).coeff(t,2)
    expect=(f-sum(a*S.diff(f,a) for a in coords)
            +sum(hi*hj*S.diff(f,a,b) for a,hi in zip(coords,tangent)
                 for b,hj in zip(coords,tangent)))
    assert S.expand(second-expect)==0

l,m,r=S.symbols('l m r', real=True)
assert S.expand(((r-l)-r)*(r-(r-m)) + l*m)==0
s,d=S.symbols('s d',real=True)
E=(1-d)*(s-(1+d)/2)
assert S.expand(E-(s-1)*(1-d)-(1-d)**2/2)==0
assert S.expand((l*l/2-l*m)-(-l*m+l*l/2))==0

T=S.symbols('T',nonnegative=True)
N=S.symbols('N',integer=True, nonnegative=True)
assert S.simplify((N+1)*S.integrate(T**N,(T,0,1))-1)==0
assert S.simplify((N+1)*S.integrate(4*(1-T)*T**N,(T,0,1))-4/(N+2))==0
print('Exact Plucker/Hodge identities, six angular Hessian controls, shifted-kernel and flat-profile identities, spherical kernel normalization and displacement: passed.')
