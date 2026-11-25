#!/usr/bin/env python3
"""Exact acoustic heat-stress identities and sharp algebraic relaxation control.
These are not numerical tests of Morrey or independent analytic certification.
"""
import sympy as s

I = s.eye(2)
H = s.Matrix(4, 4, lambda i, j: s.Symbol(f'h{min(i,j)}{max(i,j)}', real=True))
A = H[:2,:2]
B = (H[:2,2:] + H[:2,2:].T)/2
G, p, q, r, t = s.symbols('G p q r t', real=True)
P = s.Matrix([[p,q],[q,-p]])
Q = s.Matrix([[r,t],[t,-r]])
B1 = G*I/2+P
B2 = Q
S = (G*B1).row_join(G*B2/2).col_join((G*B2/2).row_join(s.zeros(2)))
frob = lambda M,N: s.trace(M.T*N)
x = s.trace(A)/2
A0 = A-x*I
B0 = B-s.trace(B)*I/2
assert s.expand(frob(H,S)-G*G*x-G*frob(A0,P)-G*frob(B0,Q)) == 0
assert s.expand(frob(B1,B1)+frob(B2,B2)-G*G/2-frob(P,P)-frob(Q,Q)) == 0
# Orthogonal-direction average inequalities: bdev^2 <= x(1-x)
# follows by subtracting two nonnegative acoustic row defects and squares.
a, ad, b, bd = s.symbols('a ad b bd', real=True)
x = (a+ad)/2
expr = x*(1-x)-(b-bd)**2/4
rhs = ((a-a*a-b*b)+(ad-ad*ad-bd*bd))/2 + (a-ad)**2/4 + (b+bd)**2/4
assert s.expand(expr-rhs) == 0
# The completion of squares in the negative-stress bound.
y,z = s.symbols('y z', nonnegative=True)
assert s.expand(y*y-s.sqrt(2)*y*z+z*z/2-(y-z/s.sqrt(2))**2) == 0
print('Exact symbolic heat contraction, trace split, perpendicular acoustic and square-completion identities passed.')

# An artificial two-state jet distribution. Each local Hessian satisfies
# the FULL Hessian norm bound 1 and the rank-one acoustic sandwich [0,1].
# It is not asserted to come from a spatial gradient or a single F.
H0=s.zeros(4)
H1=s.Matrix([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]])
assert H1*H1==s.eye(4)
u,v,n,m=s.symbols('u v n m',real=True)
R=s.Matrix([u*n,u*m,v*n,v*m])
assert s.expand((R.T*H1*R)[0]-(u*n+v*m)**2)==0
assert s.expand((R.T*R)[0]-(R.T*H1*R)[0]-(u*m-v*n)**2)==0
states=[(H0,I/2,s.zeros(2)),(H1,s.diag(0,1),s.Matrix([[0,-s.Rational(1,2)],[-s.Rational(1,2),0]]))]
energy=total=trace=dev=0
for h,b1,b2 in states:
    g1,g2=s.trace(b1),s.trace(b2)
    assert (g1,g2)==(1,0)
    st=b1.row_join(b2/2).col_join((b2/2).row_join(s.zeros(2)))
    energy+=frob(h,st)/2
    total+=(frob(b1,b1)+frob(b2,b2))/2
    trace+=(g1*g1+g2*g2)/2
    dev+=(frob(b1-I/2,b1-I/2)+frob(b2,b2))/2
assert total==trace==1 and dev==s.Rational(1,2)
assert energy==-s.Rational(1,4)==-dev/2
print('Exact two-state algebraic equality control: trace energy 1, signed cost -1/4, hence -1/8 relative to original gradient energy.')
print('This control is not an actual compatible gradient. It only rules out improving the coefficient using just local acoustic bounds and the scalar trace budget.')
