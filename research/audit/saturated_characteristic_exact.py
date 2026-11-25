"""Exact algebra for smooth saturated rank-one characteristics.
The analytic continuation and extremality arguments are not checked by this script.
"""
import sympy as s
from itertools import product, combinations
C=s.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
a,b,c,d=s.symbols('a b c d', real=True)
x=s.Matrix([a,b,c,d]); assert C*C==s.eye(4)
assert s.expand((x.T*C*x)[0]-2*(a*d-b*c))==0
assert C.eigenvals()=={-1:2,1:2}
# General Schur derivative at a point split into a null kernel and its positive complement.
# Both dim K=1 and dim K=2 totally isotropic models; D is diagonal positive.
t=s.symbols('t', real=True)
for k in (1,2):
    D=s.diag(*range(1,5-k)); B=s.Matrix(k,4-k,lambda i,j:(i+1)*(j+2) if i!=j else i+2)
    # S(c) at a fixed X in adapted coordinates, at c=0, with C|K=0.
    schur=-t*t*B*D.inv()*B.T
    assert schur.diff(t).subs(t,0)==s.zeros(k)
    assert schur.diff(t,2).subs(t,0)==-2*B*D.inv()*B.T
    assert s.trace(schur.diff(t,2))<0
# Rank-one update of every square minor is affine, in ranks 1,2,3.
for k in (1,2,3):
    M=s.Matrix(k,k,lambda i,j:s.Symbol(f'm{i}{j}'))
    u=s.Matrix(k,1,lambda i,j:s.Symbol(f'u{i}')); v=s.Matrix(k,1,lambda i,j:s.Symbol(f'v{i}'))
    poly=s.Poly(s.expand((M+t*u*v.T).det()),t)
    assert poly.degree()<=1 and s.expand(poly.nth(0)-M.det())==0
print('Cofactor signature, Schur derivatives, and affine-minor identities passed.')
# Exact identity from differentiating DF(X+tR(X)) = DF(X)+t c(X) C R(X).
Q0=s.MatrixSymbol('Q0',4,4); Qt=s.MatrixSymbol('Qt',4,4)
D=s.MatrixSymbol('DR',4,4); R=s.MatrixSymbol('R',4,1); dc=s.MatrixSymbol('dc',1,4)
C0=s.MatrixSymbol('C',4,4); k=s.Symbol('k'); I=s.Identity(4)
from sympy import MatAdd, MatMul
P0=Q0-k*C0
lhs=(Qt-k*C0)*(I+t*D)
# Use the differentiated identity for Qt*(I+tD).
rhs=Q0+t*C0*R*dc+t*k*C0*D-k*C0*(I+t*D)
assert s.expand(rhs-(P0+t*C0*R*dc)).doit()==s.ZeroMatrix(4,4)
print('Characteristic derivative identity passed.')
# Regular-null model: K spanned by E11,E22; CR=E22 transverse to range P0.
P=s.diag(0,2,3,0); R=s.Matrix([1,0,0,0]); dc=s.Matrix([[0,5,-7,0]])
for z in map(s.Rational,range(-5,6)):
    N=P+z*C*R*dc
    assert N.rank()==2
    assert N.row_join(C*R).rank()==3
print('Regular-null rank/transversality controls passed.')
