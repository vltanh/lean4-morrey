"""Exact algebra controls for the Shield and convex-volumetric transfer.
The analytic extension, distributional curvature and convexity proofs are separate.
"""
import sympy as S
from fractions import Fraction as Q
from itertools import product
x=S.symbols('a b c d',real=True); X=S.Matrix(2,2,x)
y=S.symbols('e f g h',real=True); Y=S.Matrix(2,2,y)
u=S.Matrix(S.symbols('u:2',real=True)); v=S.Matrix(S.symbols('v:2',real=True)); H=u*v.T
t=S.symbols('t',real=True)
assert S.expand((X+t*H).det()-X.det()-t*S.diff((X+t*H).det(),t).subs(t,0))==0
assert S.expand((t*X+(1-t)*Y).adjugate()-t*X.adjugate()-(1-t)*Y.adjugate())==S.zeros(2)
assert S.simplify(X.det()*X.inv()-X.adjugate())==S.zeros(2)
print('Exact determinant-affine rank-one and adjugate identities passed.')
A=S.diag(3,2)
Xs=[A+S.Matrix([[S.Rational(1,2)*i,0],[0,S.Rational(1,3)*j]]) for i,j in product((-1,1),repeat=2)]
ws=[S.Rational(1,4)]*4
assert sum((w*x for w,x in zip(ws,Xs)),S.zeros(2))==A
assert sum(w*x.det() for w,x in zip(ws,Xs))==A.det()
lams=[w*x.det()/A.det() for w,x in zip(ws,Xs)]
assert all(w>0 for w in lams) and sum(lams)==1
assert sum((w*x.inv() for w,x in zip(lams,Xs)),S.zeros(2))==A.inv()
assert sum(w/x.det() for w,x in zip(lams,Xs))==1/A.det()
print('Exact inverse-minors reweighting passed.')
lam,z,beta,c,eps=S.symbols('lam z beta c eps',positive=True)
g=S.Function('g')
assert S.diff(g(lam**2*z),z,2)==lam**4*S.Subs(S.Derivative(g(t),(t,2)),t,lam**2*z)
assert S.simplify(S.diff(-beta*S.log(z),z,2)-beta/z**2)==0
assert S.simplify(S.diff(g(z)+beta*S.log(z),z,2)-(S.diff(g(z),z,2)-beta/z**2))==0
a,b=S.symbols('a b',positive=True)
assert S.simplify(a/b-2*S.log(b)-(2+2*(a-b)-a*b)-(a*(b-1)**2/b+2*(b-1-S.log(b))))==0
print('Exact logarithmic reduction and magic-minus support identities passed.')
