"""Exact algebra accompanying analytic rank-one-null proofs; no numerical theorem inference."""
import sympy as S
from fractions import Fraction as Q
# Rank-one shift and the quotient by a rank-one ray.
a,b,c,d,u,v,w,z,t=S.symbols('a b c d u v w z t',real=True)
X=S.Matrix([[a,b],[c,d]])
H=S.Matrix([u,v])*S.Matrix([[w,z]])
cof=S.Matrix([[d,-c],[-b,a]])
assert S.expand((X+t*H).det()-X.det()-t*S.trace(cof.T*H))==0
E11=S.diag(1,0)
assert S.expand((X+t*E11).det()-X.det()-t*d)==0
assert (X.subs(a,a-X.det()/d)).det().expand()==0
# A fixed first column realizes two arbitrary determinant values at independent second columns.
b1,b2,c1,c2,d1,d2=S.symbols('b1 b2 c1 c2 d1 d2',real=True)
V=S.Matrix([b1,b2]);W=S.Matrix([c1,c2]);M=S.Matrix([[b2,-b1],[c2,-c1]])
A=M.inv()*S.Matrix([d1,d2])
assert S.simplify(S.Matrix.hstack(A,V).det()-d1)==0
assert S.simplify(S.Matrix.hstack(A,W).det()-d2)==0
assert (S.Matrix.hstack(A,V)-S.Matrix.hstack(A,W)).det()==0
print('Exact rank-one shift and common-column identities passed.')
# Trace bound using homogeneity and separate convexity, for the scalar algebra.
x,p=S.symbols('x p',positive=True)
U,V,Z=S.symbols('U V Z',real=True)
upper=(1-x)*V+x*Z
lower=x**(p-1)*Z-(1-x)*x**(p-1)*U
assert S.simplify(upper-lower-((1-x)*(V+x**(p-1)*U)-(x**(p-1)-x)*Z))==0
assert S.simplify(S.limit((x**(p-1)-x)/(1-x),x,1)-(2-p))==0
print('Exact homogeneous rank-one trace bound identities passed.')
