"""Exact linear-algebra controls for the homogeneous weak Hessian theorem.
These checks do not replace the distributional and BV arguments.
"""
import sympy as s
from itertools import product
C=s.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
assert C.T==C and C*C==s.eye(4) and s.trace(C)==0
assert s.trace(C.T*C)==4
v=s.symbols('a b c d',real=True)
x=s.Matrix(v); X=s.Matrix(2,2,v)
assert s.expand((x.T*C*x)[0]-2*X.det())==0
# Distribution coefficients treated as symbolic commuting scalar variables.
q=s.symbols('q11 q12 q13 q14 q22 q23 q24 q33 q34 q44',real=True)
Q=s.zeros(4); k=0
for i in range(4):
    for j in range(i,4):
        Q[i,j]=Q[j,i]=q[k]; k+=1
T=(Q[0,3]-Q[1,2])/2
S=Q-T*C
assert s.expand(s.trace(C*S))==0
assert s.expand(s.trace(S)-s.trace(Q))==0
assert S[0,3]==S[1,2]
# All rank-one coordinate probes recover the opposite mixed sum.
weighted=0; unweighted=0
for r,t in product((-1,1),repeat=2):
    R=s.Matrix([1,t,r,r*t]); assert s.Matrix(2,2,list(R)).det()==0
    e=(R.T*Q*R)[0]
    weighted+=r*t*e/4; unweighted+=e/4
assert s.expand(weighted-2*(Q[0,3]+Q[1,2]))==0
assert s.expand(unweighted-s.trace(Q))==0
# Radial Euler identity recovers the missing determinant coefficient.
assert s.expand((x.T*C*Q*x)[0]-(x.T*C*S*x)[0]-T*(x.dot(x)))==0
assert all(s.expand(y)==0 for y in (Q*x-S*x-T*C*x))
print('Exact rank-one probes, cofactor projection, and Euler recovery identities passed.')
# Determinant-fiber tangent directions have opposite determinants.
J=s.Matrix([[0,-1],[1,0]]); K=s.Matrix([[0,1],[1,0]])
D=X.det(); cx=C*x
for L,sgn in [(J,1),(K,-1)]:
    w=s.Matrix(list(X*L))
    assert s.expand(w.dot(cx))==0
    assert s.expand((w.T*C*w)[0]-2*sgn*D)==0
    B=cx*cx.T-2*D*C
    assert s.expand((w.T*B*w)[0]+4*sgn*D**2)==0
assert all(s.expand(y)==0 for y in B*x)
print('Exact determinant-fiber tangent and opposite-sign residual identities passed.')
# The determinant-only density Hessian residual annihilates the radial vector.
p,d,hp,hpp=s.symbols('p d hp hpp',real=True)
assert s.expand((2-p)*hp+2*d*hpp).subs(hpp,(p/2-1)*hp/d).simplify()==0
print('Homogeneous determinant-power coefficient identity passed.')
