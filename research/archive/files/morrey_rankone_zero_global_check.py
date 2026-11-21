"""Exact checks for global rank-one-zero sign theorem and quartic planar lemma.
This checks algebra; the all-degree homogeneity/separate-convexity argument is proved in the note.
"""
import sympy as sp
x,y,z,w=sp.symbols('a b c d',real=True)
A=sp.Matrix([[x,y],[z,w]])
B=sp.Matrix([[1,0],[0,0]])
S=sp.Matrix([[1,-y/w],[0,1]])
T=sp.Matrix([[1,0],[-z/w,1]])
assert sp.simplify(S*B*T)==B
assert all(sp.simplify(e)==0 for e in S*A*T-sp.diag((x*w-y*z)/w,w))
# General homogeneous quartic on the diagonal line: P(s,0;0,t).
s,t=sp.symbols('s t',real=True)
c4,c3,c2,c1,c0=sp.symbols('c4 c3 c2 c1 c0',real=True)
p=c4*s**4+c3*s**3*t+c2*s**2*t**2+c1*s*t**3+c0*t**4
assert sp.diff(p,s,2).expand()==12*c4*s**2+6*c3*s*t+2*c2*t**2
# With P(E11)=0, separate convexity in s forces c3=0 and c2 >= 0.
p=p.subs({c4:0,c3:0})
assert sp.diff(p,t,2).expand()==2*c2*s**2+6*c1*s*t+12*c0*t**2
# Convexity in t forces c0,c2>=0 and 36c1^2 <= 96 c2 c0.
# This implies discriminant c1^2-4c2c0 <= -(4/3)c2c0 <=0.
assert sp.expand(sp.Rational(8,3)-4)==-sp.Rational(4,3)

# Determinant is affine along each rank-one direction H, and det B,H = H22 when B=E11.
u,v=sp.symbols('u v', real=True)
H=sp.Matrix([[u*v,u],[v,1]])
r,k=sp.symbols('r k',real=True)
assert sp.det(H)==0
assert sp.expand(sp.det(r*B+k*H))==r*k
assert sp.expand(sp.det(A)-sp.det(A+r*B))==-r*w
print('PASS: stabilizer shears and quartic coefficient/discriminant checks (exact SymPy).')
