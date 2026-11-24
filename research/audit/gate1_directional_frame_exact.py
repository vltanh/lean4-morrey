"""Algebra checks for spatial stress constructions, not a QC proof."""
import sympy as s
# Polar reference: n' = m, m'=-n, w and its formal angular derivatives.
w=s.Matrix(s.symbols('w0:2',real=True)); z=s.Matrix(s.symbols('z0:2',real=True)); b=s.Matrix(s.symbols('b0:2',real=True))
n=s.Matrix(s.symbols('n0:2',real=True)); m=s.Matrix(s.symbols('m0:2',real=True)); a=s.Matrix(s.symbols('a0:2',real=True)); v=s.Matrix(s.symbols('v0:2',real=True))
Y=w*n.T+z*m.T
Ytheta=z*n.T+w*m.T+b*m.T-z*n.T
assert s.expand(Ytheta-(w+b)*m.T)==s.zeros(2)
Yrad=a*n.T+v*m.T
H=a*n.T
assert s.expand((Yrad-H).det())==0 and H.det()==0
# Both factors of the polar mixed tensor share the right factor m.
C=s.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
h=s.Matrix(list(a*m.T)); k=s.Matrix(list((w+b)*m.T)); T=(h*k.T+k*h.T)/2
assert s.expand(s.trace(C*T))==0
print('Polar rank-one and mixed cofactor identities passed.')
# One-parameter affine calibration: K' = DF(B)^T B', q'=DF(B)^T b'.
D=s.Matrix(2,2,s.symbols('f0:4',real=True)); Bp=s.Matrix(2,2,s.symbols('B0:4',real=True)); bp=s.Matrix(s.symbols('c0:2',real=True)); x=s.Matrix(s.symbols('x0:2',real=True)); ds=s.Matrix(s.symbols('t0:2',real=True))
R=(Bp*x+bp)*ds.T
assert s.expand(R.det())==0
assert s.expand(s.trace(D.T*R)-ds.dot(D.T*Bp*x+D.T*bp))==0
assert s.expand(s.trace(D.T*Bp)-sum(D[i,j]*Bp[i,j] for i in range(2) for j in range(2)))==0
print('One-parameter affine calibration contraction identities passed.')
# Directional heat sweep of a planar Gaussian gradient, p=4.
x,y,a=s.symbols('x y a',real=True,positive=True)
v=s.Matrix([a*x,y]); ell=s.Matrix([-a*x,-y]); X=v.jacobian([x,y])+v*ell.T
H=X.diff(x)-a*x*X
P=s.Poly(s.expand(X.det()*H.det()),x,y)
def mom(k,rate):
    return 0 if k%2 else s.factorial2(k-1)/(4*rate)**(k//2)
I=s.factor(sum(c*mom(i,a)*mom(j,1) for (i,j),c in P.terms()))
assert s.simplify(I-a**3/8)==0
spatial=s.factor(a**s.Rational(3,2)*I/2)
assert s.simplify(spatial-a**s.Rational(9,2)/16)==0
# dt=-da/(2a²), and the cofactor trace is twice the determinant.
answer=s.integrate(2*spatial/(2*a*a),(a,0,1))
assert answer==s.Rational(1,56)
print('Gaussian sweep cofactor defect/pi =',answer)
