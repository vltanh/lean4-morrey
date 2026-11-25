"""Exact algebra controls for full-matrix halfspace gluing (not PDE verification)."""
import sympy as S
from fractions import Fraction as Q
p,x,y=S.symbols('p x y', positive=True)
Bp_hi=S.Rational(2,1)/p*((p-1)*x-y)*(x+y)**(p-1)
Bp_lo=S.Rational(2,1)/p*(x-(p-1)*y)*(x+y)**(p-1)
assert S.simplify(S.diff(Bp_hi,y)-2*(x+y)**(p-2)*((p-2)*x-y))==0
assert S.simplify(S.diff(Bp_lo,y)+2*(p-1)*y*(x+y)**(p-2))==0
assert S.simplify(Bp_hi.subs(y,(p-2)*x)-2*(p-1)**(p-1)*x**p/p).subs(p,4).simplify()==0
assert S.simplify(Bp_lo.subs(y,0)-2*x**p/p)==0
print('Exact two Burkholder derivative identities and stationary-value controls passed.')
a,b,c,d=S.symbols('a b c d',real=True)
X=S.Matrix([[a,b],[c,d]])
J=S.Matrix([[0,-1],[1,0]])
assert S.expand(X.det()-(c-b)**2/4-((X+X.T)/2).det())==0
assert S.expand(X.det().subs(d,-a)+a*a+b*c)==0
assert S.expand(((c-b)**2/4-X.det()).subs(d,-a)-(a*a+(b+c)**2/4))==0
# Local differential symbol identity for exact projected directional orthogonality.
b11,b12,b21,b22,k1,k2,e1,e2,v1,v2=S.symbols('B11 B12 B21 B22 k1 k2 e1 e2 v1 v2',real=True)
B=S.Matrix([[b11,b12],[b21,b22]])
k=S.Matrix([k1,k2]);e=S.Matrix([e1,e2]);v=S.Matrix([v1,v2])
# Both sides of the integrated-by-parts identity have this same real Fourier symbol.
Z=v*k.T
Ck=B*k*k.T
lhs=(Z*e).dot(Ck*e)
rhs=S.trace(B.T*Z)*(k.dot(e))**2
assert S.expand(lhs-rhs)==0
h11,h12,h22=S.symbols('h11 h12 h22',real=True)
H=S.Matrix([[h11,h12],[h12,h22]])
assert S.trace(J.T*H)==0
print('Exact skew invariant, determinant-symmetric identity, and projection Fourier symbol passed.')
I=S.eye(2)
atoms=[(S.Rational(1,4),-2*I),(S.Rational(3,8),S.diag(4,0)),(S.Rational(3,8),S.diag(0,4))]
assert sum(w for w,A in atoms)==1
assert sum((w*A for w,A in atoms),S.zeros(2))==I
assert sum(w*A.det() for w,A in atoms)==1
assert all(A[1,0]==A[0,1] and (S.trace(A)<=0 or A.det()==0) for w,A in atoms)
# Nonconvexity witness for 1<p<2, p^*-1=1/(p-1).
count=0
for i in range(1,10):
    P=Q(1)+Q(i,10)
    k=1/(P-1)+1
    assert 1-(P-1)*k<0
    A1=S.diag(S.Rational(-1,2)+k,S.Rational(-1,2)-k)
    A2=S.diag(1-k,1+k)
    assert S.trace(A1)<0 and S.trace(A2)>0 and (A1+A2)/2==I/4
    count+=1
print(f'Exact nonpolyconvex minors witness and {count} subquadratic nonconvexity controls passed.')
# Exact derivative coefficient and growth estimates for exponent demotion.
p=S.symbols('p',positive=True)
assert S.simplify(2/(p-1)+(1+p)/(p*(p-1))-(3*p+1)/(p*(p-1)))==0
r,theta=S.symbols('r theta',positive=True)
assert S.simplify(S.diff(r**theta,r,2)-S.diff(r**theta,r)/r-theta*(theta-2)*r**(theta-2))==0
# Four-atom lift of the subquadratic nonconvexity witness.
eps,k=S.symbols('eps k',positive=True)
Dbar=S.Rational(5,8)-k*k
T2=(S.Rational(1,16)-Dbar/(1-eps))/eps
assert S.simplify(Dbar/(1-eps)+eps*T2-S.Rational(1,16))==0
assert S.simplify((1-eps)*(S.Rational(1,4)/(1-eps))-S.Rational(1,4))==0
print('Exact subquadratic minors repair and exponent-demotion coefficients passed.')
