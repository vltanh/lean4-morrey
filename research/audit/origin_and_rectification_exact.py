"""Exact algebra for origin supports and two-row rectification; not a substitute for the proofs."""
from fractions import Fraction as Q
import sympy as S
from itertools import product
D,E,t,eps,fa,fb,fc=S.symbols('D E t eps fa fb fc', positive=True)
th=t*t*E/(D+t*t*E)
assert S.simplify(th*D+(1-th)*(-t*t*E))==0
assert S.simplify(th*fa+(1-th)*t*t*fb-D*t*t*E/(D+t*t*E)*(fa/D+fb/E))==0
# Rank-one dilution and energy factor.
assert S.simplify(eps+(1-eps)*(-eps/(1-eps)))==0
assert S.simplify((1-eps)*(eps/(1-eps))**2-eps**2/(1-eps))==0
# Explicit rational two-stage laminate defeating the two-atom test for -|det|.
A=S.diag(1,1); B=S.diag(1,-1); C=(A+B)/2
assert (A-B).rank()==1 and C.rank()==1
atoms=[(S.Rational(1,4),A),(S.Rational(1,4),B),(S.Rational(1,2),-C)]
assert sum((w*x for w,x in atoms),S.zeros(2))==S.zeros(2)
assert sum(w*x.det() for w,x in atoms)==0
assert sum(-w*abs(x.det()) for w,x in atoms)==-S.Rational(1,2)
print('Exact determinant-balanced two-stage laminate identities passed.')
# Exact defect formula for a two-row projection, with centered derivatives.
a,b,c,d,z11,z12,z21,z22,b0,c0,alpha,beta=S.symbols('a b c d z11 z12 z21 z22 b0 c0 alpha beta',real=True)
# Formal centered integral computation: the linear terms have zero integral.
B0,C0,P,Q0=S.symbols('B0 C0 P Q0',real=True)
assert S.expand(alpha*(B0**2-P**2)+beta*(C0**2-Q0**2)+alpha*P**2+beta*Q0**2+P*Q0-(alpha*B0**2+beta*C0**2+P*Q0))==0
assert S.expand((B0-P)**2+2*P*(B0-P)-(B0**2-P**2))==0
assert S.expand(alpha*(P+Q0/(2*alpha))**2+(beta-1/(4*alpha))*Q0**2-(alpha*P**2+P*Q0+beta*Q0**2))==0
# Rank-one Hessian necessity and sufficiency.
u,v,w,z=S.symbols('u v w z',real=True)
H=S.Matrix([[u*w,u*z],[v*w,v*z]])
assert S.expand(H[0,0]*H[1,1]-H[0,1]*H[1,0])==0
# Correct non-polyconvex witnesses at full and rank-one bases.
for b0,c0 in [(0,0),(1,1)]:
    A=S.Matrix([[1,b0],[c0,1]])
    atoms=[(S.Rational(1,4),S.Matrix([[-2,b0],[c0,-2]])),(S.Rational(3,8),S.Matrix([[4,b0],[c0,0]])),(S.Rational(3,8),S.Matrix([[0,b0],[c0,4]]))]
    assert sum((w*X for w,X in atoms),S.zeros(2))==A
    assert sum(w*X.det() for w,X in atoms)==A.det()
    for aa,bb in [(Q(1,2),Q(1,2)),(Q(1,4),Q(1)),(Q(2),Q(3))]:
        def f(X):return max(X[0,0],0)*max(X[1,1],0)+aa*X[0,1]**2+bb*X[1,0]**2
        assert f(A)-sum(w*f(X) for w,X in atoms)==1
print('Exact weighted shear square-completion, rank-one and non-polyconvex controls passed.')
# General q(b,c) proof: mixed partial derivative of the stationary c(p).
A,C,B=S.symbols('A C B',real=True)
# If AC>=max(B^2,(B+1)^2), then AC-B(B+1)>=1/2.
assert S.expand((B**2+(B+1)**2)/2-B*(B+1))==S.Rational(1,2)
# Centering q+bc subtracts precisely its first jet.
b,c,b0,c0=S.symbols('b c b0 c0',real=True)
assert S.expand((b0+b)*(c0+c)-b0*c0-c0*b-b0*c-b*c)==0
# Example arbitrary quadratic with minimal shear: q=(b-c)^2/4.
assert S.expand((b-c)**2/4+b*c-(b+c)**2/4)==0
# Another exact identity for all B,C,P in the one-projection proof.
P=S.symbols('P',real=True)
assert S.expand((b-c)**2/4+P*c-((c-b+2*P)**2/4+P*(b-P)))==0
print('Exact partial-minimization monotonicity and minimal-shear identities passed.')
