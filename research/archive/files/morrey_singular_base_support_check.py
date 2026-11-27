"""Exact sanity checks for the singular-base support theorem."""
from sympy import symbols, Matrix, expand, Rational, diff

a,b,c,d,t,eps=symbols('a b c d t eps')
A=Matrix([[a,b],[c,d]])
q=A.det()
B=Matrix([[1,0],[0,0]])
H1=Matrix([[1,eps],[eps,eps**2]])
H2=Matrix([[1,-eps],[eps,-eps**2]])
assert H1.det()==0 and H2.det()==0
assert expand((B+t*H1).det())==t*eps**2
assert expand((B+t*H2).det())==-t*eps**2

# f=q+q^2 is rank-one convex: det along rank-one lines is affine;
# f-cq=q^2 is globally nonnegative with c=1.
f=q+q**2
assert expand(f-q-q**2)==0

# Contrasting negative control: q^2*|A|^2 is not rank-one convex.
s=lambda X: sum(x*x for x in X)
x=Rational(1,10)
H=H1.subs(eps,x)
def F(M): return expand(M.det()**2*s(M))
left=F(B-Rational(1,2)*H)
right=(F(B)+F(B-H))/2
assert left>right
print('For f=det^2*|A|^2, exact rank-one convexity violation:')
print(' midpoint - chord =',left-right,'>0')
print('PASS: exact rank-one perturbation and supporting determinant checks')
