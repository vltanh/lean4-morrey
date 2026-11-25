"""Symbolic identities for the spatial heat-stress exchange; not a QC proof."""
import sympy as s
from fractions import Fraction as Q
from itertools import product

# Column-major coordinates: [column_1, column_2].
A=s.Matrix(s.symbols('a1 a2',real=True))
B=s.Matrix(s.symbols('b1 b2',real=True))
D=s.Matrix(s.symbols('d1 d2',real=True))
g=A+D; P=(A-D)/2; R=B
outer=lambda v:v*v.T
stack=lambda a,b:a.col_join(b)
z=s.zeros(2,1)
M=outer(stack(A,B))+outer(stack(B,D))
G=outer(stack(g/2,z))+outer(stack(z,g/2))
V=outer(stack(P,R))+outer(stack(R,-P))
sym=lambda a,b:(a*b.T+b*a.T)/2
S=s.BlockMatrix([[sym(g,A),sym(g,B)],[sym(g,B),sym(g,D)]]).as_explicit()
C=s.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
assert s.expand(S-M-G+V)==s.zeros(4)
assert s.expand(s.trace(C*S))==0 and s.trace(C*G)==0
assert s.expand(s.trace(C*(M-V)))==0
assert s.expand(s.trace(S)-g.dot(g))==0
assert s.expand(s.trace(M)-(g.dot(g)/2+s.trace(V)))==0
print('Heat exchange, cofactor cancellation and trace identities passed.')

# Angular integration for n=(cos theta,sin theta).
x,y=s.symbols('x y', real=True)
# Moments through degree four on S^1; odd moments vanish.
def avg(expr):
    p=s.Poly(s.expand(expr),x,y)
    out=0
    for (i,j),c in p.terms():
        if i%2 or j%2: continue
        k,l=i//2,j//2
        out+=c*s.factorial(2*k)*s.factorial(2*l)/(4**(k+l)*s.factorial(k)*s.factorial(l)*s.factorial(k+l))
    return s.expand(out)
n=s.Matrix([x,y]); v=4*(x*x*A+2*x*y*B+y*y*D)-g
T=stack(x*g,y*g); W=stack(x*v,y*v)
assert sym(T,W).applyfunc(avg)==S.applyfunc(s.expand)
assert s.expand(avg(g.dot(v))-g.dot(g))==0
Vdev=(A-g/2).dot(A-g/2)+(D-g/2).dot(D-g/2)+2*B.dot(B)
assert s.expand(avg(v.dot(v))-(g.dot(g)+4*Vdev))==0
print('Exact directional decomposition and angular second/fourth moment identities passed.')

# Bound (sqrt(x(4-x))-x)/2 <= sqrt(2)-1 for x in [0,2].
u=s.symbols('u', real=True)
k=s.sqrt(2)-1
assert s.simplify((u+2*k)**2-u*(4-u)-2*(u-(2-s.sqrt(2)))**2)==0
# Weighted estimate algebra, p>=2: S - sqrt(S U) >= -U/4.
a,b=s.symbols('a b',real=True)
assert s.expand(a*a-a*b+b*b/4-(a-b/2)**2)==0
# p<2: x^2+(2-p)x-(p-1)=(x-(p-1))(x+1).
p=s.symbols('p',real=True)
assert s.expand(u*u+(2-p)*u-(p-1)-(u-(p-1))*(u+1))==0
assert s.simplify(1+2/(s.sqrt(3)-1)-(2+s.sqrt(3)))==0
print('Negative-mass bounds and ellipticity contrast constants passed.')
