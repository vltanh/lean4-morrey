"""Exact symbolic identities for homogeneous logarithmic regularization."""
import sympy as s
p,a,b,E,H,Dw,Dx=s.symbols('p a b E H Dw Dx',real=True)
qww,qxw,qxx,hx,hw=s.symbols('qww qxw qxx hx hw',real=True)
# Tangential w of norm b, radial component a. The scalar defect is hx-pH.
original=qww+2*a*qxw+a*a*qxx
homog=qww+(p*H-hx)*b*b+2*a*(p-1)*hw+a*a*p*(p-1)*H
err=-E*b*b-2*a*Dw-a*a*Dx-(p-1)*a*a*E
subs={E:hx-p*H,Dw:qxw-(p-1)*hw,Dx:qxx-(p-1)*hx}
assert s.expand(homog-original-err.subs(subs))==0
print('Homogeneous Hessian defect identity: passed')
# Direct differentiation of the radial extension on an arbitrary 2D slice.
t=s.symbols('t',real=True)
r=s.sqrt((1+a*t)**2+b*b*t*t)
u=(1+a*t)/r; v=b*t/r
assert s.simplify(s.diff(r,t).subs(t,0)-a)==0
assert s.simplify(s.diff(r,t,2).subs(t,0)-b*b)==0
assert s.simplify(s.diff(u,t).subs(t,0))==0
assert s.simplify(s.diff(u,t,2).subs(t,0)+b*b)==0
assert s.simplify(s.diff(v,t).subs(t,0)-b)==0
assert s.simplify(s.diff(v,t,2).subs(t,0)+2*a*b)==0
print('Radial-extension derivative controls: passed')
# For general determinant-normalized opposite-sign pair X,Y.
t=s.symbols('t',positive=True)
x1,x2,x3,x4,y1,y2,y3,y4=s.symbols('x1 x2 x3 x4 y1 y2 y3 y4',real=True)
X=s.Matrix(2,2,[x1,x2,x3,x4]);Y=s.Matrix(2,2,[y1,y2,y3,y4]);
U=(t*X+Y)/s.sqrt(1+t*t);V=(X-t*Y)/s.sqrt(1+t*t)
N=lambda X:sum(x*x for x in X)
assert s.simplify(N(U)+N(V)-N(X)-N(Y))==0
assert s.simplify((t*U+V)/s.sqrt(1+t*t)-X)==s.zeros(2)
assert s.simplify((U-t*V)/s.sqrt(1+t*t)-Y)==s.zeros(2)
D,E2,C=s.symbols('D E2 C',real=True)
# det(X-tY)=D-tC+t²E2; D=1,E2=-1.
assert s.simplify((t*t*D+t*C+E2).subs({D:1,E2:-1,C:(1-t*t)/t}))==0
# even-power two-ray weighting
k=s.symbols('k',positive=True)
assert s.simplify(k/(1+k)+k/(1+k)/k-1)==0
print('Opposite-ray orthogonal mixing and reciprocal power weights: passed')
