#!/usr/bin/env python3
"""Exact algebra controls for inner-stress shear; no Morrey witness search."""
import sympy as s

I=s.eye(2)
J=s.Matrix([[0,-1],[1,0]])
def cof(X):
    return s.Matrix([[X[1,1],-X[1,0]],[-X[0,1],X[0,0]]])
def ip(X,Y): return s.trace(X.T*Y)
def simp(X):
    if isinstance(X,s.MatrixBase): return X.applyfunc(s.cancel)
    return s.cancel(X)

def eq(X,Y):
    Z=simp(X-Y)
    if isinstance(Z,s.MatrixBase): assert Z==s.zeros(*Z.shape), Z
    else: assert Z==0,Z

# A smooth polynomial jet, evaluated exactly at several rational points.
# Polynomial need not be RC: these checks concern contact algebra only.
x=s.symbols('x0:4'); X=s.Matrix(2,2,x)
f=(x[0]**2+2*x[1]**2+3*x[2]**2+4*x[3]**2)/2+x[0]*x[3]/3+x[0]*x[1]*x[2]/5
p=s.Matrix(2,2,[s.diff(f,z) for z in x])
T=f*I-X.T*p
points=[(1,2,-1,3),(s.Rational(1,2),-1,s.Rational(2,3),1),(0,1,2,-1),(0,0,0,0)]
t=s.symbols('t')
for pt in points:
    sub=dict(zip(x,pt)); X0=X.subs(sub); f0=f.subs(sub); p0=p.subs(sub); T0=T.subs(sub)
    B=I+t*cof(T0); d=B.det(); Y=simp(X0*B.inv()); g=s.cancel((f0+t*T0.det())/d); q=simp(p0*B.T/d); S=simp((T0+t*T0.det()*I)/d)
    eq(S,g*I-Y.T*q)
    eq(cof(S),cof(T0)*B.inv())
    eq(cof(q),cof(p0)*B.inv())
    eq(S*J,T0*J*B.inv())
    eq(Y.diff(t),-Y*cof(S))
    eq(q.diff(t),-q*S)
    eq(g.diff(t),-g*g+Y.det()*q.det())
    # Fixed-base chain rule for the action and stress at t=1/1000.
    tt=s.Rational(1,1000)
    Bx=I+tt*cof(T); bx=Bx.subs(sub); dx=bx.det()
    y0=X0*bx.inv(); qt=p0*bx.T/dx
    for z in x:
        db=Bx.diff(z).subs(sub); dT=T.diff(z).subs(sub); df=s.diff(f,z).subs(sub)
        dy=X.diff(z)*bx.inv()-y0*db*bx.inv()
        dd=ip(cof(bx),db)
        dg=(df+tt*ip(cof(T0),dT))/dx-(f0+tt*T0.det())*dd/dx**2
        eq(dg,ip(qt,dy))
    # Group rule, on a rational chart where both denominators are nonzero.
    a=s.Rational(1,1000); b=s.Rational(-1,2000)
    Ya=Y.subs(t,a); qa=q.subs(t,a); Sa=S.subs(t,a); ga=g.subs(t,a)
    Bs=I+b*cof(Sa)
    eq(Ya*Bs.inv(),Y.subs(t,a+b))
    eq(qa*Bs.T/Bs.det(),q.subs(t,a+b))
    eq((ga+b*Sa.det())/Bs.det(),g.subs(t,a+b))
print('4 exact contact-action, cofactor, characteristic, gradient and composition controls passed.')

# Rank-one null direction of an RC Hessian: HR=c cof R.  Check the
# ambient second derivative of -det(fI-X^Tp) along (R,p:R,HR).
a=s.Matrix(s.symbols('a0:2')); n=s.Matrix(s.symbols('n0:2')); R=a*n.T
c=s.symbols('c'); H_R=c*cof(R)
p0=s.Matrix(2,2,s.symbols('p0:4')); f0=s.symbols('f0')
D_T=ip(p0,R)*I-R.T*p0-X.T*H_R
assert (D_T*J*J*n).applyfunc(s.expand)==s.zeros(2,1)
assert s.expand(D_T.det())==0
assert (R.T*H_R).applyfunc(s.expand)==s.zeros(2)
Tlin=(f0+t*ip(p0,R))*I-(X+t*R).T*(p0+t*H_R)
assert s.expand((-Tlin.det()).diff(t,2).subs(t,0))==0
print('Symbolic null rank-one contact-Hessian curvature identity passed.')

# Algebra of a hypothetical lifted law with mean T=-D I, mean det T=D^2.
D=s.symbols('D',positive=True)
mean_det_B=1-2*t*D+t*t*D*D
mean_action=-D+t*D*D
eq(mean_action/mean_det_B,-D/(1-t*D))
eq((-D+t*D*D)*I/mean_det_B,-D/(1-t*D)*I)
# Relative change under repeated safe chart transformations is Möbius.
b=s.symbols('b')
eq((D/(1-t*D))/(1-b*D/(1-t*D)),D/(1-(t+b)*D))
assert s.diff(D/(1-t*D),t).subs(t,0)==D**2
# Rational norm budget: |T|<=2 M R^2, |DT|<=4 M R;
# Lip(psi_t-id)<=20 t M R^2, safe t=1/(100 M R^2).
assert s.Rational(2,100)<s.Rational(1,2)
assert s.Rational(20,100)<s.Rational(1,4)
print('Exact defect-amplification, shifted stress mean, and local chart budgets passed.')
print('No qualifying non-QC planar energy or exact-zero proof was computed.')
