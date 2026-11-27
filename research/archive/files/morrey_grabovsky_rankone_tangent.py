import sympy as sp
h=sp.symbols('h0:6');p,q,t=sp.symbols('p q t',real=True)
X=sp.Matrix([[(-2 if i==0 else 0)+p*t*h[i] for i in range(3)]+[p*t*h[i] for i in range(3,6)],[q*t*h[i] for i in range(3)]+[(-2 if i==3 else 0)+q*t*h[i] for i in range(3,6)]])
u=sp.Matrix(X[0,:3]);v=sp.Matrix(X[0,3:]);s=sp.Matrix(X[1,:3]);r=sp.Matrix(X[1,3:]);dot=lambda a,b:(a.dot(b))
F2=dot(u,u)*dot(r,r)+dot(s,s)*dot(v,v)-2*dot(u,s)*dot(v,r)-2*dot(u,v)*dot(s,r)+2*dot(u,r)*dot(s,v)
G2=sp.factor(F2); G1=G2.diff(t).subs(t,0);G20=G2.subs(t,0);G2d2=G2.diff(t,2).subs(t,0)
# G=sqrt(G2), G''=G2''/(2*sqrt(G2))-(G2')²/(4*G2^(3/2))
E=sp.factor(G2d2/sp.Integer(8)-G1*G1/sp.Integer(256))
print('G2 at M=',G20);print('G2 linear=',sp.factor(G1));print('second derivative of G rankone=',sp.factor(E));print('hessian expanded=',sp.factor(E.expand()))
