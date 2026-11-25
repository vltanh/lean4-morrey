"""Check exact polynomial identity for EVERY planar pullback B whose rank-one acoustic pencil at M has common image."""
import sympy as sp
p,q,r,s,m1,m2,n1,n2,w1,w2,a,b,c,d=sp.symbols('p q r s m1 m2 n1 n2 w1 w2 a b c d',real=True)
B=sp.Matrix([[p,m1*w1,m1*w2,r,n1*w1,n1*w2],[q,m2*w1,m2*w2,s,n2*w1,n2*w2]])
A=sp.Matrix([[a,b],[c,d]])
X=sp.zeros(2,6);X[0,0]=-2;X[1,3]=-2
X+=A*B
u=sp.Matrix(X[0,:3]);v=sp.Matrix(X[0,3:]);S=sp.Matrix(X[1,:3]);t=sp.Matrix(X[1,3:]); dot=lambda x,y:x.dot(y)
Gsq=sp.expand(dot(u,u)*dot(t,t)+dot(S,S)*dot(v,v)-2*dot(u,S)*dot(v,t)-2*dot(u,v)*dot(S,t)+2*dot(u,t)*dot(S,v))
W=w1*w1+w2*w2;D=a*d-b*c
first=4-2*(a*p+b*q+c*r+d*s)+(p*s-q*r-W*(m1*n2-m2*n1))*D
second=2*(a*m1+b*m2+c*n1+d*n2) - ((p*n2-q*n1)+(m1*s-m2*r))*D
rest=sp.factor(Gsq-first**2-W*second**2)
print('Identity remainder:',rest)
assert rest==0
print('ALL PARAMETER SYMBOLIC EXACT IDENTITY VERIFIED')
