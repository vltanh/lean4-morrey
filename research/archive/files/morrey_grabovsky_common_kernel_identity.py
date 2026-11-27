"""Exact symbolic SOS identity for common-kernel planar pullbacks of the 2x6 counterexample."""
import sympy as sp
p,q,r,s,m1,m2,n1,n2,l,a,b,c,d=sp.symbols('p q r s m1 m2 n1 n2 l a b c d',real=True)
B=sp.Matrix([[p,m1,m2,r,l*m1,l*m2],[q,n1,n2,s,l*n1,l*n2]])
A=sp.Matrix([[a,b],[c,d]])
X=sp.zeros(2,6);X[0,0]=-2;X[1,3]=-2;X+=A*B
u=sp.Matrix(X[0,:3]);v=sp.Matrix(X[0,3:]);S=sp.Matrix(X[1,:3]);t=sp.Matrix(X[1,3:]); dot=lambda x,y:x.dot(y)
Gsq=sp.expand(dot(u,u)*dot(t,t)+dot(S,S)*dot(v,v)-2*dot(u,S)*dot(v,t)-2*dot(u,v)*dot(S,t)+2*dot(u,t)*dot(S,v))
D=a*d-b*c
first=4-2*(a*p+b*q+c*r+d*s)+(p*s-q*r)*D
L=[2*(a*m+b*n+l*(c*m+d*n)) for m,n in ((m1,n1),(m2,n2))]
K=[(m*s-n*r)+l*(p*n-q*m) for m,n in ((m1,n1),(m2,n2))]
RHS=sp.expand(first**2+sum((Lj-Kj*D)**2 for Lj,Kj in zip(L,K)))
rem=sp.factor(Gsq-RHS)
print('Common-kernel SOS identity remainder:',rem)
assert rem==0
print('Exact identity proves every such pullback is globally polyconvex in 2x2, all parameter values')
