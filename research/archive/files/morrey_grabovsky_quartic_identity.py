import sympy as sp
p,q,r,s,l,e,X,Y,Z=sp.symbols('p q r s l e X Y Z',real=True)
B=sp.Matrix([[p,1,l,r,0,0],[q,0,0,s,1,l]])
Du=sp.Matrix([[Y,Z],[-X,-Y]])
M=sp.zeros(2,6);M[0,0]=-2;M[1,3]=-2
A=M+e*Du*B
u=sp.Matrix(A[0,:3]);v=sp.Matrix(A[0,3:]);w=sp.Matrix(A[1,:3]);t=sp.Matrix(A[1,3:]);dot=lambda x,y:x.dot(y)
g2=sp.expand(dot(u,u)*dot(t,t)+dot(w,w)*dot(v,v)-2*dot(u,w)*dot(v,t)-2*dot(u,v)*dot(w,t)+2*dot(u,t)*dot(w,v))
poly=sp.Poly(g2,e)
L,Q,C,D=[poly.coeff_monomial(e**n) for n in range(1,5)]
G2=sp.factor(Q/8-L**2/512)
G3=sp.factor(C/8-L*Q/256+L**3/16384)
G4=sp.factor(D/8-(Q**2+2*L*C)/512+3*L**2*Q/16384-5*L**4/2097152)
print('first G term:',sp.factor(L/8))
print('second G term:',G2)
print('exact remainder:',sp.factor(g2-(4+e*(L/8)+e*e*G2)**2))
print('third G term:',G3)
print('quartic term factored:',sp.factor(G4))
print('quartic p=q=r=s=l=0:',sp.factor(G4.subs({p:0,q:0,r:0,s:0,l:0})))
print('quartic p=1,q=r=s=l=0:',sp.factor(G4.subs({p:1,q:0,r:0,s:0,l:0})))
print('quartic p=0,q=1,r=s=l=0:',sp.factor(G4.subs({p:0,q:1,r:0,s:0,l:0})))
