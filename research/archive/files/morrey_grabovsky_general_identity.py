import sympy as sp
p,q,r,s,l,a,b,c,d,e=sp.symbols('p q r s l a b c d e',real=True)
B=sp.Matrix([[p,1,l,r,0,0],[q,0,0,s,1,l]])
A=sp.Matrix([[a,b],[c,d]])
M=sp.zeros(2,6);M[0,0]=-2;M[1,3]=-2
E=M+e*A*B
u=sp.Matrix(E[0,:3]);v=sp.Matrix(E[0,3:]);w=sp.Matrix(E[1,:3]);t=sp.Matrix(E[1,3:]);dot=lambda x,y:x.dot(y)
g2=sp.expand(dot(u,u)*dot(t,t)+dot(w,w)*dot(v,v)-2*dot(u,w)*dot(v,t)-2*dot(u,v)*dot(w,t)+2*dot(u,t)*dot(w,v))
L=-2*(p*a+q*b+r*c+s*d)
Q=(p*s-q*r-1-l*l)*(a*d-b*c)
rem=sp.factor(g2-(4+e*L+e*e*Q)**2)
print('REM FACTORED:')
print(rem)
print('Coefficient in e:', [(k,sp.factor(sp.Poly(rem,e).coeff_monomial(e**k))) for k in range(5)])
print('Simplify trace-zero:',sp.factor(rem.subs(d,-a)))
print('Simplify p=q=r=s=ell=0:',sp.factor(rem.subs({p:0,q:0,r:0,s:0,l:0})))
