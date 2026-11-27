"""Exact identities explaining false promising minima in the planar family."""
import sympy as s
import json
A=s.Matrix(2,2,s.symbols('a b c d'));a,b,c,d=list(A)
def forms(B):
 M=A*B;aa,bb,cc,dd,ee,ff=list(M)
 x0=(aa-cc-ee)/2;x1=(bb+dd+ff)/2;y0=dd-ff;y1=ee;u0=bb;u1=-aa-cc;z0=(aa-cc+ee)/2;z1=(bb-dd-ff)/2
 q=(y0*u1-y1*u0)**2-4*(x0*u1-x1*u0)*(x0*y1-x1*y0)
 L=2*(x0*x0+x1*x1)+y0*y0+y1*y1+u0*u0+u1*u1;P=2*(z0*z0+z1*z1)
 return q,L,P
B=s.Matrix([[1,0,0],[0,1,0]])
q,L,P=forms(B)
assert s.expand(q+L**2/4-L*P+3*P**2/4)==0
assert s.expand(-q-L*P/2+3*P**2/2-4*A.det()**2)==0
planes=[B,s.Matrix([[1,0,1],[0,1,1]])]
for r in [s.Rational(1,2),s.Rational(1,10),s.Rational(1,100)]:
 planes.append(s.Matrix([[1-r*r,2*r,1+r*r],[1-r*r,-2*r,1+r*r]])/(1+r*r))
ranks=[]
for B in planes:
 q,L,P=forms(B);polys=[s.Poly(p,a,b,c,d) for p in [q,L**2,L*P,P**2]]
 keys=sorted(set(e for p in polys for e,_ in p.terms()))
 C=s.Matrix([[p.coeff_monomial(e) for p in polys] for e in keys]);ranks.append(C.rank())
assert ranks==[3,4,4,4,4]
print(json.dumps({'zero_integrand_identity':True,'determinant_square_identity':True,'basis_ranks':ranks}))
