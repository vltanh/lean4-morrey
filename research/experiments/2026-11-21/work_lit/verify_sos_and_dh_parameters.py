"""Exact algebra used to select the search families; not a Morrey proof."""
import sympy as s

x=s.symbols('a b c d');a,b,c,d=x
h=s.symbols('A B C D');A,B,C,D=h
beta=s.symbols('beta')
f=(a*d-2*b*c)**2+beta*(b*b+c*c+d*d)**2
LH=(s.Matrix(h).T*s.hessian(f,x)*s.Matrix(h))[0]/2
L=c*B+b*C;T=a*D-2*L;S=d*A
r=(b*b+c*c+d*d)*(B*B+C*C+D*D);z=b*B+c*C+d*D
sos=T*T+(S-2*L)**2+4*(b*B-c*C)**2+(b*B+c*C)**2+L*L
sos+=5*d*d*(B*B+C*C)+5*(b*b+c*c+d*d)*D*D+10*z*z
sos+=(beta-s.Rational(5,2))*(2*r+4*z*z)
assert s.expand(LH-4*(a*d-b*c)*(A*D-B*C)-sos)==0
print('P_beta SOS-LH identity modulo det(H): exact PASS')

E=s.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
N=s.Matrix([[8,0,0,2],[0,5,1,0],[0,1,5,0],[2,0,0,8]])
assert N*E==E*N
assert N.eigenvals()=={s.Integer(4):1,s.Integer(6):2,s.Integer(10):1}
vmin=s.Matrix([0,1,-1,0]);vmax=s.Matrix([1,0,0,1])
assert E*vmin==vmin and E*vmax==vmax
assert N*vmin==4*vmin and N*vmax==10*vmax
assert 4*4==6+10 and 4+6==10
print('DH strongest boundary matrix: exact eigenvalue/commutation PASS')
print('RC follows from DH1996 Corollary 1.5, not from this checker alone.')
