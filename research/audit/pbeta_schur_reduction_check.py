"""Exact coefficient identity for the all-field P_beta base reduction.

The displayed remainder integrates to zero for actual periodic gradients.
This checks algebra; it does not prove the remaining Schur inequality.
"""
import sympy as s
M,B,C,beta,a,b,c,e=s.symbols('M B C beta a b c e')
f=lambda a,b,c,d:(a*d-2*b*c)**2+beta*(b*b+c*c+d*d)**2
A0=a*(1+e)-2*(B+b)*(C+c)
r=(B+b)**2+(C+c)**2+(1+e)**2
C0=A0*A0+beta*r*r-4*B*B*C*C-beta*(B*B+C*C+1)**2
h=e*(a*e-2*b*c-2*B*c-2*C*b)
actual=f(M+a,B+b,C+c,1+e)-f(M,B,C,1)
remainder=2*M*M*e+2*M*(a+2*(a*e-b*c)-2*B*c-2*C*b-2*B*C*e)
assert s.expand(actual-(M*M*e*e+2*M*h+C0)-remainder)==0
print('Exact all-field base-reduction identity: PASS')
print('Remainder is a linear combination of mean a,b,c,e and mean(ae-bc).')
