#!/usr/bin/env python3
"""Independent exact regression for isotropic p>=2 proof / nonhomogeneity no-go.

SymPy and Fraction; seven global identities, rank-one Hessian SOS, rational
strict minor-Jensen deficit. This is NOT a Lean or unrestricted Morrey proof.
"""
import sympy as s
from fractions import Fraction as Q
p,t,H,m=s.symbols('p t H m',real=True)
k=(p-2)/p;C=p*H-2*t*m
x=(1+t)/2;y=(1-t)/2
phix=p*H+(1-t)*m;phiy=p*H-(1+t)*m
c=phix/(1+t);gam=2*C/(1+t);alpha=c*t-(p-1)*H
mu=-(p-1)*gam/((p-2)*c)
ellminus=H+m*(-k-t)
forms={
 'caseI stationarity':p*alpha+(p-1)*gam*y+(p-2)*c*t,
 'caseI alpha negativity':alpha+((1-t)*C+(p-2)*(1+t)*H)/(2*(1+t)),
 'caseI mu lower':mu+2+2*p*ellminus/((p-2)*phix),
 'caseI mu upper':2*t-mu-2*(t*(p-2)*phix+(p-1)*C)/((p-2)*phix),
 'CaseI base tangent':alpha+gam*y+c*t-H,
 'CaseI direction tangent':phix*((mu+1-t)/(1+t))+phiy-(gam+c*mu),
 'orientation width':(p*H+(1-t)*m)/(1+t)-((1+t)*m-p*H)/(1-t)-2*C/(1-t*t)
}
for name,expression in forms.items():
 assert s.cancel(expression)==0, (name,s.factor(expression))
print('PASS',len(forms),'exact Case I identities')
a,b,d,e,z=s.symbols('a b d e z',real=True)
S=(a+z)**2+b*b+d*d+e*e
det=(a+z)*e-b*d
q=S**2-s.Rational(9,4)*S*det
rhs=3*(a-s.Rational(9,16)*e)**2+s.Rational(13,256)*e**2+(b+s.Rational(9,16)*d)**2+s.Rational(175,256)*d**2
assert s.expand(s.diff(q,z,2).subs(z,0)/4-rhs)==0
assert q.subs({a:1,b:0,d:0,e:1,z:0})==-Q(1,2)
assert q.subs({a:Q(1,5),b:0,d:0,e:-Q(1,5),z:0})==Q(17,1250)
assert Q(19705,19728)+Q(1,6500)<1
print('PASS rank-one Hessian SOS and strict minors Jensen upper bound')
