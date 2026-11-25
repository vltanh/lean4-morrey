"""Algebra controls for determinant-centered spectral transport.
Not a verification of the analytic QC or transport theorems.
"""
from fractions import Fraction as Q
import sympy as S
s=S.symbols('s', positive=True)
h=S.Function('h')
V=s*h(S.log(s))
t=S.symbols('t', real=True)
assert S.simplify(s*S.diff(V,s,2)-(S.diff(h(t),t)+S.diff(h(t),t,2)).subs(t,S.log(s)))==0
assert S.simplify(V-s*S.diff(V,s)+s*S.diff(h(t),t).subs(t,S.log(s)))==0
a,b=S.symbols('a b', positive=True)
th=b/(a+b); lam=1/a+1/b
assert S.simplify(lam*th-1/a)==0
assert S.simplify(lam*(1-th)-1/b)==0
D0=S.symbols('D0', real=True)
assert S.simplify(th*(D0+a)+(1-th)*(D0-b)-D0)==0
m,M,N,N0,Nz,J,J0,Jav,EJ2,eta,Dabs=S.symbols('m M N N0 Nz J J0 Jav EJ2 eta Dabs', real=True)
lower=m*(N-(2*Dabs+4*EJ2))/2-(M-m)*eta/2+2*m*(EJ2-Jav**2)+2*m*(Jav**2-J0**2)
assert S.expand(lower-(m*(N-(2*Dabs+4*J0**2))/2-(M-m)*eta/2))==0
print('Symbolic log-kernel derivatives, transport marginal/determinant identities and variance cancellation passed.')
count=0
for r1 in [Q(i,2) for i in range(1,9)]:
 for r2 in [Q(i,2) for i in range(1,9)]:
  d1,d2=r1*r1,-r2*r2
  a,b=d1,-d2
  t=b/(a+b);R=max(r1,r2)
  r=R
  e1=r*r+d1*d1/(r*r)-2*r1*r1
  e2=r*r+d2*d2/(r*r)-2*r2*r2
  assert e1>=0 and e2>=0
  assert t*d1+(1-t)*d2==0
  N=t*2*r1*r1+(1-t)*2*r2*r2
  Eeta=t*e1+(1-t)*e2
  Nz=r*r
  delta2=((d1-d2)/r)**2
  assert N+Eeta-Nz==t*(1-t)*delta2
  assert Nz+t*(1-t)*delta2-Eeta==N
  count+=1
print(f'{count} exact rational pair inflation/merging controls passed.')
