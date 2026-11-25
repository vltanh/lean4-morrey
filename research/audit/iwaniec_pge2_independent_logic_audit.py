#!/usr/bin/env python3
"""Independent algebra and deterministic rational logic audit for p>=2 isotropic result.

Uses SymPy for 16 symbolic identities, Fraction for universal-case tests.
These are regression tests, not a formal proof of the quantified theorem.
"""
from fractions import Fraction as Q
from random import Random
import sympy as s

p,t,H,m=s.symbols('p t H m',real=True)
k=(p-2)/p
x0=(1+t)/2; y0=(1-t)/2
px=p*H+(1-t)*m
py=p*H-(1+t)*m
C=p*H-2*t*m
c=px/(1+t)
gamma=2*C/(1+t)
alpha=c*t-(p-1)*H
mu=-(p-1)*gamma/((p-2)*c)
L=((1+t)*m-p*H)/(1-t)
U=(p*H+(1-t)*m)/(1+t)
ct=(mu+1-t)/(1+t)
tests={
 'Euler':x0*px+y0*py-p*H,
 'C':px*y0+py*x0-C,
 'c=U':c-U,
 'gamma':gamma-py-y0/x0*px,
 'tangent stationarity':gamma*y0+2*c*t-p*H,
 'alpha sign expression':alpha+((1-t)*C+(p-2)*(1+t)*H)/(2*(1+t)),
 'mu+2':mu+2+2*p*(H-m*(t+k))/((p-2)*px),
 '2t-mu':2*t-mu-2*(t*(p-2)*px+(p-1)*C)/((p-2)*px),
 'rankone slope':gamma+mu*c-(px*ct+py),
 'contact':alpha+gamma*y0+c*t-H,
 'homogeneous contact':p*alpha+(p-1)*gamma*y0+(p-2)*c*t,
 'orientation width':U-L-2*C/(1-t*t),
 'case I clamp':(p-1)*m-U+p*(H-m*(t+k))/(1+t),
 'case II clamp':(p-1)*m-L-p*(H+m*(k-t))/(1-t),
 'angle lower':ct+1-(mu+2)/(1+t),
 'angle upper':1-ct-(2*t-mu)/(1+t)
}
for name,z in tests.items():
 assert s.cancel(z)==0,(name,s.factor(z))
print('PASS: 16 independent symbolic identities')

lam,sigma,delta,c0,m2=s.symbols('lam sigma delta c0 m2',real=True)
B=-(p-1)*c0*lam**p+lam**(p-1)*(p*c0*sigma-(p-2)*m2*delta)+(p-1)*m2*lam**(p-2)*sigma*delta
Bp=-(p-1)*lam**(p-3)*(lam-sigma)*(p*c0*lam+(p-2)*m2*delta)
assert s.simplify(s.powsimp(s.expand((s.diff(B,lam)-Bp)*lam**(3-p)),force=True))==0
assert s.simplify(s.powsimp(B.subs(lam,sigma)-sigma**(p-1)*(c0*sigma+m2*delta),force=True))==0
print('PASS: global Burkholder envelope derivative and contact')

counts={1:0,2:0,3:0}
rng=Random(7643)
for _ in range(100000):
 pp=Q(rng.randint(21,100),10)
 tt=Q(rng.randint(-990,990),1000)
 HH=Q(rng.randint(1,1000),1000)
 mm=Q(rng.randint(-1200,1200),200)
 CC=pp*HH-2*tt*mm
 if CC<0:continue
 kk=(pp-2)/pp
 left=HH+mm*(-kk-tt)
 right=HH+mm*(kk-tt)
 if left<0:
  counts[1]+=1
  assert mm>0 and tt> -kk
  phix=pp*HH+(1-tt)*mm
  assert phix>0
  cc=phix/(1+tt)
  gam=2*CC/(1+tt)
  alph=cc*tt-(pp-1)*HH
  mmu=-(pp-1)*gam/((pp-2)*cc)
  assert alph<0 and -2<=mmu<=2*tt
 elif right<0:
  counts[2]+=1
  assert mm<0 and tt<kk
 else:
  counts[3]+=1
  assert HH-tt*mm>=kk*abs(mm)
assert sum(counts.values())==76915,counts
print('PASS: exact rational case constraints',counts)
