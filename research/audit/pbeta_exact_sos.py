#!/usr/bin/env python3
"""Exact direct LH-SOS certificate at the sharp P_beta endpoint beta=2.

No optimizer output is used. The displayed ten squares certify rank-one
convexity directly; this is not a quasiconvexity certificate or priority claim.
"""
from pathlib import Path
import json
import sympy as s

a,b,c,d,alpha,beta,gamma,delta=s.symbols('a b c d alpha beta gamma delta')
X=s.Matrix([a,b,c,d]);H=s.Matrix([alpha,beta,gamma,delta])
P=(a*d-2*b*c)**2+2*(b*b+c*c+d*d)**2
LH=s.expand((H.T*s.hessian(P,X)*H)[0])
squares=[(2,d*alpha-2*c*beta-2*b*gamma),
         (2,a*delta-2*c*beta-2*b*gamma),
         (6,d*beta+b*delta),(2,d*beta-b*delta),
         (6,d*gamma+c*delta),(2,d*gamma-c*delta),
         (12,d*delta+c*gamma+b*beta),
         (12,d*delta),(12,c*gamma),(12,b*beta)]
SOS=s.expand(sum(w*q*q for w,q in squares))
factor=s.factor(LH-SOS)
assert s.expand(factor-8*(a*d-b*c)*(alpha*delta-beta*gamma))==0, factor
u0,u1,v0,v1=s.symbols('u0 u1 v0 v1')
rankone={alpha:u0*v0,beta:u0*v1,gamma:u1*v0,delta:u1*v1}
assert s.expand((LH-SOS).subs(rankone))==0
result={'integrand':str(P),'squares':[[w,str(q)] for w,q in squares],
        'identity_remainder':str(factor),
        'rank_one_substitution_identity':True,
        'scope':'Global rank-one convexity at beta=2; no quasiconvexity assertion; not Lean'}
Path(__file__).with_name('pbeta_exact_sos.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
