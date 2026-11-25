"""Exact checks for the spectral-tail identity (not a proof of general Morrey)."""
from fractions import Fraction as Q
import sympy as S
r,s,t,q,e=S.symbols('r s t q e', positive=True)
# Truncated log generator, plus orientation.
expr=S.integrate((s-r)*(r+t)/r,(r,e,s))
starter=e*(s-t)-e**2/2+(S.log(e)+1)*s*t
# SymPy's log(s/e) branch is safe because s,e>0.
assert S.simplify(S.expand_log(starter+expr-s**2/2-s*t*S.log(s),force=True))==0
# Signed quartic plus quadratic, in diagonal coordinates.
s,t=S.symbols('s t',real=True)
f=(s*s+t*t)**2-S.Rational(9,4)*(s*s+t*t)*s*t+(s*s+t*t)
tau=S.symbols('tau',real=True)
V=S.diff(f,t).subs(t,tau*s); U=f.subs(t,tau*s)-tau*s*V
assert S.expand(S.diff(U,s,2)-(S.diff(f,s,2).subs(t,tau*s)-tau**2*S.diff(f,t,2).subs(t,tau*s)-tau*s*S.diff(V,s,2)))==0
# An actual rank-one two-step laminate: independent changes of the two diagonal entries.
# Verify exact integrated tail identity at every base and at ray contact.
count=0
for a,b in [(Q(0),Q(0)),(Q(2),Q(0)),(Q(2),Q(1)),(Q(2),Q(-1)),(Q(1),Q(1))]:
  for h,k in [(Q(1),Q(2)),(Q(3,2),Q(1,2)),(Q(2),Q(2))]:
    atoms=[]
    for i in (-1,1):
      for j in (-1,1):
        x=a+i*h; y=b+j*k
        ss=max(abs(x),abs(y)); tt=x*y/ss if ss else Q(0)
        atoms.append((ss,tt,Q(1,4)))
    s0=max(abs(a),abs(b));t0=a*b/s0 if s0 else Q(0)
    tau0=t0/s0 if s0 else Q(0)
    assert sum(w*ss*tt for ss,tt,w in atoms)==s0*t0
    u=U.subs(tau,tau0);v=V.subs(tau,tau0)
    knots=sorted({Q(0),s0,*[ss for ss,tt,w in atoms]})
    tail=0
    for lo,hi in zip(knots,knots[1:]):
      mid=(lo+hi)/2
      n=sum(w*(ss-s) for ss,tt,w in atoms if ss>mid)-((s0-s) if s0>mid else 0)
      z=sum(w*tt*(ss-s) for ss,tt,w in atoms if ss>mid)-(t0*(s0-s) if s0>mid else 0)
      tail+=S.integrate(S.diff(u,s,2)*n+S.diff(v,s,2)*z,(s,lo,hi))
    F=lambda ss,tt:f.subs({s:ss,t:tt})
    rem=sum(w*(F(ss,tt)-u.subs(s,ss)-tt*v.subs(s,ss)) for ss,tt,w in atoms)
    gap=sum(w*F(ss,tt) for ss,tt,w in atoms)-F(s0,t0)
    assert S.simplify(gap-tail-rem)==0
    count+=1
print('Exact truncated-log identity and moving-ray derivative identity passed.')
print(f'{count} exact full-moment integrated tail identities passed at signed, rank-deficient and conformal bases.')
