"""Symbolic identities and exact piecewise-characteristic controls.

Requires sympy. The analytic proof is not replaced by these controls.
"""
import sympy as S

p,t,H,m,j,s,ts,ms = S.symbols('p t H m j s ts ms', real=True)
C=p*H-2*t*m


def zero(expr):
    assert S.cancel(expr)==0, S.factor(expr)


for e in (-1,1):  # -1 subquadratic, +1 superquadratic
    a=e*(p-2)/p
    c=(e*p*H+(1-e*t)*m)/(1+e*t)
    v=2*C/(1+e*t)
    alpha=c*t-(p-1)*H
    r=(1-e*t)/2
    g=H-(t+a)*m
    ode=p*g/(t+e)  # s dm/ds
    zero(alpha+v*r+c*t-H)
    zero(c-e*v/2-m)
    zero(alpha+v/2-(H-t*m))
    zero(p*alpha+(p-1)*v*r+(p-2)*c*t)
    zero((p-1)*m+ode-c)
    zero(p*(H-t*m)-t*ode-e*((p-2)*m+ode))
    rprime=(1-e*t-e*s*ts)/2
    dprime=2*s*t+s*s*ts
    zero(dprime+e*2*s*rprime-s*(t+e))

print('Both regimes: 14 exact symbolic jet, ODE, intercept and monotonicity identities passed.')

# Exact kink controls: h agrees with b(a+t) at the kink, and m evolves
# within its subgradient interval toward b.
for p0,t0,b,e in [
    (S.Rational(3,2),-S.Rational(256,625),S.Rational(1200,143),-1),
    (S.Integer(4),S.Rational(1,2),S.Integer(1),1),
]:
    a0=e*(p0-2)/p0
    H0=b*(a0+t0)
    mc=p0*H0/(2*t0)  # determinant-only branch entry slope
    assert (mc<b if e==-1 else mc>b)
    lam=p0*(t0+a0)/(t0+e)
    assert lam>0
    R=S.Symbol('R', positive=True)
    M=R**(p0-1)*(b+(mc-b)*R**(-lam))
    assert S.simplify(S.diff(M,R).subs(R,1)-mc)==0
    # e M'' = R^(p-3) e (A+B R^-lam).
    # Nonnegative for EVERY R>=1, by checking endpoints of R^-lam in [0,1].
    A=b*(p0-1)*(p0-2)
    B=(mc-b)*(p0-1-lam)*(p0-2-lam)
    assert e*A>=0 and e*(A+B)>=0
    print('Kink control:',p0,'ratio',t0,'entry slope',mc,
          'limiting slope',b,'lambda',lam,'weight coefficients',e*A,e*B)
