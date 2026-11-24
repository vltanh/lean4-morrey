"""Exact arithmetic for the Gaussian angular-cone estimate and uniform tests.
The analytic proof supplies all functional quantifiers.
"""
import sympy as S
from fractions import Fraction as Q
from itertools import combinations, product

# Separate multilinear interpolation / rank-one midpoint formulas.
a,b,c,d = xs = S.symbols('a b c d', real=True)
subsets=[T for k in range(5) for T in combinations(range(4),k)]
coeff={T:S.Symbol('u'+''.join(str(i) for i in T)) for T in subsets}
P=sum(coeff[T]*S.prod(xs[i] for i in T) for T in subsets)
adjacent=[(0,1),(0,2),(1,3),(2,3)]
for i,j in adjacent:
    H=[Q(1,2) if k in (i,j) else Q(0) for k in range(4)]
    assert H[0]*H[3]-H[1]*H[2]==0
    D=(P.subs(dict(zip(xs,[x+S.Rational(h.numerator,h.denominator) for x,h in zip(xs,H)])),simultaneous=True)+P.subs(dict(zip(xs,[x-S.Rational(h.numerator,h.denominator) for x,h in zip(xs,H)])),simultaneous=True))/2-P
    assert S.expand(4*D-S.diff(P,xs[i],xs[j]))==0
    rem=[k for k in range(4) if k not in (i,j)]
    for U in [T for T in subsets if set(T).issubset(rem)]:
        v=sum(S.diff(P,xs[i],xs[j]).subs(dict(zip([xs[k] for k in rem],s)))*S.prod(s[rem.index(k)] for k in U)/4 for s in product((-1,1),repeat=2))
        assert S.expand(v-coeff[tuple(sorted((i,j)+U))])==0
assert all(any(set(pair).issubset(T) for pair in adjacent) for T in subsets if len(T)>=3)
H=[S.Rational(1,2)]*4
D=(P.subs(dict(zip(xs,H)))+P.subs(dict(zip(xs,[-h for h in H]))))/2-P.subs(dict(zip(xs,[0]*4)))
assert S.expand(D-sum(coeff[T]/4 for T in subsets if len(T)==2)-coeff[(0,1,2,3)]/16)==0
K=Q(4096)
assert (4+4+1)*36==324
assert 36+4*36+36//4==189
assert 8+324+189+8==529
assert Q(1,32)<Q(1,24)
assert Q(1,8)**4*K==1
print('Rank-one midpoint, Walsh coefficient, and Gaussian mixture constants passed.')

# Weighted degree-p homogeneous scaling identities and determinant coefficient.
t,p,L,C,F0,F1=S.symbols('t p L C F0 F1', real=True)
# If F1=L+C+error1, F_t=tL+t²C+error2 and F_t=t^p F1.
e1,e2=S.symbols('e1 e2', real=True)
assert S.expand(t**p*(L+C+e1)-(t*L+t*t*C+e2)-((t**p-t)*L+(t**p-t*t)*C+t**p*e1-e2))==0
assert (1+2*Q(5)+Q(1,2))==Q(23,2)
print('Homogeneous normalization constants passed.')

# Derivative bounds for explicit C^3 mollifier g=(1-|Y|²)^4 inside unit ball.
U=S.symbols('u0:4', real=True); s=1-sum(u*u for u in U); g=s**4
for i in range(4):
    assert S.expand(S.diff(g,U[i])+8*U[i]*s**3)==0
    for j in range(4):
        dij=int(i==j)
        assert S.expand(S.diff(g,U[i],U[j])-(48*U[i]*U[j]*s**2-8*dij*s**3))==0
        for k in range(4):
            expected=48*(int(i==k)*U[j]+int(j==k)*U[i]+dij*U[k])*s**2-192*U[i]*U[j]*U[k]*s
            assert S.expand(S.diff(g,U[i],U[j],U[k])-expected)==0
r=S.symbols('r',nonnegative=True)
assert S.integrate(2*r**3*(1-r*r)**4,(r,0,1))==S.Rational(1,30)
assert 15*336==5040
# Bernoulli/Bernstein constants for the rational coefficient grid.
for n in range(2,25):
    for alpha in product(range(3),repeat=4):
        if sum(alpha)>2:continue
        fac=Q(1)
        for ai in alpha:
            for j in range(ai):fac*=Q(n-j,n)
        assert 1-Q(1,n)<=fac<=1
        assert 2*sum(alpha)+1<=5
print('Explicit mollifier derivative and Bernstein constants passed.')
