"""Exact algebra for the spectral-shell comparison. The proof is analytic."""
from fractions import Fraction as Q
from itertools import product
import sympy as S
s,l,r=S.symbols('s l r', nonnegative=True)
expr=(s*s+l*l-r*r-(s*l)**2/r**2)/4
assert S.simplify(expr-(s*s-r*r)*(r*r-l*l)/(4*r*r))==0
assert S.simplify(expr-((s-l)**2-(r-s*l/r)**2)/4)==0
# Variance cancellation at an arbitrary base.
N,N0,E2,d0,m,M,u=S.symbols('N N0 E2 d0 m M u',real=True)
assert S.simplify(m*(E2-d0*d0)/(2*u)+m*((N-N0)-(E2-d0*d0)/u)/2-m*(N-N0)/2)==0
# Known globally RC signed quartic plus a quadratic.
a,b,c,d=S.symbols('a b c d',real=True)
J=a*d-b*c; norm=a*a+b*b+c*c+d*d
F=norm*norm-S.Rational(9,4)*norm*J+norm
sos=4*(3*(a-S.Rational(9,16)*d)**2+S.Rational(13,256)*d*d+(b+S.Rational(9,16)*c)**2+S.Rational(175,256)*c*c)+2
assert S.expand(S.diff(F,a,2)-sos)==0
# Upper bound 2+42 B^2 for all ||X||op<=B after rotating a unit rank-one direction to E11.
assert 4*(4*Q(25,16)**2+Q(13+175,256))==42

def f(a,d):
    n=a*a+d*d; j=a*d
    return n*n-Q(9,4)*n*j+n

def h(r,d):return f(r,d/r)

n=0
for s in [Q(i,4) for i in range(9)]:
  for t in [s*Q(j,4) for j in range(-4,5)]:
    for r in [Q(i,4) for i in range(1,13)]:
      d=s*t; ell=abs(t)
      q=(s*s+ell*ell-r*r-d*d/(r*r))/4
      assert (q>=0)==(ell<=r<=s)
      B=max(Q(2),r,4/r); m=Q(2); M=2+42*B*B
      lo=2*m*max(q,0)-2*M*max(-q,0)
      hi=2*M*max(q,0)-2*m*max(-q,0)
      assert lo<=f(s,t)-h(r,d)<=hi,(s,t,r,q)
      n+=1
print('Symbolic spectral gap, variance cancellation and rank-one Hessian bounds passed.')
print(f'{n} exact rational pointwise shell comparisons passed.')
# General minors-compatible laws, with all weights rational.
laws=[
 (((Q(1),Q(0))),[(Q(1),Q(1),Q(1,2)),(Q(1),Q(-1),Q(1,2))]),
 (((Q(0),Q(0))),[(Q(1),Q(1),Q(1,52)),(Q(-1),Q(-1),Q(1,52)),(Q(1,5),Q(-1,5),Q(25,52)),(Q(-1,5),Q(1,5),Q(25,52))]),
 (((Q(1),Q(0))),[(Q(1,2),Q(1,2),Q(4,7)),(Q(5,4),Q(-5,4),Q(16,49)),(Q(3),Q(3),Q(1,14)),(Q(3),Q(-3),Q(3,98))]),
]
n=0
for A,law in laws:
    assert sum(w for a,b,w in law)==1
    assert sum(w*a for a,b,w in law)==A[0]
    assert sum(w*b for a,b,w in law)==A[1]
    d0=A[0]*A[1]; assert sum(w*a*b for a,b,w in law)==d0
    var=sum(w*((a-A[0])**2+(b-A[1])**2) for a,b,w in law)
    gap=sum(w*f(a,b) for a,b,w in law)-f(*A)
    R=max(max(abs(a),abs(b)) for a,b,w in law)
    for r in [Q(i,4) for i in range(1,17)]:
        B=max(R,r,R*R/r); m=Q(2); M=2+42*B*B
        loss=sum(w*max(0,r*r+(a*b/r)**2-a*a-b*b) for a,b,w in law)
        loss+=max(0,A[0]**2+A[1]**2-r*r-(d0/r)**2)
        assert gap>=m*var/2-(M-m)*loss/2
        n+=1
print(f'{n} exact full-moment Jensen bounds passed, including nonpolyconvex test laws.')
