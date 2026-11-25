#!/usr/bin/env python3
"""Exact signed-sheet and graph-minor algebra controls; not a Morrey solver."""
import sympy as s
from fractions import Fraction as Q
from itertools import combinations

Y=s.Matrix(2,2,s.symbols('a b c d'))
V=s.Matrix(2,2,s.symbols('e f g h'))
U=Y.col_join(V)
xi={(i,j):s.det(U[[i,j],:]) for i,j in combinations(range(4),2)}
L=s.Matrix([[-xi[1,2],xi[0,2]],[-xi[1,3],xi[0,3]]])
assert all(s.expand(z)==0 for z in L-V*Y.adjugate())
assert s.expand(xi[0,1]*xi[2,3]-L.det())==0

x,t=s.symbols('x t')
a=s.symbols('a0:12')
y=s.Matrix([a[0]+a[1]*x+a[2]*t+a[3]*x*x+a[4]*x*t+a[5]*t*t,
            a[6]+a[7]*x+a[8]*t+a[9]*x*x+a[10]*x*t+a[11]*t*t])
adj=y.jacobian([x,t]).adjugate()
assert all(s.expand(s.diff(adj[0,k],x)+s.diff(adj[1,k],t))==0 for k in range(2))

# u=(2f(x),2y), f degree one, slopes 3,-1,1 on equal thirds.
def Ldiag(a,b):
    return a*b if max(abs(a),abs(b))<=1 else abs(a+b)-1
def Hdiag(a,b):
    d=a*b
    ss=max(abs(a),abs(b))
    delta=d/ss if ss else Q(0)
    return Q(1) if delta>=1 else abs(a+b)-d
pos=[(Q(1,6),Q(1,2)),(Q(1,2),Q(1,2))]
neg=(Q(-1,2),Q(1,2))
T=tuple(sum(v[j] for v in pos)-neg[j] for j in range(2))
assert T==(Q(7,6),Q(1,2))
rhs=sum(Ldiag(*v) for v in pos)+abs(sum(neg))+1
assert rhs>=Ldiag(*T)
assert Q(2,3)*pos[0][0]+Q(1,3)*T[0]==Q(1,2)
assert Q(4)*(Q(2,3)*Ldiag(*pos[0])+Q(1,3)*Ldiag(*T))==Q(10,9)
assert sum(Hdiag(Q(a),Q(2)) for a in [6,-2,2])/3==2

ss,dd=s.symbols('s delta',real=True)
E=(1-dd)*(ss-(1+dd)/2)
H=ss+dd-ss*dd
assert s.expand(E+1-H-(1-dd)**2/2)==0
assert s.expand(-2*ss*dd+1-H-(1-dd-ss*(1+dd)))==0
print('Exact mixed-minor, Piola, three-sheet signed trace (target derivative 7/6; energy bound 10/9), and flat contact identities passed.')
