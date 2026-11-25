"""Exact global rank-one convexity / nonpolyconvexity example in R^{2x2}.

Only verifies polynomial algebra and rational witnesses. The human-readable
proof of global nonnegativity relies on Cauchy-Schwarz inequalities stated
in the accompanying research note.
"""
import sympy as sp

a,b,c,d=sp.symbols('a b c d', real=True)
A,B,C,D=sp.symbols('A B C D', real=True)
beta=sp.symbols('beta', real=True)
q=a*d-2*b*c
normsq=b*b+c*c+d*d
P=q*q+beta*normsq**2
vec=(a,b,c,d); hvec=(A,B,C,D)
hess=sp.hessian(P,vec)
halfH=sp.expand(sp.Matrix(hvec).dot(hess*sp.Matrix(hvec))/2)
L=c*B+b*C
T=a*D-2*L
S=d*A
zs=B*B+C*C+D*D
inner=b*B+c*C+d*D
rhs=sp.expand(T*T+(S-2*L)**2-4*L*L+4*b*c*B*C+beta*(2*normsq*zs+4*inner*inner))
assert sp.simplify(halfH-rhs-4*(A*D-B*C)*(a*d-b*c)) == 0
print('Exact quartic Hessian identity: PASS')

# At F=(M,0,0,1), the only minor-tangent coefficient consistent with a
# global polyconvex support is lambda=2M; see proof note.
M=sp.symbols('M', real=True)
F={a:M,b:0,c:0,d:1}
Fplus={a:M,b:1,c:1,d:1}
X=(0,1,1,0)
P_F=sp.expand(P.subs(F))
P_Fplus=sp.expand(P.subs(Fplus))
DP_F_X=sp.expand(sum(sp.diff(P,z).subs(F)*x for z,x in zip(vec,X)))
Delta=sp.expand(P_Fplus-P_F-DP_F_X)
assert sp.simplify(Delta-(-4*M+4+8*beta)) == 0
support_residual=sp.expand(Delta+2*M)  # det X=-1, lambda=2M
assert sp.simplify(support_residual-(-2*M+4+8*beta)) == 0
print('Polyconvex-support obstruction: PASS; residual =',support_residual)
assert support_residual.subs({M:20,beta:3}) == -12
print('beta=3, M=20 gives strict negative residual -12: PASS')
assert sp.simplify(sp.diff(P,a).subs(F)-2*M)==0
assert sp.simplify(P.subs({a:sp.Symbol('t'),b:0,c:0,d:0}))==0
print('Forced support coefficient from rank-one flat line: PASS')

# An entirely finite minors-compatible Jensen witness, removing any need to
# invoke supporting hyperplanes for the nonpolyconvexity conclusion.
bb=sp.Rational(1,41)
weights=(sp.Rational(1,2),bb,sp.Rational(39,82))
points=(
    (sp.Rational(20),sp.Rational(1),sp.Rational(1),sp.Rational(1)),
    (sp.Rational(-20),sp.Rational(0),sp.Rational(0),sp.Rational(0)),
    (sp.Rational(860,39),-sp.Rational(41,39),-sp.Rational(41,39),sp.Rational(41,39)),
)
fbase=(sp.Rational(20),sp.Rational(0),sp.Rational(0),sp.Rational(1))
assert sum(weights)==1
for j in range(4):
    assert sum(weights[i]*points[i][j] for i in range(3))==fbase[j]
det=lambda x: x[0]*x[3]-x[1]*x[2]
assert sum(weights[i]*det(points[i]) for i in range(3))==det(fbase)
energy=lambda v: P.subs(dict(zip(vec,v))).subs(beta,3)
gap=sp.factor(sum(weights[i]*energy(points[i]) for i in range(3))-energy(fbase))
assert gap== -sp.Rational(156317,59319)
print('Three-atom minors-compatible Jensen witness: PASS; gap =',gap)
