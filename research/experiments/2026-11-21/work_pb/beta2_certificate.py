"""Exact symbolic check: P_beta is rank-one convex iff beta >= 2.

Sufficiency: use rank-one H=[[BC/D,B],[C,D]] with D!=0. Completing
one square gives (1/2)D²P_2(M)[H,H]=(aD-2(cB+bC))² + yᵀK y/D²,
y=(b,c,d), with K below. Sylvester's criterion applies because all
three leading minors have strictly positive coefficients in squares
(and D!=0). Rank-one H with D!=0 are dense in the rank-one cone, so
continuity covers D=0. Adding (beta-2)(b²+c²+d²)² is convex.

Necessity: explicit matrices M_t,H_t below have det H_t=0 and LH/2
=(2 beta-4)t⁴+(12 beta+4)t²+12 beta+26 beta/t², negative for large t
when beta<2. The script verifies every polynomial identity exactly.
"""
import sympy as s

a,b,c,d,A,B,C,D,beta,t=s.symbols('a b c d A B C D beta t',real=True)
x=s.Matrix([a,b,c,d]);h=s.Matrix([A,B,C,D]);g=a*d-2*b*c;r=b*b+c*c+d*d
P=g*g+beta*r*r
lh=(h.T*s.hessian(P,x)*h)[0]/2
K=s.Matrix([[4*D**2*(3*B**2+C**2+D**2),10*B*C*D**2,-2*B*C**2*D+8*B*D**3],
 [10*B*C*D**2,4*D**2*(B**2+3*C**2+D**2),-2*B**2*C*D+8*C*D**3],
 [-2*B*C**2*D+8*B*D**3,-2*B**2*C*D+8*C*D**3,B**2*C**2+4*D**2*(B**2+C**2+3*D**2)]])
y=s.Matrix([b,c,d]);rhs=(a*D-2*(c*B+b*C))**2+(y.T*K*y)[0]/D**2
assert s.cancel(lh.subs({A:B*C/D,beta:2})-rhs)==0
mins=[s.factor(K[:k,:k].det()) for k in (1,2,3)]
expected=[
 4*D**2*(3*B**2+C**2+D**2),
 4*D**4*(12*B**4+15*B**2*C**2+16*B**2*D**2+12*C**4+16*C**2*D**2+4*D**4),
 12*D**4*(16*B**6*D**2+9*B**4*C**4+56*B**4*C**2*D**2+48*B**4*D**4+56*B**2*C**4*D**2+104*B**2*C**2*D**4+48*B**2*D**6+16*C**6*D**2+48*C**4*D**4+48*C**2*D**6+16*D**8)]
for k,(got,want) in enumerate(zip(mins,expected),1):
 assert s.expand(got-want)==0
 pol=s.Poly(got,B,C,D)
 assert all(coef>0 and all(power%2==0 for power in mon) for mon,coef in pol.terms())
 # positive D-only monomial guarantees strict positivity when D != 0
 assert any(mon[0]==mon[1]==0 and coef>0 for mon,coef in pol.terms())
 print('Leading minor',k,'=',got)
seq={a:2*(t*t-1),b:-1/t,c:1,d:2/t,A:t**3,B:t*t,C:t,D:1}
assert s.expand((A*D-B*C).subs(seq))==0
qseq=s.expand(lh.subs(seq))
assert s.expand(qseq-((2*beta-4)*t**4+(12*beta+4)*t*t+12*beta+26*beta/t**2))==0
print('Sharpness sequence LH/2 =',qseq)
print('PASS: all exact polynomial identities. The accompanying argument proves threshold beta=2.')
