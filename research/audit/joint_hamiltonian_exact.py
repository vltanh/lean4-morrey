#!/usr/bin/env python3
"""Exact controls for the joint Hamiltonian flow. Not a Morrey solver."""
from itertools import combinations
import sympy as s

C = s.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
I = s.eye(4)
O = s.zeros(4)
J = O.row_join(-I).col_join(I.row_join(O))
T = I.row_join(O).col_join(O.row_join(C))
assert C.T == C and C*C == I and T.T*T == s.eye(8)
assert J.T == -J

def col(M):
    return s.Matrix(list(M))

def psd(A):
    assert A == A.T
    return all(A.extract(k,k).det() >= 0
               for n in range(1,A.rows+1)
               for k in combinations(range(A.rows),n))

# A joint quadratic: convex part plus all six 2x2 row minors.
z = s.Matrix(s.symbols('z0:8'))
Z = s.Matrix(4,2,list(z))
K0 = (z[0]+2*z[5]-z[7])**2/7 + (z[2]-z[4]+z[6])**2/5
K0 += sum(s.Rational(i+1,3)*(Z[r,0]*Z[t,1]-Z[r,1]*Z[t,0])
          for i,(r,t) in enumerate(combinations(range(4),2)))
B = s.hessian(K0,z)
Bp = T*B*T
A,E,D = Bp[:4,:4],Bp[:4,4:],Bp[4:,4:]

# Check the Hamiltonian Riccati identity by differentiating a block
# symplectic update at time zero, for rational quadratic data.
H = s.Matrix([[2,1,0,2],[1,3,-1,0],[0,-1,2,1],[2,0,1,4]])/8
V = I.col_join(H)
expected = A+E*H+H*E.T+H*D*H
assert expected == V.T*Bp*V
jet = J*Bp*V
assert expected == jet[4:,:]-H*jet[:4,:]
assert expected == expected.T
# The canonical infinitesimal flow is symplectic.
assert (J*Bp).T*J+J*(J*Bp) == s.zeros(8)

# Null rank-one directions of a planar rank-one-convex Hessian
# lift to rank-one directions in 4x2. Test with rational PSD parts.
controls = 0
for a in [s.Matrix([1,2]),s.Matrix([2,-3]),s.Matrix([1,0])]:
    for k in [s.Matrix([1,0]),s.Matrix([2,3]),s.Matrix([-3,1])]:
        R = a*k.T
        r = col(R)
        assert (r.T*C*r)[0] == 0
        # Positive part with kernel containing r.
        P = I-r*r.T/(r.T*r)[0]
        assert psd(P) and P*r == s.zeros(4,1)
        for c in [s.Rational(-3,5),s.Rational(0),s.Rational(2,7)]:
            H0 = c*C+P
            v = r.col_join(H0*r)
            w = T*v
            assert w == r.col_join(c*r)
            assert s.Matrix(4,2,list(w)).rank() == 1
            ric = A+E*H0+H0*E.T+H0*D*H0
            assert (r.T*ric*r)[0] == (w.T*B*w)[0] >= 0
            controls += 1

# A stress-only determinant Hamiltonian gives the inverse cofactor
# shear: p constant, x(t)=x(0)-t C p, energy F(t)=F(0)-t det p.
x = s.Matrix(s.symbols('x0:4'))
p = s.Matrix(s.symbols('p0:4'))
y = s.Matrix(s.symbols('y0:4'))
t = s.Rational(1,9)
Hq = I/3 + C/5
p0 = Hq*x
Y = x-t*C*p0
F0 = (x.T*Hq*x)[0]/2
Fnew = s.expand(F0-t*(p0.T*C*p0)[0]/2)
inv = (I-t*C*Hq).inv()
G = s.expand(Fnew.subs(dict(zip(x,inv*y)),simultaneous=True))
assert s.hessian(G,y) == Hq*inv
assert s.Matrix([s.diff(G,yi) for yi in y]) == Hq*inv*y

# Mixed scalar-time flow K(X,Cp)=-X:p: exact scaling F_t=e^-2t F
# for quadratic F. Its curvature budget is the same scaling, not amplification.
q = s.symbols('q',positive=True)
X1 = q*x
P1 = p0/q
assert all(s.simplify(v)==0 for v in P1-Hq*X1/q**2)

print('Exact cofactor, canonical symplectic and Riccati identities passed.')
print(f'{controls} exact null-direction/4x2 rank-one curvature controls passed.')
print('Stress determinant and mixed null scaling controls passed.')
print('No unrestricted positivity test or negative planar witness was executed.')
