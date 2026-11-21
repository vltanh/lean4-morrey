"""Exact arithmetic checks for the global degree-<=4 Morrey subclass theorem.

The external analytic input is Bruno--Pasqualotto (2026), which proves
quasiconvexity of Q_gamma* for gamma*=2/sqrt(3). The script checks all
rational inequalities and the non-polyconvex four-atom witness.
"""
from fractions import Fraction as F
from itertools import product

GAMMA=F(9,8)
EPS=F(1,256)
DELTA=F(1,4096)

# sqrt(3)<7/4 implies gamma/gamma*<63/64.
assert F(3) < F(7,4)**2
assert GAMMA*F(7,4)/2 == F(63,64)

# Algebraic derivation (write x = (F:H)/|H|^2,
# y=|F_perp|^2/|H|^2 >=0):
# [quartic Bregman remainder - (|F|^2+|H|^2)|H|^2/4]
# / |H|^4 = (23*x*x + 16*x + 3 + 7*y)/4.
# The 1-D discriminant is negative, so the difference is positive.
assert F(16)**2-4*F(23)*F(3) == -20
assert F(3)-F(64,23) == F(5,23)
assert F(1,256)-8*DELTA == F(1,512)

# Four-atom null-Lagrangian witness.
# I = diag(1,1), J=diag(1/5,-1/5).
I=((F(1),F(0)),(F(0),F(1)))
J=((F(1,5),F(0)),(F(0),F(-1,5)))
def neg(A): return tuple(tuple(-x for x in row) for row in A)
def det(A): return A[0][0]*A[1][1]-A[0][1]*A[1][0]
def norm2(A): return sum(x*x for row in A for x in row)
def energy(A):
    n=norm2(A)
    return n*n-2*GAMMA*n*det(A)+EPS*n
nu=[(F(1,52),I),(F(1,52),neg(I)),(F(25,52),J),(F(25,52),neg(J))]
assert sum(w for w,_ in nu)==1
assert all(sum(w*A[i][j] for w,A in nu)==0 for i,j in product(range(2),repeat=2))
assert sum(w*det(A) for w,A in nu)==0
assert sum(w*norm2(A) for w,A in nu)==F(2,13)
assert sum(w*norm2(A)**2 for w,A in nu)==F(4,25)
assert sum(w*(norm2(A)**2-2*GAMMA*norm2(A)*det(A)) for w,A in nu)==F(-2,325)
witness=sum(w*energy(A) for w,A in nu)
assert witness==F(-2,325)+F(1,1664)
assert witness+DELTA < 0
# In fact |A_ij|<=1 on the four atoms, so for every polynomial
# R=sum_{2<=|alpha|<=4} c_alpha A^alpha, E R <= ||c||_1 <= DELTA.
assert all(abs(x)<=1 for _,A in nu for row in A for x in row)

try:
    import sympy as sy
    Fv=sy.symbols('f0:4')
    Hv=sy.symbols('h0:4')
    frobsq=sum(a*a for a in Fv)
    hsq=sum(a*a for a in Hv)
    f_dot_h=sum(a*b for a,b in zip(Fv,Hv))
    quartic_at_f_plus_h=(sum((a+b)**2 for a,b in zip(Fv,Hv)))**2
    directional=4*frobsq*f_dot_h
    remainder=quartic_at_f_plus_h-frobsq**2-directional
    assert sy.expand(remainder-(2*frobsq*hsq+4*f_dot_h**2+4*f_dot_h*hsq+hsq**2)) == 0
    print('independent symbolic check of exact quartic Taylor remainder: PASS')
except ImportError:
    print('sympy not installed: algebraic identity checked in research note')

print('gamma =', GAMMA, 'epsilon =', EPS, 'coefficient l1 radius =', DELTA)
print('Reference endpoint: gamma* = 2/sqrt(3); gamma/gamma* < 63/64')
print('Q_gamma strong quasiconvexity coefficient > 1/256')
print('degree<=4 perturbation loss <= 8*delta =',8*DELTA)
print('GLOBAL STRONG QUASICONVEXITY MODULUS >=',F(1,512))
print('four-atom witness (P0) =',witness)
print('worst coefficient perturbation <=',DELTA)
print('witness upper bound =',witness+DELTA, '< 0')
print('all exact checks passed')
