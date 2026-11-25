"""Exact algebraic checks for the rank-one-null rigidity theorem.

All theorems in the companion note have independent hand proofs for all degrees;
this program verifies key algebraic identities and finite-degree ideal checks.
Requires sympy, uses no floating-point arithmetic.
"""
from itertools import product
from math import comb
from sympy import symbols, Poly, expand, Rational, Matrix, binomial, factorial

A,B,C,D,x,y,z,w,t,e = symbols('a b c d x y z w t eps')
q=A*D-B*C
variables=(A,B,C,D)

# Exact determinant identity for both signs, used in the all-degree proof.
for sg in (1,-1):
    A0 = Matrix([[1,0],[0,0]])
    H = Matrix([[1,sg*e],[e,sg*e**2]])
    assert expand(H.det()) == 0
    assert expand((A0+t*H).det()) == sg*e**2*t

# Polynomial restrictions to the rank-one variety.
# A rank-one matrix is [[x*z, x*w],[y*z,y*w]].
sub={A:x*z,B:x*w,C:y*z,D:y*w}
assert expand(q.subs(sub,simultaneous=True)) == 0

def homogeneous_monomials(deg):
    out=[]
    for i in range(deg+1):
      for j in range(deg-i+1):
       for k in range(deg-i-j+1):
        ell=deg-i-j-k
        out.append(A**i*B**j*C**k*D**ell)
    return out

for deg in (2,3,4,6,8):
    mon=homogeneous_monomials(deg)
    # Basis in x,y,z,w with bidegree (deg,deg): dimension (deg+1)^2.
    rowpairs=list(product(range(deg+1),range(deg+1)))
    table=[]
    for m in mon:
      pm=Poly(expand(m.subs(sub,simultaneous=True)),x,y,z,w)
      dct=pm.as_dict()
      table.append([dct.get((i,deg-i,j,deg-j),0) for (i,j) in rowpairs])
    M=Matrix(table).T
    rank=M.rank()
    expected=(deg+1)**2 if deg<=1 else comb(deg+3,3)-comb(deg+1,3)
    assert rank==expected, (deg,rank,expected)
    assert len(mon)-rank== (comb(deg+1,3) if deg>=2 else 0)
    print(f'degree {deg}: restriction rank {rank}; kernel dimension {len(mon)-rank}, precisely dim(q * forms degree {deg-2})')

# Unit-circle averages of all rank-one restrictions of quartic monomials:
# E[x^(2r)y^(2s)] = (2r)!(2s)! / (4^(r+s) r! s! (r+s)!)
def circ_moment(i,j):
    if i%2 or j%2: return Rational(0)
    u,v=i//2,j//2
    return Rational(factorial(2*u)*factorial(2*v), 4**(u+v)*factorial(u)*factorial(v)*factorial(u+v))

def exposure_moment(mon):
    exps=Poly(mon,A,B,C,D).monoms()[0]
    i,j,k,h=exps
    return circ_moment(i+j,k+h)*circ_moment(i+k,j+h)

# For a composite polynomial, take the linear combination.
def L(p):
    pp=Poly(expand(p),A,B,C,D)
    return sum(c*exposure_moment(A**i*B**j*C**k*D**h)
               for (i,j,k,h),c in pp.terms())
assert L(q**2)==0
assert L((A**2+B**2+C**2+D**2)**2)==1
assert L(A**4)==Rational(9,64)
assert L(A**2*D**2)==Rational(1,64)
assert L(A*B*C*D)==Rational(1,64)
assert L(q*(A**2+B**2+C**2+D**2))==0

# Homogeneous low-degree rank-one-null polynomial possibilities.
# The exceptional polynomials are precisely q (rank-one affine), q^(2k) (rank-one convex).
for k in range(1,7):
    # On a rank-one line q(A+tH) is affine in t; x^k convex on all R iff k even or k=1 affine.
    if k==1:
        outcome='rank-one affine: any sign'
    elif k%2==0:
        outcome='rank-one convex for nonnegative coefficient'
    else:
        outcome='not rank-one convex unless zero'
    print(f'q^{k} degree {2*k}: {outcome}')
print('PASS: exact determinant, determinantal ideal, and exposed functional checks')
