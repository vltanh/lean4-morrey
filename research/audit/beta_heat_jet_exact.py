#!/usr/bin/env python3
"""Exact controls for the stronger second-jet relaxation, NOT a gradient witness."""
from itertools import product, permutations
from fractions import Fraction as Q
import sympy as s

I=s.eye(2)
C=s.Matrix([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])
T=s.Matrix([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]])
H=(4*T+C)/5
assert H.eigenvals()=={s.Integer(1):1,s.Rational(3,5):2,-s.Rational(3,5):1}
a,b,c,d=s.symbols('a b c d',real=True)
r=s.Matrix([a*c,a*d,b*c,b*d])
assert s.expand((r.T*H*r)[0]-s.Rational(4,5)*(a*c+b*d)**2)==0
assert s.expand((r.T*r)[0]-(a*c+b*d)**2-(a*d-b*c)**2)==0

base=[(s.zeros(4),[I/2,s.zeros(2)]),
      (H,[s.diag(0,1),s.Matrix([[0,-s.Rational(1,2)],[-s.Rational(1,2),0]])])]

def vec(X): return s.Matrix(list(X))
def mat(v): return s.Matrix(2,2,list(v))
def dot(x,y): return (x.T*y)[0]
def signed_perms():
    for p in permutations(range(2)):
        for signs in product((-1,1),repeat=2):
            R=s.zeros(2)
            for i in range(2): R[i,p[i]]=signs[i]
            yield R

def Bvec(B,i,j): return s.Matrix([b[i,j] for b in B])
def DX(B,k): return vec(s.Matrix(2,2,lambda a,i:B[a][i,k]))
def contractions(H,B):
    g=s.Matrix([s.trace(b) for b in B])
    M=sum((dot(DX(B,k),H*DX(B,k)) for k in range(2)),s.Integer(0))
    S=sum((H[2*a+i,2*b+j]*g[a]*B[b][i,j]
           for a,b,i,j in product(range(2),repeat=4)),s.Integer(0))
    return S,M,sum(s.trace(b*b) for b in B),dot(g,g)

assert contractions(*base[0])==(0,0,s.Rational(1,2),1)
assert contractions(*base[1])==(-s.Rational(2,5),-s.Rational(2,5),s.Rational(3,2),1)
# At the saturation state of the earlier -1/8 estimate (before the
# determinant adjustment and scaling), the two stress actions disagree.
assert contractions(T,base[1][1])==(-s.Rational(1,2),-s.Rational(3,4),s.Rational(3,2),1)

states=[]
for H0,B0 in base:
    for L,R in product(signed_perms(),repeat=2):
        O=s.Matrix.hstack(*[vec(L*mat(s.eye(4)[:,k])*R.T) for k in range(4)])
        B=[sum((L[a,b]*R*B0[b]*R.T for b in range(2)),s.zeros(2)) for a in range(2)]
        states.append((O*H0*O.T,B))
assert len(states)==128
N=len(states)
mean=lambda values:sum(values,s.Integer(0))/N
for k,expected in enumerate((-s.Rational(1,5),-s.Rational(1,5),1,1)):
    assert mean(contractions(H,B)[k] for H,B in states)==expected
# All constant-coefficient quadratic Hessian compatibility identities.
for a,b,i,j,k,l in product(range(2),repeat=6):
    assert mean(B[a][i,j]*B[b][k,l]-B[a][i,k]*B[b][j,l] for H,B in states)==0
# All weighted integration-by-parts identities with constant target
# matrices E_ab and spatial indices k,l.  E_ab span all target maps.
for a,b,k,l in product(range(2),repeat=4):
    L=s.zeros(2);L[a,b]=1
    def discrepancy(H,B):
        left=dot(vec(L*mat(DX(B,l))), H*DX(B,k))
        v=L*Bvec(B,k,l)
        right=sum(H[2*c+i,2*d+j]*v[c]*B[d][i,j] for c,d,i,j in product(range(2),repeat=4))
        return left-right
    assert mean(discrepancy(H,B) for H,B in states)==0
print('128 exact states: local RC, Hessian bound, all 64 componentwise quadratic identities and 16 weighted heat identities checked.')
print('Average signed heat cost = -1/5, trace energy = 1; relative relaxation cost = -1/10.')
print('Not an actual gradient field or a single constitutive integrand.')
# Constants used in the analytic optional quantitative strictness proof.
eta=Q(1,10**16); eps=Q(1,10**36)
assert 512*eps < eta**2
assert 128*eta**2 < Q(1,256)
assert 170*eta**2+65*eta<66*eta
assert 66*256<17000
assert 34000*eta+128*eta**2<35000*eta
assert 70000*eta < Q(1,10**5)**2
assert 2*10**9*eta**2+Q(1,10**5) < Q(2,10**5)
assert Q(4,10**5) < Q(7,1000)**2
assert Q(7,1000)+Q(6,10**5)+128*eta**2<Q(8,1000)
assert Q(3,4)*(Q(1,27)-Q(1,100))*eps>Q(1,10**38)
print('Rational near-equality stability and strictness budgets passed.')
