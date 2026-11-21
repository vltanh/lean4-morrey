"""Independent exact verifier for a 35-element global GL(2)xGL(2) quasiconvex quartic basis.

The certificate lists invertible integer matrices L_i,R_i and coefficient vectors
for 2 W_{1/2}(L_i A R_i).  Recompute every vector with independent sympy expressions
and establish rank 35 over F_104729, hence over Q. No floating point used.
"""
import json
from pathlib import Path
import sympy as sp

j=json.loads(Path('/mnt/data/morrey_quartic_gl_basis_unimodular.json').read_text())
a,b,c,d=sp.symbols('a b c d')
A=sp.Matrix([[a,b],[c,d]])
exponents=[tuple(x) for x in j['monomial_exponents']]
assert len(exponents)==35
p=104729
vectors=[]
for i,(tr,v) in enumerate(zip(j['generators'],j['integer_vectors'])):
    L=sp.Matrix(tr['L']);R=sp.Matrix(tr['R'])
    assert abs(L.det())==1 and abs(R.det())==1, (i,'not unimodular')
    Z=L*A*R
    s=sp.expand(sum(Z[k,l]**2 for k in (0,1) for l in (0,1)))
    det=sp.expand(Z.det())
    expr=sp.Poly(sp.expand(2*s*s+4*s*det-det*det),a,b,c,d)
    recomputed=[int(expr.coeff_monomial(a**x[0]*b**x[1]*c**x[2]*d**x[3])) for x in exponents]
    assert recomputed==v, (i,'polynomial mismatch')
    vectors.append(v)

# Different linear-algebra algorithm: ordinary Gaussian elimination on columns
M=[[v[i]%p for v in vectors] for i in range(35)]
rank=0;pivot_cols=[]
for col in range(35):
    pivot=next((k for k in range(rank,35) if M[k][col]!=0),None)
    if pivot is None:continue
    M[rank],M[pivot]=M[pivot],M[rank]
    t=pow(M[rank][col],-1,p)
    for idx in range(col,35):M[rank][idx]=M[rank][idx]*t%p
    for k in range(rank+1,35):
        x=M[k][col]
        if x:
            for idx in range(col,35):M[k][idx]=(M[k][idx]-x*M[rank][idx])%p
    pivot_cols.append(col)
    rank+=1
assert rank==35,(rank,pivot_cols)
# Compute a single digest of the 35x35 certificate matrix modulo p.
T=[[v[i]%p for v in vectors] for i in range(35)]
detmod=1
for col in range(35):
    pivot=next((r for r in range(col,35) if T[r][col]),None)
    assert pivot is not None
    if pivot!=col:
        T[col],T[pivot]=T[pivot],T[col]
        detmod=-detmod
    pc=T[col][col]
    detmod=detmod*pc%p
    inv=pow(pc,-1,p)
    for r in range(col+1,35):
        mult=T[r][col]*inv%p
        if mult:
            for c in range(col,35):T[r][c]=(T[r][c]-mult*T[col][c])%p
assert detmod==41797,detmod
print('35 exact sympy coefficient identities verified.')
print('All 70 change-of-variables matrices nonsingular.')
print(f'Certified rank {rank}/35 modulo {p}; det mod p = {detmod}; hence rank 35 over Q.')
print('No numeric tolerance, no optimization, no assumptions on grid size.')
