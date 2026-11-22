#!/usr/bin/env python3
"""Exact rational verification of a compactified planar LH certificate.

Variables: (t,a,b,c,d,u0,u1,v0,v1), A=((a,b),(c,d)), H=u tensor v.
For an even degree bound D, homogenize D²f(A)[H,H] to degree D-2
in (t,A). Check h-epsilon = sum(weight*square) + sum(tau_i*g_i),
where g_i are the three unit-sphere equations and epsilon>0.

The certificate proves global RC with a coercive LH lower bound. Optionally
evaluate an exact periodic PL witness. No numerical solver is trusted here.
"""

from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json


N = 9
ZERO = (0,) * N


def rat(x):
    if not isinstance(x, (str, int)) or isinstance(x, bool):
        raise ValueError("Rationals must be integers or strings, never floats")
    return F(x)


def add(p, q, scale=F(1)):
    r = p.copy()
    for e, c in q.items():
        r[e] = r.get(e, F(0)) + scale * c
        if not r[e]:
            del r[e]
    return r


def mul(p, q):
    r = {}
    for e, c in p.items():
        for f, d in q.items():
            g = tuple(x+y for x, y in zip(e, f))
            r[g] = r.get(g, F(0)) + c*d
    return {e:c for e,c in r.items() if c}


def power(p, n):
    result={ZERO:F(1)}
    for _ in range(n):result=mul(result,p)
    return result


def homogeneous_exponents(n, degree):
    if n==1:
        yield (degree,)
    else:
        for i in range(degree+1):
            for tail in homogeneous_exponents(n-1,degree-i):yield (i,)+tail


def norm_gram_basis(degree, order):
    """Exact monomial basis for the product-norm multiplier hierarchy."""
    if degree<2 or degree%2 or order<0:
        raise ValueError('Expected even degree at least two and nonnegative order')
    return [x+u+v for x in homogeneous_exponents(5,degree//2-1+order)
            for u in homogeneous_exponents(2,1+order)
            for v in homogeneous_exponents(2,1+order)]


def variable(i):
    e = list(ZERO); e[i] = 1
    return {tuple(e):F(1)}


def parse(terms, n=N):
    p = {}
    for term in terms:
        e = tuple(term['exponents'])
        if len(e) != n or any(type(k) is not int or k < 0 for k in e):
            raise ValueError("Invalid monomial exponents")
        p[e] = p.get(e,F(0)) + rat(term['coefficient'])
    return {e:c for e,c in p.items() if c}


def encode(p):
    return [{'exponents':list(e),'coefficient':str(c)} for e,c in sorted(p.items()) if c]


def sphere_equations():
    equations = []
    for indices in (range(5), range(5,7), range(7,9)):
        p = {ZERO:F(1)}
        for i in indices:
            p = add(p,mul(variable(i),variable(i)),F(-1))
        equations.append(p)
    return equations


def homogenized_lh(f, degree):
    if type(degree) is not int or degree < 2 or degree % 2:
        raise ValueError("Degree bound must be a positive even integer at least two")
    if any(sum(e)>degree for e in f):
        raise ValueError("Integrand exceeds the degree bound")
    out = {}
    for alpha, coefficient in f.items():
        k = sum(alpha)
        for i in range(4):
            for j in range(4):
                factor = alpha[i]*(alpha[j]-(i==j))
                if not factor:
                    continue
                e = [degree-k,*alpha,0,0,0,0]
                e[1+i] -= 1; e[1+j] -= 1
                e[5+i//2] += 1; e[5+j//2] += 1
                e[7+i%2] += 1; e[7+j%2] += 1
                e = tuple(e)
                out[e] = out.get(e,F(0)) + coefficient*factor
    return {e:c for e,c in out.items() if c}


def evaluate(f, A):
    result = F(0)
    for e,c in f.items():
        term = c
        for x,k in zip(A,e): term *= x**k
        result += term
    return result


def det(A):
    return A[0]*A[3]-A[1]*A[2]


def pl_gap(f, witness):
    F0 = tuple(rat(v) for v in witness['base'])
    w = [[[rat(x) for x in value] for value in row] for row in witness['nodes']]
    k = len(w)
    if len(F0)!=4 or k<2 or any(len(row)!=k or any(len(v)!=2 for v in row) for row in w):
        raise ValueError("Expected four-entry base and a square periodic two-component nodal grid")
    gradients = []
    for i in range(k):
        for j in range(k):
            a,b,c,d = w[i][j],w[(i+1)%k][j],w[i][(j+1)%k],w[(i+1)%k][(j+1)%k]
            gradients.append(tuple(k*v for r in range(2) for v in (b[r]-a[r],c[r]-a[r])))
            gradients.append(tuple(k*v for r in range(2) for v in (d[r]-c[r],d[r]-b[r])))
    count = len(gradients)
    means = [sum(g[i] for g in gradients)/count for i in range(4)]
    mean_det = sum(det(g) for g in gradients)/count
    if any(means) or mean_det:
        raise AssertionError("Internal gradient/null-Lagrangian consistency failure")
    shifted = [tuple(a+b for a,b in zip(F0,g)) for g in gradients]
    if sum(det(g) for g in shifted)/count != det(F0):
        raise AssertionError("Shifted determinant consistency failure")
    gap = sum(evaluate(f,g) for g in shifted)/count-evaluate(f,F0)
    return {'triangles':count,'gap':str(gap),'strict_violation':gap<0,
            'mean_gradient':[str(x) for x in means],'mean_det_gradient':str(mean_det)}


def verify(data):
    if data.get('schema_version') != 1 or data.get('matrix_shape') != [2,2]:
        raise ValueError("Unsupported schema or matrix dimension")
    if data.get('variables') != ['t','a','b','c','d','u0','u1','v0','v1']:
        raise ValueError("Variable order must match the fixed certificate schema")
    f = parse(data['integrand'],4)
    epsilon = rat(data['epsilon'])
    if epsilon <= 0:
        raise ValueError("Strict sphere margin must be positive")
    h = homogenized_lh(f,data['degree_bound'])
    equations=sphere_equations()
    kind=data.get('certificate_kind','sphere_ideal')
    if kind=='sphere_ideal':
        lhs=add(h,{ZERO:epsilon},F(-1))
    elif kind=='norm_multiplier':
        order=data['multiplier_order']
        if type(order) is not int or order<0:
            raise ValueError('Multiplier order must be a nonnegative integer')
        nx,nu,nv=[add({ZERO:F(1)},g,F(-1)) for g in equations]
        norm=mul(mul(nx,nu),nv)
        margin=mul(mul(power(nx,data['degree_bound']//2-1),nu),nv)
        lhs=mul(power(norm,order),add(h,margin,-epsilon))
        if data.get('sphere_multipliers'):
            raise ValueError('Norm-multiplier certificates have no ideal multipliers')
    else:
        raise ValueError('Unknown certificate kind')
    rhs = {}
    for item in data['squares']:
        weight = rat(item['weight'])
        if weight < 0:
            raise ValueError("Square weights must be nonnegative")
        p = parse(item['polynomial'])
        rhs = add(rhs,mul(p,p),weight)
    if kind=='sphere_ideal':
        multipliers = data['sphere_multipliers']
        if len(multipliers)!=3:
            raise ValueError("Exactly three sphere-ideal multipliers are required")
        for terms,equation in zip(multipliers,equations):
            rhs = add(rhs,mul(parse(terms),equation))
    difference = add(lhs,rhs,F(-1))
    if difference:
        raise ValueError(f"Coefficient identity fails at {len(difference)} monomials")
    result = {'identity':'exact','certificate_kind':kind,'global_rank_one_convex':True,'epsilon':str(epsilon),
              'degree_bound':data['degree_bound'],
              'scope':'Coercive global Legendre-Hadamard bound; not automatically quasiconvex'}
    if 'witness' in data:
        result['periodic_pl_witness'] = pl_gap(f,data['witness'])
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',type=Path)
    args = parser.parse_args()
    raw = args.certificate.read_bytes()
    result = verify(json.loads(raw))
    result['certificate_sha256'] = hashlib.sha256(raw).hexdigest()
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
