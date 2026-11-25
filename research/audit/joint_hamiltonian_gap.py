#!/usr/bin/env python3
"""Exact sufficient negative-witness check for a planar Hamiltonian flow.

Input: rational polynomial energies F (2x2), K (4x2), each with a direct
rank-one Hessian SOS identity, and actual periodic rational PL nodal data.
No numerical ODE solver or sampled curvature claim is trusted.
"""
from collections import defaultdict
from fractions import Fraction as Q
from math import ceil
import argparse
import json
from pathlib import Path


def rat(x):
    if type(x) not in (int, str):
        raise ValueError('use exact integer or rational-string data')
    return Q(x)


def parse(terms, n):
    p = defaultdict(Q)
    for a in terms:
        e = tuple(a['exponents'])
        if len(e) != n or any(type(v) != int or v < 0 for v in e):
            raise ValueError('invalid polynomial exponents')
        p[e] += rat(a['coefficient'])
    return {e:c for e,c in p.items() if c}


def mul(p, q):
    r = defaultdict(Q)
    for e,c in p.items():
        for f,d in q.items():
            r[tuple(a+b for a,b in zip(e,f))] += c*d
    return {e:c for e,c in r.items() if c}


def deriv(p, i):
    r = defaultdict(Q)
    for e,c in p.items():
        if e[i]:
            f = list(e); f[i] -= 1
            r[tuple(f)] += c*e[i]
    return {e:c for e,c in r.items() if c}


def val(p, x):
    result = Q(0)
    for e,c in p.items():
        for a,k in zip(x,e): c *= a**k
        result += c
    return result


def grad(p, x):
    return tuple(val(deriv(p,i),x) for i in range(len(x)))


def norm2(x): return sum(a*a for a in x)
def dot(x,y): return sum(a*b for a,b in zip(x,y))
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def cof(x): return (x[3],-x[2],-x[1],x[0])
def det(x): return x[0]*x[3]-x[1]*x[2]


def certify_rc(spec, d):
    if spec['shape'] != [d,2]: raise ValueError('incorrect matrix shape')
    n = 2*d; m = n+d+2
    P = parse(spec['polynomial'],n)
    lhs = defaultdict(Q)
    for e,c in P.items():
        for i in range(n):
            for j in range(n):
                a = e[i]*(e[j]-(i==j))
                if not a: continue
                f = list(e)+[0]*(d+2)
                f[i] -= 1; f[j] -= 1
                f[n+i//2] += 1; f[n+j//2] += 1
                f[n+d+i%2] += 1; f[n+d+j%2] += 1
                lhs[tuple(f)] += c*a
    rhs = defaultdict(Q)
    for term in spec['squares']:
        w = rat(term['weight'])
        if w < 0: raise ValueError('negative square weight')
        S = parse(term['factor'],m)
        for e,c in mul(S,S).items(): rhs[e] += w*c
    if any(lhs[e]!=rhs[e] for e in set(lhs)|set(rhs)):
        raise ValueError('exact LH-SOS identity mismatch')
    return P


def extension_bound(P, points, dim):
    # Exact C11 extension, via the smooth maximum of P+c and a quadratic
    # barrier on radius R=2r. See the analytic theorem for the proof.
    r = max(1,ceil(max(sum(map(abs,x)) for x in points)))
    R = 2*r
    def sup(p): return sum(abs(c)*R**sum(e) for e,c in p.items())
    B0 = sup(P)
    G0 = sum(sup(deriv(P,i)) for i in range(dim))
    H0 = sum(sup(deriv(deriv(P,i),j)) for i in range(dim) for j in range(dim))
    a = (2*B0+3)/Q(3*r*r)
    M = max(H0,2*a) + (G0+2*a*R)**2/2
    return M


def law(witness):
    A = tuple(map(rat,witness['base']))
    w = [[tuple(map(rat,p)) for p in row] for row in witness['nodes']]
    k = len(w)
    if len(A)!=4 or k<2 or any(len(row)!=k or any(len(v)!=2 for v in row) for row in w):
        raise ValueError('invalid periodic nodal witness')
    X = []
    for i in range(k):
        for j in range(k):
            a,b,c,d=w[i][j],w[(i+1)%k][j],w[i][(j+1)%k],w[(i+1)%k][(j+1)%k]
            X.append(tuple(k*v for r in range(2) for v in (b[r]-a[r],c[r]-a[r])))
            X.append(tuple(k*v for r in range(2) for v in (d[r]-c[r],d[r]-b[r])))
    if any(sum(x[i] for x in X) for i in range(4)) or sum(map(det,X)):
        raise ValueError('periodic gradient moment check failed')
    return A,X


def verify(data):
    F = certify_rc(data['F'],2)
    K = certify_rc(data['K'],4)
    A,X = law(data['witness']); n=len(X)
    E = sum(map(norm2,X))/n
    if E<=0: raise ValueError('zero gradient variance')
    p0 = grad(F,A)
    B = A+cof(p0)
    P = [add(A,x) for x in X]
    Z = [x+cof(grad(F,x)) for x in P]
    J0 = sum(val(F,x) for x in P)/n-val(F,A)
    k0 = val(K,B); dk0=grad(K,B)
    D0 = sum(val(K,z)-k0-dot(dk0,sub(z,B)) for z in Z)/n
    M = extension_bound(F,[A,*P],4)
    N = extension_bound(K,[B,*Z],8)
    T = 1/(4*N*(1+M)); L=2*(1+M)
    error = N*N*(1+L)**3
    t = rat(data['time']) if 'time' in data else min(T,max(Q(0),-D0/(2*error*E)))
    if not 0<=t<=T: raise ValueError('time outside certified interval')
    upper = J0+t*D0+error*t*t*E
    return {'variance':str(E),'planar_gap':str(J0),'joint_bregman_gap':str(D0),
            'M':str(M),'N':str(N),'safe_time':str(T),'time':str(t),
            'certified_flow_gap_upper':str(upper),'strict_negative':upper<0,
            'scope':'sufficient rational LH-SOS and Hamiltonian witness certificate; not a positive lower bound'}


def linear_factor(i,j,d):
    # u_i v_j, in the base/row/column variables of the certificate.
    e=[0]*(3*d+2);e[2*d+i]=e[2*d+d+j]=1
    return [{'exponents':e,'coefficient':'1'}]


def control():
    # F=det + |X|^2/4, K(X,Cp)=-X:p (a mixed minor null Lagrangian).
    from copy import deepcopy
    F={'shape':[2,2],'polynomial':[], 'squares':[]}
    for i in range(4):
        e=[0]*4;e[i]=2
        F['polynomial'].append({'exponents':e,'coefficient':'1/4'})
        F['squares'].append({'weight':'1/2','factor':linear_factor(i//2,i%2,2)})
    for i,j,c in [(0,3,'1'),(1,2,'-1')]:
        e=[0]*4;e[i]=e[j]=1
        F['polynomial'].append({'exponents':e,'coefficient':c})
    K={'shape':[4,2],'polynomial':[],'squares':[]}
    # -X:CZ (Z is the lower 2x2 block): -x0*z3+x1*z2+x2*z1-x3*z0.
    for i,j,c in [(0,7,'-1'),(1,6,'1'),(2,5,'1'),(3,4,'-1')]:
        e=[0]*8;e[i]=e[j]=1
        K['polynomial'].append({'exponents':e,'coefficient':c})
    data={'F':F,'K':K,'witness':{'base':[0,0,0,0], 'nodes':[[[0,0],[0,0]],[[1,0],[0,1]]]}}
    r=verify(data)
    assert rat(r['planar_gap'])==rat(r['variance'])/4
    assert rat(r['joint_bregman_gap'])==-rat(r['variance'])/2
    assert not r['strict_negative']
    bad=deepcopy(data);bad['K']['polynomial'][0]['coefficient']='-2'
    try: verify(bad)
    except ValueError: pass
    else: raise AssertionError('corrupt LH identity accepted')
    print('Exact degree-one PL control: planar gap E/4, joint derivative -E/2.')
    print('The negative derivative does not pass the strict-flow criterion.')
    print('Corrupted joint LH-SOS identity rejected.')
    print(json.dumps(r,indent=2))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('certificate',nargs='?',type=Path)
    a=p.parse_args()
    if a.certificate: print(json.dumps(verify(json.loads(a.certificate.read_text())),indent=2))
    else: control()
