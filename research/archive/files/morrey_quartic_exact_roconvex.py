"""Exact quartic rank-one-convexity reduction and certifiable interval proof.
For homogeneous quartic P, ROC iff M(P,u⊗v) >= 0 for every projective u,v.
Four charts u=(1,s)/(s,1), v=(1,t)/(t,1), s,t in [-1,1].
A *strictly* positive M on all charts is proved by positive Bernstein coefficients
of the four leading principal minors, after recursive rational subdivision.
This is an exact-rational global certificate, not a random sampling test.
"""
import sympy as sp
from fractions import Fraction
from functools import lru_cache
from math import comb
import argparse, json, sys, itertools

a,b,c,d,s,t=sp.symbols('a b c d s t')
x=(a,b,c,d); q=a*d-b*c; r=a*a+b*b+c*c+d*d
# A nonpolyconvex but quasiconvex endpoint-interior example
# |A|^4 - 9/4 |A|^2 det A, gamma = 9/8 < 2/sqrt3.
P=sp.expand(r*r-sp.Rational(9,4)*r*q)

def matrix(P,uchart=0,vchart=0):
    u=sp.Matrix([1,s]) if uchart==0 else sp.Matrix([s,1])
    v=sp.Matrix([1,t]) if vchart==0 else sp.Matrix([t,1])
    h=sp.Matrix([u[0]*v[0],u[0]*v[1],u[1]*v[0],u[1]*v[1]])
    H_P=sp.hessian(P,x)
    # D²P(A)[H,H] quadratic in A
    V=sp.Poly(sp.expand((h.T*H_P*h)[0]),x).as_expr()
    M=sp.hessian(V,x)/2
    return sp.Matrix(4,4,lambda i,j: sp.factor(M[i,j]))

@lru_cache(maxsize=None)
def bernstein_data(expr):
    p=sp.Poly(expr,s,t,domain='QQ')
    return [((int(k[0]),int(k[1])),Fraction(int(v.numerator),int(v.denominator))) for k,v in p.terms()],tuple(map(int,p.degree_list()))

def bbound(terms,degree,rect):
    """Lower Bernstein coefficient on rectangle, exact fractions."""
    lo_s,hi_s,lo_t,hi_t=rect
    ns,nt=degree
    C=[[Fraction(0) for _ in range(nt+1)] for _ in range(ns+1)]
    ds,dt=hi_s-lo_s,hi_t-lo_t
    # transform power monomials by binomial theorem
    for (i,j),w in terms:
        for k in range(i+1):
            f=w*comb(i,k)*lo_s**(i-k)*ds**k
            for l in range(j+1):
                C[k][l]+=f*comb(j,l)*lo_t**(j-l)*dt**l
    B=[]
    for i in range(ns+1):
        for j in range(nt+1):
            B.append(sum(C[k][l]*Fraction(comb(i,k),comb(ns,k))*Fraction(comb(j,l),comb(nt,l)) for k in range(i+1) for l in range(j+1)))
    return min(B)

def verify_positive(expr,max_depth=6,max_cells=30000):
    terms,degree=bernstein_data(expr)
    queue=[(Fraction(-1),Fraction(1),Fraction(-1),Fraction(1),0)]
    done=0;maxdep=0
    while queue:
        A,B,C,D,depth=queue.pop()
        z=bbound(terms,degree,(A,B,C,D))
        if z>0:
            done+=1;maxdep=max(maxdep,depth)
            continue
        if depth>=max_depth or done+len(queue)>max_cells:
            return False, {'depth':depth,'bad_rectangle':(str(A),str(B),str(C),str(D)),'lower_bound':str(z),'cells':done}
        mid1=(A+B)/2;mid2=(C+D)/2
        queue.extend([(A,mid1,C,mid2,depth+1),(mid1,B,C,mid2,depth+1),(A,mid1,mid2,D,depth+1),(mid1,B,mid2,D,depth+1)])
    return True, {'cells':done,'max_depth':maxdep,'degree':degree}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--depth',type=int,default=5);ap.add_argument('--poly',type=str,default='dm');args=ap.parse_args()
    if args.poly=='convex':P=sp.expand(r*r)
    for ui,vi in itertools.product(range(2),repeat=2):
        M=matrix(P,ui,vi)
        print('chart',(ui,vi),'matrix entry degree',sp.Poly(M[0,0],s,t).total_degree(),flush=True)
        for j in range(1,5):
            determinant=sp.factor(M[:j,:j].det(method='berkowitz'))
            ok,meta=verify_positive(determinant,args.depth)
            print(' minor',j,('EXACT POSITIVE' if ok else 'UNVERIFIED'),meta,flush=True)
            if not ok:sys.exit(1)
    print('GLOBAL STRICT RANK-ONE CONVEXITY CERTIFIED',flush=True)
