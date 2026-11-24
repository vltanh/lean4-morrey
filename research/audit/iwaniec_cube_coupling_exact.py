"""Exact finite checks for the random-cube density identity (not a Morrey proof)."""
from fractions import Fraction as Q
from itertools import product, combinations
from collections import defaultdict
from math import prod


def subsets(n):
    return [s for k in range(n+1) for s in combinations(range(n), k)]


def reconstruction():
    # Four coordinates, nonuniform nonbinary marginals, overlapping interactions.
    n = 4
    mu = ((Q(1,3),Q(2,3)),(Q(1,4),Q(1,4),Q(1,2)),
          (Q(1,2),Q(1,2)),(Q(1,3),Q(2,3)))
    states = [range(len(m)) for m in mu]
    a = ((Q(1),Q(-1,2)),(Q(1),Q(-1),Q(0)),
         (Q(1),Q(-1)),(Q(1),Q(-1,2)))
    assert all(sum(m*x for m,x in zip(mi,ai)) == 0 for mi,ai in zip(mu,a))
    S = [s for s in subsets(n) if len(s)>=3]
    active = ((0,1,2),(0,1,3),(0,2,3),(0,1,2,3))
    eps = Q(1,512)
    def g(s,x):
        d=dict(zip(s,x))
        return eps*sum(prod(a[i][d[i]] for i in t) for t in active if set(t)<=set(s))
    # Relative density is 1+g(full,x). Verify all marginals and norm.
    full=tuple(range(n)); xs=list(product(*states))
    mass={x:prod(mu[i][x[i]] for i in full)*(1+g(full,x)) for x in xs}
    assert sum(mass.values())==1
    assert max(abs(g(full,x)) for x in xs)<=Q(1,2*(3**n-2*n*n-1))
    for s in subsets(n):
        marg=defaultdict(Q)
        for x,w in mass.items(): marg[tuple(x[i] for i in s)]+=w
        for x,w in marg.items():
            assert w==prod(mu[i][xi] for i,xi in zip(s,x))*(1+g(s,x))
            if len(s)<=2: assert g(s,x)==0
    out=defaultdict(Q); eall=list(product((0,1),repeat=n))
    # pairs are sampled iid in each coordinate, independently across coordinates
    for pairs in product(*(list(product(st,repeat=2)) for st in states)):
        w=prod(mu[i][p[0]]*mu[i][p[1]] for i,p in enumerate(pairs))
        rho={s:sum((-1)**sum(e)*g(s,tuple(pairs[i][j] for i,j in zip(s,e)))
                   for e in product((0,1),repeat=len(s))) for s in S}
        assert sum(map(abs,rho.values()))<=Q(1,2)
        for e in eall:
            prob=(1+sum(r*(-1)**sum(e[i] for i in s) for s,r in rho.items()))/2**n
            assert prob>=0
            out[tuple(pairs[i][e[i]] for i in full)]+=w*prob
    assert dict(out)==mass
    print('nonbinary nonuniform four-coordinate density: exact reconstruction, local parity budget, all pair marginals passed')


def sign(t): return 1 if t%1<Q(1,2) else -1


def grid_controls():
    # Check exact discrepancy estimates at moderate parameter sizes; no search for counterexamples.
    D=101; L=(1,7,23); m=len(L)
    for phases in ((Q(0),Q(0),Q(0)),(Q(1,7),Q(2,9),Q(3,11)),(Q(1,2),Q(1,5),Q(2,3))):
        cuts={Q(0),Q(1)}
        for l,c in zip(L,phases):
            for j in range(-2,2*l+3):
                t=(Q(j,2)-c)/l
                if 0<t<1: cuts.add(t)
        cuts=sorted(cuts); cont=defaultdict(Q); grid=defaultdict(Q)
        def pat(t): return tuple(sign(l*t+c) for l,c in zip(L,phases))
        for a,b in zip(cuts,cuts[1:]): cont[pat((a+b)/2)]+=b-a
        for j in range(D): grid[pat(Q(j,D))]+=Q(1,D)
        assert max(abs(cont[e]-grid[e]) for e in product((-1,1),repeat=m))<=Q(1+2*sum(L),D)
        # Conditional grid residues unchanged by adding even multiples of D.
        for j,k in product(range(10),repeat=2):
            for l,c in zip(L,phases):
                assert sign(Q((2*D+l)*j+(2*D+1)*k,D)+c)==sign(Q(l*j+k,D)+c)
    print('three exact phase controls: interval/grid discrepancy and comparable-frequency residue lift passed')


def parameter_controls():
    # Construct arbitrary-size families by arithmetic; no huge grid enumeration needed.
    for m in (1,2,5,20,100):
        n=m+2; B=3**n-2*n*n-1; eta=Q(1,2*B*2**m)
        L=[1]
        for _ in range(1,m):
            J=1+2*sum(L); x=int(4*J/eta)+1
            L.append(x if x%2 else x+1)
            assert Q(J,L[-1])<=eta/4
        J=1+2*sum(L); D=int(2*J/eta)+1; D+=1-D%2
        assert D%2 and Q(J,D)<=eta/2 and max(L)<D
        K=[(2*D+l,2*D+1) for l in L]
        assert all(a%2==b%2==1 and a*a+b*b<25*D*D for a,b in K)
        assert len(set(K))==m
    print('parameter inequalities verified through 102 variables (exact integer arithmetic)')


if __name__=='__main__':
    reconstruction(); grid_controls(); parameter_controls()
