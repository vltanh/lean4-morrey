#!/usr/bin/env python3
"""Joint energy/positive-filling MILP. Floating discovery, exact candidate repair.

No solver bound is used as a mathematical certificate. All selected triangles
must project positively; a degree-one boundary then gives an actual graph.
The energy search uses a finite rational dictionary of LH square factors.
"""
import argparse, json, itertools, math, time
from fractions import Fraction as Q
from collections import defaultdict
from pathlib import Path
import numpy as np
from scipy.optimize import milp, linprog, Bounds, LinearConstraint
from scipy.sparse import coo_matrix
from integer_filling_exact import rat, wedge_half, mixed, det, graph, edge_add

Z=(0,)*9

def add(p,q,c=Q(1)):
    p=p.copy()
    for e,v in q.items():
        p[e]=p.get(e,Q(0))+c*v
    return {e:v for e,v in p.items() if v}

def mul(p,q):
    r=defaultdict(Q)
    for e,v in p.items():
        for f,w in q.items():
            r[tuple(a+b for a,b in zip(e,f))]+=v*w
    return {e:v for e,v in r.items() if v}

def var(i,n=9):
    return tuple(int(j==i) for j in range(n))

def exps(n,k):
    if n==1:
        yield (k,)
    else:
        for i in range(k+1):
            for tail in exps(n-1,k-i): yield (i,)+tail

def lh(alpha,degree=4):
    r=defaultdict(Q)
    for i in range(4):
        for j in range(4):
            c=alpha[i]*(alpha[j]-(i==j))
            if c:
                e=[degree-sum(alpha),*alpha,0,0,0,0]
                e[1+i]-=1;e[1+j]-=1
                e[5+i//2]+=1;e[5+j//2]+=1
                e[7+i%2]+=1;e[7+j%2]+=1
                r[tuple(e)]+=c
    return dict(r)

def lh_poly(P,degree=4):
    r={}
    for a,c in P.items(): r=add(r,lh(a,degree),c)
    return r

def value(P,X):
    return sum(c*math.prod(x**k for x,k in zip(X,a)) for a,c in P.items())

def encode(P):
    return [{'exponents':list(e),'coefficient':str(v)} for e,v in sorted(P.items()) if v]

def decode(P,n):
    r=defaultdict(Q)
    for x in P:
        e=tuple(x['exponents'])
        if len(e)!=n or any(type(i)!=int or i<0 for i in e): raise ValueError('bad monomial')
        r[e]+=rat(x['coefficient'])
    return {e:v for e,v in r.items() if v}

def dictionary(extra=True):
    """Rational square factors at degree four, direct LH-SOS.

    Pair dictionary plus the sharp P2 squares and all independent signed
    row/column permutations, and transpose. Rational factors, exact matching.
    """
    basis=[]
    for i in range(5):
        for j in range(2):
            for k in range(2):
                e=[0]*9;e[i]=e[5+j]=e[7+k]=1
                basis.append(tuple(e))
    keys=set();fac=[]
    def insert(d):
        d={e:Q(v) for e,v in d.items() if v}
        if not d:return
        # Normalise by leading coefficient: square factor sign/scale irrelevant.
        c=d[min(d)];d={e:v/c for e,v in d.items()}
        key=tuple(sorted(d.items()))
        if key not in keys:keys.add(key);fac.append(d)
    for e in basis:insert({e:1})
    for i,j in itertools.combinations(range(len(basis)),2):
        for s in [-1,1]:
            insert({basis[i]:1,basis[j]:s})
    if extra:
        # P2 factors after substitution H_ij=u_i v_j; list (A_entry,H_entry,coefficient).
        terms=[[(3,0,1),(2,1,-2),(1,2,-2)],[(0,3,1),(2,1,-2),(1,2,-2)],
               [(3,1,1),(1,3,1)],[(3,1,1),(1,3,-1)],
               [(3,2,1),(2,3,1)],[(3,2,1),(2,3,-1)],
               [(3,3,1),(2,2,1),(1,1,1)],[(3,3,1)],[(2,2,1)],[(1,1,1)],
               [(0,0,1),(1,1,1),(2,2,1),(3,3,1)]]
        for rp in itertools.permutations(range(2)):
            for cp in itertools.permutations(range(2)):
                for tr in [False,True]:
                    for rs in itertools.product([-1,1],repeat=2):
                        for cs in itertools.product([-1,1],repeat=2):
                            def perm(i):
                                r,c=divmod(i,2)
                                if tr:r,c=c,r
                                return 2*rp[r]+cp[c],rs[r]*cs[c]
                            for t in terms:
                                d=defaultdict(Q)
                                for i,j,c in t:
                                    I,s=perm(i);J,h=perm(j)
                                    d[basis[4*(I+1)+J]]+=c*s*h
                                insert(d)
        # Include translated P2 factors. Translation in one coordinate of A
        # adds t*H terms; these permit cubic terms in the integrand.
        for t in terms[:7]:
            for i0 in range(4):
                for shift in [-1,1]:
                    d=defaultdict(Q)
                    for i,j,c in t:
                        d[basis[4*(i+1)+j]]+=c
                        if i==i0:d[basis[j]]+=c*shift
                    insert(d)
    return fac

def triangles(data):
    V=[tuple(map(rat,v)) for v in data['vertices']]
    if len(set(V))!=len(V) or any(len(v)!=4 for v in V): raise ValueError('invalid vertices')
    A=tuple(map(rat,data.get('base',[0,0,0,0])))
    if A!=(Q(0),)*4: raise ValueError('translate to zero base before this experiment')
    ids=[V.index(graph(A,y)) for y in ((Q(0),Q(0)),(Q(1),Q(0)),(Q(1),Q(1)),(Q(0),Q(1)))]
    if any(not(0<=v[0]<=1 and 0<=v[1]<=1) for v in V):raise ValueError('projection outside square')
    bd=defaultdict(int)
    for i,j in zip(ids,ids[1:]+ids[:1]):edge_add(bd,i,j,1)
    ts=[];R=rat(data.get('gradient_bound','1'))
    for i,j,k in itertools.combinations(range(len(V)),3):
        xi=wedge_half(V[i],V[j],V[k])
        if not xi[0]:continue
        if xi[0]<0:j,k=k,j;xi=tuple(-v for v in xi)
        X=tuple(v/xi[0] for v in mixed(xi))
        if sum(v*v for v in X)>R*R:continue
        ts.append(((i,j,k),xi[0],X))
    return V,ids,bd,ts

class Rows:
    def __init__(self):self.i=[];self.j=[];self.v=[];self.lo=[];self.hi=[];self.exact=[]
    def row(self,terms,lo=-np.inf,hi=np.inf):
        idx=len(self.lo)
        self.exact.append(({j:Q(v) for j,v in terms.items() if v},None if lo==-np.inf else Q(lo),None if hi==np.inf else Q(hi)))
        for j,v in terms.items():
            if v:self.i.append(idx);self.j.append(j);self.v.append(float(v))
        self.lo.append(float(lo));self.hi.append(float(hi))
    def mat(self,n):return coo_matrix((self.v,(self.i,self.j)),shape=(len(self.lo),n)).tocsc()

def model(data):
    V,ids,bd,ts=triangles(data)
    # Remove affine and determinant gauge by excluding the ad monomial;
    # any quadratic ad coefficient can be transferred to bc with det.
    alphas=[a for d in range(2,5) for a in exps(4,d) if a!=(1,0,0,1)]
    factors=dictionary(extra=True)
    sq=[mul(q,q) for q in factors]
    h=[lh(a) for a in alphas]
    E=sorted(set().union(*(p.keys() for p in h+sq)))
    idx={e:i for i,e in enumerate(E)}
    nP=len(alphas);nQ=len(factors);nT=len(ts);nV=len(V)
    # coefficient c=p+-p-, nonnegative square weights, face indicators,
    # one height choice per projection, face cost epigraphs.
    cp=0;cm=nP;wt=2*nP;ft=wt+nQ;ht=ft+nT;ct=ht+nV;n=ct+nT
    rows=Rows();match=[{} for e in E]
    for j,p in enumerate(h):
        for e,v in p.items():match[idx[e]][cp+j]=v;match[idx[e]][cm+j]=-v
    for j,p in enumerate(sq):
        for e,v in p.items():match[idx[e]][wt+j]=-v
    for r in match:rows.row(r,0,0)
    rows.row({j:1 for j in range(2*nP)},hi=1)
    rows.row({wt+j:sum(v*v for v in f.values()) for j,f in enumerate(factors)},hi=1)
    edge=defaultdict(dict)
    area={};moments=[{} for _ in range(5)]
    for j,((a,b,c),ar,X) in enumerate(ts):
        for i,k,s in [(b,c,1),(a,c,-1),(a,b,1)]:
            if i>k:i,k,s=k,i,-s
            edge[i,k][ft+j]=s
        area[ft+j]=ar
        for i,v in enumerate((*X,det(X))):moments[i][ft+j]=ar*v
    for e in sorted(set(edge)|set(bd)):rows.row(edge.get(e,{}),bd[e],bd[e])
    rows.row(area,1,1)
    for r in moments:rows.row(r,0,0)
    groups=defaultdict(list)
    for i,v in enumerate(V):groups[v[:2]].append(i)
    for g in groups.values():rows.row({ht+i:1 for i in g},hi=1)
    bounds_cost=[]
    for j,(t,ar,X) in enumerate(ts):
        for i in t:rows.row({ft+j:1,ht+i:-1},hi=0)
        vals=[ar*math.prod(x**k for x,k in zip(X,a)) for a in alphas]
        M=max(map(abs,vals),default=Q(0))  # l1 coefficient budget
        bounds_cost.append(M)
        terms={ct+j:1,ft+j:-M}
        for k,v in enumerate(vals):
            terms[cp+k]=-v;terms[cm+k]=v
        rows.row(terms,lo=-M)
        rows.row({ct+j:1,ft+j:M},lo=0)
    # At most 2P-6 triangles: planar triangulation with four boundary vertices.
    rows.row({ft+j:1 for j in range(nT)},hi=2*len(groups)-6)
    lo_exact=[Q(0)]*ct+[-M for M in bounds_cost]
    hi_exact=[Q(1)]*ct+bounds_cost
    for i in ids:lo_exact[ht+i]=Q(1)
    lb=np.array(list(map(float,lo_exact)));ub=np.array(list(map(float,hi_exact)))
    # At boundary corner the zero-height graph vertex is selected.
    for i in ids:lb[ht+i]=1
    objective=np.zeros(n);objective[ct:]=1
    integrality=np.zeros(n);integrality[ft:ct]=1
    return dict(V=V,ids=ids,bd=bd,ts=ts,alphas=alphas,factors=factors,h=h,sq=sq,E=E,
                nP=nP,nQ=nQ,nT=nT,nV=nV,cp=cp,cm=cm,wt=wt,ft=ft,ht=ht,ct=ct,n=n,
                rows=rows,lb=lb,ub=ub,objective=objective,integrality=integrality,
                lo_exact=lo_exact,hi_exact=hi_exact)

def exact_repair(P,weighted_factors,margin=Q(1,10**10)):
    r=lh_poly(P)
    for w,q in weighted_factors:
        if w<0:raise ValueError('negative square weight')
        r=add(r,mul(q,q),-w)
    err=sum(map(abs,r.values()),Q(0))
    # Qrad=|X|^2/2+|X|^4/4; LH >= Nx Nu Nv on product spheres.
    norm={tuple(2*int(j==i) for j in range(4)):Q(1) for i in range(4)}
    radial=add({e:v/2 for e,v in norm.items()},mul(norm,norm),Q(1,4))
    Pfix=add(P,radial,err+margin)
    return Pfix,err

def check_boundary(data,faces):
    V=[tuple(map(rat,v)) for v in data['vertices']]
    if len(set(V))!=len(V) or any(len(v)!=4 or not(0<=v[0]<=1 and 0<=v[1]<=1) for v in V):raise ValueError('invalid vertices')
    if tuple(map(rat,data.get('base',[0,0,0,0])))!=(Q(0),)*4:raise ValueError('nonzero base')
    ids=[V.index(graph((Q(0),)*4,y)) for y in ((Q(0),Q(0)),(Q(1),Q(0)),(Q(1),Q(1)),(Q(0),Q(1)))]
    bd=defaultdict(int)
    for i,j in zip(ids,ids[1:]+ids[:1]):edge_add(bd,i,j,1)
    actual=defaultdict(int);tot=[Q(0)]*6;law=[]
    used=set()
    for t in faces:
        if len(t)!=3 or len(set(t))!=3 or any(type(i)!=int or not 0<=i<len(V) for i in t):raise ValueError('invalid face')
        i,j,k=t
        key=tuple(sorted(t))
        if key in used:raise ValueError('duplicate face')
        used.add(key)
        xi=wedge_half(V[i],V[j],V[k]);a=xi[0]
        if a<=0:raise ValueError('nonpositive projection')
        X=tuple(x/a for x in mixed(xi))
        R=rat(data.get('gradient_bound','1'))
        if sum(x*x for x in X)>R*R:raise ValueError('gradient bound violated')
        for u,v,s in [(j,k,1),(i,k,-1),(i,j,1)]:edge_add(actual,u,v,s)
        tot=[s+x for s,x in zip(tot,xi)];law.append((a,X))
    if {e:v for e,v in actual.items() if v}!={e:v for e,v in bd.items() if v}:raise ValueError('exact boundary mismatch')
    if tuple(tot)!=(Q(1),Q(0),Q(0),Q(0),Q(0),Q(0)):raise ValueError('bivector mean mismatch')
    # Exact incidence + nonnegative degree-one projection is the proof of
    # compatibility; no floating point matrix-law inference is used.
    return law

def check_certificate(data):
    P=decode(data['polynomial'],4)
    if any(sum(a)>4 for a in P):raise ValueError('degree >4')
    weighted=[(rat(s['weight']),decode(s['factor'],9)) for s in data['squares']]
    for w,q in weighted:
        if w<0 or any((sum(e[:5]),sum(e[5:7]),sum(e[7:9]))!=(1,1,1) for e in q):raise ValueError('bad LH factor')
    margin=rat(data['margin'])
    if margin<=0:raise ValueError('margin must be positive')
    Pfix,err=exact_repair(P,weighted,margin)
    law=check_boundary(data,data['faces'])
    g=sum(a*value(Pfix,X) for a,X in law)-value(Pfix,(Q(0),)*4)
    raw=sum(a*value(P,X) for a,X in law)-value(P,(Q(0),)*4)
    return {'faces':len(law),'raw_exact_gap':str(raw),'repair':str(err+margin),
            'repaired_exact_gap':str(g),'strict_negative':g<0,
            'global_rc':'exact rational residual bound plus radial repair',
            'compatibility':'positive integer filling with exact degree-one boundary'}

def solve(data,seconds=20):
    m=model(data);rows=m['rows'];n=m['n'];t=time.monotonic()
    res=milp(m['objective'],integrality=m['integrality'],bounds=Bounds(m['lb'],m['ub']),constraints=LinearConstraint(rows.mat(n),rows.lo,rows.hi),options={'time_limit':seconds,'mip_rel_gap':0.0})
    report={'vertices':m['nV'],'projected_vertices':len({v[:2] for v in m['V']}),
        'triangles':m['nT'],'polynomial_coefficients':m['nP'],'square_factors':m['nQ'],
        'variables':n,'constraints':len(rows.lo),'seconds_limit':seconds,'wall_seconds':time.monotonic()-t,
        'solver_status':int(res.status),'solver_message':res.message,
        'objective':None if res.fun is None else float(res.fun),'mip_dual_bound':getattr(res,'mip_dual_bound',None),
        'mip_gap':getattr(res,'mip_gap',None),'mip_nodes':getattr(res,'mip_node_count',None),
        'scope':'finite joint numerical search only; no positive lower-bound certificate'}
    candidate=None
    if res.x is not None:
        # Exact-check integer solution and optimize its energy over the same
        # cone with face indicators fixed (linear subproblem).
        faces=[list(m['ts'][i][0]) for i,v in enumerate(res.x[m['ft']:m['ht']]) if round(v)]
        try:law=check_boundary(data,faces)
        except ValueError as exc:report['candidate_rejected']=str(exc);return report,None
        obj=np.array([float(sum(a*math.prod(x**k for x,k in zip(X,e)) for a,X in law)) for e in m['alphas']])
        nP,nQ=m['nP'],m['nQ'];A=np.zeros((len(m['E']),2*nP+nQ));idx={e:i for i,e in enumerate(m['E'])}
        for j,p in enumerate(m['h']):
            for e,v in p.items():A[idx[e],j]=float(v);A[idx[e],nP+j]=-float(v)
        for j,p in enumerate(m['sq']):
            for e,v in p.items():A[idx[e],2*nP+j]=-float(v)
        ub=np.zeros((2,2*nP+nQ));ub[0,:2*nP]=1;ub[1,2*nP:]=[float(sum(v*v for v in f.values())) for f in m['factors']]
        l=linprog(np.concatenate([obj,-obj,np.zeros(nQ)]),A_eq=A,b_eq=np.zeros(len(idx)),A_ub=ub,b_ub=[1,1],bounds=(0,None),method='highs')
        report['fixed_chain_LP_status']=int(l.status);report['fixed_chain_LP_objective']=None if l.fun is None else float(l.fun)
        if l.x is not None:
            den=10**10
            P={e:Q(round((l.x[j]-l.x[nP+j])*den),den) for j,e in enumerate(m['alphas'])}
            weights=[Q(round(max(0,v)*den),den) for v in l.x[2*nP:]]
            candidate=dict(data);candidate.update(faces=faces,polynomial=encode(P),squares=[{'weight':str(w),'factor':encode(q)} for w,q in zip(weights,m['factors']) if w],margin='1/10000000000')
            report['exact_candidate']=check_certificate(candidate)
    return report,candidate

def make_input(case):
    V=[[0,0,0,0],[1,0,0,0],[1,1,0,0],[0,1,0,0]]
    if case=='small':
        # Two interior nodes, three states each; variable triangulation.
        locs=[('1/3','1/3'),('2/3','2/3')];heights=[[(0,0),('1/12',0),(0,'1/12')],[(0,0),('-1/12','1/12'),('1/12','-1/12')]]
    elif case=='four':
        locs=[('1/4','1/4'),('3/4','1/4'),('3/4','3/4'),('1/4','3/4')]
        heights=[[(0,0),('1/8','1/16'),('-1/8','-1/16')],[(0,0),('1/16','-1/8'),('-1/16','1/8')],[(0,0),('-1/8','1/8'),('1/8','-1/8')],[(0,0),('1/8','1/8'),('-1/8','-1/8')]]
    else:raise ValueError('unknown case')
    for y,h in zip(locs,heights):V.extend([list(y)+list(w) for w in h])
    return {'base':[0,0,0,0],'vertices':V,'gradient_bound':'1','case':case}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--case',choices=['small','four']);p.add_argument('--input',type=Path);p.add_argument('--verify',type=Path);p.add_argument('--seconds',type=float,default=20);p.add_argument('--output',type=Path);p.add_argument('--candidate',type=Path)
    a=p.parse_args()
    if a.verify:print(json.dumps(check_certificate(json.loads(a.verify.read_text())),indent=2));raise SystemExit
    data=json.loads(a.input.read_text()) if a.input else make_input(a.case or 'small')
    r,c=solve(data,a.seconds)
    s=json.dumps(r,indent=2)+'\n';print(s)
    if a.output:a.output.write_text(s)
    if a.candidate and c:a.candidate.write_text(json.dumps(c,indent=2)+'\n')
